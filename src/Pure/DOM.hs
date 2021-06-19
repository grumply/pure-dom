{-# LANGUAGE CPP, OverloadedStrings, RankNTypes, ScopedTypeVariables, PatternSynonyms, ViewPatterns, MagicHash, RecordWildCards, BangPatterns, LambdaCase #-}
module Pure.DOM (inject,prebuild) where

-- from base
import Control.Concurrent (MVar,newEmptyMVar,putMVar,takeMVar,yield,forkIO)
import Control.Exception (SomeException,catch)
import Control.Monad.ST (ST,runST)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad (void,unless,join,when,(>=>),forM_)
import Data.Coerce (coerce)
import Data.Foldable (for_,traverse_)
import Data.Function (fix)
import Data.IORef (IORef,newIORef,modifyIORef',readIORef,writeIORef)
import Data.List as List (null,reverse,filter,length)
import Data.Maybe (fromJust,isJust)
import Data.STRef (STRef,newSTRef,readSTRef,modifySTRef',writeSTRef)
import Data.Traversable (for,traverse)
import Data.Typeable (Typeable)
import GHC.Exts (reallyUnsafePtrEquality#,isTrue#,unsafeCoerce#)
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

-- from containers
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map.Strict as Map (fromList,toList,insert,difference,keys,differenceWith,null,elems,mergeWithKey,mapWithKey)
import qualified Data.Set as Set (fromList,toList,insert,delete,null)

-- from pure-core
import Pure.Data.View (Pure(..),View(..),Features(..),Listener(..),Lifecycle(..),Comp(..),Target(..),getHost,setProps,queueComponentUpdate,Ref(..),ComponentPatch(..),sameTypeWitness,asProxyOf)

-- from pure-lifted
import Pure.Animation
import Pure.IdleWork
import Pure.Data.Lifted
  (
   Element(..)
  ,Node(..)
  ,Win(..)
  ,Doc(..)
  ,IsNode(..)
  ,toJSV

  -- node creation
  ,create
  ,createNS
  ,createFrag
  ,createText

  -- node insertion
  ,append
  ,insertAt
  ,insertBefore
  ,setInnerHTML

  -- node replacement
  ,replaceNode
  ,replaceText

  -- node removal
  ,removeNode
  ,removeNodeMaybe
  ,clearNode

  -- attributes
  ,setAttribute
  ,setAttributeNS
  ,removeAttribute
  ,removeAttributeNS

  -- properties
  ,setProperty
  ,removeProperty

  -- styles
  ,setStyle
  ,removeStyle

  -- events
  ,Evt(..)
  ,Options(..)
  ,stopPropagation
  ,preventDefault
  ,addEventListener
  ,removeEventListener

  -- node getters
  ,getDocument
  ,getWindow

  -- JSV reference equality
  ,same

  -- callbacks
#ifdef __GHCJS__
  ,asyncCallback1
  ,syncCallback1
  ,OnBlocked(..)
  ,releaseCallback
#endif
  )

-- from pure-queue
import Pure.Data.Queue (Queue,newQueue,arrive,collect)

-- from pure-txt
import Pure.Data.Txt (Txt)
import qualified Pure.Data.Txt as Txt (intercalate)

{-
Be careful in this module or GHC might eat your lunch.
-}

type Plan s = STRef s [IO ()]
type DiffST s a = a -> a -> a -> ST s a
type Removals s = STRef s [View]

newPlan :: ST s (Plan s)
newPlan = newSTRef []

{-# INLINE buildPlan #-}
buildPlan :: (forall s. Plan s -> Plan s -> ST s a) -> ([IO ()],[IO ()],a)
buildPlan f = runST $ do
  p  <- newPlan
  p' <- newPlan
  a  <- f p p'
  p  <- readSTRef p
  p' <- readSTRef p'
  return (p,p',a)

{-# INLINE amendPlan #-}
amendPlan :: Plan s -> IO () -> ST s ()
amendPlan plan f = modifySTRef' plan (f:)

{-# INLINE runPlan #-}
runPlan :: [IO ()] -> IO ()
runPlan = go
  where
    {-# NOINLINE go #-}
    go = go'

    {-# INLINE go' #-}
    go' [] = pure ()
    go' (x:xs) = do
      go xs
      x

{-# INLINE sync #-}
sync :: (MVar () -> IO a) -> IO ()
sync f = do
  barrier <- newEmptyMVar
  f barrier
  takeMVar barrier

yield_ :: IO ()
yield_ =
#ifndef RENDER_SYNC
  yield
#else
  return ()
#endif

-- | Given a host node and a View, build and embed the View.
{-# INLINE inject #-}
inject :: IsNode e => e -> View -> IO ()
inject host v = do
  mtd <- newIORef []
  build mtd (Just $ toNode host) v
  runPlan =<< readIORef mtd

-- | Pre-build a view for later use.
{-# INLINE prebuild #-}
prebuild :: View -> IO View
prebuild v = do
  mtd <- newIORef []
  !v' <- build mtd Nothing v
  runPlan =<< readIORef mtd
  pure (Prebuilt v')

{-# NOINLINE build #-}
build :: IORef [IO ()] -> Maybe Node -> View -> IO View
build = build'

{-# INLINE build' #-}
build' :: IORef [IO ()] -> Maybe Node -> View -> IO View
build' mtd = start
  where
    {-# NOINLINE start #-}
    start = start'

    {-# INLINE start' #-}
    start' mparent = go
      where
        {-# NOINLINE go #-}
        go = go'

        {-# INLINE go' #-}
        go' o@(Prebuilt v) = 
          case mparent of
            Nothing -> pure (Prebuilt v)
            Just p  -> do
              case getHost v of
                Just h -> do
                  append p h
                  pure o 
                Nothing -> 
                  error "Pure.DOM.build': Invalid Prebuilt View. No host node found."
        go' o@HTMLView {..} = do
          e <- create tag
          let n = Just (toNode e)
          fs <- setFeatures mtd e features
          cs <- traverse (start n) children
          for_ mparent (`append` e)
          return o 
            { elementHost = Just e
            , features = fs
            , children = cs 
            }
        go' (SomeView r) = go (view r)
        go' o@(ComponentView witness _ comp props) = do
          stq_   <- newIORef . Just =<< newQueue
          props_ <- newIORef props
          state_ <- newIORef undefined
          live_  <- newIORef undefined
          c_     <- newIORef undefined
          let cr = Ref live_ props_ state_ c_ stq_
              c  = comp cr
          writeIORef c_ c
          state1 <- construct c
          writeIORef state_ state1
          state2 <- mount c state1
          writeIORef state_ state2
          let new = render c props state2
          live <- go new
          writeIORef live_ live
          modifyIORef' mtd (mounted c:)
          addIdleWork $ void $ forkIO $ newComponentThread cr c live new props state2
          -- GHC doesn't allow for record update of a ComponentView here
          return (ComponentView witness (Just cr) comp props)
        go' (LazyView f a) = go (f a)
        go' TaggedView{..} = go taggedView
        go' o@TextView {..} = do
          tn <- createText content
          for_ mparent (`append` tn)
          pure o { textHost = Just tn }
        go' o@NullView{} = do
          e <- create "template"
          for_ mparent (`append` e)
          pure o { elementHost = Just e } 
        go' o@RawView {..} = do
          e <- create tag
          setInnerHTML e content
          fs <- setFeatures mtd e features
          for_ mparent (`append` e)
          return o 
            { elementHost = Just e
            , features = fs
            }
        go' o@KHTMLView {..} = do
          e <- create tag
          let n = Just (toNode e)
          fs <- setFeatures mtd e features
          cs <- traverse (traverse (start n)) keyedChildren
          for_ mparent (`append` e)
          return o
            { elementHost = Just e
            , features = fs
            , keyedChildren = cs
            }
        go' o@SVGView {..} = do
          e <- createNS "http://www.w3.org/2000/svg" tag
          let n = Just (toNode e)
          setXLinks e xlinks
          fs <- setFeatures mtd e features
          cs <- traverse (start n) children
          for_ mparent (`append` e)
          return o 
            { elementHost = Just e
            , features = fs 
            , children = cs
            }
        go' o@KSVGView {..} = do
          e <- createNS "http://www.w3.org/2000/svg" tag
          let n = Just (toNode e)
          setXLinks e xlinks
          fs <- setFeatures mtd e features
          cs <- traverse (traverse (start n)) keyedChildren
          for_ mparent (`append` e)
          return o
            { elementHost = Just e
            , features = fs
            , keyedChildren = cs
            }
        go' o@PortalView{..} = do
          e <- create "template"
          v <- start (Just $ toNode portalDestination) portalView
          for_ mparent (`append` e)
          return o
            { portalProxy = Just e
            , portalView = v
            }

setXLinks :: Element -> Map Txt Txt -> IO ()
setXLinks e = traverse_ (uncurry (setAttributeNS e "http://www.w3.org/1999/xlink")) . Map.toList

setFeatures :: IORef [IO ()] -> Element -> Features -> IO Features
setFeatures mtd e = go
  where
    go fs@Features_ {..} = do
      setClasses e classes
      setStyles e styles
      setAttributes e attributes
      setProperties e properties
      for_ lifecycles (addLifecycle mtd e)
      ls <- for listeners (addListener e)
      pure fs { listeners = ls }

setClasses :: Element -> Set Txt -> IO ()
setClasses e cs
  | Set.null cs = return ()
  | otherwise   = setClasses' e cs

setClasses' :: Element -> Set Txt -> IO ()
setClasses' e = setAttribute e "class" . Txt.intercalate " " . Set.toList . Set.delete ""

setStyles :: Element -> Map Txt Txt -> IO ()
setStyles e ss
  | Map.null ss = return ()
  | otherwise = setStyles' e ss

setStyles' :: Element -> Map Txt Txt -> IO ()
setStyles' e = traverse_ (uncurry (setStyle e)) . Map.toList

setAttributes :: Element -> Map Txt Txt -> IO ()
setAttributes e as
  | Map.null as = return ()
  | otherwise = setAttributes' e as

setAttributes' :: Element -> Map Txt Txt -> IO ()
setAttributes' e = traverse_ (uncurry (setAttribute e)) . Map.toList

setProperties :: Element -> Map Txt Txt -> IO ()
setProperties e ps
  | Map.null ps = return ()
  | otherwise = setProperties' e ps

setProperties' :: Element -> Map Txt Txt -> IO ()
setProperties' e = traverse_ (uncurry (setProperty e)) . Map.toList

addListener :: Element -> Listener -> IO Listener
addListener e f@(On n t o a _) = do
#ifdef __GHCJS__
    target <- case t of
                ElementTarget  -> return (toJSV e)
                WindowTarget   -> fmap toJSV getWindow
                DocumentTarget -> fmap toJSV getDocument
    stopper <- do

      stopper <- newIORef undefined

      let stpr = join $ readIORef stopper

      if not (asynchronous o) then do

        cb <- syncCallback1 ContinueAsync $ \jsv -> do
          when (preventDef o) (preventDefault jsv)
          when (stopProp o) (stopPropagation jsv)
          a (Evt jsv (toJSV e) stpr)
        
        writeIORef stopper $ do
          removeEventListener target n cb
          releaseCallback cb

        addEventListener target n cb (passive o)

      else do
        cb <- asyncCallback1 $ \jsv -> a (Evt jsv (toJSV e) stpr)

        writeIORef stopper $ do
          removeEventListener target n cb
          releaseCallback cb

        addEventListener target n cb (passive o)

        when (preventDef o || stopProp o) $ do
          cb' <- syncCallback1 ContinueAsync $ \jsv -> do
            when (preventDef o) (preventDefault jsv)
            when (stopProp o) (stopPropagation jsv)
          addEventListener target n cb' True
          modifyIORef' stopper $ \original -> do
            original
            removeEventListener target n cb'
            releaseCallback cb'

      return stpr

    return f { eventStopper = stopper }
#else
    return f
#endif

addLifecycle :: IORef [IO ()] -> Element -> Lifecycle -> IO Lifecycle
addLifecycle mtd e hr@(HostRef w) = do
  modifyIORef' mtd ((w (toNode e)):)
  return hr { withHost = w }

awaitComponentPatches pq = do
  mpq <- readIORef pq
  for mpq collect `catch` \(_ :: SomeException) -> return Nothing

{-# NOINLINE newComponentThread #-}
newComponentThread :: forall props state. Ref props state -> Comp props state -> View -> View -> props -> state -> IO ()
newComponentThread ref@Ref {..} comp@Comp {..} = \live view props state -> 
  executing state >>= \st -> loop (not $ isTrue# (reallyUnsafePtrEquality# state st)) live view props st
  where
    {-# NOINLINE loop' #-}
    loop' :: Bool -> View -> View -> props -> state -> IO ()
    loop' = loop

    {-# INLINE loop #-}
    loop :: Bool -> View -> View -> props -> state -> IO ()
    loop !first !old !mid props state = do
      mps <- if first then pure (Just []) else awaitComponentPatches crPatchQueue
      forM_ mps (go props state [])
      where
        {-# NOINLINE go' #-}
        go' :: props -> state -> [(IO (),IO (),IO ())] -> [ComponentPatch props state] -> IO ()
        go' = go

        {-# INLINE go #-}
        go :: props -> state -> [(IO (),IO (),IO ())] -> [ComponentPatch props state] -> IO ()
        go newProps newState = go1
          where
            go1 :: [(IO (),IO (),IO ())] -> [ComponentPatch props state] -> IO ()
            go1 acc [] = do
              let (wills,dids,after) = unzip3 (List.reverse acc)

              sequence_ wills

              mtd <- newIORef []

              let
                sameProps = isTrue# (reallyUnsafePtrEquality# props newProps)
                sameState = isTrue# (reallyUnsafePtrEquality# state newState)

                !new
                  | first = render props state
                  | sameProps && sameState = mid
                  | sameProps = render props newState
                  | sameState = render newProps state
                  | otherwise = render newProps newState

                sameView = isTrue# (reallyUnsafePtrEquality# mid new)

                (plan,plan',new_old)
                  | first || not sameView = buildPlan $ \p p' -> diffDeferred mtd p p' old mid new
                  | otherwise = ([],[],old)

                hasAnimations = not (List.null plan)
                hasIdleWork   = not (List.null plan')

              mounts <- plan `seq` plan' `seq` readIORef mtd

              if hasAnimations && hasIdleWork then do
                let !a = runPlan plan
                    !i = runPlan plan'
                sync $ \barrier ->
                  addAnimationsReverse
                    [ putMVar barrier ()
                    , void (addIdleWork i)
                    , writeIORef crView new_old
                    , a
                    ]

              else do

                when hasAnimations $ do
                  let !a = runPlan plan

                  sync $ \barrier ->
                    addAnimationsReverse
                      [ putMVar barrier ()
                      , writeIORef crView new_old
                      , a
                      ]

                when hasIdleWork $ void $ do
                  let !i = runPlan plan'
                  addIdleWork i

              runPlan mounts

              sequence_ dids

              sequence_ after

              loop' False new_old new newProps newState


            go1 acc (cp:cps) =
              case cp of
                Unmount mv mtd -> do

                  unmounted

                  writeIORef crPatchQueue Nothing

                  let
                    (plan,plan',res) =

                      buildPlan $ \plan plan' ->
                        maybe
                          (amendPlan plan' (cleanup old))
                          (void . replaceDeferred plan plan' old)
                          mv

                    hasAnimations = not (List.null plan)
                    hasIdleWork = not (List.null plan')

                  if hasAnimations && hasIdleWork
                    then do
                      let !a = runPlan plan
                          !i = runPlan plan'
                      sync $ \barrier ->
                        addAnimationsReverse
                          [ putMVar barrier ()
                          , void (addIdleWork i) 
                          , a
                          ]

                    else do

                      when hasAnimations $ do
                        let !a = runPlan plan

                        sync $ \barrier ->
                          addAnimationsReverse
                            [ putMVar barrier ()
                            , a
                            ]

                      when hasIdleWork $ void $ do
                        let !i = runPlan plan'
                        addIdleWork i

                  writeIORef crProps (error "ask: Component invalidated.")
                  writeIORef crState (error "get: Component invalidated.")
                  writeIORef crView  (error "look: Component invalidated.")
                  mtd

                UpdateProperties newProps' -> do

                  newState'    <- receive newProps' newState
                  shouldUpdate <- force   newProps' newState'

                  let
                    writeRefs = do
                      writeIORef crProps newProps'
                      writeIORef crState newState'

                  if shouldUpdate || not (List.null acc) then

                    let
                      will = update  newProps' newState'
                      did  = updated newProps  newState
                      acts = (will >> writeRefs,did,return ())
                    in
                      go' newProps' newState' (acts : acc) cps

                  else do

                    writeRefs
                    go' newProps' newState' acc cps

                UpdateState f -> do

                  (newState',after) <- f newProps newState
                  shouldUpdate      <- force newProps newState'

                  let writeRef = writeIORef crState newState'

                  if shouldUpdate || not (List.null acc) then

                    let
                      will = update  newProps newState'
                      did  = updated newProps newState
                      acts = (will >> writeRef,did,after)
                    in
                      go' newProps newState' (acts : acc) cps

                  else do

                    writeRef
                    go' newProps newState' acc cps

cleanupListener :: Listener -> IO ()
cleanupListener (On _ _ _ _ stp) = stp

{-# NOINLINE cleanup' #-}
cleanup' :: View -> IO ()
cleanup' = cleanup

{-# INLINE cleanup #-}
cleanup :: View -> IO ()
cleanup RawView {..} =
  for_ (listeners features) cleanupListener
cleanup HTMLView {..} = do
  for_ (listeners features) cleanupListener
  for_ children cleanup'
cleanup SVGView {..} = do
  for_ (listeners features) cleanupListener
  for_ children cleanup'
cleanup ComponentView {..} = do
  for_ record (\r -> queueComponentUpdate r (Unmount Nothing (return ())))
cleanup PortalView {..} = do
  for_ (getHost portalView) (addAnimation . removeNodeMaybe)
  cleanup' portalView
cleanup KHTMLView {..} = do
  for_ (listeners features) cleanupListener
  for_ keyedChildren (cleanup' . snd)
cleanup KSVGView {..} = do
  for_ (listeners features) cleanupListener
  for_ keyedChildren (cleanup' . snd)
cleanup Prebuilt {..} = do
  cleanup' prebuilt
cleanup _ = return ()

{-# NOINLINE diffDeferred #-}
diffDeferred :: forall s. IORef [IO ()] -> Plan s -> Plan s -> View -> View -> View -> ST s View
diffDeferred = diffDeferred'

{-# INLINE diffDeferred' #-}
diffDeferred' :: forall s. IORef [IO ()] -> Plan s -> Plan s -> View -> View -> View -> ST s View
diffDeferred' mounted plan plan' old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> 
      let
          replace = do
            new' <- unsafeIOToST (build mounted Nothing new)
            replaceDeferred plan plan' old new'

          sameTag = 
            let 
              !t1 = tag mid
              !t2 = tag new
             in 
              isTrue# (reallyUnsafePtrEquality# t1 t2)
          cmpTag = sameTag || tag mid == tag new
      in
        case (mid,new) of
          (Prebuilt pb,Prebuilt pb') -> 
            diffDeferred mounted plan plan' old pb pb'

          (LazyView f a,LazyView f' a')
            |  isTrue# (unsafeCoerce# reallyUnsafePtrEquality# a a') 
            -> return old
            | otherwise -> 
              diffDeferred mounted plan plan' old (f a) (f' a')

          (TaggedView t v,TaggedView t' v')
            | sameTypeWitness t t' -> 
              diffDeferred mounted plan plan' old v v'

          (ComponentView t _ v p,ComponentView t' _ v' p')
            | ComponentView _ (Just r0) _ _ <- old 
            , sameTypeWitness t t' ->
              case unsafeCoerce# reallyUnsafePtrEquality# p p' of
                1# -> return old
                _  -> do
                      let r = unsafeCoerce# r0
                      unsafeIOToST $ setProps r p'
                      -- GHC doesn't allow for record update of a ComponentView here
                      return (ComponentView t' (Just r) v' p')

          (ComponentView _ _ _ _,_)
            | ComponentView _ (Just r0) _ _ <- old -> do
              new' <- unsafeIOToST (build mounted Nothing new)
              amendPlan plan $ do
                old <- readIORef (crView r0)
                replaceNode (fromJust $ getHost old) (fromJust $ getHost new')
                void $ queueComponentUpdate r0 (Unmount Nothing (pure ()))
              return new'

          (HTMLView{},HTMLView{})
            | cmpTag -> diffElementDeferred mounted plan plan' old mid new
            | otherwise -> replace

          (TextView _ t,TextView _ t')
            | isTrue# (reallyUnsafePtrEquality# t t') || t == t' -> return old
            | otherwise -> replaceTextContentDeferred plan old new

          (NullView{},NullView{}) -> return old

          (RawView{},RawView{}) 
            | cmpTag
            , isTrue# (reallyUnsafePtrEquality# (content mid) (content new)) -> do
              fs <- diffFeaturesDeferred' (coerce $ fromJust $ getHost old) plan (features old) (features mid) (features new)
              return old { features = fs }
            | otherwise -> replace

          (SomeView m,SomeView n)
            | isTrue# (unsafeCoerce# reallyUnsafePtrEquality# m n) -> return old
            | otherwise -> diffDeferred mounted plan plan' old (view m) (view n)

          (SVGView{},SVGView{})
            | cmpTag -> diffSVGElementDeferred mounted plan plan' old mid new
            | otherwise -> replace

          (KHTMLView{},KHTMLView{})
            | cmpTag -> diffKeyedElementDeferred mounted plan plan' old mid new
            | otherwise -> replace

          (KSVGView{},KSVGView{})
            | cmpTag -> diffSVGKeyedElementDeferred mounted plan plan' old mid new
            | otherwise -> replace

          (PortalView{},PortalView{})
            | same (toJSV (portalDestination old)) (toJSV (portalDestination new)) -> do
              v <- diffDeferred mounted plan plan' (portalView old) (portalView mid) (portalView new)
              return old { portalView = v }
            | otherwise -> do
              built@(getHost -> Just h) <- unsafeIOToST (build mounted Nothing (portalView new))
              amendPlan plan' (cleanup old)
              amendPlan plan $ do
                for_ (getHost (portalView old)) removeNode
                append (toNode $ portalDestination new) h
              -- Recycling the portalProxy. Might lose some reference equality here?
              return (PortalView (portalProxy old) (portalDestination new) built)

          (_,PortalView{}) -> do
            proxy <- unsafeIOToST (build mounted Nothing (NullView Nothing))
            replaceDeferred plan plan' old proxy
            built@(getHost -> Just h) <- unsafeIOToST (build mounted Nothing (portalView new))
            amendPlan plan $ append (toNode $ portalDestination new) h
            return (PortalView (fmap coerce $ getHost proxy) (portalDestination new) built)

          (PortalView{},_) -> do
            amendPlan plan' (cleanup old)
            amendPlan plan $ for_ (getHost (portalView old)) removeNode
            replace

          _ -> replace

diffElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

diffSVGElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffSVGElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

{-# INLINE diffFeaturesDeferred #-}
diffFeaturesDeferred :: Element -> Plan s -> DiffST s Features
diffFeaturesDeferred e plan old !mid !new = do
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> diffFeaturesDeferred' e plan old mid new

{-# NOINLINE diffFeaturesDeferred' #-}
diffFeaturesDeferred' :: Element -> Plan s -> DiffST s Features
diffFeaturesDeferred' e plan old mid new = do
  diffClassesDeferred    e plan (classes mid) (classes new)
  diffStylesDeferred     e plan (styles mid) (styles new)
  diffAttributesDeferred e plan (attributes mid) (attributes new)
  diffPropertiesDeferred e plan (properties mid) (properties new)
  ls <- diffListenersDeferred e plan (listeners old) (listeners mid) (listeners new)
  diffLifecyclesDeferred e plan (lifecycles old) (lifecycles mid) (lifecycles new)
  return old { listeners = ls }

{-# INLINE diffXLinksDeferred #-}
diffXLinksDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffXLinksDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffXLinksDeferred' e p mid new

diffXLinksDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffXLinksDeferred' e p mid new = do
  let r = diffXLinkMaps mid new
  amendPlan p $! sequence_ (fmap ($ e) r)

diffXLinkMaps :: Map Txt Txt -> Map Txt Txt -> Map Txt (Element -> IO ())
diffXLinkMaps = Map.mergeWithKey diff remove add
  where
      diff nm val1 val2 
        | b <- isTrue# (reallyUnsafePtrEquality# val1 val2) 
        , c <- val1 == val2 
        , b || c
        = Nothing
        | otherwise = Just $ \e -> setAttributeNS e "http://www.w3.org/1999/xlink" nm val2
      remove = Map.mapWithKey (\k _ -> (\e -> removeAttributeNS e "http://www.w3.org/1999/xlink" k))
      add = Map.mapWithKey (\k v -> \e -> setAttributeNS e "http://www.w3.org/1999/xlink" k v)

{-# INLINE diffClassesDeferred #-}
diffClassesDeferred :: Element -> Plan s -> Set Txt -> Set Txt -> ST s ()
diffClassesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffClassesDeferred' e p mid new

diffClassesDeferred' :: Element -> Plan s -> Set Txt -> Set Txt -> ST s ()
diffClassesDeferred' e p mid new
  | Set.null mid && Set.null new = return ()
  | Set.null new = amendPlan p (removeAttribute e "class")
  | otherwise =
    let cs = Txt.intercalate " " $ Set.toList $ Set.delete "" new
    in amendPlan p (setAttribute e "class" cs)

{-# INLINE diffStylesDeferred #-}
diffStylesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffStylesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffStylesDeferred' e p mid new

diffStylesDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffStylesDeferred' e p mid new = do
  let r = diffStyleMaps mid new
  amendPlan p $! sequence_ (fmap ($ e) r)

diffStyleMaps :: Map Txt Txt -> Map Txt Txt -> Map Txt (Element -> IO ())
diffStyleMaps = Map.mergeWithKey diff remove add
  where
      diff nm val1 val2 
        | b <- isTrue# (reallyUnsafePtrEquality# val1 val2) 
        , c <- val1 == val2 
        , b || c
        = Nothing
        | otherwise = Just $ \e -> setStyle e nm val2
      remove = Map.mapWithKey (\k _ -> (\e -> removeStyle e k))
      add = Map.mapWithKey (\k v -> \e -> setStyle e k v)

{-# INLINE diffAttributesDeferred #-}
diffAttributesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffAttributesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffAttributesDeferred' e p mid new

diffAttributesDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffAttributesDeferred' e p mid new = do
  let r = diffAttributeMaps mid new
  amendPlan p $! sequence_ (fmap ($ e) r)

diffAttributeMaps :: Map Txt Txt -> Map Txt Txt -> Map Txt (Element -> IO ())
diffAttributeMaps = Map.mergeWithKey diff remove add
  where
      diff nm val1 val2 
        | b <- isTrue# (reallyUnsafePtrEquality# val1 val2) 
        , c <- val1 == val2 
        , b || c
        = Nothing
        | otherwise = Just $ \e -> setAttribute e nm val2
      remove = Map.mapWithKey (\k _ -> (\e -> removeAttribute e k))
      add = Map.mapWithKey (\k v -> \e -> setAttribute e k v)

{-# INLINE diffPropertiesDeferred #-}
diffPropertiesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffPropertiesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffPropertiesDeferred' e p mid new

diffPropertiesDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffPropertiesDeferred' e p mid new = do
  let r = diffPropertyMaps mid new
  amendPlan p $! sequence_ (fmap ($ e) r)

diffPropertyMaps :: Map Txt Txt -> Map Txt Txt -> Map Txt (Element -> IO ())
diffPropertyMaps = Map.mergeWithKey diff remove add
  where
      diff nm val1 val2 
        | b <- isTrue# (reallyUnsafePtrEquality# val1 val2) 
        , c <- val1 == val2 
        , b || c
        = Nothing
        | otherwise = Just $ \e -> setProperty e nm val2
      remove = Map.mapWithKey (\k _ -> (\e -> removeProperty e k))
      add = Map.mapWithKey (\k v -> \e -> setProperty e k v)

addListenerDeferred :: Element -> Plan s -> Listener -> ST s Listener
addListenerDeferred e plan l@(On n t o a _) = do
#ifdef __GHCJS__
  (target,mcb,cb,stopper) <- unsafeIOToST $ do
    target <- case t of
                ElementTarget  -> return (toJSV e)
                WindowTarget   -> fmap toJSV getWindow
                DocumentTarget -> fmap toJSV getDocument
    (mcb,cb,stopper) <- do

            stopper <- newIORef undefined

            let stpr = join $ readIORef stopper

            if not (asynchronous o) then do

              cb <- syncCallback1 ContinueAsync $ \jsv -> do
                when (preventDef o) (preventDefault jsv)
                when (stopProp o) (stopPropagation jsv)
                a (Evt jsv (toJSV e) stpr)
              
              writeIORef stopper $ do
                removeEventListener target n cb
                releaseCallback cb
              
              addEventListener target n cb (passive o)

              return (Nothing,cb,stpr)

            else do
              cb <- asyncCallback1 $ \jsv -> a (Evt jsv (toJSV e) stpr)

              writeIORef stopper $ do
                removeEventListener target n cb
                releaseCallback cb

              mcb <- 
                if preventDef o || stopProp o then do
                  cb' <- syncCallback1 ContinueAsync $ \jsv -> do
                    when (preventDef o) (preventDefault jsv)
                    when (stopProp o) (stopPropagation jsv)
                  modifyIORef' stopper $ \original -> do
                    original
                    removeEventListener target n cb'
                    releaseCallback cb'
                  pure (Just cb')
                else
                  pure Nothing

              return (mcb,cb,stpr)

    return (target,mcb,cb,stopper)

  amendPlan plan $ do
    addEventListener target n cb (passive o)
    for_ mcb (\cb -> addEventListener target n cb (passive o))
  return (On n t o a stopper)
#else
  return l
#endif

removeListenerDeferred :: Plan s -> Listener -> ST s ()
removeListenerDeferred p (On _ _ _ _ stp) = amendPlan p stp

{-# INLINE diffListenersDeferred #-}
diffListenersDeferred :: Element -> Plan s -> [Listener] -> [Listener] -> [Listener] -> ST s [Listener]
diffListenersDeferred e p old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> diffListenersDeferred' e p old mid new

diffListenersDeferred' :: Element -> Plan s -> [Listener] -> [Listener] -> [Listener] -> ST s [Listener]
diffListenersDeferred' e p old mid new = do
      let om = zip old mid

      -- removes
      for_ om $ \(o,m) -> do
        case unsafeLookup new m of
          Nothing -> removeListenerDeferred p o
          Just n  -> return ()

      -- adds
      for new $ \n -> do
        case unsafeLookupPair om n of
          Nothing -> addListenerDeferred e p n
          Just o  -> return o

unsafeLookup :: [a] -> a -> Maybe a
unsafeLookup [] _ = Nothing
unsafeLookup (x : xs) n =
  case reallyUnsafePtrEquality# x n of
    1# -> Just x
    _  -> unsafeLookup xs n

unsafeLookupPair :: [(a,a)] -> a -> Maybe a
unsafeLookupPair [] _ = Nothing
unsafeLookupPair ((o,m) : xs) n =
  case reallyUnsafePtrEquality# m n of
    1# -> Just o
    _  -> unsafeLookupPair xs n

addLifecycleDeferred :: Element -> Plan s -> Lifecycle -> ST s ()
addLifecycleDeferred e p (HostRef w) = amendPlan p $ w (toNode e)

{-# INLINE diffLifecyclesDeferred #-}
diffLifecyclesDeferred :: Element -> Plan s -> [Lifecycle] -> [Lifecycle] -> [Lifecycle] -> ST s ()
diffLifecyclesDeferred e p old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffLifecyclesDeferred' e p old mid new

diffLifecyclesDeferred' :: Element -> Plan s -> [Lifecycle] -> [Lifecycle] -> [Lifecycle] -> ST s ()
diffLifecyclesDeferred' e p old mid new =
  let adds = List.filter (not . (old `unsafeContains`)) new
  in for_ adds (addLifecycleDeferred e p)

unsafeContains :: [a] -> a -> Bool
unsafeContains [] _ = False
unsafeContains (x : xs) a =
  case reallyUnsafePtrEquality# x a of
    1# -> True
    _  -> unsafeContains xs a

-- styleDiff :: Element -> Map Txt Txt -> Map Txt Txt -> Map Txt (IO ())
-- styleDiff e = Map.mergeWithKey diff remove add
--   where
--     diff nm val1 val2
--       | val1 == val2           = Nothing
--       | otherwise              = Just $ setStyle e nm val2
--     remove = Map.mapWithKey (\nm  _  -> removeStyle e nm)
--     add    = Map.mapWithKey (\nm val -> setStyle e nm val)
{-# INLINE diffChildrenDeferred #-}
diffChildrenDeferred :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> DiffST s [View]
diffChildrenDeferred e mounted plan plan' olds !mids !news =
  case reallyUnsafePtrEquality# mids news of
    1# -> return olds
    _  -> diffChildrenDeferred' e mounted plan plan' olds mids news

{-# NOINLINE diffChildrenDeferred' #-}
diffChildrenDeferred' :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> DiffST s [View]
diffChildrenDeferred' (toNode -> e) mounted plan plan' olds mids news =
  case (mids,news) of
    ([],[]) -> return olds

    -- 0 1+
    ([],_ ) -> do
      frag <- unsafeIOToST createFrag
      let n = Just (toNode frag)
      news' <- unsafeIOToST (traverse (build mounted n) news)
      amendPlan plan (append e frag)
      return news'

    -- 1+ 0
    (_,[]) -> do
      amendPlan plan (clearNode e)
      amendPlan plan' (for_ olds cleanup)
      return []

    -- 1+ 1+
    _ -> go olds mids news
  where
    {-# NOINLINE go #-}
    go = go'

    {-# INLINE go' #-}
    go' os ms ns =
      case reallyUnsafePtrEquality# ms ns of
        1# -> return os
        _  -> diff os ms ns
      where
        diff (old:olds) (mid:mids) (new:news) = do
          new'  <- diffDeferred mounted plan plan' old mid new
          news' <- go olds mids news
          return (new' : news')

        diff olds _ [] = do
          removeManyDeferred plan plan' olds
          return []

        diff [] _ news = do
          frag <- unsafeIOToST createFrag
          let n = Just (toNode frag)
          news' <- unsafeIOToST (for news (build mounted n))
          amendPlan plan (append e frag)
          return news'

removeManyDeferred :: Plan s -> Plan s -> [View] -> ST s ()
removeManyDeferred plan plan' vs = do
  amendPlan plan (for_ vs (traverse_ removeNodeMaybe . getHost))
  amendPlan plan' (for_ vs cleanup)

removeDeferred :: Plan s -> Plan s -> View -> ST s ()
removeDeferred plan plan' v = do
  for_ (getHost v) (amendPlan plan . removeNodeMaybe)
  amendPlan plan' (cleanup v)

replaceDeferred :: Plan s -> Plan s -> View -> View -> ST s View
replaceDeferred plan plan' old@(getHost -> oldHost) new@(getHost -> newHost) = do
  case oldHost of
    Nothing -> error "Expected old host in replaceDeferred; got nothing."
    Just oh ->
      case newHost of
        Nothing -> error "Expected new host in replaceDeferred; got nothing."
        Just nh -> do
          amendPlan plan (replaceNode oh nh)
          amendPlan plan' (cleanup old)
          return new

replaceTextContentDeferred :: Plan s -> View -> View -> ST s View
replaceTextContentDeferred plan old@(textHost -> Just oh) new = do
  amendPlan plan (oh `replaceText` content new)
  return new { textHost = Just oh }

diffSVGKeyedElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffSVGKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  cs <- diffKeyedChildrenDeferred e mounted plan plan' (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  return $ old
    { features = fs
    , keyedChildren = cs
    }

diffKeyedElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  cs <- diffKeyedChildrenDeferred e mounted plan plan' (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  return $ old
    { features = fs
    , keyedChildren = cs
    }

-- Keyed diffing works very much like elm's virtual-dom with short-cut in the case that the children are unchanged.
-- We use a fragment in the case of a transition from 0 children to some (n /= 0) children so that the animation frame
-- only has to do one node append. We use `clearNode` for quick empty with deferred cleanup.
--
-- Note: We try to do as little work as possible in the animation frame, so lists of the same action are collapsed into a single action.
--       See, for example, 0 1+, 1+ 0, 0 0+, and cleanup
--       Remaining cases are:
--          swap where three actions are added to the plan rather than one
--          2+ 2+/insert nk0 where insert is immediately followed by diff
{-# INLINE diffKeyedChildrenDeferred #-}
diffKeyedChildrenDeferred :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s [(Int,View)]
diffKeyedChildrenDeferred e mounted plan plan' olds !mids !news = do
  case reallyUnsafePtrEquality# mids news of
    1# -> return olds
    _  -> diffKeyedChildrenDeferred' e mounted plan plan' olds mids news

{-# NOINLINE diffKeyedChildrenDeferred' #-}
diffKeyedChildrenDeferred' :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s [(Int,View)]
diffKeyedChildrenDeferred' (toNode -> e) mounted plan plan' olds mids news =
  case (mids,news) of
    ([],[]) -> do
      return olds

    -- 0 1+
    ([],_ ) -> do
      frag <- unsafeIOToST createFrag
      let n = Just (toNode frag)
      news' <- unsafeIOToST (traverse (traverse (build mounted n)) news)
      amendPlan plan (append e frag)
      return news'

    -- 1+ 0
    (_,[]) -> do
      amendPlan plan (clearNode e)
      amendPlan plan' (for_ (fmap snd olds) cleanup)
      return []

    -- 1+ 1+
    _ -> do
      dc       <- newSTRef mempty
      news'    <- go dc 0 olds mids news
      removals <- readSTRef dc

      -- cleanup
      -- remove them in reverse order they were added since they were
      -- diffed beginning to end and added with (_:) rather than (++[_])
      removeManyDeferred plan plan' (reverse removals)

      return news'

  where
        {-# NOINLINE go #-}
        go :: Removals s -> Int -> DiffST s [(Int,View)]
        go = go'

        {-# INLINE go' #-}
        go' :: Removals s -> Int -> DiffST s [(Int,View)]
        go' _ _ olds mids news
          | isTrue# (reallyUnsafePtrEquality# mids news) = pure olds

        -- Invariant: we can always infer the shape of `mids` from the shape of `olds`;
        --            mids should always be an irrefutable pattern

        -- 2+ 2+
        go' dc i (o0@(ok0,old0):os1@(o1@(ok1,old1):os2)) ~(m0@(mk0,mid0):ms1@(m1@(mk1,mid1):ms2)) ns@(n0@(nk0,new0):ns1@(n1@(nk1,new1):ns2))
          | mk0 == nk0 = do
              -- diff mk0 and nk0
              n  <- dKCD_helper o0 m0 n0
              ns <- go dc (i + 1) os1 ms1 ns1
              return (n:ns)

          | mk0 == nk1 && mk1 == nk0 = do
              -- swap mk0 mk1 and diff them in turn
              let ins (Just _0) (Just _1) = amendPlan plan (insertBefore _1 _0)
              ins (getHost old0) (getHost old1)
              n0' <- dKCD_helper o1 m1 n0
              n1' <- dKCD_helper o0 m0 n1
              ns  <- go dc (i + 2) os2 ms2 ns2
              return (n0':n1':ns)

          | mk0 == nk1 = do
              -- insert nk0
              n0' <- dKCD_ins i nk0 new0
              n1' <- dKCD_helper o0 m0 n1
              ns  <- go dc (i + 2) os1 ms1 ns2
              return (n0':n1':ns)

          | otherwise = do
              -- delete m0
              modifySTRef' dc (old0:)
              go dc (i + 1) os1 ms1 ns

        -- 1 2+
        go' dc i (os@[o@(ok,old)]) ~(ms@[m@(mk,mid)]) new@(n0@(nk0,new0):ns@((nk1,new1):_))
          | mk == nk0 = do
              -- diff mk and nk0
              n'  <- dKCD_helper o m n0
              ns' <- go dc (i + 1) [] [] ns
              return (n':ns')
          | mk == nk1 = do
              -- insert nk0
              n'  <- dKCD_ins i nk0 new0
              ns' <- go dc (i + 1) os ms ns
              return (n':ns')
          | otherwise = do
              -- delete mk
              modifySTRef' dc (old:)
              go dc (i + 1) [] [] new

        -- 1+ 1
        go' dc i (o@(ok,old):os) ~(m@(mk,mid):ms) (ns@[n@(nk,new)])
          | mk == nk = do
              -- diff mk and nk
              n' <- dKCD_helper o m n
              ns' <- go dc (i + 1) os ms []
              return (n':ns')
          | otherwise = do
              -- delete mk
              modifySTRef' dc (old:)
              go dc (i + 1) os ms ns

        -- 0+ 0
        go' dc _ olds mids [] = do
          for_ olds (modifySTRef' dc . (:) . snd)
          return []

        -- 0 0+
        go' dc _ [] _ news = do
          frag <- unsafeIOToST createFrag
          let n = Just (toNode frag)
          news' <- unsafeIOToST (traverse (traverse (build mounted n)) news)
          amendPlan plan (append e frag)
          return news'

        dKCD_helper :: DiffST s (Int,View)
        dKCD_helper (_,old) (_,mid) (nk,new) = do
          new' <- diffDeferred mounted plan plan' old mid new
          return (nk,new')

        dKCD_ins :: Int -> Int -> View -> ST s (Int,View)
        dKCD_ins i nk new = do
          let ins (Just a) = amendPlan plan (insertAt (coerce e) a i)
          n' <- unsafeIOToST (build mounted Nothing new)
          ins (getHost n')
          return (nk,n')
