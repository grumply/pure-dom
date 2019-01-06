{-# LANGUAGE CPP, OverloadedStrings, RankNTypes, ScopedTypeVariables, PatternSynonyms, ViewPatterns, MagicHash, RecordWildCards, BangPatterns, LambdaCase #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
module Pure.DOM (inject) where

-- from base
import Control.Concurrent (MVar,newEmptyMVar,putMVar,takeMVar,yield,forkIO)
import Control.Monad.ST (ST,runST)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad (void,unless,join,when)
import Data.Coerce (coerce)
import Data.Foldable (for_,traverse_)
import Data.Function (fix)
import Data.IORef (IORef,newIORef,modifyIORef',readIORef,writeIORef)
import Data.List as List (null,reverse,filter)
import Data.Maybe (fromJust)
import Data.STRef (STRef,newSTRef,readSTRef,modifySTRef',writeSTRef)
import Data.Traversable (for,traverse)
import Data.Typeable (Typeable)
import GHC.Exts (reallyUnsafePtrEquality#)
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (head)

-- from containers
import Data.Map.Lazy (Map)
import Data.IntMap (IntMap)
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.Map.Strict as Map (fromList,toList,insert,difference,keys,differenceWith)
import qualified Data.IntMap.Strict as IntMap (fromList,toList,insert,lookup,delete)
import qualified Data.Set as Set (fromList,toList,insert,delete,null)
import qualified Data.IntSet as IntSet (fromList,member)

-- from pure-core
import Pure.Data.View (Pure(..),View(..),Features(..),Listener(..),Lifecycle(..),Comp(..),Target(..),getHost,setProps,queueComponentUpdate,Ref(..),ComponentPatch(..),sameTypeWitness)

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

type Plan s = STRef s [IO ()]
type DiffST s a = a -> a -> a -> ST s a
type Removals s = STRef s (IntMap (View,View))

{-# INLINE newPlan #-}
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
runPlan = foldr (flip (>>)) (return ())

yield_ :: IO ()
yield_ =
#ifndef RENDER_SYNC
  yield
#else
  return ()
#endif

-- | Given a host node and a View, build and embed the View.
{-# NOINLINE inject #-}
inject :: IsNode e => e -> View -> IO ()
inject host v = do
  mtd <- newIORef []
  !_ <- build True mtd (Just $ toNode host) v
  runPlan =<< readIORef mtd

build :: Bool -> IORef [IO ()] -> Maybe Node -> View -> IO View
build first mtd = go
  where
    go mparent (SomeView _ r) = go mparent (view r)
    go mparent v@ComponentView{} = buildComponent mtd mparent v
    go mparent tv@(TextView{}) = do
      tn <- createText (content tv)
      for_ mparent (`append` tn)
      return $ tv { textHost = Just tn }
    go mparent HTMLView {..} = do
      e <- create tag
      for_ mparent (`append` e)
      ls <- setFeatures e features
      let n = Just (toNode e)
      unless first yield_
      cs <- traverse (go n) children
      return $ HTMLView (Just e) tag features { listeners = ls } cs
    go mparent RawView {..} = do
      e <- create tag
      for_ mparent (`append` e)
      ls <- setFeatures e features
      setInnerHTML e content
      return $ RawView (Just e) tag features { listeners = ls } content
    go mparent SVGView {..} = do
      e <- createNS "http://www.w3.org/2000/svg" tag
      ls <- setFeatures e features
      for_ mparent (`append` e)
      setXLinks e xlinks
      let n = Just (toNode e)
      unless first yield_
      cs <- traverse (go n) children
      return $ SVGView (Just e) tag features { listeners = ls } xlinks cs
    go mparent KHTMLView {..} = do
      e <- create tag
      ls <- setFeatures e features
      for_ mparent (`append` e)
      let n = Just (toNode e)
      unless first yield_
      cs <- traverse (traverse (go n)) keyedChildren
      return $ KHTMLView (Just e) tag features { listeners = ls } cs
    go mparent KSVGView {..} = do
      e <- createNS "http://www.w3.org/2000/svg" tag
      ls <- setFeatures e features
      setXLinks e xlinks
      for_ mparent (`append` e)
      let n = Just (toNode e)
      unless first yield_
      cs <- traverse (traverse (go n)) keyedChildren
      return $ KSVGView (Just e) tag features { listeners = ls } xlinks cs
    go mparent NullView{} = do
      e <- create "template"
      for_ mparent (`append` e)
      return $ NullView (Just e)
    go mparent PortalView{..} = do
      e <- create "template"
      for_ mparent (`append` e)
      v <- go (Just $ toNode portalDestination) portalView
      return $ PortalView (Just e) portalDestination v
    go mparent (LazyView f a) = go mparent (view $ f a)

    setXLinks :: Element -> Map Txt Txt -> IO ()
    setXLinks e = traverse_ (uncurry (setAttributeNS e "http://www.w3.org/1999/xlink")) . Map.toList

    setFeatures e Features_ {..} = do
      setClasses e classes
      setStyles e styles
      setAttributes e attributes
      setProperties e properties
      for_ lifecycles (addLifecycle e)
      for listeners (addListener e)
      where
        setClasses :: Element -> Set Txt -> IO ()
        setClasses e cs
          | Set.null cs = return ()
          | otherwise   = setAttribute e "class" $ Txt.intercalate " " $ Set.toList $ Set.delete "" cs

        setStyles :: Element -> Map Txt Txt -> IO ()
        setStyles e = traverse_ (uncurry (setStyle e)) . Map.toList

        setAttributes :: Element -> Map Txt Txt -> IO ()
        setAttributes e = traverse_ (uncurry (setAttribute e)) . Map.toList

        setProperties :: Element -> Map Txt Txt -> IO ()
        setProperties e = traverse_ (uncurry (setProperty e)) . Map.toList

        addListener :: Element -> Listener -> IO Listener
        addListener e f@(On n t o a _) = do
#ifdef __GHCJS__
            target <- case t of
                        ElementTarget  -> return (toJSV e)
                        WindowTarget   -> fmap toJSV getWindow
                        DocumentTarget -> fmap toJSV getDocument
            (cb,stopper) <- do

              stopper <- newIORef undefined

              let stpr = join $ readIORef stopper

              cb <- syncCallback1 ContinueAsync $ \jsv -> do
                when (preventDef o) (preventDefault jsv)
                when (stopProp o) (stopPropagation jsv)
                a (Evt jsv target stpr)

              writeIORef stopper $ do
                removeEventListener target n cb
                releaseCallback cb

              return (cb,stpr)

            addEventListener target n cb (passive o)
            return (On n t o a stopper)
#else
            return f
#endif

        addLifecycle :: Element -> Lifecycle -> IO Lifecycle
        addLifecycle e (HostRef w) = do
          modifyIORef' mtd ((w (toNode e)):)
          return (HostRef w)

buildComponent mtd mparent (ComponentView witness props _ comp) = do
  stq    <- newIORef . Just =<< newQueue
  props_ <- newIORef props
  state_ <- newIORef undefined
  live_  <- newIORef undefined
  let c = comp cr
      cr = Ref live_ props_ state_ c stq
  state1 <- construct c
  writeIORef state_ state1
  state2 <- mount c state1
  writeIORef state_ state2
  let new = render c props state2
  live <- build False mtd mparent new
  writeIORef live_ live
  modifyIORef' mtd ((mounted c):)
  addIdleWork (newComponentThread cr new live props state2)
  return $ ComponentView witness props (Just cr) comp
  where
    newComponentThread ref@Ref { crComponent = Comp {..}, ..} view0 live0 props0 state0 = do
        st <- newIORef (view0,live0,props0,state0,props0,state0)
        Just pq <- readIORef crPatchQueue
        void $ forkIO $ execute $ do
          executing
          flip fix ([],[]) $ \worker -> \case
            ([],[]) -> performIO (collect pq) >>= \cps -> worker ([],cps)
            (acc,[]) -> do
              dus <- for (List.reverse acc) $ \(willUpd,didUpd,callback) -> do
                willUpd
                return (didUpd,callback)
              performIO $ do
                (old,live,props,state,newProps,newState) <- readIORef st
                let new =
                      case reallyUnsafePtrEquality# props newProps of
                        1# -> case reallyUnsafePtrEquality# state newState of
                                1# -> old
                                _  -> render props newState
                        _  -> case reallyUnsafePtrEquality# state newState of
                                1# -> render newProps state
                                _  -> render newProps newState
                mtd <- newIORef []
                let (plan,plan',new_live) = buildPlan (\p p' -> do
                        !new' <- diffDeferred mtd p p' live old new
                        return new'
                        )
                writeIORef st (new,new_live,newProps,newState,newProps,newState)
                mtd <- plan `seq` plan' `seq` readIORef mtd
                let hasAnimations = not $ List.null plan
                    hasIdleWork = not $ List.null plan'
                if hasAnimations && hasIdleWork
                  then do
                    barrier <- newEmptyMVar
                    addAnimationsReverse ( (putMVar barrier ()) : (void $ addIdleWorksReverse plan') : (writeIORef crView new_live) : plan )
                    takeMVar barrier
                  else do
                    when hasAnimations $ do
                      barrier <- newEmptyMVar
                      addAnimationsReverse ( (putMVar barrier ()) : (writeIORef crView new_live) : plan )
                      takeMVar barrier
                    when hasIdleWork $ do
                      void (addIdleWorksReverse plan')
                runPlan mtd
              cbs <- for dus $ \(du,c) -> do
                du
                return c
              foldr (>>) (return ()) cbs
              worker ([],[])
            (acc,cp:cps) ->
              case cp of
                Unmount mv mtd -> do
                  unmounted
                  performIO $ do
                    (old,live,_,_,_,_) <- readIORef st
                    writeIORef crPatchQueue Nothing
                    let (plan,plan',res) = buildPlan $ \plan plan' ->
                            let removeDeferred = do
                                  amendPlan plan' (cleanup live)
                                    -- for_ (getHost live) $ \host -> amendPlan plan' $ removeNodeMaybe host
                                replaceDeferred old@(getHost -> oldHost) new@(getHost -> newHost) =
                                  case oldHost of
                                    Nothing -> error "Expected old host in replaceDeferred; got nothing."
                                    Just oh ->
                                      case newHost of
                                        Nothing -> error "Expected new host in replaceDeferred; got nothing."
                                        Just nh -> do
                                          amendPlan plan  (replaceNode oh nh)
                                          amendPlan plan' (cleanup old)
                            in maybe removeDeferred (replaceDeferred live) mv
                    plan `seq` plan' `seq`
                      let hasAnimations = not $ List.null plan
                          hasIdleWork   = not $ List.null plan'
                      in
                        if hasAnimations && hasIdleWork
                          then do
                            barrier <- newEmptyMVar
                            addAnimationsReverse ( (putMVar barrier ()) : (void $ addIdleWorksReverse plan') : plan )
                            takeMVar barrier
                          else do
                            when hasAnimations $ do
                              barrier <- newEmptyMVar
                              addAnimationsReverse ( (putMVar barrier ()) : plan )
                              takeMVar barrier
                            when hasIdleWork $ do
                              void $ addIdleWorksReverse plan'
                    writeIORef st      undefined
                    writeIORef crProps (error "ask: Component invalidated.")
                    writeIORef crState (error "get: Component invalidated.")
                    writeIORef crView  (error "look: Component invalidated.")
                    mtd
                UpdateProperties newProps' -> do
                  (old,live,props,state,newProps,newState) <- performIO $ readIORef st
                  newState'    <- receive newProps' newState
                  shouldUpdate <- force   newProps' newState'
                  performIO $ writeIORef st (old,live,props,state,newProps',newState')
                  let writeRefs = writeIORef crProps newProps' >> writeIORef crState newState'
                  if shouldUpdate || not (List.null acc) then do
                    let
                      will = update  newProps' newState'
                      did  = updated newProps  newState
                    worker ((will >> performIO writeRefs,did,performIO (return ())) : acc,cps)
                  else do
                    performIO writeRefs
                    worker (acc,cps)
                UpdateState f -> do
                  (old,live,props,state,newProps,newState) <- performIO $ readIORef st
                  (newState',updatedCallback) <- f newProps newState
                  shouldUpdate                <- force newProps newState'
                  performIO $ writeIORef st (old,live,props,state,newProps,newState')
                  let writeRef = writeIORef crState newState'
                  if shouldUpdate || not (List.null acc) then
                    let
                      will = update  newProps newState'
                      did  = updated newProps newState
                    in
                      worker ((will >> performIO writeRef,did,updatedCallback) : acc,cps)
                  else do
                    performIO writeRef
                    worker (acc,cps)

cleanupListener :: Listener -> IO ()
cleanupListener (On _ _ _ _ stp) = stp

cleanup :: View -> IO ()
cleanup RawView {..} =
  for_ (listeners features) cleanupListener
cleanup HTMLView {..} = do
  for_ (listeners features) cleanupListener
  for_ children cleanup
cleanup SVGView {..} = do
  for_ (listeners features) cleanupListener
  for_ children cleanup
cleanup ComponentView {..} = do
  for_ record (\r -> queueComponentUpdate r (Unmount Nothing (return ())))
cleanup PortalView {..} = do
  cleanup portalView
cleanup KHTMLView {..} = do
  for_ (listeners features) cleanupListener
  for_ keyedChildren (cleanup . snd)
cleanup KSVGView {..} = do
  for_ (listeners features) cleanupListener
  for_ keyedChildren (cleanup . snd)
cleanup _ = return ()

diffDeferred :: forall s. IORef [IO ()] -> Plan s -> Plan s -> View -> View -> View -> ST s View
diffDeferred mounted plan plan' old mid new =

  case reallyUnsafePtrEquality# mid new of
    1# -> return old

    _  ->
      let
          replace = do
            !new' <- unsafeIOToST (build False mounted Nothing new)
            replaceDeferred plan plan' old new'
      in
        case (mid,new) of
          (LazyView f a,LazyView f' a') ->
            case reallyUnsafePtrEquality# f (unsafeCoerce f') of
              1# -> case reallyUnsafePtrEquality# a (unsafeCoerce a') of
                      1# -> return old
                      _  -> diffDeferred mounted plan plan' old (view (f a)) (view (f' a'))
              _  -> replace

          (ComponentView t p _ v,ComponentView t' p' _ v')
            | sameTypeWitness t t' -> do
              unsafeIOToST $ print "same component witness"
              case reallyUnsafePtrEquality# p (unsafeCoerce p') of
                1# -> return old
                _  -> do
                  case old of
                    ComponentView _ _ ~(Just r0) _ -> do
                      let r = unsafeCoerce r0
                      unsafeIOToST $ setProps r p'
                      return (ComponentView t' p' (Just r) v')
            | otherwise -> unsafeIOToST $ do
              case old of
                ComponentView _ _ ~(Just r0) _ -> do
                  print "Different component witness"
                  mtd <- newIORef []
                  !new' <- build False mtd Nothing new
                  queueComponentUpdate r0 (Unmount (Just new') (readIORef mtd >>= runPlan))
                  return new'

          (HTMLView{},HTMLView{}) ->
            case reallyUnsafePtrEquality# (tag mid) (tag new) of
              1# -> diffElementDeferred mounted plan plan' old mid new
              _ | tag mid == tag new -> diffElementDeferred mounted plan plan' old mid new
                | otherwise          -> replace

          (TextView _ t,TextView _ t') ->
            case reallyUnsafePtrEquality# t t' of
              0# | t /= t' -> replaceTextContentDeferred plan old new
              _            -> return old

          (NullView{},NullView{}) -> return old

          (RawView{},RawView{}) ->
            case reallyUnsafePtrEquality# (tag mid) (tag new) of
              1# -> do
                case reallyUnsafePtrEquality# (content mid) (content new) of
                  1# -> do
                    fs <- diffFeaturesDeferred (coerce $ fromJust $ getHost old) plan plan' (features old) (features mid) (features new)
                    return old { features = fs }
                  _  -> replace
              _ -> replace

          (SomeView t m,SomeView t' n) ->
            if sameTypeWitness t t'
              then do
                unsafeIOToST $ print "same pure witness"
                -- we know these types share a Pure instance, so we can safely unsafeCoerce
                case reallyUnsafePtrEquality# m (unsafeCoerce n) of
                  1# -> return old
                  _  -> diffDeferred mounted plan plan' old (view m) (view n)
              else do
                unsafeIOToST $ print "different pure witness"
                replace

          (SVGView{},SVGView{}) ->
            case reallyUnsafePtrEquality# (tag mid) (tag new) of
              1# -> diffSVGElementDeferred mounted plan plan' old mid new
              _ | tag mid == tag new -> diffSVGElementDeferred mounted plan plan' old mid new
                | otherwise          -> replace

          (KHTMLView{},KHTMLView{}) ->
            case reallyUnsafePtrEquality# (tag mid) (tag new) of
              1# -> diffKeyedElementDeferred mounted plan plan' old mid new
              _ | tag mid == tag new -> diffKeyedElementDeferred mounted plan plan' old mid new
                | otherwise          -> replace

          (KSVGView{},KSVGView{}) ->
            case reallyUnsafePtrEquality# (tag mid) (tag new) of
              1# -> diffSVGKeyedElementDeferred mounted plan plan' old mid new
              _ | tag mid == tag new -> diffSVGKeyedElementDeferred mounted plan plan' old mid new
                | otherwise          -> replace

          (PortalView{},PortalView{})
            | same (toJSV (portalDestination old)) (toJSV (portalDestination new)) -> do
              v <- diffElementDeferred mounted plan plan' (portalView old) (portalView mid) (portalView new)
              return old { portalView = v }
            | otherwise -> do
              !built@(getHost -> Just h) <- unsafeIOToST (build False mounted Nothing (portalView new))
              amendPlan plan' (cleanup old)
              amendPlan plan $ do
                for_ (getHost (portalView old)) removeNode
                append (toNode $ portalDestination new) h
              -- recycling the portalProxy
              return (PortalView (portalProxy old) (portalDestination new) built)

          (_,PortalView{}) -> do
            !proxy <- unsafeIOToST (build False mounted Nothing (NullView Nothing))
            replaceDeferred plan plan' old proxy
            !built@(getHost -> Just h) <- unsafeIOToST (build False mounted Nothing (portalView new))
            amendPlan plan $ append (toNode $ portalDestination new) h
            return (PortalView (fmap coerce $ getHost proxy) (portalDestination new) built)

          (PortalView{},_) -> do
            amendPlan plan (cleanup old)
            amendPlan plan $ for_ (getHost (portalView old)) removeNode
            replace

          _ -> replace

diffElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
  unsafeIOToST yield_
  !cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

diffSVGElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffSVGElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  unsafeIOToST yield_
  !cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

diffFeaturesDeferred :: Element -> Plan s -> Plan s -> DiffST s Features
diffFeaturesDeferred e plan plan' old !mid !new = do
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> do
      diffClassesDeferred    e plan (classes mid) (classes new)
      diffStylesDeferred     e plan (styles mid) (styles new)
      diffAttributesDeferred e plan (attributes mid) (attributes new)
      diffPropertiesDeferred e plan (properties mid) (properties new)
      ls <- diffListenersDeferred e plan plan' (listeners old) (listeners mid) (listeners new)
      diffLifecyclesDeferred e plan (lifecycles old) (lifecycles mid) (lifecycles new)
      return old { listeners = ls }

diffXLinksDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffXLinksDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let remove = removeAttributeNS e "http://www.w3.org/1999/xlink"
          !removals = Map.keys (Map.difference mid new)
          !r = traverse_ remove removals
      amendPlan p r

      let add (k,v) = setAttributeNS e "http://www.w3.org/1999/xlink" k v
          !adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          !a = traverse_ add adds
      amendPlan p a

diffClassesDeferred :: Element ->Plan s -> Set Txt -> Set Txt -> ST s ()
diffClassesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> amendPlan p (setProperty e "className" $ Txt.intercalate " " $ Set.toList $ Set.delete "" new)

diffStylesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffStylesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let remove = removeStyle e
          !removes = Map.keys (Map.difference mid new)
          !r = traverse_ remove removes
      amendPlan p r

      let add (k,v) = setStyle e k v
          !adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          !a = traverse_ add adds
      amendPlan p a

diffAttributesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffAttributesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let remove = removeAttribute e
          !removes = Map.keys (Map.difference mid new)
          !r = traverse_ remove removes
      amendPlan p r

      let add (k,v) = setAttribute e k v
          !adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          !a = traverse_ add adds
      amendPlan p a

diffPropertiesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffPropertiesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let remove = removeProperty e
          !removes = Map.keys (Map.difference mid new)
          !r = traverse_ remove removes
      amendPlan p r

      let add (k,v) = setProperty e k v
          !adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          !a = traverse_ add adds
      amendPlan p a

addListenerDeferred :: Element -> Plan s -> Listener -> ST s Listener
addListenerDeferred e plan l@(On n t o a _) = do
#ifdef __GHCJS__
  (target,cb,stopper) <- unsafeIOToST $ do
    target <- case t of
                ElementTarget  -> return (toJSV e)
                WindowTarget   -> fmap toJSV getWindow
                DocumentTarget -> fmap toJSV getDocument
    (cb,stopper) <- do

            stopper <- newIORef undefined

            let stpr = join $ readIORef stopper

            cb <- syncCallback1 ContinueAsync $ \jsv -> do
              when (preventDef o) (preventDefault jsv)
              when (stopProp o) (stopPropagation jsv)
              a (Evt jsv target stpr)

            writeIORef stopper $ do
              removeEventListener target n cb
              releaseCallback cb

            return (cb,stpr)

    return (target,cb,stopper)

  amendPlan plan (addEventListener target n cb (passive o))
  return (On n t o a stopper)
#else
  return l
#endif

removeListenerDeferred :: Plan s -> Listener -> ST s ()
removeListenerDeferred p (On _ _ _ _ stp) = amendPlan p stp

diffListenersDeferred :: Element -> Plan s -> Plan s -> [Listener] -> [Listener] -> [Listener] -> ST s [Listener]
diffListenersDeferred e p p' old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> do
      let om = zip old mid

      -- removes
      for_ om $ \(o,m) -> do
        case unsafeLookup new m of
          Nothing -> removeListenerDeferred p' o
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

diffLifecyclesDeferred :: Element -> Plan s -> [Lifecycle] -> [Lifecycle] -> [Lifecycle] -> ST s ()
diffLifecyclesDeferred e p old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  ->
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

diffChildrenDeferred :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> DiffST s [View]
diffChildrenDeferred (toNode -> e) mounted plan plan' = cleanupCheck
  where
    cleanupCheck :: DiffST s [View]
    cleanupCheck olds mids news = do
      case reallyUnsafePtrEquality# mids news of
        1# -> return olds
        _  -> if List.null news
                then do
                  amendPlan plan (clearNode e)
                  let cs = fmap cleanup olds
                  for_ cs (amendPlan plan')
                  return []
                else go olds mids news

    start :: DiffST s [View]
    start olds mids news =
      case reallyUnsafePtrEquality# mids news of
        1# -> return olds
        _  -> go olds mids news

    go :: DiffST s [View]
    go olds _ [] = do
      !_ <- for_ olds (removeDeferred plan plan')
      return []

    go [] _ news = do
      frag <- unsafeIOToST createFrag
      let n = Just (toNode frag)
      !news' <- for news $ \new -> do
        !new' <- unsafeIOToST (build False mounted n new)
        return new'
      amendPlan plan (append e frag)
      return news'

    go (old:olds) (mid:mids) (new:news) = do
      !new'  <- diffDeferred mounted plan plan' old mid new
      !news' <- start olds mids news
      return (new' : news')

removeDeferred :: Plan s -> Plan s -> View -> ST s ()
removeDeferred plan plan' v = do
  for_ (getHost v) (amendPlan plan . removeNodeMaybe)
  amendPlan plan' (cleanup v)

replaceDeferred :: Plan s -> Plan s -> View -> View -> ST s View
replaceDeferred plan plan' old@(getHost -> oldHost) new@(getHost -> newHost) =
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
diffSVGKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  unsafeIOToST yield_
  !cs <- diffKeyedChildrenDeferred e mounted plan plan' (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  return old
    { features = fs
    , keyedChildren = cs
    }

diffKeyedElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
  unsafeIOToST yield_
  !cs <- diffKeyedChildrenDeferred e mounted plan plan' (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  return old
    { features = fs
    , keyedChildren = cs
    }

diffKeyedChildrenDeferred :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s [(Int,View)]
diffKeyedChildrenDeferred (toNode -> e) mounted plan plan' olds !mids !news = do
  case reallyUnsafePtrEquality# mids news of
    1# -> return olds
    _  ->
      case (mids,news) of
        ([],[]) -> return olds

        ([],_ ) -> do
          frag <- unsafeIOToST createFrag
          let n = Just (toNode frag)
          news' <- for news $ \(nk,new) -> do
              !new' <- unsafeIOToST (build False mounted n new)
              return (nk,new')
          amendPlan plan (append e frag)
          return news'

        (_,[]) -> do
          amendPlan plan (clearNode e)
          for_ (fmap (cleanup . snd) olds) (amendPlan plan')
          return []

        _ -> do
          dc       <- newSTRef mempty
          !news'   <- dKCD_slow dc olds mids news
          removals <- readSTRef dc
          for_ removals (removeDeferred plan plan' . fst)
          return news'

  where

    dKCD_slow :: Removals s -> DiffST s [(Int,View)]
    dKCD_slow dc = check 0
      where
        check !i olds !mids !news = do
          case reallyUnsafePtrEquality# mids news of
            1# -> return olds
            _  -> start olds mids news
          where
            start ((ok,old):olds') ((mk,mid):mids') ((nk,new):news')
              | mk == nk = do
                !new' <- diffDeferred mounted plan plan' old mid new
                news'' <- check (i + 1) olds' mids' news'
                return ((nk,new'):news'')
              | otherwise =
                go olds mids news
              where
                go os0@(o0@(ok0,old0):os1@(o1@(ok1,old1):os2)) ms0@(m0@(mk0,mid0):ms1@(m1@(mk1,mid1):ms2)) ns@(n0@(nk0,new0):ns1@(n1@(nk1,new1):ns2))
                  | mk0 == nk0 = do
                      n <- dKCD_helper o0 m0 n0
                      ns <- check (i + 1) os1 ms1 ns1
                      return (n:ns)

                  | mk0 == nk1 && mk1 == nk0 = do
                      -- swap mk0 mk1
                      let ins (Just _0) (Just _1) = amendPlan plan (insertBefore _1 _0)
                      ins (getHost old0) (getHost old1)
                      ns <- check (i + 2) os2 ms2 ns2
                      return (o1:o0:ns)

                  | mk0 == nk1 = do
                      -- insert nk0
                      n0 <- dKCD_ins nk0 new0
                      ns <- check (i + 1) os0 ms0 ns1
                      return (n0:ns)

                  | otherwise = do
                      -- delete m0
                      modifySTRef' dc (IntMap.insert ok0 (old0,mid0))
                      check i os1 ms1 ns

                go [o@(ok,old)] [m@(mk,mid)] (n0@(nk0,new0):n1@(nk1,new1):ns) =
                  if mk == nk0
                    then do
                      n' <- dKCD_helper o m n0
                      ns' <- check (i + 1) [] [] (n1:ns)
                      return (n':ns')
                    else
                      if mk == nk1
                        then do
                          n'  <- dKCD_ins nk0 new0
                          ns' <- check (i + 1) [o] [m] (n1:ns)
                          return (n':ns')
                        else do
                          modifySTRef' dc (IntMap.insert ok (old,mid))
                          n' <- dKCD_ins nk0 new0
                          ns' <- check (i + 1) [] [] (n1:ns)
                          return (n':ns')

                go [o@(ok,old)] [m@(mk,mid)] [n@(nk,new)] =
                  if mk == nk
                    then do
                      n' <- dKCD_helper o m n
                      return [n']
                    else do
                      modifySTRef' dc (IntMap.insert ok (old,mid))
                      n' <- dKCD_ins nk new
                      return [n']

                go (o@(ok,old):os) (m@(mk,mid):ms) ns@[n@(nk,new)] =
                  if mk == nk
                    then do
                      n' <- dKCD_helper o m n
                      ns' <- check (i + 1) os ms []
                      return (n':ns')
                    else do
                      modifySTRef' dc (IntMap.insert ok (old,mid))
                      check i os ms ns

                dKCD_helper :: (Int,View) -> (Int,View) -> (Int,View) -> ST s (Int,View)
                dKCD_helper (_,old) (_,mid) (nk,new) = do
                  !new' <- diffDeferred mounted plan plan' old mid new
                  return (nk,new')

                dKCD_ins :: Int -> View -> ST s (Int,View)
                dKCD_ins nk new = do
                  removals <- readSTRef dc
                  let ins (Just a) = amendPlan plan (insertAt (coerce e) a i)
                  case IntMap.lookup nk removals of
                    Nothing -> do
                      !n' <- unsafeIOToST (build False mounted Nothing new)
                      ins (getHost n')
                      return (nk,n')
                    Just (o,m) -> do
                      writeSTRef dc $ IntMap.delete nk removals
                      !new' <- diffDeferred mounted plan plan' o m new
                      ins (getHost new')
                      return (nk,new')

            start olds mids [] = do
              for_ (zip olds mids) $ \((ok,o),(_,m)) -> modifySTRef' dc (IntMap.insert ok (o,m))
              return []

            start [] _ news = do
              for news $ \(nk,new) -> do
                removals <- readSTRef dc
                case IntMap.lookup nk removals of
                  Nothing -> do
                    !new' <- unsafeIOToST $ build False mounted Nothing new
                    for_ (getHost new') (amendPlan plan . append e)
                    return (nk,new')

                  Just (old,mid) -> do
                    writeSTRef dc (IntMap.delete nk removals)
                    !new' <- diffDeferred mounted plan plan' old mid new
                    for_ (getHost new) (amendPlan plan . append e)
                    return (nk,new')

