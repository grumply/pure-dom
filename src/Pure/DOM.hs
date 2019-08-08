{-# LANGUAGE CPP, OverloadedStrings, RankNTypes, ScopedTypeVariables, PatternSynonyms, ViewPatterns, MagicHash, RecordWildCards, BangPatterns, LambdaCase #-}
module Pure.DOM (inject) where

-- from base
import Control.Concurrent (MVar,newEmptyMVar,putMVar,takeMVar,yield,forkIO)
import Control.Exception (SomeException,catch)
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

-- from containers
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map.Strict as Map (fromList,toList,insert,difference,keys,differenceWith,null)
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

buildPlan :: (forall s. Plan s -> Plan s -> ST s a) -> ([IO ()],[IO ()],a)
buildPlan f = runST $ do
  p  <- newPlan
  p' <- newPlan
  a  <- f p p'
  p  <- readSTRef p
  p' <- readSTRef p'
  return (p,p',a)

amendPlan :: Plan s -> IO () -> ST s ()
amendPlan plan f = modifySTRef' plan (f:)

runPlan :: [IO ()] -> IO ()
runPlan = foldr (flip (>>)) (return ())

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

build :: IORef [IO ()] -> Maybe Node -> View -> IO View
build mtd mparent HTMLView {..} = do
  e <- create tag
  let n = Just (toNode e)
  fs <- setFeatures mtd e features
  cs <- traverse (build mtd n) children
  for_ mparent (`append` e)
  return $ HTMLView (Just e) tag fs cs
build mtd mparent (SomeView r) =
  build mtd mparent (view r)
build mtd mparent v@ComponentView{} =
  buildComponent mtd mparent v
build mtd mparent (LazyView f a) =
  build mtd mparent (view $ f a)
build mtd mparent TextView {..} = do
  tn <- createText content
  for_ mparent (`append` tn)
  pure $ TextView (Just tn) content
build mtd mparent NullView{} = do
  e <- create "template"
  for_ mparent (`append` e)
  pure $ NullView (Just e)
build mtd mparent RawView {..} = do
  e <- create tag
  setInnerHTML e content
  fs <- setFeatures mtd e features
  for_ mparent (`append` e)
  return $ RawView (Just e) tag fs content
build mtd mparent KHTMLView {..} = do
  e <- create tag
  let n = Just (toNode e)
  fs <- setFeatures mtd e features
  cs <- traverse (traverse (build mtd n)) keyedChildren
  for_ mparent (`append` e)
  return $ KHTMLView (Just e) tag fs cs
build mtd mparent SVGView {..} = do
  e <- createNS "http://www.w3.org/2000/svg" tag
  let n = Just (toNode e)
  setXLinks e xlinks
  fs <- setFeatures mtd e features
  cs <- traverse (build mtd n) children
  for_ mparent (`append` e)
  return $ SVGView (Just e) tag fs xlinks cs
build mtd mparent KSVGView {..} = do
  e <- createNS "http://www.w3.org/2000/svg" tag
  let n = Just (toNode e)
  setXLinks e xlinks
  fs <- setFeatures mtd e features
  cs <- traverse (traverse (build mtd n)) keyedChildren
  for_ mparent (`append` e)
  return $ KSVGView (Just e) tag fs xlinks cs
build mtd mparent p@PortalView{} = do
  buildPortal mtd mparent p

setXLinks :: Element -> Map Txt Txt -> IO ()
setXLinks e = traverse_ (uncurry (setAttributeNS e "http://www.w3.org/1999/xlink")) . Map.toList

setFeatures mtd e fs@Features_ {..} = do
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

setClasses' e = setAttribute e "class" . Txt.intercalate " " . Set.toList . Set.delete ""

setStyles :: Element -> Map Txt Txt -> IO ()
setStyles e ss
  | Map.null ss = return ()
  | otherwise = setStyles' e ss

setStyles' e = traverse_ (uncurry (setStyle e)) . Map.toList

setAttributes :: Element -> Map Txt Txt -> IO ()
setAttributes e as
  | Map.null as = return ()
  | otherwise = setAttributes' e as

setAttributes' e = traverse_ (uncurry (setAttribute e)) . Map.toList

setProperties :: Element -> Map Txt Txt -> IO ()
setProperties e ps
  | Map.null ps = return ()
  | otherwise = setProperties' e ps

setProperties' e = traverse_ (uncurry (setProperty e)) . Map.toList

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

addLifecycle :: IORef [IO ()] -> Element -> Lifecycle -> IO Lifecycle
addLifecycle mtd e (HostRef w) = do
  modifyIORef' mtd ((w (toNode e)):)
  return (HostRef w)

buildPortal :: IORef [IO ()] -> Maybe Node -> View -> IO View
buildPortal mtd mparent (PortalView {..}) = do
  e <- create "template"
  v <- build mtd (Just $ toNode portalDestination) portalView
  for_ mparent (`append` e)
  return $ PortalView (Just e) portalDestination v

buildComponent :: IORef [IO ()] -> Maybe Node -> View -> IO View
buildComponent mtd mparent (ComponentView witness props _ comp) = do
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
  live <- build mtd mparent new
  writeIORef live_ live
  modifyIORef' mtd ((mounted c):)
  addIdleWork $ void $ forkIO $ newComponentThread cr c live new props state2
  return $ ComponentView witness props (Just cr) comp

awaitComponentPatches pq = do
  mpq <- readIORef pq
  for mpq collect `catch` \(_ :: SomeException) -> return Nothing

newComponentThread :: forall props state. Ref props state -> Comp props state -> View -> View -> props -> state -> IO ()
newComponentThread ref@Ref {..} comp@Comp {..} = \live view props state -> do
  executing state >>= loop live view props
  where
    loop :: View -> View -> props -> state -> IO ()
    loop !old !mid !props !state = do
      mps <- awaitComponentPatches crPatchQueue
      case mps of
        Nothing  -> return ()
        Just cps -> go props state [] cps
      where
        go :: props -> state -> [(IO (),IO (),IO ())] -> [ComponentPatch props state] -> IO ()
        go newProps newState = go1
          where
            go1 :: [(IO (),IO (),IO ())] -> [ComponentPatch props state] -> IO ()
            go1 acc [] = do
              let (wills,dids,after) = unzip3 (List.reverse acc)

              sequence_ wills

              let new = render newProps newState

              mtd <- newIORef []

              let
                (plan,plan',new_old) =
                  buildPlan $ \p p' -> diffDeferred mtd p p' old mid new

                hasAnimations = not (List.null plan)
                hasIdleWork   = not (List.null plan')

              mounts <- plan `seq` plan' `seq` readIORef mtd

              if hasAnimations && hasIdleWork then

                sync $ \barrier ->
                  addAnimationsReverse
                    ( (putMVar barrier ())
                    : (void (addIdleWorksReverse plan'))
                    : (writeIORef crView new_old)
                    : plan
                    )

              else do

                when hasAnimations $

                  sync $ \barrier ->
                    addAnimationsReverse
                      ( putMVar barrier ()
                      : writeIORef crView new_old
                      : plan
                      )

                when hasIdleWork $ void $
                  addIdleWorksReverse plan'

              runPlan mounts

              sequence_ dids

              sequence_ after

              yield
              loop new_old new newProps newState


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

                  plan `seq` plan' `seq`
                    let
                      hasAnimations = not $ List.null plan
                      hasIdleWork   = not $ List.null plan'
                    in
                      if hasAnimations && hasIdleWork
                        then

                          sync $ \barrier ->
                            addAnimationsReverse
                              ( putMVar barrier ()
                              : void (addIdleWorksReverse plan')
                              : plan
                              )

                        else do

                          when hasAnimations $

                            sync $ \barrier ->
                              addAnimationsReverse
                                ( putMVar barrier ()
                                : plan
                                )

                          when hasIdleWork $ void $
                            addIdleWorksReverse plan'

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
                      go newProps' newState' (acts : acc) cps

                  else do

                    writeRefs
                    go newProps' newState' acc cps

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
                      go newProps newState' (acts : acc) cps

                  else do

                    writeRef
                    go newProps newState' acc cps

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
diffDeferred mounted plan plan' old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> diffDeferred' mounted plan plan' old mid new

diffDeferred' :: forall s. IORef [IO ()] -> Plan s -> Plan s -> View -> View -> View -> ST s View
diffDeferred' mounted plan plan' old mid new =
  let
      replace = do
        new' <- unsafeIOToST (build mounted Nothing new)
        replaceDeferred plan plan' old new'
  in
    case (mid,new) of
      (LazyView f a,LazyView f' a') ->
        case reallyUnsafePtrEquality# f (unsafeCoerce f') of
          1# -> case reallyUnsafePtrEquality# a (unsafeCoerce a') of
                  1# -> return old
                  _  -> diffDeferred mounted plan plan' old (view (f a)) (view (f' a'))
          _  -> replace

      (ComponentView t p _ v,ComponentView t' p' _ v') ->
        case old of
          ComponentView _ _ ~(Just r0) _
            | sameTypeWitness t t' ->
              case reallyUnsafePtrEquality# p (unsafeCoerce p') of
                1# -> return old
                _  -> do
                      let r = unsafeCoerce r0
                      unsafeIOToST $ setProps r p'
                      return (ComponentView t' p' (Just r) v')
            | otherwise -> unsafeIOToST $ do
              mtd <- newIORef []
              new' <- build mtd Nothing new
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
                fs <- diffFeaturesDeferred (coerce $ fromJust $ getHost old) plan (features old) (features mid) (features new)
                return old { features = fs }
              _  -> replace
          _ -> replace

      (SomeView m,SomeView n)
        | sameTypeWitness (__pure_witness (asProxyOf m)) (__pure_witness (asProxyOf n)) ->
          case reallyUnsafePtrEquality# m (unsafeCoerce n) of
            1# -> return old
            _  -> diffDeferred mounted plan plan' old (view m) (view n)
        | otherwise -> replace

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
          built@(getHost -> Just h) <- unsafeIOToST (build mounted Nothing (portalView new))
          amendPlan plan' (cleanup old)
          amendPlan plan $ do
            for_ (getHost (portalView old)) removeNode
            append (toNode $ portalDestination new) h
          -- recycling the portalProxy
          return (PortalView (portalProxy old) (portalDestination new) built)

      (_,PortalView{}) -> do
        proxy <- unsafeIOToST (build mounted Nothing (NullView Nothing))
        replaceDeferred plan plan' old proxy
        built@(getHost -> Just h) <- unsafeIOToST (build mounted Nothing (portalView new))
        amendPlan plan $ append (toNode $ portalDestination new) h
        return (PortalView (fmap coerce $ getHost proxy) (portalDestination new) built)

      (PortalView{},_) -> do
        amendPlan plan (cleanup old)
        amendPlan plan $ for_ (getHost (portalView old)) removeNode
        replace

      _ -> replace

diffElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
  unsafeIOToST yield_
  !fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  !cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
  return $ old
    { features = fs
    , children = cs
    }

diffSVGElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffSVGElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
  unsafeIOToST yield_
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  !fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  !cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

diffFeaturesDeferred :: Element -> Plan s -> DiffST s Features
diffFeaturesDeferred e plan old !mid !new = do
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> diffFeaturesDeferred' e plan old mid new

diffFeaturesDeferred' :: Element -> Plan s -> DiffST s Features
diffFeaturesDeferred' e plan old mid new = do
  diffClassesDeferred    e plan (classes mid) (classes new)
  diffStylesDeferred     e plan (styles mid) (styles new)
  diffAttributesDeferred e plan (attributes mid) (attributes new)
  diffPropertiesDeferred e plan (properties mid) (properties new)
  ls <- diffListenersDeferred e plan (listeners old) (listeners mid) (listeners new)
  diffLifecyclesDeferred e plan (lifecycles old) (lifecycles mid) (lifecycles new)
  return old { listeners = ls }

diffXLinksDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffXLinksDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffXLinksDeferred' e p mid new

diffXLinksDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffXLinksDeferred' e p mid new = do

      let remove = removeAttributeNS e "http://www.w3.org/1999/xlink"
          removals = Map.keys (Map.difference mid new)
          r = traverse_ remove removals
      amendPlan p r

      let add (k,v) = setAttributeNS e "http://www.w3.org/1999/xlink" k v
          adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          a = traverse_ add adds
      amendPlan p a

diffClassesDeferred :: Element ->Plan s -> Set Txt -> Set Txt -> ST s ()
diffClassesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffClassesDeferred' e p mid new

diffClassesDeferred' :: Element ->Plan s -> Set Txt -> Set Txt -> ST s ()
diffClassesDeferred' e p mid new
  | Set.null mid && Set.null new = return ()
  | Set.null new = amendPlan p (removeProperty e "className")
  | otherwise =
    let cs = Txt.intercalate " " $ Set.toList $ Set.delete "" new
    in amendPlan p (setProperty e "className" cs)

diffStylesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffStylesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffStylesDeferred' e p mid new

diffStylesDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffStylesDeferred' e p mid new = do

      let remove = removeStyle e
          removes = Map.keys (Map.difference mid new)
          r = traverse_ remove removes
      amendPlan p r

      let add (k,v) = setStyle e k v
          adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          a = traverse_ add adds
      amendPlan p a

diffAttributesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffAttributesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffAttributesDeferred' e p mid new

diffAttributesDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffAttributesDeferred' e p mid new = do

      let remove = removeAttribute e
          removes = Map.keys (Map.difference mid new)
          r = traverse_ remove removes
      amendPlan p r

      let add (k,v) = setAttribute e k v
          adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          a = traverse_ add adds
      amendPlan p a

diffPropertiesDeferred :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffPropertiesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> diffPropertiesDeferred' e p mid new

diffPropertiesDeferred' :: Element -> Plan s -> Map Txt Txt -> Map Txt Txt -> ST s ()
diffPropertiesDeferred' e p mid new = do

      let remove = removeProperty e
          removes = Map.keys (Map.difference mid new)
          r = traverse_ remove removes
      amendPlan p r

      let add (k,v) = setProperty e k v
          adds = Map.toList $ Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
          a = traverse_ add adds
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

diffLifecyclesDeferred :: Element -> Plan s -> [Lifecycle] -> [Lifecycle] -> [Lifecycle] -> ST s ()
diffLifecyclesDeferred e p old mid new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  ->
      diffLifecyclesDeferred' e p old mid new

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

diffChildrenDeferred :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> DiffST s [View]
diffChildrenDeferred e mounted plan plan' olds mids news =
  case reallyUnsafePtrEquality# mids news of
    1# -> return olds
    _  -> diffChildrenDeferred' e mounted plan plan' olds mids news

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
    go olds mids news =
      case reallyUnsafePtrEquality# mids news of
        1# -> return olds
        _  -> go' olds mids news

    go' (old:olds) (mid:mids) (new:news) = do
      new'  <- diffDeferred mounted plan plan' old mid new
      news' <- go olds mids news
      return (new' : news')

    go' olds _ [] = do
      removeManyDeferred plan plan' olds
      return []

    go' [] _ news = do
      frag <- unsafeIOToST createFrag
      let n = Just (toNode frag)
      news' <- unsafeIOToST (for news (build mounted n))
      amendPlan plan (append e frag)
      return news'

removeManyDeferred :: Plan s -> Plan s -> [View] -> ST s ()
removeManyDeferred plan plan' vs = do
  amendPlan plan  (for_ vs (traverse_ removeNodeMaybe . getHost))
  amendPlan plan' (for_ vs cleanup)

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
diffSVGKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
  unsafeIOToST yield_
  !fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  !cs <- diffKeyedChildrenDeferred e mounted plan plan' (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  return $ old
    { features = fs
    , keyedChildren = cs
    }

diffKeyedElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
diffKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
  unsafeIOToST yield_
  !fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  !cs <- diffKeyedChildrenDeferred e mounted plan plan' (keyedChildren old) (keyedChildren mid) (keyedChildren new)
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
diffKeyedChildrenDeferred :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s [(Int,View)]
diffKeyedChildrenDeferred e mounted plan plan' olds mids news = do
  case reallyUnsafePtrEquality# mids news of
    1# -> return olds
    _  -> diffKeyedChildrenDeferred' e mounted plan plan' olds mids news

diffKeyedChildrenDeferred' :: forall s. Element -> IORef [IO ()] -> Plan s -> Plan s -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s [(Int,View)]
diffKeyedChildrenDeferred' (toNode -> e) mounted plan plan' olds mids news = do
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
          news'    <- dKCD_slow dc olds mids news
          removals <- readSTRef dc

          -- cleanup
          -- remove them in reverse order they were added since they were
          -- diffed beginning to end and added with (_:) rather than (++[_])
          removeManyDeferred plan plan' (reverse removals)

          return news'

  where
    dKCD_slow :: Removals s -> DiffST s [(Int,View)]
    dKCD_slow dc = go 0
      where
        go :: Int -> DiffST s [(Int,View)]
        go !i olds0 mids0 news0 = do
          case reallyUnsafePtrEquality# mids0 news0 of
            1# -> return olds0
            _  -> go' i olds0 mids0 news0

        go' :: Int -> DiffST s [(Int,View)]

        -- Invariant: we can always infer the shape of `mids` from the shape of `olds`;
        --            mids should always be an irrefutable pattern

        -- 2+ 2+
        go' i (o0@(ok0,old0):os1@(o1@(ok1,old1):os2)) ~(m0@(mk0,mid0):ms1@(m1@(mk1,mid1):ms2)) ns@(n0@(nk0,new0):ns1@(n1@(nk1,new1):ns2))
          | mk0 == nk0 = do
              -- diff mk0 and nk0
              n  <- dKCD_helper o0 m0 n0
              ns <- go (i + 1) os1 ms1 ns1
              return (n:ns)

          | mk0 == nk1 && mk1 == nk0 = do
              -- swap mk0 mk1 and diff them in turn
              let ins (Just _0) (Just _1) = amendPlan plan (insertBefore _1 _0)
              ins (getHost old0) (getHost old1)
              n0' <- dKCD_helper o1 m1 n0
              n1' <- dKCD_helper o0 m0 n1
              ns  <- go (i + 2) os2 ms2 ns2
              return (n0':n1':ns)

          | mk0 == nk1 = do
              -- insert nk0
              n0' <- dKCD_ins i nk0 new0
              n1' <- dKCD_helper o0 m0 n1
              ns  <- go (i + 2) os1 ms1 ns2
              return (n0':n1':ns)

          | otherwise = do
              -- delete m0
              modifySTRef' dc (old0:)
              go (i + 1) os1 ms1 ns

        -- 1 2+
        go' i (os@[o@(ok,old)]) ~(ms@[m@(mk,mid)]) new@(n0@(nk0,new0):ns@((nk1,new1):_))
          | mk == nk0 = do
              -- diff mk and nk0
              n'  <- dKCD_helper o m n0
              ns' <- go (i + 1) [] [] ns
              return (n':ns')
          | mk == nk1 = do
              -- insert nk0
              n'  <- dKCD_ins i nk0 new0
              ns' <- go (i + 1) os ms ns
              return (n':ns')
          | otherwise = do
              -- delete mk
              modifySTRef' dc (old:)
              go (i + 1) [] [] new

        -- 1+ 1
        go' i (o@(ok,old):os) ~(m@(mk,mid):ms) (ns@[n@(nk,new)])
          | mk == nk = do
              -- diff mk and nk
              n' <- dKCD_helper o m n
              ns' <- go (i + 1) os ms []
              return (n':ns')
          | otherwise = do
              -- delete mk
              modifySTRef' dc (old:)
              go (i + 1) os ms ns

        -- 0+ 0
        go' _ olds mids [] = do
          for_ olds (modifySTRef' dc . (:) . snd)
          return []

        -- 0 0+
        go' _ [] _ news = do
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
          removals <- readSTRef dc
          let ins (Just a) = amendPlan plan (insertAt (coerce e) a i)
          n' <- unsafeIOToST (build mounted Nothing new)
          ins (getHost n')
          return (nk,n')

