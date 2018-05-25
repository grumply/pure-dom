{-# LANGUAGE CPP, OverloadedStrings, RankNTypes, ScopedTypeVariables, PatternSynonyms, ViewPatterns, MagicHash, RecordWildCards, BangPatterns #-}
module Pure.DOM (inject) where

-- from base
import Control.Arrow ((&&&))
import Control.Concurrent (MVar,newEmptyMVar,putMVar,takeMVar,tryPutMVar,yield,forkIO,myThreadId,killThread)
import Control.Monad.ST (ST,runST)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad (void,(<=<),unless,join,when)
import Data.Coerce (coerce)
import Data.Foldable (for_,traverse_)
import Data.Function (fix)
import Data.IORef (IORef,newIORef,atomicModifyIORef',modifyIORef',readIORef,writeIORef)
import Data.List as List (null,reverse,filter,length,lookup) -- REMOVE LENGTH
import Data.Maybe (fromJust,isNothing)
import Data.STRef (STRef,newSTRef,readSTRef,modifySTRef,modifySTRef,modifySTRef',writeSTRef)
import Data.Traversable (for,traverse)
import Data.Typeable (Typeable)
import GHC.Exts (inline,lazy,reallyUnsafePtrEquality#,Any)
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (head)

-- from unordered-containers
import Data.Map.Lazy (Map)
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.Map.Lazy as Map (fromList,toList,insert,lookup,delete,difference,keys,foldlWithKey',empty,null,differenceWith)
import qualified Data.Set as Set (fromList,toList,insert,delete,null)
import qualified Data.IntSet as IntSet (fromList,member)

-- from pure-core
import Pure.Data.View (Pure(..),View(..),Features(..),Listener(..),Lifecycle(..),Comp(..),Target(..),getHost,setProps,queueComponentUpdate,Ref(..),ComponentPatch(..))

-- from pure-lifted
import Pure.Animation (addAnimation)
import Pure.IdleWork (addIdleWork)
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
  ,setInnerHTML

  -- node replacement
  ,replaceNode
  ,replaceText
  ,insertBefore

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

  -- idle callback
  ,requestIdleCallback

  -- node getters
  ,getBody
  ,getDocument
  ,getHead
  ,getWindow

  -- JSV reference equality check
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
import qualified Pure.Data.Txt as Txt (append,intercalate)

import Debug.Trace

type Plan s = STRef s [IO ()]
type DiffST s a = a -> a -> a -> ST s a
type DiffCtx s = STRef s (Node,Map Int View)

{-# INLINE newPlan #-}
newPlan :: ST s (Plan s)
newPlan = newSTRef []

{-# INLINE buildPlan #-}
buildPlan :: IO () -> (forall s. Plan s -> Plan s -> ST s a) -> ([IO ()],a)
buildPlan bc f = runST $ do
  p  <- newPlan
  p' <- newPlan
  a  <- f p p'
  p  <- readSTRef p
  p' <- readSTRef p'
  let plan =
        case p' of
          [] -> bc : p
          _  -> void (addIdleWork (runPlan p')) : bc : p
  return (plan,a)

{-# INLINE amendPlan #-}
amendPlan :: Plan s -> IO () -> ST s ()
amendPlan plan f = modifySTRef' plan (f:)

{-# INLINE runPlan #-}
runPlan :: [IO ()] -> IO ()
runPlan = foldr (flip (>>)) (return ())

-- | Given a host node and a View, build and embed the View.
inject :: Element -> View -> IO ()
inject host v = do
  mtd <- newIORef []
  build True mtd (Just $ toNode host) v
  foldr (flip (>>)) (return ()) =<< readIORef mtd
  where
    build :: Bool -> IORef [IO ()] -> Maybe Node -> View -> IO View
    build first mtd = go
      where
        go mparent (SomeView _ r) = go mparent (view r)
        go mparent (ComponentView name props _ comp) = do
          stq    <- newIORef . Just =<< newQueue
          props_ <- newIORef props
          state_ <- newIORef undefined
          live_  <- newIORef undefined
          let c = comp cr
              cr = Ref name live_ props_ state_ c stq
          state1 <- construct c
          writeIORef state_ state1
          state2 <- mount c state1
          writeIORef state_ state2
          let new = render c props state2
          live <- go mparent new
          writeIORef live_ live
          modifyIORef' mtd ((mounted c):)
          newComponentThread cr new live props state2
          return $ ComponentView name props (Just cr) comp
        go mparent (TextView _ t) = do
          tn <- createText t
          for_ mparent (`append` tn)
          return $ TextView (Just tn) t
        go mparent HTMLView {..} = do
          e <- create tag
          ls <- setFeatures e features
          let n = Just (toNode e)
          -- unless first yield
          !cs <- for children (go n)
          for_ mparent (`append` e)
          return $ HTMLView (Just e) tag features { listeners = ls } cs
        go mparent RawView {..} = do
          e <- create tag
          ls <- setFeatures e features
          setInnerHTML e content
          for_ mparent (`append` e)
          return $ RawView (Just e) tag features { listeners = ls } content
        go mparent SVGView {..} = do
          e <- createNS "http://www.w3.org/2000/svg" tag
          ls <- setFeatures e features
          setXLinks e xlinks
          let n = Just (toNode e)
          -- unless first yield
          !cs <- for children (go n)
          for_ mparent (`append` e)
          return $ SVGView (Just e) tag features { listeners = ls } xlinks cs
        go mparent KHTMLView {..} = do
          e <- create tag
          ls <- setFeatures e features
          let n = Just (toNode e)
          -- unless first yield
          !cs <- for keyedChildren (traverse (go n))
          for_ mparent (`append` e)
          return $ KHTMLView (Just e) tag features { listeners = ls } cs
        go mparent KSVGView {..} = do
          e <- createNS "http://www.w3.org/2000/svg" tag
          ls <- setFeatures e features
          setXLinks e xlinks
          let n = Just (toNode e)
          -- unless first yield
          !cs <- for keyedChildren (traverse (go n))
          for_ mparent (`append` e)
          return $ KSVGView (Just e) tag features { listeners = ls } xlinks cs
        go mparent NullView{} = do
          e <- create "template"
          for_ mparent (`append` e)
          return $ NullView (Just e)
        go mparent PortalView{..} = do
          v <- go (Just $ toNode portalDestination) portalView
          return $ PortalView portalDestination v

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
              | otherwise   = setProperty e "className" $ Txt.intercalate " " $ Set.toList $ Set.delete "" cs

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

        newComponentThread :: forall m props state. Ref m props state -> View -> View -> props -> state -> IO ()
        newComponentThread ref@Ref { crComponent = Comp {..}, ..} view0 live0 props0 state0 = do
            Just pq <- readIORef crPatchQueue
            void $ forkIO $ execute $
              flip fix (view0,live0,props0,state0) $ \start (old,live,props,state) -> do
                flip fix (props,state,[],[]) $ \worker (newProps,newState,acc,cps) ->
                  case (acc,cps) of
                    ([],[]) -> performIO (collect pq) >>= \cps -> worker (newProps,newState,[],cps)
                    (acc,[]) -> do
                      dus <- for (List.reverse acc) $ \(willUpd,didUpd,callback) -> do
                        willUpd
                        return (didUpd,callback)
                      (new,new_live) <- performIO $ do
                        let new =
                              case reallyUnsafePtrEquality# props newProps of
                                1# -> case reallyUnsafePtrEquality# state newState of
                                        1# -> old
                                        _  -> render props newState
                                _  -> case reallyUnsafePtrEquality# state newState of
                                        1# -> render newProps state
                                        _  -> render newProps newState
                        mtd <- newIORef []
                        barrier <- newEmptyMVar
                        let (plan,new_live) = buildPlan (putMVar barrier ()) (\p p' -> diffDeferred mtd p p' live old new)
                        plan `seq` new_live `seq` writeIORef crView new_live
                        mtd <- readIORef mtd
                        case plan of
                          -- Just the putMVar
                          [_] -> do
                            runPlan mtd
                            return (new,new_live)
                          _   -> do
                            addAnimation (runPlan plan)
                            takeMVar barrier
                            runPlan mtd
                            return (new,new_live)
                      cbs <- for dus $ \(du,c) -> do
                        du new_live
                        return c
                      sequence_ cbs
                      start (new,new_live,newProps,newState)
                    (acc,cp:cps) ->
                      case cp of
                        Unmount mv mtd -> do
                          unmount
                          performIO $ do
                            writeIORef crPatchQueue Nothing
                            barrier <- newEmptyMVar
                            live <- readIORef crView
                            let (p,_) = buildPlan (putMVar barrier ()) (\p p' ->
                                            let removeDeferred plan plan' live = do
                                                  for_ (getHost live) $ \host -> amendPlan p $ removeNodeMaybe host
                                                  amendPlan p' (cleanup live)
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
                                            in maybe (removeDeferred p p' live) (void . replaceDeferred p p' live) mv
                                          )
                            addAnimation (runPlan p)
                            takeMVar barrier
                            mtd
                          unmounted
                        UpdateProperties newProps' -> do
                          newState'    <- receive newProps' newState
                          shouldUpdate <- force   newProps' newState'
                          let writeRefs = writeIORef crProps newProps' >> writeIORef crState newState'
                          if shouldUpdate || not (List.null acc) then
                            let
                              will = update  newProps' newState'
                              did  = updated newProps  newState
                            in
                              worker (newProps',newState',(will >> performIO writeRefs,did,performIO (return ())) : acc,cps)
                          else do
                            performIO writeRefs
                            worker (newProps',newState',acc,cps)
                        UpdateState f -> do
                          (newState',updatedCallback) <- f newProps newState
                          shouldUpdate                <- force newProps newState'
                          let writeRef = writeIORef crState newState'
                          if shouldUpdate || not (List.null acc) then
                            let
                              will = update  newProps newState'
                              did  = updated newProps newState
                            in
                              worker (newProps,newState',(will >> performIO writeRef,did,updatedCallback) : acc,cps)
                          else do
                            performIO writeRef
                            worker (newProps,newState',acc,cps)

              -- for_ mcs $ outer view0 live0 props0 state0 []
          where
          --   {-# INLINE await #-}
          --   await = performIO $ do
          --     mq <- readIORef crPatchQueue
          --     for mq collect

          --   {-# INLINE outer #-}
          --   outer old live props state = inner props state
          --     where
          --       {-# INLINE inner #-}
          --       inner newProps newState = worker
          --         where
          --           {-# INLINE worker #-}
          --           worker :: [(m (),View -> m (),m ())] -> [ComponentPatch m props state] -> m ()
          --           worker [] [] = await >>= traverse_ (worker [])
          --           worker acc [] = do
          --             dus <- for (List.reverse acc) $ \(willUpd,didUpd,callback) -> do
          --               willUpd
          --               return (didUpd,callback)
          --             (new,new_live) <- performIO $ do
          --               let new = render newProps newState
          --               case reallyUnsafePtrEquality# old new of
          --                 1# -> print "Same view"
          --                 _  -> print "Different view"
          --               mtd <- newIORef []
          --               barrier <- newEmptyMVar
          --               let (plan,new_live) = buildPlan (putMVar barrier ()) (\p p' -> diffDeferred mtd p p' live old new)
          --               plan `seq` new_live `seq` writeIORef crView new_live
          --               mtd <- readIORef mtd
          --               case plan of
          --                 -- Just the putMVar
          --                 [_] -> do
          --                   runPlan mtd
          --                   return (new,new_live)
          --                 _   -> do
          --                   addAnimation (runPlan plan)
          --                   takeMVar barrier
          --                   runPlan mtd
          --                   return (new,new_live)
          --             cbs <- for dus $ \(du,c) -> do
          --               du new_live
          --               return c
          --             sequence_ cbs
          --             mcs <- await
          --             for_ mcs $ outer new new_live newProps newState []

          --           worker acc (cp : cps) = do
          --             case cp of
          --               Unmount mv mtd -> do
          --                 unmount
          --                 performIO $ do
          --                   writeIORef crPatchQueue Nothing
          --                   barrier <- newEmptyMVar
          --                   live <- readIORef crView
          --                   let (p,_) = buildPlan (putMVar barrier ()) (\p p' ->
          --                                   let removeDeferred plan plan' live = do
          --                                         for_ (getHost live) $ \host -> amendPlan p $ removeNodeMaybe host
          --                                         amendPlan p' (cleanup live)
          --                                       replaceDeferred plan plan' old@(getHost -> oldHost) new@(getHost -> newHost) =
          --                                         case oldHost of
          --                                           Nothing -> error "Expected old host in replaceDeferred; got nothing."
          --                                           Just oh ->
          --                                             case newHost of
          --                                               Nothing -> error "Expected new host in replaceDeferred; got nothing."
          --                                               Just nh -> do
          --                                                 amendPlan plan (replaceNode oh nh)
          --                                                 amendPlan plan' (cleanup old)
          --                                                 return new
          --                                   in maybe (removeDeferred p p' live) (void . replaceDeferred p p' live) mv
          --                                 )
          --                   addAnimation (runPlan p)
          --                   takeMVar barrier
          --                   mtd
          --                 unmounted
          --                 performIO $ do
          --                   killThread =<< myThreadId
          --               UpdateProperties newProps' -> do
          --                 newState'    <- receive newProps' newState
          --                 shouldUpdate <- force   newProps' newState'
          --                 let writeRefs = writeIORef crProps newProps' >> writeIORef crState newState'
          --                 if shouldUpdate || not (List.null acc) then
          --                   let
          --                     will = update  newProps' newState'
          --                     did  = updated newProps  newState
          --                   in
          --                     inner newProps' newState' ((will >> performIO writeRefs,did,performIO (return ())) : acc) cps
          --                 else do
          --                   performIO writeRefs
          --                   inner newProps' newState' acc cps
          --               UpdateState f -> do
          --                 (newState',updatedCallback) <- f newProps newState
          --                 case reallyUnsafePtrEquality# newState newState' of
          --                   1# -> performIO $ print "Same new state"
          --                   _  -> performIO $ print "Different new state"
          --                 shouldUpdate                <- force newProps newState'
          --                 let writeRef = writeIORef crState newState'
          --                 if shouldUpdate || not (List.null acc) then
          --                   let
          --                     will = update  newProps newState'
          --                     did  = updated newProps newState
          --                   in
          --                     inner newProps newState' ((will >> performIO writeRef,did,updatedCallback) : acc) cps
          --                 else do
          --                   performIO writeRef
          --                   inner newProps newState' acc cps

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

                _  ->
                  let
                      replace = unsafeIOToST (build False mounted Nothing new) >>= replaceDeferred plan plan' old
                  in
                    case (mid,new) of
                      (NullView{},NullView{}) -> return old

                      (TextView _ t,TextView _ t') ->
                        case reallyUnsafePtrEquality# t t' of
                          0# | t /= t' -> replaceTextContentDeferred plan old new
                          _ -> return old

                      (SomeView t m,SomeView t' n) ->
                        case reallyUnsafePtrEquality# m (unsafeCoerce n) of
                          1# -> return old
                          _  ->
                            case reallyUnsafePtrEquality# t t' of
                              0# | t /= t' -> replace
                              _            -> diffDeferred mounted plan plan' old (view m) (view n)

                      (HTMLView{},HTMLView{}) ->
                        case reallyUnsafePtrEquality# (tag mid) (tag new) of
                          1# -> diffElementDeferred mounted plan plan' old mid new
                          _ | tag mid == tag new -> diffElementDeferred mounted plan plan' old mid new
                            | otherwise          -> replace

                      (SVGView{},SVGView{})
                        | tag mid == tag new -> diffElementDeferred mounted plan plan' old mid new
                        | otherwise          -> replace

                      (KHTMLView{},KHTMLView{})
                        | tag mid == tag new -> diffKeyedElementDeferred mounted plan plan' old mid new
                        | otherwise          -> replace

                      (KSVGView{},KSVGView{})
                        | tag mid == tag new -> diffKeyedElementDeferred mounted plan plan' old mid new
                        | otherwise          -> replace

                      (PortalView{},PortalView{})
                        | same (toJSV (portalDestination old)) (toJSV (portalDestination new)) ->
                          diffElementDeferred mounted plan plan' (portalView old) (portalView mid) (portalView new)
                        | otherwise -> do
                              built@(getHost -> Just h) <- unsafeIOToST (build False mounted Nothing (portalView new))
                              amendPlan plan' (cleanup old)
                              amendPlan plan $ do
                                remove old
                                append h (toNode $ portalDestination new)
                              return (PortalView (portalDestination new) built)

                      (ComponentView t p _ v,ComponentView t' p' _ v') -> unsafeIOToST $
                        case reallyUnsafePtrEquality# p (unsafeCoerce p') of
                          1# -> return old
                          _  ->
                                  case old of
                                    ComponentView _ _ ~(Just r0) _ ->
                                      case reallyUnsafePtrEquality# t t' of
                                        0# | t /= t' -> do
                                          mtd <- newIORef []
                                          new' <- build False mtd Nothing new
                                          queueComponentUpdate r0 (Unmount (Just new') (readIORef mtd >>= runPlan))
                                          return new'
                                        _ -> do
                                          let r = unsafeCoerce r0
                                          setProps r p'
                                          return (ComponentView t' p' (Just r) v')

                      _ -> replace

              where
                diffElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
                diffElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
                  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
                  !cs <- diffChildrenDeferred e mounted plan plan' (children old) (children mid) (children new)
                  return old
                    { features = fs
                    , children = cs
                    }

                diffSVGElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
                diffSVGElementDeferred mounted plan plan' old@(elementHost -> Just e) mid new = do
                  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
                  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
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

                removeStyles :: Element -> Map Txt Txt -> IO ()
                removeStyles e = traverse_ (removeStyle e . fst) . Map.toList

                removeAttributes :: Element -> Map Txt Txt -> IO ()
                removeAttributes e = traverse_ (removeAttribute e . fst) . Map.toList

                removeProperties :: Element -> Map Txt Txt -> IO ()
                removeProperties e = traverse_ (removeProperty e . fst) . Map.toList

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

                diffChildrenDeferred :: Element -> IORef [IO ()] -> Plan s -> Plan s -> DiffST s [View]
                diffChildrenDeferred (toNode -> e) mounted plan plan' = cleanupCheck
                  where
                    cleanupCheck :: DiffST s [View]
                    cleanupCheck olds mids news = do
                      case reallyUnsafePtrEquality# mids news of
                        1# -> return olds
                        _  -> if Prelude.null news
                                then do
                                  amendPlan plan (clearNode e)
                                  amendPlan plan' (for_ olds cleanup)
                                  return []
                                else go olds mids news

                    start :: DiffST s [View]
                    start olds mids news =
                      case reallyUnsafePtrEquality# mids news of
                        1# -> return olds
                        _  -> go olds mids news

                    go :: DiffST s [View]
                    go olds _ [] = do
                      for_ olds (removeDeferred plan plan')
                      return []

                    go [] _ news = do
                      frag <- unsafeIOToST createFrag
                      let n = Just (toNode frag)
                      news' <- for news (unsafeIOToST . build False mounted n)
                      amendPlan plan (append e frag)
                      return news'

                    go (old:olds) (mid:mids) (new:news) = do
                      new'  <- diffDeferred mounted plan plan' old mid new
                      news' <- start olds mids news
                      return (new' : news')

                removeDeferred :: Plan s -> Plan s -> View -> ST s ()
                removeDeferred plan plan' v = do
                  for_ (getHost v) $ \host -> amendPlan plan $ do
                    removeNodeMaybe host
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
                  return old { content = content new }

                remove :: View -> IO ()
                remove v = do
                  for_ (getHost v) removeNode
                  cleanup v

                diffSVGKeyedElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
                diffSVGKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
                  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
                  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
                  !cs <- diffKeyedChildrenDeferred e mounted plan plan' (IntSet.fromList $ fmap fst (keyedChildren new)) (keyedChildren old) (keyedChildren mid) (keyedChildren new)
                  return old
                    { features = fs
                    , keyedChildren = cs
                    }

                diffKeyedElementDeferred :: IORef [IO ()] -> Plan s -> Plan s -> DiffST s View
                diffKeyedElementDeferred mounted plan plan' old@(elementHost -> Just e) !mid !new = do
                  !fs <- diffFeaturesDeferred e plan plan' (features old) (features mid) (features new)
                  !cs <- diffKeyedChildrenDeferred e mounted plan plan' (IntSet.fromList $ fmap fst (keyedChildren new)) (keyedChildren old) (keyedChildren mid) (keyedChildren new)
                  return old
                    { features = fs
                    , keyedChildren = cs
                    }

                diffKeyedChildrenDeferred :: Element -> IORef [IO ()] -> Plan s -> Plan s -> IntSet -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s [(Int,View)]
                diffKeyedChildrenDeferred (toNode -> e) mounted plan plan' keys olds mids news =
                  case reallyUnsafePtrEquality# mids news of
                    1# -> return olds
                    _  ->
                      case (mids,news) of
                        ([],[]) -> return olds
                        ([],_)  -> do
                          frag <- unsafeIOToST createFrag
                          let f = Just (toNode frag)
                          amendPlan plan (append e frag)
                          news' <- for news $ \(i,n) -> do
                            new' <- unsafeIOToST $ build False mounted f n
                            return (i,new')
                          return news'
                        (_,[])  -> do
                          amendPlan plan (clearNode e)
                          amendPlan plan' (for_ olds (traverse_ cleanup))
                          return []
                        _       -> do
                          dc             <- newSTRef (e,mempty)
                          news'          <- dKCD_slow dc mounted plan plan' keys olds mids news
                          (_,removals)   <- readSTRef dc
                          for_ (Map.toList removals) $ \(i,r) ->
                            removeDeferred plan plan' r
                          return news'

                dKCD_ins :: DiffCtx s -> IORef [IO ()] -> Plan s -> Int -> Int -> View -> ST s (Int,View)
                dKCD_ins dc mounted plan i nk new = do
                  (e,removals) <- readSTRef dc
                  let ins i ~(Just a) = amendPlan plan (insertAt (coerce e) a i)
                  case Map.lookup nk removals of
                    Nothing -> do
                      n' <- unsafeIOToST (build False mounted Nothing new)
                      writeSTRef dc (e,removals)
                      ins i (getHost n')
                      return (nk,n')
                    Just n -> do
                      let removals' = Map.delete nk removals
                      writeSTRef dc (e,removals')
                      ins (i + 1) (getHost n)
                      return (nk,n)

                dKCD_slow :: DiffCtx s -> IORef [IO ()] -> Plan s -> Plan s -> IntSet -> DiffST s [(Int,View)]
                dKCD_slow dc mounted plan plan' keys = start 0
                  where
                    start _ olds _ [] = do
                      for_ olds $ \(ok,o) -> modifySTRef' dc $ \(e,removals) ->
                        let !removals' = Map.insert ok o removals
                        in (e,removals')
                      return []

                    start _ [] _ news = do
                      for news $ \(i,new) -> do
                        (e,removals) <- readSTRef dc
                        case Map.lookup i removals of
                          Nothing -> do
                            new' <- unsafeIOToST (build False mounted Nothing new)
                            for (getHost new') $ amendPlan plan . append e
                            return (i,new')
                          Just r  -> do
                            let removals' = Map.delete i removals
                            writeSTRef dc (e,removals')
                            for (getHost r) $ amendPlan plan . append e
                            return (i,r)

                    start i ~olds@((ok,old):olds') ~mids@((mk,mid):mids') ~news@((nk,new):news')
                      | mk == nk = do
                        new' <- diffDeferred mounted plan plan' old mid new
                        news'' <- start (i + 1) olds' mids' news'
                        return ((nk,new'):news'')
                      | otherwise = go i olds mids news

                    go i [o@(ok,old)] ~[m@(mk,mid)] (n0@(nk0,new0):n1@(nk1,new1):ns) = do
                      if mk == nk0
                        then do
                          n' <- dKCD_helper dc mounted plan plan' o m n0
                          ns' <- go (i + 1) [] [] (n1:ns)
                          return (n':ns')
                        else
                          if mk == nk1
                            then do
                              n'  <- dKCD_ins dc mounted plan i nk0 new0
                              ns' <- go (i + 1) [o] [m] (n1:ns)
                              return (n':ns')
                            else do
                              modifySTRef' dc $ \(e,removals) ->
                                let !removals' = Map.insert mk old removals
                                in (e,removals')
                              n' <- dKCD_ins dc mounted plan i nk0 new0
                              ns' <- go (i + 1) [] [] (n1:ns)
                              return (n':ns')

                    go i [o@(ok,old)] ~[m@(mk,mid)] ~[n@(nk,new)] = do
                      if mk == nk
                        then do
                          n' <- dKCD_helper dc mounted plan plan' o m n
                          return [n']
                        else do
                          modifySTRef' dc $ \(e,removals) ->
                            let !removals' = Map.insert mk old removals
                            in (e,removals')
                          n' <- dKCD_ins dc mounted plan i nk new
                          return [n']

                    go i ~(o@(ok,old):os) ~(m@(mk,mid):ms) ns@[n@(nk,new)] = do
                      if mk == nk
                        then do
                          n' <- dKCD_helper dc mounted plan plan' o m n
                          ns' <- go (i + 1) os ms []
                          return (n':ns')
                        else do
                          modifySTRef' dc $ \(e,removals) ->
                            let !removals' = Map.insert mk old removals
                            in (e,removals')
                          start i os ms ns

                    go i ~os0@(o0@(ok0,old0):os1@(o1@(ok1,old1):os2)) ~ms0@(m0@(mk0,mid0):ms1@(m1@(mk1,mid1):ms2)) ~ns@(n0@(nk0,new0):ns1@(n1@(nk1,new1):ns2))
                      | mk0 == nk0 = do
                          n <- dKCD_helper dc mounted plan plan' o0 m0 n0
                          case reallyUnsafePtrEquality# ms1 ns1 of
                            1# -> return (n:os1)
                            _  -> do
                              ns <- start (i + 1) os1 ms1 ns1
                              return (n:ns)

                      | mk0 == nk1 && mk1 == nk0 = do
                          -- swap mk0 mk1
                          (e,_) <- readSTRef dc
                          let ins ~(Just b) = amendPlan plan (insertAt (coerce e) b i)
                          ins (getHost old1)
                          case reallyUnsafePtrEquality# ms2 ns2 of
                            1# -> return (o1:o0:os2)
                            _  -> do
                              ns <- start (i + 2) os2 ms2 ns2
                              return (o1:o0:ns)

                      | mk0 == nk1 = do
                          -- insert nk0
                          n0 <- dKCD_ins dc mounted plan i nk0 new0
                          case reallyUnsafePtrEquality# ms0 ns1 of
                            1# -> return (n0:os0)
                            _  -> do
                              ns <- start (i + 1) os0 ms0 ns1
                              return (n0:ns)

                      | mk1 == nk0 = do
                          -- delete mk0
                          modifySTRef' dc $ \(e,removals) ->
                            let !removals' = Map.insert mk0 old0 removals
                            in (e,removals')
                          case reallyUnsafePtrEquality# ms1 ns of
                            1# -> return os1
                            _  -> start i os1 ms1 ns

                      | not (IntSet.member mk0 keys) = do
                          n <- dKCD_helper dc mounted plan plan' o0 m0 n0
                          case reallyUnsafePtrEquality# ms1 ns1 of
                            1# -> return (n:os1)
                            _  -> do
                              ns <- start (i + 1) os1 ms1 ns1
                              return (n:ns)

                      | otherwise = do
                          -- remove mk0, insert nk0, diff mk1 nk1 or recurse
                          modifySTRef' dc $ \(e,removals) ->
                            let !removals' = Map.insert mk0 old0 removals
                            in (e,removals')
                          n0 <- dKCD_ins dc mounted plan i nk0 new0
                          if mk1 == nk1
                            then do
                              n1 <- dKCD_helper dc mounted plan plan' o1 m1 n1
                              case reallyUnsafePtrEquality# ms2 ns2 of
                                1# -> return (n0:n1:os2)
                                _  -> do
                                  ns <- start (i + 2) os2 ms2 ns2
                                  return (n0:n1:ns)
                            else
                              case reallyUnsafePtrEquality# ms1 ns1 of
                                1# -> return (n0:os1)
                                _  -> do
                                  ns <- start (i + 1) os1 ms1 ns1
                                  return (n0:ns)


                dKCD_helper :: DiffCtx s -> IORef [IO ()] -> Plan s -> Plan s -> (Int,View) -> (Int,View) -> (Int,View) -> ST s (Int,View)
                dKCD_helper dc mounted plan plan' (ok,old) (mk,mid) (nk,new) = do
                  new' <- diffDeferred mounted plan plan' old mid new
                  return (nk,new')
