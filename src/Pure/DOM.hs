{-# LANGUAGE CPP, OverloadedStrings, RankNTypes, ScopedTypeVariables, PatternSynonyms, ViewPatterns, MagicHash, RecordWildCards, BangPatterns #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
module Pure.DOM
  ( getProps, getState, getView, setState, setState_
  , addAnimation
  , inject, body, head
  ) where

-- from base
import Control.Arrow ((&&&))
import Control.Concurrent (MVar,newEmptyMVar,putMVar,takeMVar,tryPutMVar,yield,forkIO)
import Control.Monad.ST (ST,runST)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad (void,(<=<),unless,join,when)
import Data.Coerce (coerce)
import Data.Foldable (for_)
import Data.IORef (IORef,newIORef,atomicModifyIORef',modifyIORef,readIORef,writeIORef)
import Data.List as List (null,reverse,filter)
import Data.Maybe (fromJust)
import Data.STRef (STRef,newSTRef,readSTRef,modifySTRef',writeSTRef)
import Data.Traversable (for,traverse)
import Data.Typeable (Typeable)
import GHC.Exts (inline,lazy,reallyUnsafePtrEquality#)
import System.IO.Unsafe (unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (head)

-- from containers
import qualified Data.IntMap.Strict as IntMap (IntMap,fromList,toList,insert,lookup,delete)
import qualified Data.Map.Strict as Map (Map,mapWithKey,mergeWithKey,foldMapWithKey,difference,null,differenceWith)
import qualified Data.Set as Set (Set,null,toList)

-- from ghcjs-base
#ifdef __GHCJS__
import GHCJS.Foreign.Callback (syncCallback1,OnBlocked(..),releaseCallback)
#endif

-- from pure-core
import Pure.Data.View

-- from pure-lifted
import Pure.Data.Lifted
  (requestAnimationFrame
  ,create,createNS,createFrag,createText
  ,append
  ,setInnerHTML
  ,insertAt
  ,replaceNode,replaceText
  ,removeNode
  ,setAttribute,setAttributeNS,removeAttribute,removeAttributeNS
  ,setProperty,removeProperty
  ,setStyle,removeStyle
  ,window,document
  ,stopPropagation
  ,preventDefault
  ,addEventListener,removeEventListener
  ,getBody,getHead,getDocument
  )

-- from pure-queue
import Pure.Data.Queue (Queue,newQueue,arrive,collect)

-- from pure-txt
import Pure.Data.Txt (Txt)
import qualified Pure.Data.Txt as Txt (append,intercalate)

inject :: (IsNode host) => View -> host -> IO ()
inject v host = animator `seq` do
  mtd <- newIORef (return ())
  build mtd (Just $ toNode host) v
  join $ readIORef mtd

head :: View -> IO ()
head v = animator `seq` do
  h <- getHead
  mtd <- newIORef (return ())
  built <- build mtd Nothing v
  for_ (getHost built) (replaceNode (toNode h))
  join (readIORef mtd)

body :: View -> IO ()
body v = animator `seq` do
  b <- getBody
  mtd <- newIORef (return ())
  built <- build mtd Nothing v
  for_ (getHost built) (replaceNode (toNode b))
  join (readIORef mtd)

reallyVeryUnsafeEq :: a -> b -> Bool
reallyVeryUnsafeEq a b =
  case reallyUnsafePtrEquality# a (unsafeCoerce b) of
    1# -> True
    _  -> False

reallyUnsafeEq :: a -> a -> Bool
reallyUnsafeEq a b =
  case reallyUnsafePtrEquality# a b of
    1# -> True
    _  -> False

prettyUnsafeEq :: Eq a => a -> a -> Bool
prettyUnsafeEq a b =
  case reallyUnsafePtrEquality# a b of
    1# -> True
    _  -> a == b

newPlan :: ST s (Plan s)
newPlan = newSTRef []

buildPlan :: (forall s. Plan s -> ST s a) -> ([IO ()],a)
buildPlan f = runST $ do
  p <- newPlan
  a <- f p
  p <- readSTRef p
  return (p,a)

amendPlan :: Plan s -> IO () -> ST s ()
amendPlan plan f = modifySTRef' plan (f:)

runPlan :: [IO ()] -> IO ()
runPlan = foldr (flip (>>)) (return ())

-- If SYNC_RENDER /isn't/ defined, node building yields to other threads
-- before descending into the children of a newly built node. This allows
-- multiple components to efficiently interleave their node construction
-- which could be important in cases where one DOM subtree is excessively
-- large. If SYNC_RENDER is specified, the RTS will allow GHCJS_BUSY_YIELD
-- milliseconds (500 by default) to pass, or an entire subtree to be built,
-- before switching to another rendering thread.
-- NOTE:
--   * to avoid excessive layout thrashing, built nodes are not embedded
--     into the live DOM until all children are built
--   * SYNC_RENDER should be faster, but the default async renderer should
--     have better interactivity characteristics
#ifndef SYNC_RENDER
renderYield = yield
#else
renderYield = return ()
#endif

{-# NOINLINE build #-}
build mounted mparent (SomeView _ r) = build mounted mparent (view r)

build mounted mparent c@ComponentView{} = buildComponentView mounted mparent c

build mounted mparent (NullView _) = do
  e <- create "template"
  for_ mparent (`append` e)
  return $ NullView (Just e)

build mounted mparent (TextView _ t) = do
  tn <- createText t
  for_ mparent (`append` tn)
  return $ TextView (Just tn) t

build mounted mparent HTMLView {..} = do
  let Features_ {..} = features
  e <- create tag
  setClasses e classes
  setStyles e styles
  setAttributes e attributes
  setProperties e properties
  for lifecycles (addLifecycle mounted e)
  ls <- for listeners (addListener e)

  renderYield

  cs <- for children (build mounted (Just $ toNode e))

  for_ mparent (`append` e)

  return $ HTMLView (Just e) tag features { listeners = ls } cs

build mounted mparent KHTMLView {..} = do
  let Features_ {..} = features
  e <- create tag
  setClasses e classes
  setStyles e styles
  setAttributes e attributes
  setProperties e properties
  for lifecycles (addLifecycle mounted e)
  ls <- for listeners (addListener e)

  renderYield

  cs <- for keyedChildren (traverse (build mounted (Just $ toNode e)))

  for_ mparent (`append` e)

  return $ KHTMLView (Just e) tag features { listeners = ls } cs (IntMap.fromList cs)

build mounted mparent RawView {..} = do
  let Features_ {..} = features
  e <- create tag
  setClasses e classes
  setStyles e styles
  setAttributes e attributes
  setProperties e properties
  for lifecycles (addLifecycle mounted e)
  ls <- for listeners (addListener e)

  setInnerHTML e content

  for_ mparent (`append` e)

  return $ RawView (Just e) tag features { listeners = ls } content

build mounted mparent SVGView {..} = do
  let Features_ {..} = features
  e <- createNS "http://www.w3.org/2000/svg" tag
  setClasses e classes
  setStyles e styles
  setXLinks e xlinks
  setAttributes e attributes
  setProperties e properties
  for lifecycles (addLifecycle mounted e)
  ls <- for listeners (addListener e)

  renderYield

  cs <- for children (build mounted (Just $ toNode e))

  for_ mparent (`append` e)

  return $ SVGView (Just e) tag features { listeners = ls } xlinks cs

build mounted mparent KSVGView {..} = do
  let Features_ {..} = features
  e <- createNS "http://www.w3.org/2000/svg" tag
  setClasses e classes
  setStyles e styles
  setXLinks e xlinks
  setAttributes e attributes
  setProperties e properties
  for lifecycles (addLifecycle mounted e)
  ls <- for listeners (addListener e)

  renderYield

  cs <- for keyedChildren (traverse (build mounted (Just $ toNode e)))

  for_ mparent (`append` e)

  return $ KSVGView (Just e) tag features { listeners = ls } xlinks cs (IntMap.fromList cs)

buildComponentView :: IORef (IO ()) -> Maybe Node -> View -> IO View
buildComponentView mtd mparent ComponentView {..} = do
    stq    <- newPatchQueue
    props_ <- newIORef props
    state_ <- newIORef undefined
    live_  <- newIORef undefined
    let c = comp cr
        cr  = Ref name live_ props_ state_ c stq
    state1 <- construct c
    writeIORef state_ state1
    state2 <- mount c state1
    writeIORef state_ state2
    let new = render c props state2
    live <- build mtd mparent new
    writeIORef live_ live
    modifyIORef mtd (>> mounted c)

    -- HACK: inject the Monad dict into the componentThread by witnessing
    --       the constructor that is carrying the dict
    --  * This makes me feel like I've got the wrong interface....
    case c of Comp {} -> componentThread cr live props state2

    return $ ComponentView name props (Just cr) comp

setClasses :: Element -> Set.Set Txt -> IO ()
setClasses e cs
  | Set.null cs = return ()
  | otherwise   = setProperty e "className" $ Txt.intercalate " " $ Set.toList cs

setStyles :: Element -> Map.Map Txt Txt -> IO ()
setStyles = Map.foldMapWithKey . setStyle

setXLinks :: Element -> Map.Map Txt Txt -> IO ()
setXLinks = Map.foldMapWithKey . flip setAttributeNS "http://www.w3.org/1999/xlink"

setAttributes :: Element -> Map.Map Txt Txt -> IO ()
setAttributes = Map.foldMapWithKey . setAttribute

setProperties :: Element -> Map.Map Txt Txt -> IO ()
setProperties = Map.foldMapWithKey . setProperty

addListener :: Element -> Listener -> IO Listener
addListener e f@(On n t o a _) = do
#ifdef __GHCJS__
    let target = case t of
                  ElementTarget  -> toJSV e
                  WindowTarget   -> toJSV window
                  DocumentTarget -> toJSV document
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

addLifecycle :: IORef (IO ()) -> Element -> Lifecycle -> IO Lifecycle
addLifecycle mounted e (HostRef w) = do
  modifyIORef mounted (>> (w (toNode e)))
  return (HostRef w)

newPatchQueue :: IO (IORef (Maybe (Queue (ComponentPatch m props state))))
newPatchQueue = newIORef . Just =<< newQueue

getState :: Ref m props state -> IO state
getState = readIORef . crState

getProps :: Ref m props state -> IO props
getProps = readIORef . crProps

getView :: Ref m props state -> IO View
getView = readIORef . crView

setState :: Ref m props state -> (props -> state -> m (state,m ())) -> IO Bool
setState cr = queueComponentUpdate cr . UpdateState

setState_ :: Ref m props state -> (props -> state -> m (state,m ())) -> IO ()
setState_ r f = void (setState r f)

setProps :: Ref m props state -> props -> IO Bool
setProps cr = queueComponentUpdate cr . UpdateProperties

unmountComponent :: Ref m props state -> (Plan s -> View -> ST s (),MVar (IO ())) -> IO Bool
unmountComponent cr = queueComponentUpdate cr . uncurry Unmount

queueComponentUpdate :: Ref m props state -> ComponentPatch m props state -> IO Bool
queueComponentUpdate crec cp = do
  mq <- readIORef (crPatchQueue crec)
  case mq of
    Nothing -> return False
    Just q  -> do
      arrive q cp
      return True

componentThread :: Ref m props state -> View -> props -> state -> IO ()
componentThread ref@Ref { crComponent = c,..} live props state = void $ forkIO $ execute c $
  withRender ref c (render c props state) live props state props state [] []

withRender Ref {..} Comp {..} = outer
  where
    {-# INLINE outer #-}
    outer !old live props state = inner
      where
        {-# INLINE inner #-}
        inner newProps newState = worker
          where
            {-# INLINE worker #-}
            worker [] [] = do
              mq <- performIO (readIORef crPatchQueue)
              for_ mq (worker [] <=< performIO . collect)

            worker acc [] = do
              dus <- for (List.reverse acc) $ \(willUpd,didUpd,callback) -> do
                willUpd
                return (didUpd,callback)
              let !new = render newProps newState
              new_live <- performIO $ do
                mtd <- newIORef (return ())
                let (plan,new_live) = buildPlan (\p -> diffDeferred mtd p live old new)
                writeIORef crView new_live
                mtd <- plan `seq` readIORef mtd
                unless (List.null plan) $ do
                  barrier <- newEmptyMVar
                  addAnimation (runPlan (putMVar barrier ():plan))
                  takeMVar barrier
                mtd
                return new_live
              cbs <- for dus $ \(du,c) -> do
                du new_live
                return c
              sequence_ cbs
              performIO renderYield
              outer new new_live newProps newState newProps newState [] []

            worker acc (cp : cps) = do
              case cp of
                Unmount f plan -> do
                  unmount
                  performIO $ do
                    writeIORef crPatchQueue Nothing
                    barrier <- newEmptyMVar
                    let (p,_) = buildPlan (flip (unsafeCoerce f) live)
                    putMVar plan (runPlan (putMVar barrier ():p))
                    takeMVar barrier
                  unmounted
                UpdateProperties newProps' -> do
                  newState'      <- receive newProps' newState
                  shouldUpdate   <- force   newProps' newState'
                  let writeRefs = writeIORef crProps newProps' >> writeIORef crState newState'
                  if shouldUpdate || not (List.null acc) then
                    let
                      will = update  newProps' newState'
                      did  = updated newProps  newState
                    in
                      inner newProps' newState' ((will >> performIO writeRefs,did,performIO (return ())) : acc) cps
                  else do
                    performIO writeRefs
                    inner newProps' newState' acc cps
                UpdateState f -> do
                  (newState',updatedCallback) <- f     newProps newState
                  shouldUpdate                <- force newProps newState'
                  let writeRef = writeIORef crState newState'
                  if shouldUpdate || not (List.null acc) then
                    let
                      will = update  newProps newState'
                      did  = updated newProps newState
                    in
                      inner newProps newState' ((will >> performIO writeRef,did,updatedCallback) : acc) cps
                  else do
                    performIO writeRef
                    inner newProps newState' acc cps

{-# NOINLINE diffDeferred #-}
diffDeferred :: forall s. IORef (IO ()) -> Plan s -> View -> View -> View -> ST s View
diffDeferred mounted plan old mid new =

  case reallyUnsafePtrEquality# mid new of
    1# -> return old

    _  ->
      let
          replace = unsafeIOToST (build mounted Nothing new) >>= replaceDeferred plan old
      in
        case (mid,new) of
          (NullView{},NullView{}) -> return old

          (TextView{},TextView{}) -> replaceTextContentDeferred plan old new

          (SomeView t m,SomeView t' n) ->
            let diff = diffDeferred mounted plan old (view m) (view n)
            in
                -- if the data exactly the same, return the old
                case reallyUnsafePtrEquality# m (unsafeCoerce n) of
                  1# -> return old
                  _  ->
                      -- if the type of data is the same, diff; otherwise, replace
                      case reallyUnsafePtrEquality# t t' of
                          1#            -> diff
                          _ | t == t'   -> diff
                            | otherwise -> replace

          (HTMLView{},HTMLView{})
            | tag mid == tag new -> diffElementDeferred mounted plan old mid new
            | otherwise          -> replace

          (SVGView{},SVGView{})
            | tag mid == tag new -> diffElementDeferred mounted plan old mid new
            | otherwise          -> replace

          (KHTMLView{},KHTMLView{})
            | tag mid == tag new -> diffKeyedElementDeferred mounted plan old mid new
            | otherwise          -> replace

          (KSVGView{},KSVGView{})
            | tag mid == tag new -> diffKeyedElementDeferred mounted plan old mid new
            | otherwise          -> replace

          (ComponentView{},ComponentView{})                  -> do
            case (old,new) of
              (ComponentView t p r v,ComponentView t' p' _ v')

                -- same properties => same view
                | reallyVeryUnsafeEq p p' -> return old

                -- same type, different properties => inject properties
                | t == t' -> unsafeIOToST $ do
                    let cr = fromJust (unsafeCoerce r)
                    setProps cr (unsafeCoerce p')
                    return (ComponentView t (unsafeCoerce p') r v)

                -- different type => unmount old with a replacement
                | otherwise -> do
                    new' <- unsafeIOToST $ build mounted Nothing new
                    let cr = fromJust (unsafeCoerce r)
                    cb <- unsafeIOToST newEmptyMVar
                    unsafeIOToST $ unmountComponent cr (\p live -> void $ replaceDeferred p live new',cb)
                    -- TODO: Figure out why I decided to block here
                    plan' <- unsafeIOToST $ takeMVar cb
                    amendPlan plan plan'
                    return new'

          _ -> replace

diffSVGKeyedElementDeferred :: IORef (IO ()) -> Plan s -> DiffST s View
diffSVGKeyedElementDeferred mounted plan old@(elementHost &&& childMap -> (Just e,cm)) !mid !new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  unsafeIOToST renderYield
  (cm,cs) <- diffKeyedChildrenDeferred e mounted plan cm (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  return old
    { features = fs
    , keyedChildren = cs
    , childMap = cm
    }

diffKeyedElementDeferred :: IORef (IO ()) -> Plan s -> DiffST s View
diffKeyedElementDeferred mounted plan old@(elementHost &&& childMap -> (Just e,cm)) !mid !new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  unsafeIOToST renderYield
  (cm,cs) <- diffKeyedChildrenDeferred e mounted plan cm (keyedChildren old) (keyedChildren mid) (keyedChildren new)
  return old
    { features = fs
    , keyedChildren = cs
    , childMap = cm
    }

diffElementDeferred :: IORef (IO ()) -> Plan s -> DiffST s View
diffElementDeferred mounted plan old@(elementHost -> Just e) !mid !new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  unsafeIOToST renderYield
  cs <- diffChildrenDeferred e mounted plan (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

diffSVGElementDeferred :: IORef (IO ()) -> Plan s -> DiffST s View
diffSVGElementDeferred mounted plan old@(elementHost -> Just e) !mid !new = do
  fs <- diffFeaturesDeferred e plan (features old) (features mid) (features new)
  diffXLinksDeferred e plan (xlinks mid) (xlinks new)
  unsafeIOToST renderYield
  cs <- diffChildrenDeferred e mounted plan (children old) (children mid) (children new)
  return old
    { features = fs
    , children = cs
    }

{-# INLINE diffFeaturesDeferred #-}
diffFeaturesDeferred :: Element -> Plan s -> DiffST s Features
diffFeaturesDeferred e plan old !mid !new = do
  case reallyUnsafePtrEquality# mid new of
    1# -> return old
    _  -> do
      diffClassesDeferred    e plan (classes mid) (classes new)
      diffStylesDeferred     e plan (styles mid) (styles new)
      diffAttributesDeferred e plan (attributes mid) (attributes new)
      diffPropertiesDeferred e plan (properties mid) (properties new)
      ls <- diffListenersDeferred  e plan (listeners old) (listeners mid) (listeners new)
      diffLifecyclesDeferred e plan (lifecycles old) (lifecycles mid) (lifecycles new)
      return new { listeners = ls }

diffXLinksDeferred :: Element -> Plan s -> Map.Map Txt Txt -> Map.Map Txt Txt -> ST s ()
diffXLinksDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let !removes = Map.difference mid new
      unless (Map.null removes) $
        amendPlan p $
          Map.foldMapWithKey (\k _ -> removeAttributeNS e "http://www.w3.org/1999/xlink" k) removes

      let !adds = Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
      unless (Map.null adds) $
        amendPlan p $
          Map.foldMapWithKey (\k v -> setAttributeNS e "http://www.w3.org/1999/xlink" k v) adds

diffClassesDeferred :: Element -> Plan s -> Set.Set Txt -> Set.Set Txt -> ST s ()
diffClassesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> amendPlan p (setClasses e new)

diffStylesDeferred :: Element -> Plan s -> Map.Map Txt Txt -> Map.Map Txt Txt -> ST s ()
diffStylesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let !removes = Map.difference mid new
      unless (Map.null removes) $
        amendPlan p $
          removeStyles e removes

      let !adds = Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
      unless (Map.null adds) $
        amendPlan p $
          setStyles e adds

removeStyles :: Element -> Map.Map Txt Txt -> IO ()
removeStyles e = Map.foldMapWithKey (\k _ -> removeStyle e k)

removeAttributes :: Element -> Map.Map Txt Txt -> IO ()
removeAttributes e = Map.foldMapWithKey (\k _ -> removeAttribute e k)

removeProperties :: Element -> Map.Map Txt Txt -> IO ()
removeProperties e = Map.foldMapWithKey (\k _ -> removeProperty e k)

diffAttributesDeferred :: Element -> Plan s -> Map.Map Txt Txt -> Map.Map Txt Txt -> ST s ()
diffAttributesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let !removes = Map.difference mid new
      unless (Map.null removes) $
        amendPlan p $
          removeAttributes e removes

      let !adds = Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
      unless (Map.null adds) $
        amendPlan p $
          setAttributes e adds

diffPropertiesDeferred :: Element -> Plan s -> Map.Map Txt Txt -> Map.Map Txt Txt -> ST s ()
diffPropertiesDeferred e p !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  -> do

      let !removes = Map.difference mid new
      unless (Map.null removes) $
        amendPlan p $
          removeProperties e removes

      let !adds = Map.differenceWith (\a b -> if a /= b then Just a else Nothing) new mid
      unless (Map.null adds) $
        amendPlan p $
          setProperties e adds

addListenerDeferred :: Element -> Plan s -> Listener -> ST s Listener
addListenerDeferred e plan l@(On n t o a _) = do
#ifdef __GHCJS__
  let target = case t of
                ElementTarget  -> toJSV e
                WindowTarget   -> toJSV window
                DocumentTarget -> toJSV document
  (cb,stopper) <- unsafeIOToST $ do

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
    _  -> do
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
diffLifecyclesDeferred e p old !mid !new =
  case reallyUnsafePtrEquality# mid new of
    1# -> return ()
    _  ->
      let !adds = List.filter (not . (old `unsafeContains`)) new
      in for_ adds (addLifecycleDeferred e p)

unsafeContains :: [a] -> a -> Bool
unsafeContains [] _ = False
unsafeContains (x : xs) a =
  case reallyUnsafePtrEquality# x a of
    1# -> True
    _  -> unsafeContains xs a

styleDiff :: Element -> Map.Map Txt Txt -> Map.Map Txt Txt -> Map.Map Txt (IO ())
styleDiff e = Map.mergeWithKey diff remove add
  where
    diff nm val1 val2
      | val1 == val2           = Nothing
      | otherwise              = Just $ setStyle e nm val2
    remove = Map.mapWithKey (\nm  _  -> removeStyle e nm)
    add    = Map.mapWithKey (\nm val -> setStyle e nm val)

diffKeyedChildrenDeferred :: forall s. Element -> IORef (IO ()) -> Plan s -> IntMap.IntMap View -> [(Int,View)] -> [(Int,View)] -> [(Int,View)] -> ST s (IntMap.IntMap View,[(Int,View)])
diffKeyedChildrenDeferred (toNode -> e) mounted plan keys olds !mids !news =
  case reallyUnsafePtrEquality# mids news of
    1# -> return (keys,olds)
    _  ->
      case (mids,news) of
        ([],[]) -> return (keys,olds)
        _       -> do
          dc                  <- newSTRef (e,keys,mempty)
          news'               <- start dc olds mids news
          (_,keys,removals)   <- readSTRef dc
          ks                  <- newSTRef keys
          plan'               <- newSTRef []
          for_ (IntMap.toList removals) $ \(i,r) -> do
            modifySTRef' ks (IntMap.delete i)
            removeDeferred plan' r
          p' <- readSTRef plan'
          amendPlan plan (sequence_ $ List.reverse p')
          keys' <- readSTRef ks
          return (keys',news')
          where
            start dc [] _ news      = dKCD_new dc mounted plan news
            start dc olds _ []      = dKCD_rm dc plan olds
            start dc olds mids news = dKCD_upd dc mounted plan olds mids news

type Keys = IntMap.IntMap View
type Removals = IntMap.IntMap View
type DiffCtx s = STRef s (Node,Keys,Removals)

dKCD_new :: DiffCtx s -> IORef (IO ()) -> Plan s -> [(Int,View)] -> ST s [(Int,View)]
dKCD_new dc mounted plan news = do
  (e,_,removals) <- readSTRef dc
  plan' <- newSTRef []
  keys <- newSTRef mempty
  news' <- for news $ \(i,n) -> do
    new' <- unsafeIOToST $ build mounted Nothing n
    for_ (getHost new') $ amendPlan plan' . append e
    modifySTRef' keys (IntMap.insert i new')
    return (i,new')
  ks <- readSTRef keys
  p <- readSTRef plan'
  writeSTRef dc (e,ks,removals)
  amendPlan plan $! sequence_ (List.reverse p)
  return news'

dKCD_rm :: DiffCtx s -> Plan s -> [(Int,View)] -> ST s [(Int,View)]
dKCD_rm dc plan olds = do
  plan' <- newSTRef []
  for_ olds $ traverse (removeDeferred plan')
  p <- readSTRef plan'
  amendPlan plan $! sequence_ (List.reverse p)
  modifySTRef' dc $ \(e,_,_) -> (e,mempty,mempty)
  return []

dKCD_ins :: DiffCtx s -> IORef (IO ()) -> Plan s -> Int -> Int -> View -> ST s (Int,View)
dKCD_ins dc mounted plan i nk new = do
  (e,keys,removals) <- readSTRef dc
  let ins i ~(Just a) = amendPlan plan (insertAt (coerce e) a i)
  case IntMap.lookup nk removals of
    Nothing -> do
      n' <- unsafeIOToST (build mounted Nothing new)
      writeSTRef dc (e,IntMap.insert nk n' keys,removals)
      ins i (getHost n')
      return (nk,n')
    Just n -> do
      writeSTRef dc (e,keys,IntMap.delete nk removals)
      ins (i + 1) (getHost n)
      return (nk,n)

dKCD_upd :: DiffCtx s -> IORef (IO ()) -> Plan s -> DiffST s [(Int,View)]
dKCD_upd dc mounted plan = go 0
  where
    go !i olds !mids !news =
      case reallyUnsafePtrEquality# mids news of
        1# -> return olds
        _  -> dKCD_slow dc mounted plan i olds mids news

dKCD_slow :: DiffCtx s -> IORef (IO ()) -> Plan s -> Int -> DiffST s [(Int,View)]
dKCD_slow dc mounted plan = go
  where
    go !_ olds _ [] = do
      for_ olds $ \(ok,o) -> modifySTRef' dc $ \(e,keys,removals) -> (e,IntMap.delete ok keys,IntMap.insert ok o removals)
      return []

    go _ [] _ news = do
      for news $ \(i,new) -> do
        (e,keys,removals) <- readSTRef dc
        case IntMap.lookup i removals of
          Nothing -> do
            new' <- unsafeIOToST (build mounted Nothing new)
            writeSTRef dc (e,IntMap.insert i new' keys,removals)
            for (getHost new') $ amendPlan plan . append e
            return (i,new')
          Just r  -> do
            writeSTRef dc (e,keys,IntMap.delete i removals)
            for (getHost r) $ amendPlan plan . append e
            return (i,r)

    go i [o@(ok,old)] ~[m@(mk,mid)] (n0@(nk0,new0):n1@(nk1,new1):ns) = do
      if mk == nk0
        then do
          n' <- dKCD_helper dc mounted plan o m n0
          ns' <- go (i + 1) [] [] (n1:ns)
          return (n':ns')
        else
          if mk == nk1
            then do
              n'  <- dKCD_ins dc mounted plan i nk0 new0
              ns' <- go (i + 1) [o] [m] (n1:ns)
              return (n':ns')
            else do
              modifySTRef' dc $ \(e,keys,removals) -> (e,keys,IntMap.insert mk old removals)
              n' <- dKCD_ins dc mounted plan i nk0 new0
              ns' <- go (i + 1) [] [] (n1:ns)
              return (n':ns')

    go i [o@(ok,old)] ~[m@(mk,mid)] ~[n@(nk,new)] = do
      if mk == nk
        then do
          n' <- dKCD_helper dc mounted plan o m n
          return [n']
        else do
          modifySTRef' dc $ \(e,keys,removals) -> (e,keys,IntMap.insert mk old removals)
          n' <- dKCD_ins dc mounted plan i nk new
          return [n']

    go i ~(o@(ok,old):os) ~(m@(mk,mid):ms) ns@[n@(nk,new)] = do
      if mk == nk
        then do
          n' <- dKCD_helper dc mounted plan o m n
          ns' <- go (i + 1) os ms []
          return (n':ns')
        else do
          modifySTRef' dc $ \(e,keys,removals) -> (e,keys,IntMap.insert mk old removals)
          go i os ms ns

    go i ~os0@(o0@(ok0,old0):os1@(o1@(ok1,old1):os2)) ~ms0@(m0@(mk0,mid0):ms1@(m1@(mk1,mid1):ms2)) ~ns@(n0@(nk0,new0):ns1@(n1@(nk1,new1):ns2))
      | mk0 == nk0 = do
          n  <- dKCD_helper dc mounted plan o0 m0 n0
          case reallyUnsafePtrEquality# ms1 ns1 of
            1# -> return (n:os1)
            _  -> do
              ns <- go (i + 1) os1 ms1 ns1
              return (n:ns)

      | mk0 == nk1 && mk1 == nk0 = do
          -- swap mk0 mk1
          (e,_,_) <- readSTRef dc
          let ins ~(Just b) = amendPlan plan (insertAt (coerce e) b i)
          ins (getHost old1)
          case reallyUnsafePtrEquality# ms2 ns2 of
            1# -> return (o1:o0:os2)
            _  -> do
              ns <- go (i + 2) os2 ms2 ns2
              return (o1:o0:ns)

      | mk0 == nk1 = do
          -- insert nk0
          n0 <- dKCD_ins dc mounted plan i nk0 new0
          case reallyUnsafePtrEquality# ms0 ns1 of
            1# -> return (n0:os0)
            _  -> do
              ns <- go (i + 1) os0 ms0 ns1
              return (n0:ns)

      | mk1 == nk0 = do
          -- delete mk0
          modifySTRef' dc $ \(e,keys,removals) -> (e,keys,IntMap.insert mk0 old0 removals)
          case reallyUnsafePtrEquality# ms1 ns of
            1# -> return os1
            _  -> go i os1 ms1 ns

      | otherwise = do
          -- remove mk0, insert nk0, diff mk1 nk1 or recurse
          modifySTRef' dc $ \(e,keys,removals) -> (e,keys,IntMap.insert mk0 old0 removals)
          n0 <- dKCD_ins dc mounted plan i nk0 new0
          if mk1 == nk1
            then do
              n1 <- dKCD_helper dc mounted plan o1 m1 n1
              case reallyUnsafePtrEquality# ms2 ns2 of
                1# -> return (n0:n1:os2)
                _  -> do
                  ns <- go (i + 2) os2 ms2 ns2
                  return (n0:n1:ns)
            else
              case reallyUnsafePtrEquality# ms1 ns1 of
                1# -> return (n0:os1)
                _  -> do
                  ns <- go (i + 1) os1 ms1 ns1
                  return (n0:ns)

dKCD_helper :: DiffCtx s -> IORef (IO ()) -> Plan s -> (Int,View) -> (Int,View) -> (Int,View) -> ST s (Int,View)
dKCD_helper dc mounted plan (ok,old) (mk,mid) (nk,new) = do
  (e,keys,removals) <- readSTRef dc
  new' <- diffDeferred mounted plan old mid new
  writeSTRef dc (e,IntMap.insert nk new' keys,removals)
  return (nk,new')

diffChildrenDeferred :: forall s. Element -> IORef (IO ()) -> Plan s -> DiffST s [View]
diffChildrenDeferred (toNode -> e) mounted plan = start
  where
    start :: DiffST s [View]
    start olds !mids !news =
      case reallyUnsafePtrEquality# mids news of
        1# -> return olds
        _  -> go olds mids news

    go :: DiffST s [View]
    go olds _ [] = do
      plan' <- newSTRef []
      for_ olds (removeDeferred plan')
      p <- readSTRef plan'
      amendPlan plan $! sequence_ (List.reverse p)
      return []

    go [] _ news = do
      frag <- unsafeIOToST createFrag
      news' <- for news (unsafeIOToST . build mounted (Just (toNode frag)))
      amendPlan plan (append e frag)
      return news'

    go (old:olds) (mid:mids) (new:news) = do
      new'  <- diffDeferred mounted plan old mid new
      news' <- start olds mids news
      return (new' : news')

cleanup :: View -> IO ()
cleanup RawView {..} =
  for_ (listeners features) cleanupListener
cleanup HTMLView {..} = do
  for_ (listeners features) cleanupListener
  for_ children cleanup
cleanup KHTMLView {..} = do
  for_ (listeners features) cleanupListener
  for_ keyedChildren (cleanup . snd)
cleanup SVGView {..} = do
  for_ (listeners features) cleanupListener
  for_ children cleanup
cleanup KSVGView {..} = do
  for_ (listeners features) cleanupListener
  for_ keyedChildren (cleanup . snd)
cleanup ComponentView {..} = do
  for_ record $ \cr -> do
    componentCleanup <- newEmptyMVar
    unmountComponent cr (\p v -> unsafeIOToST (cleanup v),componentCleanup)
    join $ takeMVar componentCleanup
cleanup _ = return ()

cleanupDeferred :: Plan s -> View -> ST s ()
cleanupDeferred plan = go
  where
    go RawView {..} =
      for_ (listeners features) (unsafeIOToST . cleanupListener)
    go HTMLView {..} = do
      for_ (listeners features) (unsafeIOToST . cleanupListener)
      for_ children go
    go KHTMLView {..} = do
      for_ (listeners features) (unsafeIOToST . cleanupListener)
      for_ keyedChildren (go . snd)
    go SVGView {..} = do
      for_ (listeners features) (unsafeIOToST . cleanupListener)
      for_ children go
    go KSVGView {..} = do
      for_ (listeners features) (unsafeIOToST . cleanupListener)
      for_ keyedChildren (go . snd)
    go stv@(ComponentView {..}) = do
      for_ record $ \cr -> do
        componentCleanup <- unsafeIOToST newEmptyMVar
        unsafeIOToST $ unmountComponent cr (cleanupDeferred,componentCleanup)
        cc <- unsafeIOToST $ takeMVar componentCleanup
        amendPlan plan cc
    go _ = return ()

cleanupListener :: Listener -> IO ()
cleanupListener (On _ _ _ _ stp) = stp

replaceDeferred :: Plan s -> View -> View -> ST s View
replaceDeferred plan old@(getHost -> oldHost) new@(getHost -> newHost) =
  case oldHost of
    Nothing -> error "Expected old host in replaceDeferred; got nothing."
    Just oh ->
      case newHost of
        Nothing -> error "Expected new host in replaceDeferred; got nothing."
        Just nh -> do
          amendPlan plan (replaceNode oh nh)
          cleanupDeferred plan old
          return new

replaceTextContentDeferred :: Plan s -> View -> View -> ST s View
replaceTextContentDeferred plan old@(textHost -> Just oh) new = do
  amendPlan plan (oh `replaceText` content new)
  return old { content = content new }

remove :: View -> IO ()
remove v = do
  for_ (getHost v) removeNode
  cleanup v

removeDeferred :: Plan s -> View -> ST s ()
removeDeferred plan v = do
  for_ (getHost v) (amendPlan plan . removeNode)
  cleanupDeferred plan v

getHost :: View -> Maybe Node
-- EEK!
getHost ComponentView {..} = join $ for record (getHost . unsafePerformIO . readIORef . crView)
getHost TextView  {..} = fmap toNode textHost
getHost SomeView {}    = Nothing
getHost x              = fmap toNode $ elementHost x

{-# NOINLINE addAnimation #-}
addAnimation a = do
  atomicModifyIORef' animationQueue $ \as -> (a:as,())
  tryPutMVar animationsAwaiting ()

{-# NOINLINE animationsAwaiting #-}
animationsAwaiting = unsafePerformIO newEmptyMVar

{-# NOINLINE animationQueue #-}
animationQueue = unsafePerformIO (newIORef [])

{-# NOINLINE animator #-}
animator = unsafePerformIO $ void $ forkIO await
  where
    await = do
      renderYield
      takeMVar animationsAwaiting
      as <- atomicModifyIORef' animationQueue $ \as -> ([],as)
      animate as

    animate [] = await
    animate as = do
#ifdef __GHCJS__
      barrier <- newEmptyMVar
      callback <- syncCallback1 ContinueAsync $ \_ -> do
        bs <- atomicModifyIORef' animationQueue $ \bs -> ([],bs)
        sequence_ (List.reverse as)
        sequence_ (List.reverse bs)
        putMVar barrier ()
      requestAnimationFrame callback
      takeMVar barrier
      releaseCallback callback
#else
      bs <- atomicModifyIORef' animationQueue $ \bs -> ([],bs)
      sequence_ (List.reverse as)
      sequence_ (List.reverse bs)
#endif
      await
