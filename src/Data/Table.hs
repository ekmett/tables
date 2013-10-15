{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

#ifndef MIN_VERSION_containers
#define MIN_VERSION_containers(x,y,z) 1
#endif
#ifndef MIN_VERSION_lens
#define MIN_VERSION_lens(x,y,z) 1
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Table
-- Copyright   :  (C) 2012-2013 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module provides tables with multiple indices that support a simple
-- API based on the lenses and traversals from the @lens@ package.
----------------------------------------------------------------------------
module Data.Table
  (
  -- * Tables
    Table(..)
  , Tabular(..)
  , Tab(..)
  , Key(..)
  -- ** Template Haskell helpers
  , makeTabular
  -- ** Table Construction
  , empty
  , singleton
  , table
  , fromList
  , unsafeFromList
  -- ** Combining Tables
  , union
  , difference
  , intersection
  -- ** Reading and Writing
  , null
  , count
  , With(..)
  , Withal(..)
  , Group(..)
  , insert
  , insert'
  , unsafeInsert
  , delete
  , rows
  -- * Esoterica
  , Auto(..)
  , autoKey
  , auto
  , autoIncrement
  -- * Implementation Details
  , IsKeyType(..)
  , KeyType(..)
  , Primary
  , Candidate, CandidateInt, CandidateHash
  , Supplemental, SupplementalInt, SupplementalHash
  , Inverted, InvertedInt, InvertedHash
  , AnIndex(..)
  ) where

import Control.Applicative hiding (empty)
import Control.Comonad
import Control.DeepSeq (NFData(rnf))
import Control.Lens hiding (anon)
import Control.Monad
import Control.Monad.Fix
import Data.Binary (Binary)
import qualified Data.Binary as B
import Data.Char (toUpper)
import Data.Data
import Data.Foldable as F hiding (foldl1)
import Data.Function (on)
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.SafeCopy (SafeCopy(..), safeGet, safePut, contain)
import Data.Serialize (Serialize)
import qualified Data.Serialize as C
import Data.Set (Set)
import qualified Data.Set as S
import Data.Traversable hiding (mapM)
import Language.Haskell.TH
import qualified Prelude as P
import Prelude hiding (null)

{-# ANN module "HLint: ignore Reduce duplication" #-}
{-# ANN module "HLint: ignore Eta reduce" #-}

-- | This class describes how to index a user-defined data type.
class Ord (PKT t) => Tabular (t :: *) where
  -- | The primary key type
  type PKT t

  -- | Used to store indices
  data Tab t m

  -- | The type used internally for columns
  data Key (k :: *) t :: * -> *

  -- | Extract the value of a 'Key'
  fetch :: Key k t a -> t -> a

  -- | Every 'Table' has one 'Primary' 'Key'
  primary :: Key Primary t (PKT t)

  -- | ... and so if you find one, it had better be that one!
  primarily :: Key Primary t a -> ((a ~ PKT t) => r) -> r

  -- | Construct a 'Tab' given a function from key to index.
  mkTab :: Applicative h => (forall k a. IsKeyType k a => Key k t a -> h (i k a)) -> h (Tab t i)

  -- | Lookup an index in a 'Tab'
  ixTab :: Tab t i -> Key k t a -> i k a

  -- | Loop over each index in a 'Tab'
  forTab :: Applicative h => Tab t i -> (forall k a . IsKeyType k a => Key k t a -> i k a -> h (j k a)) -> h (Tab t j)

  -- | Adjust a record using meta-information about the table allowing for auto-increments.
  autoTab :: t -> Maybe (Tab t (AnIndex t) -> t)
  autoTab _ = Nothing
  {-# INLINE autoTab #-}

-- | This lets you define 'autoKey' to increment to 1 greater than the existing maximum key in a table.
--
-- In order to support this you need a numeric primary key, and the ability to update the primary key in a record, indicated by a
-- lens to the field.
--
-- To enable auto-increment for a table with primary key @primaryKeyField@, set:
--
-- @'autoTab' = 'autoIncrement' primaryKeyField@
autoIncrement :: (Tabular t, Num (PKT t)) => ALens' t (PKT t) -> t -> Maybe (Tab t (AnIndex t) -> t)
autoIncrement pk t
  | t ^# pk == 0 = Just $ \ tb -> t & pk #~ 1 + fromMaybe 0 (tb ^? primaryMap.traverseMax.asIndex)
  | otherwise    = Nothing
{-# INLINE autoIncrement #-}

-- | This is used to store a single index.
data AnIndex t k a where
  PrimaryMap          ::                       Map (PKT t) t      -> AnIndex t Primary          a
  CandidateIntMap     ::                       IntMap t           -> AnIndex t CandidateInt     Int
  CandidateHashMap    :: (Eq a, Hashable a) => HashMap a t        -> AnIndex t CandidateHash    a
  CandidateMap        :: Ord a              => Map a t            -> AnIndex t Candidate        a
  InvertedIntMap      ::                       IntMap [t]         -> AnIndex t InvertedInt      IntSet
  InvertedHashMap     :: (Eq a, Hashable a) => HashMap a [t]      -> AnIndex t InvertedHash     (HashSet a)
  InvertedMap         :: Ord a              => Map a [t]          -> AnIndex t Inverted         (Set a)
  SupplementalIntMap  ::                       IntMap [t]         -> AnIndex t SupplementalInt  Int
  SupplementalHashMap :: (Eq a, Hashable a) => HashMap a [t]      -> AnIndex t SupplementalHash a
  SupplementalMap     :: Ord a              => Map a [t]          -> AnIndex t Supplemental     a

-- | Find the primary key index a tab
primaryMap :: Tabular t => Lens' (Tab t (AnIndex t)) (Map (PKT t) t)
primaryMap f t = case ixTab t primary of
  PrimaryMap m -> f m <&> \u -> runIdentity $ forTab t $ \k o -> Identity $ case o of
    PrimaryMap _ -> primarily k (PrimaryMap u)
    _              -> o
{-# INLINE primaryMap #-}

-- * Overloaded keys

------------------------------------------------------------------------------
-- Table
------------------------------------------------------------------------------

-- | Every 'Table' has a 'Primary' 'key' and may have 'Candidate',
-- 'Supplemental' or 'Inverted' keys, plus their variants.
data Table t where
  EmptyTable ::                                   Table t
  Table      :: Tabular t => Tab t (AnIndex t) -> Table t
  deriving Typeable

instance (Tabular t, Data t) => Data (Table t) where
  gfoldl f z im = z fromList `f` toList im
  toConstr _ = fromListConstr
  gunfold k z c = case constrIndex c of
    1 -> k (z fromList)
    _ -> error "gunfold"
  dataTypeOf _ = tableDataType
  dataCast1 f = gcast1 f

instance (Tabular t, Binary t) => Binary (Table t) where
  put = reviews table B.put
  get = view table <$> B.get

instance (Tabular t, Serialize t) => Serialize (Table t) where
  put = reviews table C.put
  get = view table <$> C.get

instance (Typeable t, Tabular t, SafeCopy t) => SafeCopy (Table t) where
  putCopy = contain . reviews table safePut
  getCopy = contain $ view table <$> safeGet
  errorTypeName pt = show $ typeOf (undefined `asProxyTypeOf` pt)
    where asProxyTypeOf :: a -> p a -> a
          asProxyTypeOf a _ = a

fromListConstr :: Constr
fromListConstr = mkConstr tableDataType "fromList" [] Prefix

tableDataType :: DataType
tableDataType = mkDataType "Data.Table.Table" [fromListConstr]

instance Monoid (Table t) where
  mempty = EmptyTable
  {-# INLINE mempty #-}

  EmptyTable `mappend` r          = r
  r          `mappend` EmptyTable = r
  r          `mappend` s@Table{}  = F.foldl' (flip insert) s r
  {-# INLINE mappend #-}

instance Eq t => Eq (Table t) where
  (==) = (==) `on` toList
  {-# INLINE (==) #-}

instance Ord t => Ord (Table t) where
  compare = compare `on` toList
  {-# INLINE compare #-}

instance Show t => Show (Table t) where
  showsPrec d t = showParen (d > 10) $ showString "fromList " . showsPrec 11 (toList t)

instance (Tabular t, Read t) => Read (Table t) where
  readsPrec d = readParen (d > 10) $ \r -> do
    ("fromList",s) <- lex r
    (m, t) <- readsPrec 11 s
    return (fromList m, t)

instance Foldable Table where
  foldMap _ EmptyTable = mempty
  foldMap f (Table m)  = foldMapOf (primaryMap.folded) f m
  {-# INLINE foldMap #-}

type instance Index (Table t) = PKT t
type instance IxValue (Table t) = t

instance Contains (Table t) where
  type Containing (Table t) f = (Contravariant f, Functor f)
  contains k f EmptyTable = coerce $ indexed f k False
  contains k f (Table m) = Table <$> primaryMap (contains k f) m

instance Ixed (Table t) where
  ix _ _ EmptyTable = pure EmptyTable
  ix k f (Table m) = Table <$> primaryMap (ix k f) m
  {-# INLINE ix #-}

instance Tabular t => At (Table t) where
  at k f EmptyTable = maybe EmptyTable singleton <$> indexed f k Nothing
  at k f (Table m)  = Table <$> primaryMap (at k f) m
  {-# INLINE at #-}

anon :: APrism' a () -> Iso' (Maybe a) a
anon p = iso (fromMaybe def) go where
  def                           = review (clonePrism p) ()
  go b | has (clonePrism p) b   = Nothing
       | otherwise              = Just b
{-# INLINE anon #-}

nil :: Prism' [a] ()
nil = prism' (const []) (guard . P.null)
{-# INLINE nil #-}

deleteCollisions :: Table t -> [t] -> Table t
deleteCollisions EmptyTable _ = EmptyTable
deleteCollisions (Table tab) ts = Table $ runIdentity $ forTab tab $ \k i -> Identity $ case i of
  PrimaryMap idx          -> PrimaryMap $ primarily k $ F.foldl' (flip (M.delete . fetch primary)) idx ts
  CandidateMap idx        -> CandidateMap             $ F.foldl' (flip (M.delete . fetch k)) idx ts
  CandidateIntMap idx     -> CandidateIntMap          $ F.foldl' (flip (IM.delete . fetch k)) idx ts
  CandidateHashMap idx    -> CandidateHashMap         $ F.foldl' (flip (HM.delete . fetch k)) idx ts
  SupplementalMap idx     -> SupplementalMap $ M.foldlWithKey' ?? idx ?? M.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon nil %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  SupplementalIntMap idx  -> SupplementalIntMap $ IM.foldlWithKey' ?? idx ?? IM.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon nil %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  SupplementalHashMap idx -> SupplementalHashMap $ HM.foldlWithKey' ?? idx ?? HM.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon nil %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedMap idx         -> InvertedMap     $ M.foldlWithKey' ?? idx ?? M.fromListWith (++) [ (f, [t]) | t <- ts, f <- S.toList $ fetch k t ] $ \m ky ys ->
    m & at ky . anon nil %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedIntMap idx      -> InvertedIntMap  $ IM.foldlWithKey' ?? idx ?? IM.fromListWith (++) [ (f, [t]) | t <- ts, f <- IS.toList $ fetch k t ] $ \m ky ys ->
    m & at ky . anon nil %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedHashMap idx     -> InvertedHashMap $ HM.foldlWithKey' ?? idx ?? HM.fromListWith (++) [ (f, [t]) | t <- ts, f <- HS.toList $ fetch k t ] $ \m ky ys ->
    m & at ky . anon nil %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
{-# INLINE deleteCollisions #-}

emptyTab :: Tabular t => Tab t (AnIndex t)
emptyTab = runIdentity $ mkTab $ \k -> Identity $ case keyType k of
  Primary          -> primarily k (PrimaryMap M.empty)
  Candidate        -> CandidateMap        M.empty
  CandidateHash    -> CandidateHashMap    HM.empty
  CandidateInt     -> CandidateIntMap     IM.empty
  Inverted         -> InvertedMap         M.empty
  InvertedHash     -> InvertedHashMap     HM.empty
  InvertedInt      -> InvertedIntMap      IM.empty
  Supplemental     -> SupplementalMap     M.empty
  SupplementalHash -> SupplementalHashMap HM.empty
  SupplementalInt  -> SupplementalIntMap  IM.empty
{-# INLINE emptyTab #-}

-- * Public API

-- | Generate a Tabular instance for a data type. Currently, this only
-- works for types which have no type variables, and won't generate autoTab.
--
-- @
-- data Foo = Foo { fooId :: Int, fooBar :: String, fooBaz :: Double }
--
-- makeTabular 'fooId [(''Candidate, 'fooBaz), (''Supplemental, 'fooBar)]
-- @
makeTabular :: Name -> [(Name, Name)] -> Q [Dec]
makeTabular p ks = do
  -- Get the type name and PKT from the primary selector
  -- FIXME: Work for more flexible type names
  VarI _ (AppT (AppT ArrowT t) pkt) _ _ <- reify p


  -- Locally used variable names
  k <- VarT <$> newName "k"
  a <- VarT <$> newName "a"
  f <- newName "f"

  tabName <- newName $ "Tab_" ++ nameBase p

  let keys = (''Primary, p) : ks
      keyCons@(pK:_) = map (uppercase.snd) keys

      idiom, idiom' :: [Exp] -> Exp
      idiom' = foldl1 (\l r -> AppE (AppE (VarE '(<*>)) l) r)

      idiom [] = AppE (VarE 'pure) (ConE '())
      idiom (x:xs) = idiom' $ AppE (VarE 'pure) x : xs

  -- FIXME: Work for more flexible type names
  keyTypes <- map (\(VarI _ (AppT _ t) _ _) -> t) <$> mapM (reify . snd) keys
  keyVars  <- mapM (newName . nameBase . snd) keys

  return [InstanceD [] (AppT (ConT ''Tabular) t)
    [ TySynInstD ''PKT [t] pkt

    , DataInstD [] ''Key [k, t, a] (zipWith (\(kk,n) kt ->
        ForallC [] [EqualP k (ConT kk), EqualP a kt]
          (NormalC (uppercase n) [])) keys keyTypes) []

    , DataInstD [] ''Tab [t, a] [NormalC tabName $ zipWith
        (\(k,_) t -> (NotStrict, AppT (AppT a (ConT k)) t)) keys keyTypes] []

    , FunD 'fetch $ map (\(_,k) ->
        Clause [ConP (uppercase k) []] (NormalB (VarE k)) []) keys

    , ValD (VarP 'primary) (NormalB (ConE pK)) []

    , FunD 'primarily [Clause [ConP pK [], VarP f] (NormalB (VarE f)) []]

    , FunD 'mkTab [Clause [VarP f]
      ( NormalB . idiom $ ConE tabName : map (AppE (VarE f) . ConE) keyCons
      ) []]

    , FunD 'forTab [Clause [ConP tabName (map VarP keyVars), VarP f]
      ( NormalB . idiom $ ConE tabName : zipWith
          (\c x -> AppE (AppE (VarE f) (ConE c)) (VarE x)) keyCons keyVars
      ) []]

    , FunD 'ixTab [Clause [ConP tabName (map VarP keyVars), VarP f]
      ( NormalB . CaseE (VarE f) $ zipWith
        (\c x -> Match (ConP c []) (NormalB $ VarE x) []) keyCons keyVars
      ) []]
    ]]
  where uppercase :: Name -> Name
        uppercase = iso nameBase mkName._head %~ toUpper

-- | Construct an empty relation
empty :: Table t
empty = EmptyTable
{-# INLINE empty #-}

-- | Check to see if the relation is empty
null :: Table t -> Bool
null EmptyTable = True
null (Table m)  = M.null (m^.primaryMap)
{-# INLINE null #-}

-- | Construct a relation with a single row
singleton :: Tabular t => t -> Table t
singleton row = Table $ runIdentity $ mkTab $ \ k -> Identity $ case keyType k of
  Primary          -> primarily k $ PrimaryMap $ M.singleton  (fetch k row) row
  Candidate        -> CandidateMap             $ M.singleton  (fetch k row) row
  CandidateInt     -> CandidateIntMap          $ IM.singleton (fetch k row) row
  CandidateHash    -> CandidateHashMap         $ HM.singleton (fetch k row) row
  Supplemental     -> SupplementalMap          $ M.singleton  (fetch k row) [row]
  SupplementalInt  -> SupplementalIntMap       $ IM.singleton (fetch k row) [row]
  SupplementalHash -> SupplementalHashMap      $ HM.singleton (fetch k row) [row]
#if MIN_VERSION_containers(0,5,0)
  Inverted         -> InvertedMap              $ M.fromSet  (const [row]) (fetch k row)
  InvertedInt      -> InvertedIntMap           $ IM.fromSet (const [row]) (fetch k row)
#else
  Inverted         -> InvertedMap              $ M.fromDistinctAscList  [ (e, [row]) | e <- S.toAscList  (fetch k row) ]
  InvertedInt      -> InvertedIntMap           $ IM.fromDistinctAscList [ (e, [row]) | e <- IS.toAscList (fetch k row) ]
#endif
  InvertedHash     -> InvertedHashMap          $ HS.foldl' (\m k -> HM.insert k [row] m) HM.empty (fetch k row)
{-# INLINE singleton #-}

-- | Return the set of rows that would be delete by deleting or inserting this row
collisions :: t -> Table t -> [t]
collisions _ EmptyTable = []
collisions t (Table m)  = getConst $ forTab m $ \k i -> Const $ case i of
  PrimaryMap idx       -> primarily k $ idx^..ix (fetch k t)
  CandidateMap idx     ->               idx^..ix (fetch k t)
  CandidateIntMap idx  ->               idx^..ix (fetch k t)
  CandidateHashMap idx ->               idx^..ix (fetch k t)
  _                  -> []
{-# INLINE collisions #-}

-- | Delete this row from the database. This will remove any row that collides with the specified
-- row on any primary or candidate key.
delete :: t -> Table t -> Table t
delete t m = deleteCollisions m (collisions t m)
{-# INLINE delete #-}

-- | Insert a row into a relation, removing collisions.
insert :: Tabular t => t -> Table t -> Table t
insert t r = snd $ insert' t r
{-# INLINE insert #-}

-- | Insert a row into a relation, removing collisions.
insert' :: Tabular t => t -> Table t -> (t, Table t)
insert' t0 r = case autoTab t0 of
  Just p -> case r of
    EmptyTable -> go (p emptyTab)
    Table m    -> go (p m)
  Nothing -> go t0
  where
  go t = (,) t $ unsafeInsert t (delete t r)
  {-# INLINE go #-}
{-# INLINE insert' #-}

-- | Insert a row into a relation, ignoring collisions.
unsafeInsert :: Tabular t => t -> Table t -> Table t
unsafeInsert t r = case r of
  EmptyTable -> singleton t
  Table m -> Table $ runIdentity $ forTab m $ \k i -> Identity $ case i of
    PrimaryMap idx          -> primarily k $ PrimaryMap $ idx & at (fetch k t) ?~ t
    CandidateMap idx        -> CandidateMap             $ idx & at (fetch k t) ?~ t
    CandidateIntMap idx     -> CandidateIntMap          $ idx & at (fetch k t) ?~ t
    CandidateHashMap idx    -> CandidateHashMap         $ idx & at (fetch k t) ?~ t
    SupplementalMap idx     -> SupplementalMap          $ idx & at (fetch k t) . anon nil %~ (t:)
    SupplementalIntMap idx  -> SupplementalIntMap       $ idx & at (fetch k t) . anon nil %~ (t:)
    SupplementalHashMap idx -> SupplementalHashMap      $ idx & at (fetch k t) . anon nil %~ (t:)
    InvertedMap idx         -> InvertedMap              $ idx & flip (F.foldr $ \ik -> at ik . anon nil %~ (t:)) (fetch k t)
    InvertedIntMap idx      -> InvertedIntMap           $ idx & flip (IS.foldr $ \ik -> at ik . anon nil %~ (t:)) (fetch k t)
    InvertedHashMap idx     -> InvertedHashMap          $ idx & flip (F.foldr $ \ik -> at ik . anon nil %~ (t:)) (fetch k t)
{-# INLINE unsafeInsert #-}

-- | Retrieve a row count.
count :: Table t -> Int
count EmptyTable = 0
count (Table m)  = M.size (m^.primaryMap)

-- | Convert a list to and from a 'Table'.
--
-- The real isomorphism laws hold if the original list makes no use of the auto-increment
-- functionality of the table, has no duplicates and is sorted according to the primary key.
--
-- However,
--
-- @'from' 'table' '.' 'table' ≡ 'id'@
--
-- always holds.
table :: Tabular t => Iso' [t] (Table t)
table = iso fromList toList
{-# INLINE table #-}

instance (Tabular b, PKT a ~ PKT b) => Each (Table a) (Table b) a b where
  each _ EmptyTable = pure EmptyTable
  each f r@Table{}  = P.foldr insert empty <$> traverse f (toList r)
  {-# INLINE each #-}

{-
-- | Traverse all of the rows in a table without changing any types
rows' :: Traversal' (Table t) t
rows' _ EmptyTable = pure EmptyTable
rows' f r@Table{} = P.foldr insert empty <$> traverse f (toList r)
{-# INLINE rows' #-}
-}

-- | Traverse all of the rows in a table, potentially changing table types completely.
rows :: (Tabular t, PKT s ~ PKT t) => IndexedTraversal (PKT s) (Table s) (Table t) s t
rows _ EmptyTable = pure EmptyTable
rows f (Table m)  = P.foldr insert empty <$> sequenceA (M.foldrWithKey (\i a r -> indexed f i a : r) [] $ m^.primaryMap)
{-# INLINE rows #-}

class Group f q t i | q -> t i where
  -- | Group by a given key or arbitrary function.
  group :: Ord i => q -> IndexedLensLike' i f (Table t) (Table t)

instance Applicative f => Group f (t -> a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = traverse (\(k,vs) -> indexed f k (fromList vs)) (M.toList idx) <&> mconcat where
    idx = M.fromListWith (++) (m^..primaryMap.folded.to(\v -> (ky v, [v])))
  {-# INLINE group #-}

instance Applicative f => Group f (Key Primary t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    PrimaryMap idx -> primarily ky $ for (toList idx) (\v -> indexed f (fetch primary v) (singleton v)) <&> mconcat
  {-# INLINE group #-}

instance Applicative f => Group f (Key Candidate t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    CandidateMap idx -> traverse (\(k,v) -> indexed f k (singleton v)) (M.toList idx) <&> mconcat
  {-# INLINE group #-}

instance (Applicative f, a ~ Int) => Group f (Key CandidateInt t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    CandidateIntMap idx -> traverse (\(k,v) -> indexed f k (singleton v)) (IM.toList idx) <&> mconcat
  {-# INLINE group #-}

instance Applicative f => Group f (Key CandidateHash t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    CandidateHashMap idx -> traverse (\(k,v) -> indexed f k (singleton v)) (HM.toList idx) <&> mconcat
  {-# INLINE group #-}

instance Applicative f => Group f (Key Supplemental t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    SupplementalMap idx -> traverse (\(k,vs) -> indexed f k (fromList vs)) (M.toList idx) <&> mconcat
  {-# INLINE group #-}

instance (Applicative f, a ~ Int) => Group f (Key SupplementalInt t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    SupplementalIntMap idx -> traverse (\(k,vs) -> indexed f k (fromList vs)) (IM.toList idx) <&> mconcat
  {-# INLINE group #-}

instance Applicative f => Group f (Key SupplementalHash t a) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    SupplementalHashMap idx -> traverse (\(k,vs) -> indexed f k (fromList vs)) (HM.toList idx) <&> mconcat
  {-# INLINE group #-}

instance (Applicative f, Gettable f) => Group f (Key Inverted t (Set a)) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    InvertedMap idx -> coerce $ traverse (\(k,vs) -> indexed f k (fromList vs)) $ M.toList idx

instance (Applicative f, Gettable f, a ~ Int) => Group f (Key InvertedInt t IntSet) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    InvertedIntMap idx -> coerce $ traverse (\(k,vs) -> indexed f k (fromList vs)) $ IM.toList idx

instance (Applicative f, Gettable f) => Group f (Key InvertedHash t (HashSet a)) t a where
  group _  _ EmptyTable = pure EmptyTable
  group ky f (Table m)  = case ixTab m ky of
    InvertedHashMap idx -> coerce $ traverse (\(k,vs) -> indexed f k (fromList vs)) $ HM.toList idx

-- | Search inverted indices
class Withal q s t | q -> s t where
  withAny :: q -> s -> Lens' (Table t) (Table t)
  withAll ::q -> s -> Lens' (Table t) (Table t)

  deleteWithAny :: q -> s -> Table t -> Table t
  deleteWithAny p as t = set (withAny p as) empty t
  {-# INLINE deleteWithAny #-}

  deleteWithAll :: q -> s -> Table t -> Table t
  deleteWithAll p as t = set (withAll p as) empty t
  {-# INLINE deleteWithAll #-}

instance Ord a => Withal (t -> [a]) [a] t where
  withAny _ _  f EmptyTable  = f EmptyTable
  withAny k as f r@(Table m) = go $ m^..primaryMap.folded.filtered (P.any (\e -> ss^.contains e) . k)
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
          ss = S.fromList as
  {-# INLINE withAny #-}

  withAll _ _  f EmptyTable  = f EmptyTable
  withAll k as f r@(Table m) = go $ m^..primaryMap.folded.filtered (P.all (\e -> ss^.contains e) . k)
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
          ss = S.fromList as
  {-# INLINE withAll #-}

instance Ord a => Withal (Key Inverted t (Set a)) [a] t where
  withAny _  _  f EmptyTable  = f EmptyTable
  withAny ky as f r@(Table m) = go $ case ixTab m ky of
    InvertedMap idx -> as >>= \a -> idx^..ix a.folded
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAny #-}

  withAll _  _  f EmptyTable  = f EmptyTable
  withAll _  [] f r           = f r -- every row has all of an empty list of keywords
  withAll ky (a:as) f r@(Table m) = case ixTab m ky of
    InvertedMap idx -> let mkm c = M.fromList [ (fetch primary v, v) | v <- idx^..ix c.folded ]
                         in go $ F.toList $ F.foldl' (\r -> M.intersection r . mkm) (mkm a) as
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAll #-}

instance Withal (Key InvertedInt t IntSet) [Int] t where
  withAny _  _  f EmptyTable  = f EmptyTable
  withAny ky as f r@(Table m) = go $ case ixTab m ky of
    InvertedIntMap idx -> as >>= \a -> idx^..ix a.folded
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAny #-}

  withAll _  _  f EmptyTable  = f EmptyTable
  withAll _  [] f r           = f r -- every row has all of an empty list of keywords
  withAll ky (a:as) f r@(Table m) = case ixTab m ky of
    InvertedIntMap idx -> let mkm c = M.fromList [ (fetch primary v, v) | v <- idx^..ix c.folded ]
                          in go $ F.toList $ F.foldl' (\r -> M.intersection r . mkm) (mkm a) as
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAll #-}

instance (Eq a, Hashable a) =>Withal (Key InvertedHash t (HashSet a)) [a] t where
  withAny _  _  f EmptyTable  = f EmptyTable
  withAny ky as f r@(Table m) = go $ case ixTab m ky of
    InvertedHashMap idx -> as >>= \a -> idx^..ix a.folded
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAny #-}

  withAll _  _  f EmptyTable  = f EmptyTable
  withAll _  [] f r           = f r -- every row has all of an empty list of keywords
  withAll ky (a:as) f r@(Table m) = case ixTab m ky of
    InvertedHashMap idx -> let mkm c = M.fromList [ (fetch primary v, v) | v <- idx^..ix c.folded ]
                          in go $ F.toList $ F.foldl' (\r -> M.intersection r . mkm) (mkm a) as
    where go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAll #-}


class With q t | q -> t where
  -- | Select a smaller, updateable subset of the rows of a table using an index or an arbitrary function.
  with :: Ord a => q a -> (forall x. Ord x => x -> x -> Bool) -> a -> Lens' (Table t) (Table t)

  -- | Delete selected rows from a table
  --
  -- @'deleteWith' p cmp a t ≡ 'set' ('with' p cmp a) 'empty' t@
  deleteWith :: Ord a => q a -> (forall x. Ord x => x -> x -> Bool) -> a -> Table t -> Table t
  deleteWith p cmp a t = set (with p cmp a) empty t
  {-# INLINE deleteWith #-}

instance With ((->) t) t where
  with _  _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r
    | lt || eq || gt = go $ m^..primaryMap.folded.filtered (\row -> cmp (ky row) a)
    | otherwise      = f EmptyTable <&> mappend r
    where
      lt = cmp LT EQ
      eq = cmp EQ EQ
      gt = cmp GT EQ
      go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key Primary t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r
    | not lt && eq && not gt = primarily ky $ go $ m^..primaryMap.ix a
    | lt || eq || gt = primarily ky $ go $ case M.splitLookup a (m^.primaryMap) of
        (l,e,g) -> (if lt then F.toList l else []) ++ (if eq then F.toList e else []) ++ (if gt then F.toList g else [])
    | otherwise = f EmptyTable <&> mappend r
    where
      lt = cmp LT EQ
      eq = cmp EQ EQ
      gt = cmp GT EQ
      go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key Candidate t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r
    | not lt && eq && not gt = case ixTab m ky of
      CandidateMap idx    -> go $ idx^..ix a
    | lt || eq || gt = case ixTab m ky of
      CandidateMap idx -> go $ case M.splitLookup a idx of
        (l,e,g) -> (if lt then F.toList l else []) ++ (if eq then F.toList e else []) ++ (if gt then F.toList g else [])
    | otherwise = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key CandidateInt t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r
    | not lt && eq && not gt = case ixTab m ky of
      CandidateIntMap idx    -> go $ idx^..ix a
    | lt || eq || gt = case ixTab m ky of
      CandidateIntMap idx -> go $ case IM.splitLookup a idx of
        (l,e,g) -> (if lt then F.toList l else []) ++ (if eq then F.toList e else []) ++ (if gt then F.toList g else [])
    | otherwise = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key CandidateHash t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt     && eq && gt     = f r
    | not lt && eq && not gt = case ixTab m ky of CandidateHashMap idx    -> go $ idx^..ix a
    | lt     || eq || gt     = go $ m^..primaryMap.folded.filtered (\row -> cmp (fetch ky row) a) -- table scan
    | otherwise              = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key Supplemental t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r -- all rows
    | not lt && eq && not gt = case ixTab m ky of
      SupplementalMap idx -> go $ idx^..ix a.folded
    | lt || eq || gt = go $ case ixTab m ky of
      SupplementalMap idx -> case M.splitLookup a idx of
        (l,e,g) -> (if lt then F.concat l else []) ++ (if eq then F.concat e else []) ++ (if gt then F.concat g else [])
    | otherwise      = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key SupplementalInt t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r -- all rows
    | not lt && eq && not gt = case ixTab m ky of
      SupplementalIntMap idx -> go $ idx^..ix a.folded
    | lt || eq || gt = go $ case ixTab m ky of
      SupplementalIntMap idx -> case IM.splitLookup a idx of
        (l,e,g) -> (if lt then F.concat l else []) ++ (if eq then F.concat e else []) ++ (if gt then F.concat g else [])
    | otherwise      = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

instance With (Key SupplementalHash t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    |     lt && eq &&     gt = f r -- all rows
    | not lt && eq && not gt = case ixTab m ky of SupplementalHashMap idx -> go $ idx^..ix a.folded
    |     lt || eq ||     gt = go $ m^..primaryMap.folded.filtered (\row -> cmp (fetch ky row) a) -- table scan
    | otherwise              = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (unsafeFromList xs) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

-- | Build up a table from a list
fromList :: Tabular t => [t] -> Table t
fromList = foldl' (flip insert) empty
{-# INLINE fromList #-}

-- | Build up a table from a list, without checking for collisions
unsafeFromList :: Tabular t => [t] -> Table t
unsafeFromList = foldl' (flip unsafeInsert) empty
{-# INLINE unsafeFromList #-}

-- | Left-biased union of the two tables
--
-- This is a synonym for 'mappend'
union :: Table t -> Table t -> Table t
union = mappend
{-# INLINE union #-}

-- | Return the elements of the first table that do not share a key with an element of the second table
difference :: (Tabular t1, Tabular t2, PKT t1 ~ PKT t2) => Table t1 -> Table t2 -> Table t1
difference t1 t2 = deleteWithAny ((:[]) . fetch primary) (t2 ^.. each . to (fetch primary)) t1
{-# INLINE difference #-}

-- | Return the elements of the first table that share a key with an element of the second table
intersection :: (Tabular t1, Tabular t2, PKT t1 ~ PKT t2) => Table t1 -> Table t2 -> Table t1
intersection t1 t2 = t1 ^. withAny ((:[]) . fetch primary) (t2 ^.. each . to (fetch primary))
{-# INLINE intersection #-}

-- * Lifting terms to types

-- | Value-level key types
data KeyType t a where
  Primary          :: Ord a              => KeyType Primary          a
  Candidate        :: Ord a              => KeyType Candidate        a
  CandidateInt     ::                       KeyType CandidateInt     Int
  CandidateHash    :: (Eq a, Hashable a) => KeyType CandidateHash    a
  Supplemental     :: Ord a              => KeyType Supplemental     a
  SupplementalInt  ::                       KeyType SupplementalInt  Int
  SupplementalHash :: (Eq a, Hashable a) => KeyType SupplementalHash a
  Inverted         :: Ord a              => KeyType Inverted         (Set a)
  InvertedInt      ::                       KeyType InvertedInt      IntSet
  InvertedHash     :: (Eq a, Hashable a) => KeyType InvertedHash     (HashSet a)

-- |  Type level key types
data Primary
data Candidate
data CandidateInt
data CandidateHash
data Supplemental
data SupplementalInt
data SupplementalHash
data Inverted
data InvertedInt
data InvertedHash

class IsKeyType k a where
  keyType :: Key k t a -> KeyType k a

instance Ord a => IsKeyType Primary a where
  keyType _ = Primary
  {-# INLINE keyType #-}

instance Ord a => IsKeyType Candidate a where
  keyType _ = Candidate
  {-# INLINE keyType #-}

instance a ~ Int => IsKeyType CandidateInt a where
  keyType _ = CandidateInt
  {-# INLINE keyType #-}

instance (Eq a, Hashable a)=> IsKeyType CandidateHash a where
  keyType _ = CandidateHash
  {-# INLINE keyType #-}

instance Ord a => IsKeyType Supplemental a where
  keyType _ = Supplemental
  {-# INLINE keyType #-}

instance a ~ Int => IsKeyType SupplementalInt a where
  keyType _ = SupplementalInt
  {-# INLINE keyType #-}

instance (Eq a, Hashable a)=> IsKeyType SupplementalHash a where
  keyType _ = SupplementalHash
  {-# INLINE keyType #-}

instance (t ~ Set, Ord a) => IsKeyType Inverted (t a) where
  keyType _ = Inverted
  {-# INLINE keyType #-}

instance IsKeyType InvertedInt IntSet where
  keyType _ = InvertedInt
  {-# INLINE keyType #-}

instance (t ~ HashSet, Eq a, Hashable a) => IsKeyType InvertedHash (t a) where
  keyType _ = InvertedHash
  {-# INLINE keyType #-}

class HasValue p q f s t a b | s -> a, t -> b, s b -> t, t a -> s where
  value :: Optical p q f s t a b

------------------------------------------------------------------------------
-- A simple table with an auto-incremented key
------------------------------------------------------------------------------

-- | Generate a row with an auto-incremented key
auto :: a -> Auto a
auto = Auto 0
{-# INLINE auto #-}

instance Field1 (Auto a) (Auto a) Int Int where
  _1 f (Auto k a) = indexed f (0 :: Int) k <&> \k' -> Auto k' a
  {-# INLINE _1 #-}

instance Field2 (Auto a) (Auto b) a b where
  _2 f (Auto k a) = indexed f (1 :: Int) a <&> Auto k
  {-# INLINE _2 #-}

type instance Index (Auto a) = Int

instance (a ~ Int, b ~ Int) => Each (Auto a) (Auto b) a b where
  each f (Auto k a) = Auto <$> f k <*> f a
  {-# INLINE each #-}

data Auto a = Auto !Int a
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Data,Typeable)

autoKey :: Lens' (Auto a) Int
autoKey f (Auto k a) = f k <&> \k' -> Auto k' a
{-# INLINE autoKey #-}

instance (Indexable Int p, q ~ (->), Functor f) => HasValue p q f (Auto a) (Auto b) a b where
  value f (Auto k a) = indexed f k a <&> Auto k
  {-# INLINE value #-}

instance FunctorWithIndex Int Auto where
  imap f (Auto k a) = Auto k (f k a)
  {-# INLINE imap #-}

instance FoldableWithIndex Int Auto where
  ifoldMap f (Auto k a) = f k a
  {-# INLINE ifoldMap #-}

instance TraversableWithIndex Int Auto where
  itraverse f (Auto k a) = Auto k <$> f k a
  {-# INLINE itraverse #-}

instance Comonad Auto where
  extract (Auto _ a) = a
  {-# INLINE extract #-}
  extend f w@(Auto k _) = Auto k (f w)
  {-# INLINE extend #-}

instance Binary a => Binary (Auto a) where
  put (Auto k a) = B.put k >> B.put a
  get = Auto <$> B.get <*> B.get

instance Serialize a => Serialize (Auto a) where
  put (Auto k a) = C.put k >> C.put a
  get = Auto <$> C.get <*> C.get

instance SafeCopy a => SafeCopy (Auto a) where
  getCopy = contain $ Auto <$> safeGet <*> safeGet
  putCopy (Auto k a) = contain $ safePut k >> safePut a  

instance Tabular (Auto a) where
  type PKT (Auto a) = Int
  data Tab (Auto a) i = AutoTab (i Primary Int)
  data Key p (Auto a) b where
    AutoKey :: Key Primary (Auto a) Int
  fetch AutoKey (Auto k _) = k
  {-# INLINE fetch #-}
  primary = AutoKey
  {-# INLINE primary #-}
  primarily AutoKey r = r
  {-# INLINE primarily #-}
  mkTab f = AutoTab <$> f AutoKey
  {-# INLINE mkTab #-}
  ixTab (AutoTab x) AutoKey = x
  {-# INLINE ixTab #-}
  forTab (AutoTab x) f = AutoTab <$> f AutoKey x
  {-# INLINE forTab #-}
  autoTab = autoIncrement autoKey
  {-# INLINE autoTab #-}

------------------------------------------------------------------------------
-- A simple key-value pair, indexed on the key
------------------------------------------------------------------------------

instance (Indexable k p, q ~ (->), Functor f) => HasValue p q f (k, a) (k, b) a b where
  value f (k, a) = indexed f k a <&> (,) k
  {-# INLINE value #-}

-- | Simple (key, value) pairs
instance Ord k => Tabular (k,v) where
  type PKT (k,v) = k
  data Tab (k,v) i = KVTab (i Primary k)
  data Key p (k,v) b where
    Fst :: Key Primary (k,v) k
  fetch Fst = fst
  {-# INLINE fetch #-}
  primary = Fst
  {-# INLINE primary #-}
  primarily Fst r = r
  {-# INLINE primarily #-}
  mkTab f = KVTab <$> f Fst
  {-# INLINE mkTab #-}
  ixTab (KVTab x) Fst = x
  {-# INLINE ixTab #-}
  forTab (KVTab x) f = KVTab <$> f Fst x
  {-# INLINE forTab #-}

------------------------------------------------------------------------------
-- Set-like tables with Identity
------------------------------------------------------------------------------

instance (Profunctor p, Functor f, p ~ q) => HasValue p q f (Identity a) (Identity b) a b where
  value = _Unwrapped
  {-# INLINE value #-}

instance Ord a => Tabular (Identity a) where
  type PKT (Identity a) = a
  data Tab (Identity a) i = IdentityTab (i Primary a)
  data Key p (Identity a) b where
    Id :: Key Primary (Identity a) a
  fetch Id = extract
  {-# INLINE fetch #-}
  primary = Id
  {-# INLINE primary #-}
  primarily Id r = r
  {-# INLINE primarily #-}
  mkTab f = IdentityTab <$> f Id
  {-# INLINE mkTab #-}
  ixTab (IdentityTab x) Id = x
  {-# INLINE ixTab #-}
  forTab (IdentityTab x) f = IdentityTab <$> f Id x
  {-# INLINE forTab #-}

-----------------------------------------------------------------------------
-- A simple value for set-like tables.
-----------------------------------------------------------------------------

instance Field1 (Value a) (Value b) a b where
  _1 f (Value a) = Value <$> indexed f (0 :: Int) a
  {-# INLINE _1 #-}

type instance Index (Value a) = ()
type instance IxValue (Value a) = a

instance Each (Value a) (Value b) a b where
  each f (Value a) = Value <$> f a
  {-# INLINE each #-}

instance Contains (Value a) where
  type Containing (Value a) f = (Contravariant f, Functor f)
  contains () pafb _ = coerce (indexed pafb () True)
  {-# INLINE contains #-}

instance Ixed (Value a) where
  ix () pafb (Value a) = Value <$> indexed pafb () a
  {-# INLINE ix #-}

instance Wrapped (Value a) where
  type Unwrapped (Value a) = a
  _Wrapped' = iso Value $ \(Value a) -> a
  {-# INLINE _Wrapped' #-}

data Value a = Value a
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Data,Typeable)

instance Applicative Value where
  pure = Value
  {-# INLINE pure #-}
  Value f <*> Value a = Value (f a)
  {-# INLINE (<*>) #-}

instance Monad Value where
  return = Value
  {-# INLINE return #-}
  Value a >>= f = f a
  {-# INLINE (>>=) #-}

instance MonadFix Value where
  mfix f = let m = f (extract m) in m
  {-# INLINE mfix #-}

instance Comonad Value where
  extract (Value a) = a
  {-# INLINE extract #-}
  extend f w@(Value _) = Value (f w)
  {-# INLINE extend #-}

instance ComonadApply Value where
  Value f <@> Value a = Value (f a)
  {-# INLINE (<@>) #-}

instance (Profunctor p, Functor f, p ~ q) => HasValue p q f (Value a) (Value b) a b where
  value = _Unwrapped
  {-# INLINE value #-}

instance Ord a => Tabular (Value a) where
  type PKT (Value a) = a
  data Tab (Value a) i = ValueTab (i Primary a)
  data Key p (Value a) b where
    Val :: Key Primary (Value a) a
  fetch Val = extract
  {-# INLINE fetch #-}
  primary = Val
  {-# INLINE primary #-}
  primarily Val r = r
  {-# INLINE primarily #-}
  mkTab f = ValueTab <$> f Val
  {-# INLINE mkTab #-}
  ixTab (ValueTab x) Val = x
  {-# INLINE ixTab #-}
  forTab (ValueTab x) f = ValueTab <$> f Val x
  {-# INLINE forTab #-}

instance (Tabular a, NFData a, NFData (Tab a (AnIndex a))) => NFData (Table a) where
    rnf (Table tab) = rnf tab
    rnf EmptyTable = ()

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t Primary a) where
    rnf (PrimaryMap m) = rnf m

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t Supplemental a) where
    rnf (SupplementalMap m) = rnf m

instance (NFData t, NFData (PKT t)) => NFData (AnIndex t SupplementalInt Int) where
    rnf (SupplementalIntMap m) = rnf m

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t SupplementalHash a) where
    rnf (SupplementalHashMap m) = rnf m

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t Candidate a) where
    rnf (CandidateMap m) = rnf m

instance (NFData t, NFData (PKT t)) => NFData (AnIndex t CandidateInt Int) where
    rnf (CandidateIntMap m) = rnf m

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t CandidateHash a) where
    rnf (CandidateHashMap m) = rnf m

instance (NFData t, NFData (PKT t)) => NFData (AnIndex t InvertedInt IntSet) where
    rnf (InvertedIntMap m) = rnf m

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t Inverted (Set a)) where
    rnf (InvertedMap m) = rnf m

instance (NFData t, NFData a, NFData (PKT t)) => NFData (AnIndex t InvertedHash (HashSet a)) where
    rnf (InvertedHashMap m) = rnf m

