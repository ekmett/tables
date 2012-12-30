{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
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
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Table
-- Copyright   :  (C) 2012 Edward Kmett,
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
  -- ** Table Construction
  , empty
  , singleton
  , table
  , fromList
  -- ** Reading and Writing
  , null
  , count
  , With(..)
  , Withal(..)
  , Group(..)
  , insert
  , delete
  , rows
  , rows'
  -- * Esoterica
  , Auto(..)
  , autoKey
  , auto
  , Value(..)
  , autoIncrement
  -- * Implementation Details
  , IsKeyType(..)
  , KeyType(..)
  , Primary
  , Candidate, CandidateInt, CandidateHash
  , Supplemental, SupplementalInt, SupplementalHash
  , Inverted, InvertedInt, InvertedHash
  , Index(..)
  ) where

import Control.Applicative hiding (empty)
import Control.Comonad
import Control.Lens
import Control.Lens.Internal
import Control.Monad
import Control.Monad.Fix
import Data.Data
import Data.Foldable as F
import Data.Function (on)
import Data.Functor.Identity
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
import Data.Set (Set)
import qualified Data.Set as S
import Data.Traversable
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
  autoTab :: t -> Maybe (Tab t (Index t) -> t)
  autoTab _ = Nothing
  {-# INLINE autoTab #-}

-- | This lets you define 'autoKey' to increment to 1 greater than the existing maximum key in a table.
--
-- In order to support this you need a numeric primary key, and the ability to update the primary key in a record, indicated by a
-- lens to the field.
--
-- To enable auto-increment for a table with primary key @primaryKeyField@, set:
--
-- @'autoKey' = 'autoIncrement' primaryKeyField@
autoIncrement :: (Tabular t, PKT t ~ Int) => ALens' t Int -> t -> Maybe (Tab t (Index t) -> t)
autoIncrement pk t
  | t ^# pk == 0 = Just $ \ tb -> t & pk #~ 1 + fromMaybe 0 (tb ^? primaryMap.traverseMax.asIndex)
  | otherwise    = Nothing
{-# INLINE autoIncrement #-}

-- | This is used to store a single index.
data Index t k a where
  PrimaryMap          ::                       Map (PKT t) t      -> Index t Primary          a
  CandidateIntMap     ::                       IntMap t           -> Index t CandidateInt     Int
  CandidateHashMap    :: (Eq a, Hashable a) => HashMap a t        -> Index t CandidateHash    a
  CandidateMap        :: Ord a              => Map a t            -> Index t Candidate        a
  InvertedIntMap      ::                       IntMap [t]         -> Index t InvertedInt      IntSet
  InvertedHashMap     :: (Eq a, Hashable a) => HashMap a [t]      -> Index t InvertedHash     (HashSet a)
  InvertedMap         :: Ord a              => Map a [t]          -> Index t Inverted         (Set a)
  SupplementalIntMap  ::                       IntMap [t]         -> Index t SupplementalInt  Int
  SupplementalHashMap :: (Eq a, Hashable a) => HashMap a [t]      -> Index t SupplementalHash a
  SupplementalMap     :: Ord a              => Map a [t]          -> Index t Supplemental     a

-- | Find the primary key index a tab
primaryMap :: Tabular t => Lens' (Tab t (Index t)) (Map (PKT t) t)
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
  EmptyTable ::                                 Table t
  Table      :: Tabular t => Tab t (Index t) -> Table t
  deriving Typeable

instance (Tabular t, Data t) => Data (Table t) where
  gfoldl f z im = z fromList `f` toList im
  toConstr _ = fromListConstr
  gunfold k z c = case constrIndex c of
    1 -> k (z fromList)
    _ -> error "gunfold"
  dataTypeOf _ = tableDataType
  dataCast1 f = gcast1 f

fromListConstr :: Constr
fromListConstr = mkConstr tableDataType "fromList" [] Prefix

tableDataType :: DataType
tableDataType = mkDataType "Data.Table.Table" [fromListConstr]

instance Monoid (Table t) where
  mempty = EmptyTable
  {-# INLINE mempty #-}

  EmptyTable `mappend` r          = r
  r          `mappend` EmptyTable = r
  r@Table{}  `mappend` s          = F.foldl' (flip insert) r s
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

type instance IxKey (Table t) = PKT t
type instance IxValue (Table t) = t

instance Applicative f => Ixed f (Table t) where
  ix _ _ EmptyTable = pure EmptyTable
  ix k f (Table m) = Table <$> primaryMap (ix k f) m
  {-# INLINE ix #-}

instance Tabular t => At (Table t) where
  at k f EmptyTable = maybe EmptyTable singleton <$> indexed f k Nothing
  at k f (Table m)  = Table <$> primaryMap (at k f) m
  {-# INLINE at #-}

deleteCollisions :: Table t -> [t] -> Table t
deleteCollisions EmptyTable _ = EmptyTable
deleteCollisions (Table tab) ts = Table $ runIdentity $ forTab tab $ \k i -> Identity $ case i of
  PrimaryMap idx          -> PrimaryMap $ primarily k $ F.foldl' (flip (M.delete . fetch primary)) idx ts
  CandidateMap idx        -> CandidateMap             $ F.foldl' (flip (M.delete . fetch k)) idx ts
  CandidateIntMap idx     -> CandidateIntMap          $ F.foldl' (flip (IM.delete . fetch k)) idx ts
  CandidateHashMap idx    -> CandidateHashMap         $ F.foldl' (flip (HM.delete . fetch k)) idx ts
  SupplementalMap idx     -> SupplementalMap $ M.foldlWithKey' ?? idx ?? M.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  SupplementalIntMap idx  -> SupplementalIntMap $ IM.foldlWithKey' ?? idx ?? IM.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  SupplementalHashMap idx -> SupplementalHashMap $ HM.foldlWithKey' ?? idx ?? HM.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedMap idx         -> InvertedMap     $ M.foldlWithKey' ?? idx ?? M.fromListWith (++) [ (f, [t]) | t <- ts, f <- S.toList $ fetch k t ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedIntMap idx      -> InvertedIntMap  $ IM.foldlWithKey' ?? idx ?? IM.fromListWith (++) [ (f, [t]) | t <- ts, f <- IS.toList $ fetch k t ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedHashMap idx     -> InvertedHashMap $ HM.foldlWithKey' ?? idx ?? HM.fromListWith (++) [ (f, [t]) | t <- ts, f <- HS.toList $ fetch k t ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)

{-# INLINE deleteCollisions #-}

emptyTab :: Tabular t => Tab t (Index t)
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
insert t0 r = case autoTab t0 of
  Just p -> case r of
    EmptyTable -> go (p emptyTab)
    Table m    -> go (p m)
  Nothing -> go t0
  where
  go t = case delete t r of
    EmptyTable -> singleton t
    Table m -> Table $ runIdentity $ forTab m $ \k i -> Identity $ case i of
      PrimaryMap idx          -> primarily k $ PrimaryMap $ idx & at (fetch k t) ?~ t
      CandidateMap idx        -> CandidateMap             $ idx & at (fetch k t) ?~ t
      CandidateIntMap idx     -> CandidateIntMap          $ idx & at (fetch k t) ?~ t
      CandidateHashMap idx    -> CandidateHashMap         $ idx & at (fetch k t) ?~ t
      SupplementalMap idx     -> SupplementalMap          $ idx & at (fetch k t) . anon [] P.null %~ (t:)
      SupplementalIntMap idx  -> SupplementalIntMap       $ idx & at (fetch k t) . anon [] P.null %~ (t:)
      SupplementalHashMap idx -> SupplementalHashMap      $ idx & at (fetch k t) . anon [] P.null %~ (t:)
      InvertedMap idx         -> InvertedMap              $ idx & flip (F.foldr $ \ik -> at ik . anon [] P.null %~ (t:)) (fetch k t)
      InvertedIntMap idx      -> InvertedIntMap           $ idx & flip (IS.foldr $ \ik -> at ik . anon [] P.null %~ (t:)) (fetch k t)
      InvertedHashMap idx     -> InvertedHashMap          $ idx & flip (F.foldr $ \ik -> at ik . anon [] P.null %~ (t:)) (fetch k t)
  {-# INLINE go #-}
{-# INLINE insert #-}

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

instance (Tabular b, Applicative f, i ~ PKT a) => Each i f (Table a) (Table b) a b where
  each _ EmptyTable = pure EmptyTable
  each f (Table m)  = P.foldr insert empty <$> sequenceA (M.foldrWithKey (\i a r -> indexed f i a : r) [] $ m^.primaryMap)

-- | Traverse all of the rows in a table without changing any types
rows' :: Traversal' (Table t) t
rows' _ EmptyTable = pure EmptyTable
rows' f r@Table{} = P.foldr insert empty <$> traverse f (toList r)
{-# INLINE rows' #-}

-- | Traverse all of the rows in a table, potentially changing table types completely.
rows :: Tabular t => Traversal (Table s) (Table t) s t
rows f r = P.foldr insert empty <$> traverse f (toList r)
{-# INLINE rows #-}

class Group f q t i | q -> t i where
  -- | Group by a given key or arbitrary function.
  group :: (Indexable i p, Ord i) => q -> IndexedLensLike' p f (Table t) (Table t)

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
  withAny k as f r@(Table m) = go $ m^..primaryMap.folded.filtered (P.any (\e -> ss^.ix e) . k)
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
          ss = S.fromList as
  {-# INLINE withAny #-}

  withAll _ _  f EmptyTable  = f EmptyTable
  withAll k as f r@(Table m) = go $ m^..primaryMap.folded.filtered (P.all (\e -> ss^.ix e) . k)
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
          ss = S.fromList as
  {-# INLINE withAll #-}

instance Ord a => Withal (Key Inverted t (Set a)) [a] t where
  withAny _  _  f EmptyTable  = f EmptyTable
  withAny ky as f r@(Table m) = go $ case ixTab m ky of
    InvertedMap idx -> as >>= \a -> idx^..ix a.folded
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAny #-}

  withAll _  _  f EmptyTable  = f EmptyTable
  withAll _  [] f r           = f r -- every row has all of an empty list of keywords
  withAll ky (a:as) f r@(Table m) = case ixTab m ky of
    InvertedMap idx -> let mkm c = M.fromList [ (fetch primary v, v) | v <- idx^..ix c.folded ]
                         in go $ F.toList $ F.foldl' (\r -> M.intersection r . mkm) (mkm a) as
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAll #-}

instance Withal (Key InvertedInt t (IntSet)) [Int] t where
  withAny _  _  f EmptyTable  = f EmptyTable
  withAny ky as f r@(Table m) = go $ case ixTab m ky of
    InvertedIntMap idx -> as >>= \a -> idx^..ix a.folded
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAny #-}

  withAll _  _  f EmptyTable  = f EmptyTable
  withAll _  [] f r           = f r -- every row has all of an empty list of keywords
  withAll ky (a:as) f r@(Table m) = case ixTab m ky of
    InvertedIntMap idx -> let mkm c = M.fromList [ (fetch primary v, v) | v <- idx^..ix c.folded ]
                          in go $ F.toList $ F.foldl' (\r -> M.intersection r . mkm) (mkm a) as
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAll #-}

instance (Eq a, Hashable a) =>Withal (Key InvertedHash t (HashSet a)) [a] t where
  withAny _  _  f EmptyTable  = f EmptyTable
  withAny ky as f r@(Table m) = go $ case ixTab m ky of
    InvertedHashMap idx -> as >>= \a -> idx^..ix a.folded
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE withAny #-}

  withAll _  _  f EmptyTable  = f EmptyTable
  withAll _  [] f r           = f r -- every row has all of an empty list of keywords
  withAll ky (a:as) f r@(Table m) = case ixTab m ky of
    InvertedHashMap idx -> let mkm c = M.fromList [ (fetch primary v, v) | v <- idx^..ix c.folded ]
                          in go $ F.toList $ F.foldl' (\r -> M.intersection r . mkm) (mkm a) as
    where go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
      go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
      go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
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
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

-- | Build up a table from a list
fromList :: Tabular t => [t] -> Table t
fromList = foldl' (flip insert) empty
{-# INLINE fromList #-}

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

instance Ord a => IsKeyType Inverted (Set a) where
  keyType _ = Inverted
  {-# INLINE keyType #-}

instance a ~ [Int] => IsKeyType InvertedInt IntSet where
  keyType _ = InvertedInt
  {-# INLINE keyType #-}

instance (Eq a, Hashable a)=> IsKeyType InvertedHash (HashSet a) where
  keyType _ = InvertedHash
  {-# INLINE keyType #-}

class HasValue p q f s t a b | s -> a, t -> b, s b -> t, t a -> s where
  value :: Overloading p q f s t a b

------------------------------------------------------------------------------
-- A simple table with an auto-incremented key
------------------------------------------------------------------------------

-- | Generate a row with an auto-incremented key
auto :: a -> Auto a
auto = Auto 0

instance Field1 (Auto a) (Auto a) Int Int where
  _1 f (Auto k a) = indexed f (0 :: Int) k <&> \k' -> Auto k' a

instance Field2 (Auto a) (Auto b) a b where
  _2 f (Auto k a) = indexed f (1 :: Int) a <&> Auto k

instance (a ~ Int, b ~ Int, Applicative f) => Each Int f (Auto a) (Auto b) a b where
  each f (Auto k a) = Auto <$> indexed f (0 :: Int) k <*> indexed f (1 :: Int) a

data Auto a = Auto !Int a
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Data,Typeable)

autoKey :: Lens' (Auto a) Int
autoKey f (Auto k a) = f k <&> \k' -> Auto k' a

instance (Indexable Int p, q ~ (->), Functor f) => HasValue p q f (Auto a) (Auto b) a b where
  value f (Auto k a) = indexed f k a <&> Auto k

instance FunctorWithIndex Int Auto where
  imap f (Auto k a) = Auto k (f k a)

instance FoldableWithIndex Int Auto where
  ifoldMap f (Auto k a) = f k a

instance TraversableWithIndex Int Auto where
  itraverse f (Auto k a) = Auto k <$> f k a

instance Comonad Auto where
  extract (Auto _ a) = a
  extend f w@(Auto k _) = Auto k (f w)

instance Tabular (Auto a) where
  type PKT (Auto a) = Int
  data Tab (Auto a) i = AutoTab (i Primary Int)
  data Key p (Auto a) b where
    AutoKey :: Key Primary (Auto a) Int
  fetch AutoKey (Auto k _) = k
  primary = AutoKey
  primarily AutoKey r = r
  mkTab f = AutoTab <$> f AutoKey
  ixTab (AutoTab x) AutoKey = x
  forTab (AutoTab x) f = AutoTab <$> f AutoKey x
  autoTab = autoIncrement autoKey

------------------------------------------------------------------------------
-- A simple key-value pair, indexed on the key
------------------------------------------------------------------------------

instance (Indexable k p, q ~ (->), Functor f) => HasValue p q f (k, a) (k, b) a b where
  value f (k, a) = indexed f k a <&> (,) k

-- | Simple (key, value) pairs
instance Ord k => Tabular (k,v) where
  type PKT (k,v) = k
  data Tab (k,v) i = KVTab (i Primary k)
  data Key p (k,v) b where
    Fst :: Key Primary (k,v) k
  fetch Fst = fst
  primary = Fst
  primarily Fst r = r
  mkTab f = KVTab <$> f Fst
  ixTab (KVTab x) Fst = x
  forTab (KVTab x) f = KVTab <$> f Fst x

------------------------------------------------------------------------------
-- A simple value for set-like tables.
------------------------------------------------------------------------------

instance Field1 (Value a) (Value b) a b where
  _1 f (Value a) = Value <$> indexed f (0 :: Int) a

instance Functor f => Each Int f (Value a) (Value b) a b where
  each f (Value a) = Value <$> indexed f (0 :: Int) a

instance Wrapped a b (Value a) (Value b) where
  wrapped = iso Value $ \(Value a) -> a

data Value a = Value a
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Data,Typeable)

instance Applicative Value where
  pure = Value
  Value f <*> Value a = Value (f a)

instance Monad Value where
  return = Value
  Value a >>= f = f a

instance MonadFix Value where
  mfix f = let m = f (extract m) in m

instance Comonad Value where
  extract (Value a) = a
  extend f w@(Value _) = Value (f w)

instance ComonadApply Value where
  Value f <@> Value a = Value (f a)

instance (Profunctor p, Functor f, p ~ q) => HasValue p q f (Value a) (Value b) a b where
  value = unwrapped

instance Ord a => Tabular (Value a) where
  type PKT (Value a) = a
  data Tab (Value a) i = ValueTab (i Primary a)
  data Key p (Value a) b where
    Val :: Key Primary (Value a) a
  fetch Val = extract
  primary = Val
  primarily Val r = r
  mkTab f = ValueTab <$> f Val
  ixTab (ValueTab x) Val = x
  forTab (ValueTab x) f = ValueTab <$> f Val x
