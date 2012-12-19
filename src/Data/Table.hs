{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Table

  (
  -- * Tables
    Table(..)
  -- * Keys
  , Key
  -- ** Table Construction
  , empty
  , singleton
  , table
  , fromList
  , insert
  -- ** Querying
  , null
  , group
  , with
  , rows
  , rows'
  -- * Deleting
  , delete
  -- * Esoterica
  , deleteWith
  , autoIncrement
  -- * Implementation Details
  , Tabular(..)
  , Keyed(..)
  , ColumnType(..), Primary, Secondary, Other
  , Uniqueness(..), Unique, NonUnique
  , Index(..)
  , Fob(..)
  ) where

import Control.Applicative hiding (empty)
import Control.Lens
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Identity
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Traversable
import qualified Prelude
import Prelude hiding (null)

class Ord (PKT t) => Tabular (t :: *) where
  -- | The type of the primary key
  type PKT t :: *
  -- | The type used internally for tables
  data Tab t :: *
  -- | The type used internally for columns
  data Column t :: (* -> *) -> * -> *

  -- | evaluate an internal column
  val        :: Column t ty a -> Simple Lens t a

  -- | Every relation has one primary key
  primaryKey :: Key Primary t (PKT t)

  -- | ... and so if you find one, it had better be that one!
  primarily  :: Keying Primary t a -> ((a ~ PKT t) => r) -> r

  -- | Construct a table given a function from key to index.
  tabulate   :: (forall k a. IsColumn k a => Key k t a -> Index t k a) -> Tab t

  -- | Lookup an index
  ixMeta     :: Tab t -> Keying k t a -> Index t k a

  -- | Loop over each index
  forMeta    :: Applicative h => Tab t -> (forall k a . Key k t a -> Index t k a -> h (Index t k a)) -> h (Tab t)

  -- | Find the primary key in a table
  prim       :: SimpleIndexedLens (Column t Primary (PKT t)) (Tab t) (Index t Primary (PKT t))

  -- | Adjust a record using meta-information about the table allowing for auto-increments, etc.
  autoKey    :: t -> Maybe (Tab t -> (t, Tab t))
  autoKey _ = Nothing

-- | This lets you define 'autoKey' using a lens to a counter stored in the Tab.
autoIncrement :: (Tabular t, Num a, PKT t ~ a) => Simple Lens (Tab t) a -> t -> Maybe (Tab t -> (t, Tab t))
autoIncrement l t
  | t^.primaryKey == 0 = Just $ \ tbl -> tbl & l %%~ \ i -> let i' = i + 1 in i' `seq` (t & primaryKey .~ i' , i')
  | otherwise          = Nothing

data Index t k a where
  PrimaryIndex      :: Map a t -> Index t Primary a
  CandidateIndex    :: Ord a => Map a t -> Index t (Secondary Unique) a
  SupplementalIndex :: Ord a => Map a [t] -> Index t (Secondary NonUnique) a
  OtherIndex        :: Index t Other a

primaryMap :: Tabular t => Simple Lens (Index t Primary (PKT t)) (Map (PKT t) t)
primaryMap f (PrimaryIndex m) = PrimaryIndex <$> f m
{-# INLINE primaryMap #-}

-- * Lifting terms to types

data Uniqueness u where
  Unique :: Uniqueness Unique
  NonUnique :: Uniqueness NonUnique
data Unique
data NonUnique

class IsUniqueness (u :: *) where
  uniq :: Fob (k u) (a -> f a) y -> Uniqueness u
instance IsUniqueness Unique where
  uniq _ = Unique
  {-# INLINE uniq #-}
instance IsUniqueness NonUnique where
  uniq _ = NonUnique
  {-# INLINE uniq #-}

data ColumnType t a where
  Primary   :: ColumnType Primary a
  Secondary :: Ord a => Uniqueness u -> ColumnType (Secondary u) a
  Other     :: ColumnType Other a
data Primary (a :: *)
data Secondary (u :: *) (a :: *)
data Other (a :: *)

class IsColumn u a where
  columnType :: Fob u (a -> Mutator a) y -> ColumnType u a
instance Ord a => IsColumn Primary a where
  columnType _ = Primary
  {-# INLINE columnType #-}
instance (IsUniqueness u, Ord a) => IsColumn (Secondary u) a where
  columnType t = Secondary (uniq t)
  {-# INLINE columnType #-}
instance IsColumn Other a where
  columnType _ = Other
  {-# INLINE columnType #-}

-- * Overloaded keys
type Key u t a = forall k f. (Keyed u k, Functor f) => k (a -> f a) (t -> f t)

class Keyed u k where
  key :: (Tabular t, Functor f) => Column t u a -> SimpleOverloaded k f t a
  nokey :: (Functor f, u ~ Other) => SimpleLens t a -> SimpleOverloaded k f t a

instance Keyed u (->) where
  key     = val
  nokey l = l

type Keying u t a = Fob u (a -> Mutator a) (t -> Mutator t)

type family CoF (x :: *) b :: *
type instance CoF (x -> y) b = FunOf y b

type family FunOf (x :: *) (b :: *) :: *
type instance FunOf (f a) b = f b

data Fob u x y where
  Fob :: (CoA x ~ CoB x, CoA y ~ CoB y) => Column (CoA y) u (CoA x) -> Fob u x y
  NoFob :: (CoA x ~ CoB x, CoA y ~ CoB y) => (forall f. Functor f => (CoA x -> f (CoB x)) -> CoA y -> f (CoB y)) -> Fob Other x y

instance u ~ v => Keyed u (Fob v) where
  key   = Fob
  nokey l = NoFob l

fob :: forall u t a. Tabular t => Keying u t a -> Key u t a
fob (Fob k)   = key k
fob (NoFob l) = nokey l
{-# INLINE fob #-}

-- * Helpers

data Table t where
  EmptyTable :: Table t
  Table :: Tabular t => Tab t -> Table t

instance Monoid (Table t) where
  mempty               = EmptyTable
  EmptyTable `mappend` r = r
  r `mappend` EmptyTable = r
  r@Table{} `mappend` s  = Foldable.foldl' (flip insert) r s

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
  foldMap f (Table m)  = foldMapOf (prim.primaryMap.folded) f m
  {-# INLINE foldMap #-}

deleteCollisions :: Table t -> [t] -> Table t
deleteCollisions EmptyTable _ = EmptyTable
deleteCollisions (Table tab) ts = Table $ runIdentity $ forMeta tab $ \k i -> Identity $ case i of
  PrimaryIndex idx      -> PrimaryIndex $ primarily k $ foldl' (flip (Map.delete . view primaryKey)) idx ts
  CandidateIndex idx    -> CandidateIndex $ foldl' (flip (Map.delete . view k)) idx ts
  SupplementalIndex idx -> SupplementalIndex $ Map.foldlWithKey' ?? idx ?? Map.fromListWith (++) [ (t^.k, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon [] Prelude.null %~ let pys = view primaryKey <$> ys in filter (\e -> e^.primaryKey `Prelude.notElem` pys)
  OtherIndex -> OtherIndex
{-# INLINE deleteCollisions #-}

emptyTab :: Tabular t => Tab t
emptyTab = tabulate $ \c -> case columnType c of
  Primary             -> primarily c $ PrimaryIndex Map.empty
  Secondary Unique    -> CandidateIndex Map.empty
  Secondary NonUnique -> SupplementalIndex Map.empty
  Other               -> OtherIndex
{-# INLINE emptyTab #-}

-- * Public API

-- | Construct an empty relation
empty :: Table t
empty = EmptyTable
{-# INLINE empty #-}

-- | Check to see if the relation is empty
null :: Table t -> Bool
null EmptyTable = True
null (Table m)  = Map.null (m^.prim.primaryMap)
{-# INLINE null #-}

-- | Construct a relation with a single row
singleton :: Tabular t => t -> Table t
singleton row = Table $ tabulate $ \c -> case columnType c of
  Primary             -> primarily c $ PrimaryIndex (Map.singleton (row^.primaryKey) row)
  Secondary Unique    -> CandidateIndex (Map.singleton (row^.fob c) row)
  Secondary NonUnique -> SupplementalIndex (Map.singleton (row^.fob c) [row])
  Other               -> OtherIndex
{-# INLINE singleton #-}

-- | Return the set of rows that would be delete by deleting or inserting this row
collisions :: t -> Table t -> [t]
collisions _ EmptyTable = []
collisions t (Table m)  = getConst $ forMeta m $ \k i -> Const $ case i of
  PrimaryIndex idx   -> primarily k $ idx^..at (t^.k).traverse
  CandidateIndex idx -> idx^..at (t^.k).traverse
  _                  -> []
{-# INLINE collisions #-}

-- | Delete this row from the database
delete :: t -> Table t -> Table t
delete t m = deleteCollisions m (collisions t m)
{-# INLINE delete #-}

deleteWith :: (IsColumn u a, Ord a) => Keying u t a -> (forall x. Ord x => x -> x -> Bool) -> a -> Table t -> Table t
deleteWith ky cmp a tbl = tbl & with ky cmp a .~ empty
{-# INLINE deleteWith #-}

-- | Insert a row into a relation, removing collisions.
insert :: Tabular t => t -> Table t -> Table t
insert t0 r0 = case autoKey t0 of
  Just p -> case r0 of
    EmptyTable -> case p emptyTab of
      (t1,m1) -> go t1 (Table m1)
    Table m    -> case p m of
      (t1,m1) -> go t1 (Table m1)
  Nothing -> go t0 r0
  where
  go t r = case delete t r of
    EmptyTable -> singleton t
    Table m -> Table $ runIdentity $ forMeta m $ \k i -> Identity $ case i of
      PrimaryIndex idx      -> primarily k $ PrimaryIndex $ idx & at (t^.primaryKey) ?~ t
      CandidateIndex idx    -> CandidateIndex $ idx & at (t^.k) ?~ t
      SupplementalIndex idx -> SupplementalIndex $ idx & at (t^.k) . anon [] Prelude.null %~ (t:)
      OtherIndex            -> OtherIndex
  {-# INLINE go #-}
{-# INLINE insert #-}

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
table :: Tabular t => Simple Lens [t] (Table t)
table = iso fromList toList
{-# INLINE table #-}

with :: Ord a => Keying u t a -> (forall x. Ord x => x -> x -> Bool) -> a -> Simple Lens (Table t) (Table t)
with _   _   _ f EmptyTable  = f EmptyTable
with ky cmp a f r@(Table m)
    | lt && eq && gt = f r -- all rows
    | not lt && eq && not gt = case ixMeta m ky of
      PrimaryIndex idx      -> go $ primarily ky (idx^..at a.traverse)
      CandidateIndex idx    -> go $ idx^..at a.folded
      SupplementalIndex idx -> go $ idx^..at a.folded.folded
      OtherIndex            -> getOther
    | lt || eq || gt = case ixMeta m ky of
      PrimaryIndex idx -> primarily ky $ case Map.splitLookup a idx of
        (l,e,g) -> go $ (if lt then Foldable.toList l else [])
                     ++ (if eq then Foldable.toList e else [])
                     ++ (if gt then Foldable.toList g else [])
      CandidateIndex idx -> case Map.splitLookup a idx of
        (l,e,g) -> go $ (if lt then Foldable.toList l else [])
                     ++ (if eq then Foldable.toList e else [])
                     ++ (if gt then Foldable.toList g else [])
      SupplementalIndex idx -> case Map.splitLookup a idx of
        (l,e,g) -> go $ (if lt then Foldable.concat l else [])
                     ++ (if eq then Foldable.concat e else [])
                     ++ (if gt then Foldable.concat g else [])
      OtherIndex -> getOther
    | otherwise      = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
        getOther = go $ m^..prim.primaryMap.folded.filtered (\row -> cmp (row^.fob ky) a)
{-# INLINE with #-}

-- | @'group' :: 'Key' u s a -> 'SimpleIndexedTraversal' a ('Table' s) ('Table' s)@
group :: forall k f u s a. (Indexable a k, Applicative f, Ord a) => Keying u s a -> SimpleOverloaded k f (Table s) (Table s)
group ky = indexed $ \(f :: a -> Table s -> f (Table s)) r -> case r of
  EmptyTable -> pure EmptyTable
  Table m    -> case ixMeta m ky of
    PrimaryIndex idx      -> primarily ky $ for (toList idx) (\v -> f (v^.primaryKey) (singleton v)) <&> mconcat
    CandidateIndex idx    -> traverse (\(k,v) -> f k (singleton v)) (Map.toList idx) <&> mconcat
    SupplementalIndex idx -> traverse (\(k,vs) -> f k (fromList vs)) (Map.toList idx) <&> mconcat
    OtherIndex
      | idx <- Map.fromListWith (++) (m^..prim.primaryMap.folded.to(\v -> (v^.fob ky, [v])))
      -> traverse (\(k,vs) -> f k (fromList vs)) (Map.toList idx) <&> mconcat
{-# INLINE group #-}

-- * Traverse all of the rows in a table without changing any types
rows' :: Simple Traversal (Table t) t
rows' _ EmptyTable = pure EmptyTable
rows' f r@Table{} = Prelude.foldr insert empty <$> traverse f (toList r)
{-# INLINE rows' #-}

-- * Traverse all of the rows in a table, potentially changing table types completely.
rows :: Tabular t => Traversal (Table s) (Table t) s t
rows f r = Prelude.foldr insert empty <$> traverse f (toList r)
{-# INLINE rows #-}

-- * Build up a table from a list
fromList :: Tabular t => [t] -> Table t
fromList = foldl' (flip insert) empty
{-# INLINE fromList #-}
