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
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
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
  , KeyType(..), Primary, Candidate, Supplemental, Inverted
  , Index(..)
  ) where

import Control.Applicative hiding (empty)
import Control.Comonad
import Control.Lens
import Control.Monad
import Control.Monad.Fix
import Data.Data
import Data.Foldable as F
import Data.Function (on)
import Data.Functor.Identity
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
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
  fetch :: Key k t a -> t -> KeyResult k a

  -- | Every 'Table' has one 'Primary' 'Key'
  primary :: Key Primary t (PKT t)

  -- | ... and so if you find one, it had better be that one!
  primarily :: Key Primary t a -> ((a ~ PKT t) => r) -> r

  -- | Construct a 'Tab' given a function from key to index.
  mkTab :: Applicative h => (forall k a. (IsKeyType k, Ord a) => Key k t a -> h (i k a)) -> h (Tab t i)

  -- | Lookup an index in a 'Tab'
  ixTab :: Tab t i -> Key k t a -> i k a

  -- | Loop over each index in a 'Tab'
  forTab :: Applicative h => Tab t i -> (forall k a . (IsKeyType k, Ord a) => Key k t a -> i k a -> h (j k a)) -> h (Tab t j)

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
autoIncrement :: (Tabular t, PKT t ~ Int) => Loupe' t Int -> t -> Maybe (Tab t (Index t) -> t)
autoIncrement pk t
  | t ^# pk == 0 = Just $ \ tb -> t & pk #~ 1 + fromMaybe 0 (tb ^? primaryMap.traverseMax.index)
  | otherwise    = Nothing
{-# INLINE autoIncrement #-}

-- | This is used to store a single index.
data Index t k a where
  PrimaryIndex      :: Map (PKT t) t      -> Index t Primary      a
  CandidateIndex    :: Ord a => Map a t   -> Index t Candidate    a
  SupplementalIndex :: Ord a => Map a [t] -> Index t Supplemental a
  InvertedIndex     :: Ord a => Map a [t] -> Index t Inverted     a

-- | Find the primary key index a tab
primaryMap :: Tabular t => Lens' (Tab t (Index t)) (Map (PKT t) t)
primaryMap f t = case ixTab t primary of
  PrimaryIndex m -> f m <&> \u -> runIdentity $ forTab t $ \k o -> Identity $ case o of
    PrimaryIndex _ -> primarily k (PrimaryIndex u)
    _              -> o
{-# INLINE primaryMap #-}

-- * Overloaded keys

------------------------------------------------------------------------------
-- Table
------------------------------------------------------------------------------

-- | Every 'Table' has a 'Primary' 'key' and may have 'Candidate' or
-- 'Supplemental' keys.
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
  PrimaryIndex idx      -> PrimaryIndex $ primarily k $ foldl' (flip (M.delete . fetch primary)) idx ts
  CandidateIndex idx    -> CandidateIndex $ foldl' (flip (M.delete . fetch k)) idx ts
  SupplementalIndex idx -> SupplementalIndex $ M.foldlWithKey' ?? idx ?? M.fromListWith (++) [ (fetch k t, [t]) | t <- ts ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
  InvertedIndex idx -> InvertedIndex $ M.foldlWithKey' ?? idx ?? M.fromListWith (++) [ (f, [t]) | t <- ts, f <- fetch k t ] $ \m ky ys ->
    m & at ky . anon [] P.null %~ let pys = fetch primary <$> ys in filter (\e -> fetch primary e `P.notElem` pys)
{-# INLINE deleteCollisions #-}

emptyTab :: Tabular t => Tab t (Index t)
emptyTab = runIdentity $ mkTab $ \k -> Identity $ case keyType k of
  Primary      -> primarily k (PrimaryIndex M.empty)
  Candidate    -> CandidateIndex M.empty
  Supplemental -> SupplementalIndex M.empty
  Inverted     -> InvertedIndex M.empty
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
  Primary      -> primarily k $ PrimaryIndex $ M.singleton (fetch k row) row
  Candidate    -> CandidateIndex             $ M.singleton (fetch k row) row
  Supplemental -> SupplementalIndex          $ M.singleton (fetch k row) [row]
  Inverted     -> InvertedIndex              $ M.fromList $ zip (fetch k row) (repeat [row])
{-# INLINE singleton #-}

-- | Return the set of rows that would be delete by deleting or inserting this row
collisions :: t -> Table t -> [t]
collisions _ EmptyTable = []
collisions t (Table m)  = getConst $ forTab m $ \k i -> Const $ case i of
  PrimaryIndex idx   -> primarily k $ idx^..ix (fetch k t)
  CandidateIndex idx ->               idx^..ix (fetch k t)
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
      PrimaryIndex idx      -> primarily k $ PrimaryIndex $ idx & at (fetch k t) ?~ t
      CandidateIndex idx    -> CandidateIndex             $ idx & at (fetch k t) ?~ t
      SupplementalIndex idx -> SupplementalIndex          $ idx & at (fetch k t) . anon [] P.null %~ (t:)
      InvertedIndex idx     -> InvertedIndex              $ idx & flip (F.foldr $ \ik -> at ik . anon [] P.null %~ (t:)) (fetch k t)
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

class With q t | q -> t where
  -- | Select a smaller, updateable subset of the rows of a table using an index or an arbitrary function.
  with :: Ord a => q a -> (forall x. Ord x => x -> x -> Bool) -> a -> Lens' (Table t) (Table t)

  -- | Group by a given key or arbitrary function.
  group :: (Indexable a p, Applicative f, Ord a) => q a -> IndexedLensLike' p f (Table t) (Table t)

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

  group _ _ EmptyTable = pure EmptyTable
  group ky f (Table m) = traverse (\(k,vs) -> indexed f k (fromList vs)) (M.toList idx) <&> mconcat where 
    idx = M.fromListWith (++) (m^..primaryMap.folded.to(\v -> (ky v, [v])))
  {-# INLINE group #-}

instance With (Key k t) t where
  with _   _   _ f EmptyTable  = f EmptyTable
  with ky cmp a f r@(Table m)
    | lt && eq && gt = f r -- all rows
    | not lt && eq && not gt = case ixTab m ky of
      PrimaryIndex idx      -> go $ primarily ky (idx^..ix a)
      CandidateIndex idx    -> go $ idx^..ix a
      SupplementalIndex idx -> go $ idx^..ix a.folded
      InvertedIndex idx     -> go $ idx^..ix a.folded
    | lt || eq || gt = case ixTab m ky of
      PrimaryIndex idx -> primarily ky $ case M.splitLookup a idx of
        (l,e,g) -> go $ (if lt then F.toList l else [])
                     ++ (if eq then F.toList e else [])
                     ++ (if gt then F.toList g else [])
      CandidateIndex idx -> case M.splitLookup a idx of
        (l,e,g) -> go $ (if lt then F.toList l else [])
                     ++ (if eq then F.toList e else [])
                     ++ (if gt then F.toList g else [])
      SupplementalIndex idx -> case M.splitLookup a idx of
        (l,e,g) -> go $ (if lt then F.concat l else [])
                     ++ (if eq then F.concat e else [])
                     ++ (if gt then F.concat g else [])
      InvertedIndex idx -> case M.splitLookup a idx of
        (l,e,g) -> go $ (if lt then F.concat l else [])
                     ++ (if eq then F.concat e else [])
                     ++ (if gt then F.concat g else [])
    | otherwise      = f EmptyTable <&> mappend r -- no match
    where
        lt = cmp LT EQ
        eq = cmp EQ EQ
        gt = cmp GT EQ
        go xs = f (xs^.table) <&> mappend (deleteCollisions r xs)
  {-# INLINE with #-}

  group _ _ EmptyTable = pure EmptyTable
  group ky f (Table m) = case ixTab m ky of
    PrimaryIndex idx      -> primarily ky $ for (toList idx) (\v -> indexed f (fetch primary v) (singleton v)) <&> mconcat
    CandidateIndex idx    -> traverse (\(k,v) -> indexed f k (singleton v)) (M.toList idx) <&> mconcat
    SupplementalIndex idx -> traverse (\(k,vs) -> indexed f k (fromList vs)) (M.toList idx) <&> mconcat
    InvertedIndex idx     -> traverse (\(k,vs) -> indexed f k (fromList vs)) (M.toList idx) <&> mconcat
  {-# INLINE group #-}



-- | Build up a table from a list
fromList :: Tabular t => [t] -> Table t
fromList = foldl' (flip insert) empty
{-# INLINE fromList #-}

-- * Lifting terms to types

-- | Value-level key types
data KeyType t where
  Primary      :: KeyType Primary
  Candidate    :: KeyType Candidate
  Supplemental :: KeyType Supplemental
  Inverted     :: KeyType Inverted

-- |  Type level key types
data Primary
data Candidate
data Supplemental
data Inverted

class IsKeyType k where
  type KeyResult k a
  keyType :: Key k t a -> KeyType k

instance IsKeyType Primary where
  type KeyResult Primary a = a
  keyType _ = Primary
  {-# INLINE keyType #-}

instance IsKeyType Candidate where
  type KeyResult Candidate a = a
  keyType _ = Candidate
  {-# INLINE keyType #-}

instance IsKeyType Supplemental where
  type KeyResult Supplemental a = a
  keyType _ = Supplemental
  {-# INLINE keyType #-}

instance IsKeyType Inverted where
  type KeyResult Inverted a = [a]
  keyType _ = Inverted
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
