{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Foo where

import Control.Applicative hiding (empty)
import Control.Lens
import Data.Data
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Identity
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Table
import Data.Traversable
import qualified Prelude
import Prelude hiding (null)

-- * Example Table

data Foo a = Foo { _fooId :: Int, _fooBar :: a, _fooBaz :: Double }
  deriving (Eq,Ord,Show,Read,Data,Typeable)

makeLenses ''Foo

instance Tabular (Foo a) where
  type PKT (Foo a) = Int
  data Key k (Foo a) b where
    FooId  :: Key Primary               (Foo a) Int
    FooBaz :: Key (Secondary NonUnique) (Foo a) Double

  data Tab (Foo a) = FooTab
    {-# UNPACK #-} !Int
    (Index Primary               (Foo a) Int)
    (Index (Secondary NonUnique) (Foo a) Double)

  val FooId  = _fooId
  val FooBaz = _fooBaz

  primaryKey = fooId

  primarily FooId r = r

  tabulate f = FooTab 0 (f FooId) (f FooBaz)

  ixMeta (FooTab _ x _) FooId  = x
  ixMeta (FooTab _ _ x) FooBaz = x

  forMeta (FooTab n x z) f = FooTab n <$> f FooId x <*> f FooBaz z

  prim f (FooTab n x z) = indexed f (FooId :: Key Primary (Foo a) Int) x <&> \x' -> FooTab n x' z

  autoKey = autoIncrement $ \f (FooTab n x z) -> f n <&> \n' -> FooTab n' x z

test :: Table (Foo String)
test = [Foo 0 "One" 1.0, Foo 0 "Two" 2.0, Foo 0 "Three" 3.0, Foo 0 "Four" 4.0, Foo 0 "Five" 5.0]^.table
