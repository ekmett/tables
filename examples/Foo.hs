{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Foo where

import Control.Applicative hiding (empty)
import Control.Lens
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Identity
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Proxy
import Data.Table
import Data.Traversable
import Prelude.Extras
import qualified Prelude
import Prelude hiding (null)

-- * Example Table

data Foo a = Foo { __fooId :: Int, __fooBar :: a, __fooBaz :: Double }
  deriving (Eq,Ord,Show,Read)

makeLenses ''Foo

class HasFooKeys t a | t -> a where
  foo    :: Simple Lens t (Foo a)
  fooId  :: Key Primary t Int
  fooBar :: Key Other t a
  fooBaz :: Key (Secondary NonUnique) t Double

instance HasFooKeys (Foo a) a where
  foo    = id
  fooId  = key FooId
  fooBar = key FooBar
  fooBaz = key FooBaz

instance Tabular (Foo a) where
  type PKT (Foo a) = Int
  data Column (Foo a) k b where
    FooId  :: Column (Foo a) Primary Int
    FooBar :: Column (Foo a) Other a
    FooBaz :: Column (Foo a) (Secondary NonUnique) Double

  data Tab (Foo a) = FooTab
    {-# UNPACK #-} !Int
    (Index (Foo a) Primary Int)
    (Index (Foo a) Other a)
    (Index (Foo a) (Secondary NonUnique) Double)

  val FooId  = _fooId
  val FooBar = _fooBar
  val FooBaz = _fooBaz

  primaryKey = fooId

  primarily (Fob FooId) r = r

  tabulate f = FooTab 0 (f fooId) (f fooBar) (f fooBaz)

  ixMeta (FooTab _ x _ _) (Fob FooId)  = x
  ixMeta (FooTab _ _ x _) (Fob FooBar) = x
  ixMeta (FooTab _ _ _ x) (Fob FooBaz) = x

  forMeta (FooTab n x y z) f = FooTab n <$> f fooId x <*> f fooBar y <*> f fooBaz z

  prim = indexed $ \ f (FooTab n x y z) -> f (FooId :: Column (Foo a) Primary Int) x <&> \x' -> FooTab n x' y z

  autoKey = autoIncrement $ \f (FooTab n x y z) -> f n <&> \n' -> FooTab n' x y z

test :: Table (Foo String)
test = [Foo 0 "One" 1.0, Foo 0 "Two" 2.0, Foo 0 "Three" 3.0, Foo 0 "Four" 4.0, Foo 0 "Five" 5.0]^.table
