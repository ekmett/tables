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
import Data.Proxy
import Data.Table
import Data.Traversable
import Prelude.Extras
import qualified Prelude
import Prelude hiding (null)

-- * Example Table

data Foo a = Foo { __fooId :: Int, __fooBar :: a, __fooBaz :: Double }
  deriving (Eq,Ord,Show,Read,Data,Typeable)

makeLenses ''Foo

class HasFooKeys t a | t -> a where
  foo    :: Simple Lens t (Foo a)
  fooId  :: Key Primary t Int
  fooBar :: Key Other t a
  fooBaz :: Key (Secondary NonUnique) t Double

instance HasFooKeys (Foo a) a where
  foo    = id
  fooId  = key FooId
  fooBar = nokey _fooBar
  fooBaz = key FooBaz

instance Tabular (Foo a) where
  type PKT (Foo a) = Int
  data Column (Foo a) k b where
    FooId  :: Column (Foo a) Primary Int
    FooBaz :: Column (Foo a) (Secondary NonUnique) Double

  data Tab (Foo a) = FooTab
    {-# UNPACK #-} !Int
    (Index (Foo a) Primary Int)
    (Index (Foo a) (Secondary NonUnique) Double)

  val FooId  = _fooId
  val FooBaz = _fooBaz

  primaryKey = fooId

  primarily (Fob FooId) r = r

  tabulate f = FooTab 0 (f fooId) (f fooBaz)

  ixMeta (FooTab _ x _) (Fob FooId)  = x
  ixMeta (FooTab _ _ x) (Fob FooBaz) = x
  ixMeta _              (NoFob _)    = OtherIndex

  forMeta (FooTab n x z) f = FooTab n <$> f fooId x <*> f fooBaz z

  prim = indexed $ \ f (FooTab n x z) -> f (FooId :: Column (Foo a) Primary Int) x <&> \x' -> FooTab n x' z

  autoKey = autoIncrement $ \f (FooTab n x z) -> f n <&> \n' -> FooTab n' x z

test :: Table (Foo String)
test = [Foo 0 "One" 1.0, Foo 0 "Two" 2.0, Foo 0 "Three" 3.0, Foo 0 "Four" 4.0, Foo 0 "Five" 5.0]^.table
