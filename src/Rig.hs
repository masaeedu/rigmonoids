{-# LANGUAGE RankNTypes, DataKinds, KindSignatures, PolyKinds, TypeOperators, MultiParamTypeClasses, GADTs, FlexibleContexts, AllowAmbiguousTypes, TypeSynonymInstances, FlexibleInstances #-}

module Rig where

import Prelude hiding (Num(..))
import Data.Functor.Const

-- https://ncatlab.org/nlab/show/category+of+monoids

type Hom c = c -> c -> *

-- A (small) category
class GCategory (p :: Hom c)
  where
  gidentity :: forall a. p a a
  gcompose :: forall a b c. (b `p` c) -> (a `p` b) -> a `p` c

-- A functor between categories
class GFunctor (p :: Hom c) (q :: Hom d) (f :: c -> d)
  where
  gfmap :: p a b -> q (f a) (f b)

-- A product of two categories
data Product p q a b
  where
  Product :: p a c -> q b d -> Product p q '(a, b) '(c, d)

-- Isomorphisms in a category
data Iso (p :: Hom c) (a :: c) (b :: c) = Iso { fwd :: p a b, bwd :: p b a }

-- An associative tensor
class (GFunctor (Product p p) p t, GCategory p) => Tensor p t
  where
  assoc :: Iso p (t '(a, t '(b, c))) (t '(t '(a, b), c))

-- A symmetric, associative tensor
class Tensor p t => Symmetric p t
  where
  swap :: t '(a, b) `p` t '(b, a)

-- A full monoidal structure
class Tensor p t => MTensor p t i
  where
  lunit :: Iso p (t '(i, a)) a
  runit :: Iso p (t '(a, i)) a

-- A semigroup object in a monoidal category
class Tensor p t => GSemigroup p t a
  where
  gmappend :: t '(a, a) `p` a

-- A monoid object in a monoidal category
class (MTensor p t i, GSemigroup p t a) => GMonoid p t i a
  where
  gmempty :: i `p` a

-- A pair of monoidal structures over a category where one distributes over the other
class (Tensor p add, Tensor p mul) => LeftDistributive p mul add
  where
  ldistrib :: Iso p (mul '(a, add '(b, c))) (add '(mul '(a, b), mul '(a, c)))

class (Tensor p add, Tensor p mul) => RightDistributive p mul add
  where
  rdistrib :: Iso p (mul '(add '(a, b), c)) (add '(mul '(a, c), mul '(b, c)))

class (LeftDistributive p mul add, RightDistributive p mul add) => Distributive p mul add

-- A monoidal tensor with an annihilating element
class Tensor p mul => Annihilates p mul zero
  where
  lnil :: Iso p (mul '(a, zero)) zero
  rnil :: Iso p (mul '(zero, a)) zero

-- A semiring category
class (MTensor p mul one, MTensor p add zero, Distributive p mul add, Annihilates p mul zero) => Semiring p mul one add zero

-- The fixpoint of some indexed type constructor
data GFix (f :: (k -> *) -> (k -> *)) (a :: k) = GFix { unGFix :: f (GFix f) a }

type Ix i = i -> *
-- I claim that there is a free functor from any semirig category to a category of monoid objects
-- Here is the free monoid induced by any indexed type constructor with products and coproducts
data SRFreeF (mul :: (Ix i, Ix i) -> Ix i) (one :: Ix i) (add :: (Ix i, Ix i) -> Ix i) (a :: Ix i) (rec :: Ix i) (k :: i)
  where
  SRFreeF :: add '(one, mul '(a, rec)) k -> SRFreeF mul one add a rec k

type SRFree mul one add a = GFix (SRFreeF mul one add a)

instance (MTensor p mul one, Tensor p add, Distributive p mul add) => GSemigroup p mul (SRFree mul one add a)
  where
  gmappend = _

instance (MTensor p mul one, Tensor p add, Distributive p mul add) => GMonoid p mul one (SRFree mul one add a)
  where
  gmempty = _

-- Try it out for free monoids
data IndexedProduct ab k
  where
  IndexedProduct :: a k -> b k -> IndexedProduct '(a, b) k

(*) = IndexedProduct

data IndexedSum ab k
  where
  IndexedSum :: Either (a k) (b k) -> IndexedSum '(a, b) k

data IndexedUnit k
  where
  IndexedUnit :: IndexedUnit k

type FreeMonoid a = SRFree IndexedProduct IndexedUnit IndexedSum (Const a) '()

nil :: FreeMonoid a
nil = GFix $ SRFreeF $ IndexedSum $ Left $ IndexedUnit

cons :: a -> FreeMonoid a -> FreeMonoid a
cons a as = _
