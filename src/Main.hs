{-# LANGUAGE ImpredicativeTypes #-}
module Main where

import Prelude hiding (id, (.))
import Control.Category
import Data.Bifunctor
import Data.Profunctor

import Iso

type f ~~~> g = forall x y z. f x y z -> g x y z

-- Here's the notion of profunctor strength I'm familiar with
-- type Strength t p = forall a b c. p a b -> p (t a c) (t b c) -- problem
type Strength t p = forall a b c. p c a -> p (t c b) (t a b) -- no problem

-- Here's what the strength of a Prof-monad on Hask looks like based on my
-- understanding of the paper http://www.cse.chalmers.se/~rjmh/Papers/arrows.pdf
data I0 t p a b c = forall x y. I0 (c -> t x y) (p x a) (y -> b)
data O0 t p a b c = forall x  . O0 (p c x) (x -> t a b)

type Strength0 t p = I0 t p ~~~> O0 t p

-- I want to prove that these two are isomorphic
type Proof = forall t p.
  ( Bifunctor t
  , Profunctor p
  ) =>
  Iso (Strength0 t p) (Strength t p)

-- Step 1: Apply co-Yoneda lemma to domain of function
data I1 t p a b c = forall x. I1 (c -> t x b) (p x a)

type Strength1 t p = I1 t p ~~~> O0 t p

coyoInput :: Bifunctor t => Iso (I0 t p a b c) (I1 t p a b c)
coyoInput = Iso
  (\(I0 f g h) -> I1 (bimap id h . f) g)
  (\(I1 f g) -> I0 f g id)

s0s1 :: Bifunctor t => Strength0 t p -> Strength1 t p
s0s1 = (. bwd coyoInput)

s1s0 :: Bifunctor t => Strength1 t p -> Strength0 t p
s1s0 = (. fwd coyoInput)

step1 :: Bifunctor t => Iso (Strength0 t p) (Strength1 t p)
step1 = _
-- step1 = lmapIso coyoInput
-- step1 = Iso s0s1 s1s0

-- Step 2: Apply co-Yoneda lemma on codomain of function
type O1 t p a b c = p c (t a b)

type Strength2 t p = I1 t p ~~~> O1 t p

coyoOutput :: Profunctor p => Iso (O0 t p a b c) (O1 t p a b c)
coyoOutput = Iso (\(O0 f g) -> rmap g f) (\p -> O0 p id)

s1s2 :: Profunctor p => Strength1 t p -> Strength2 t p
s1s2 = (fwd coyoOutput .)

s2s1 :: Profunctor p => Strength2 t p -> Strength1 t p
s2s1 = (bwd coyoOutput .)

step2 :: Profunctor p => Iso (Strength1 t p) (Strength2 t p)
step2 = _
-- step2 = rmapIso coyoOutput
-- step2 = Iso s1s2 s2s1

-- Step 3: Pull existential out of domain
type Strength3 t p = forall a b c x. (c -> t x b) -> p x a -> p c (t a b)

s2s3 :: Strength2 t p -> Strength3 t p
s2s3 f d1 d2 = f (I1 d1 d2)

s3s2 :: Strength3 t p -> Strength2 t p
s3s2 f (I1 d1 d2) = f d1 d2

step3 :: Iso (Strength2 t p) (Strength3 t p)
step3 = _
-- step3 = Iso s2s3 s3s2

-- Step 4: Apply Yoneda lemma
type Strength4 t p = forall a b x. p x a -> p (t x b) (t a b)

s3s4 :: Strength3 t p -> Strength4 t p
s3s4 f a = f id a

s4s3 :: Profunctor p => Strength4 t p -> Strength3 t p
s4s3 f a b = lmap a $ f b

step4 :: Iso (Strength3 t p) (Strength4 t p)
step4 = _
-- step4 = Iso s3s4 s4s3

-- All together now:
s0s4 :: (Bifunctor t, Profunctor p) => Strength0 t p -> Strength4 t p
s0s4 f = s3s4 $ s2s3 $ s1s2 $ s0s1 $ f
-- s0s4 = s0s1 >>> s1s2 >>> s2s3 >>> s3s4

s4s0 :: (Bifunctor t, Profunctor p) => Strength4 t p -> Strength0 t p
s4s0 f = s1s0 $ s2s1 $ s3s2 $ s4s3 $ f
-- s4s0 = s1s0 <<< s2s1 <<< s3s2 <<< s4s3

proof :: Proof
proof = step1 >>> step2 >>> step3 >>> step4
-- proof = Iso s0s4 s4s0

main :: IO ()
main = putStrLn "Hello, Haskell!"
