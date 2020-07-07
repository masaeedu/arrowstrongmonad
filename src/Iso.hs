module Iso where

import Prelude hiding (id, (.))
import Control.Category
import Data.Profunctor

data Iso a b = Iso { fwd :: a -> b, bwd :: b -> a }

lmapIso :: Profunctor p => Iso a b -> Iso (p a x) (p b x)
lmapIso (Iso f g) = Iso (lmap g) (lmap f)

rmapIso :: Profunctor p => Iso a b -> Iso (p x a) (p x b)
rmapIso (Iso f g) = Iso (rmap f) (rmap g)

instance Category Iso
  where
  id = Iso id id
  Iso f g . Iso h i = Iso (f . h) (i . g)
