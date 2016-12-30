module Filter.Direct where


open import Data.Bool
open import Data.Product
open import Function
open import Size

open import Stream.Direct

open Stream.Direct.Stream


sfilter : ∀ {A} {P : A -> Bool} {s : Stream A ∞} -> InfinitelyOften (isTrue ∘ P) ∞ ∞ s -> Stream (Σ A (isTrue ∘ P)) ∞
force (sfilter p) j with InfinitelyOften-step p
... | (x , (xs , pxs)) = x :: sfilter pxs
