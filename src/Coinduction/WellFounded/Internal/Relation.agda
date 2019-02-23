module Coinduction.WellFounded.Internal.Relation where

open import Relation.Binary.Indexed.Heterogeneous public


on-setoid : ∀ {a b l i} {I : Set i} {A : I → Set a} (S : IndexedSetoid I b l)
  → (∀ {i} → A i → IndexedSetoid.Carrier S i)
  → IndexedSetoid I a l
on-setoid {I = I} {A} S f = record
    { Carrier = A
    ; _≈_ = λ x y → f x S.≈ f y
    ; isEquivalence = record
        { refl = S.refl
        ; sym = S.sym
        ; trans = S.trans
        }
    }
  where
    module S = IndexedSetoid S
