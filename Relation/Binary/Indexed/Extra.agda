module Relation.Binary.Indexed.Extra where

open import Relation.Binary.Indexed public


on-setoid : ∀ {a b l i} {I : Set i} {A : I → Set a} (S : Setoid I b l)
  → (∀ {i} → A i → Setoid.Carrier S i)
  → Setoid I a l
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
    module S = Setoid S
