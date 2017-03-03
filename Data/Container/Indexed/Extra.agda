module Data.Container.Indexed.Extra where

open import Data.Product
open import Relation.Binary.Indexed
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Binary.HeterogeneousEquality using (refl)
open import Level using (_⊔_)

open import Data.Container.Indexed public hiding (setoid)


-- This is a generalisation of Data.Container.Indexed.setoid: The setoid
-- argument is at an arbitrary level `l` rather than `r ⊔ c`. The code
-- remains unchanged.
setoid : ∀ {i o c r l} {I : Set i} {O : Set o}
  → Container I O c r
  → Setoid I l l
  → Setoid O (l ⊔ r ⊔ c) (l ⊔ r ⊔ c ⊔ o)
setoid C X = record
    { Carrier       = ⟦ C ⟧ X.Carrier
    ; _≈_           = _≈_
    ; isEquivalence = record
        { refl  = refl , refl , λ { r .r refl → X.refl }
        ; sym   = sym
        ; trans = λ { {_} {i = xs} {ys} {zs} → trans {_} {i = xs} {ys} {zs}  }
        }
    }
  where
    module X = Setoid X

    _≈_ : Rel (⟦ C ⟧ X.Carrier) _
    _≈_ = Eq C X.Carrier X.Carrier X._≈_

    sym : Symmetric (⟦ C ⟧ X.Carrier) _≈_
    sym {_} {._} {_ , _} {._ , _} (refl , refl , k) =
      refl , refl , λ { r .r refl → X.sym (k r r refl) }

    trans : Transitive (⟦ C ⟧ X.Carrier) _≈_
    trans {._} {_} {._} {_ , _} {._ , _} {._ , _}
      (refl , refl , k) (refl , refl , k′) =
      refl , refl , λ { r .r refl → X.trans (k r r refl) (k′ r r refl) }
