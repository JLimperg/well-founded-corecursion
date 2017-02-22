module M where


open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Well-founded ; Acc ; acc)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Size using (Size ; Size<_ ; ∞)


open import Data.Container public using (Container ; _▷_ ; ⟦_⟧)

open import M.Indexed as Ix public using (funext⇒F-ext ; inf)


container⇒indexedContainer : ∀ {l} → Container l → Ix.Container ⊤ ⊤ _ _
container⇒indexedContainer (Shape ▷ Position)
    = (λ _ → Shape) Ix.◃ (λ {_} → Position) / (λ _ _ → tt)


M : ∀ {l} → Container l → Size → Set _
M C s = Ix.M (container⇒indexedContainer C) s tt


module _
  {l lin l<} {C : Container l} {In : Set lin}
  {_<_ : Rel In l<} (<-wf : Well-founded _<_)
  (F : ∀ {t}
      → (x : In)
      → (In → M C t)
      → ((y : In) → y < x → ⟦ C ⟧ (M C t))
      → ⟦ C ⟧ (M C t))
  where

  fixM : In → M C ∞
  fixM = Ix.fixM <-wf F


  fixM-unfold
    : (∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≡ g' y y<x)
        → F x f g ≡ F x f' g')
    → ∀ x
    → inf (fixM x) ≡ F x fixM (λ y _ → inf (fixM y))
  fixM-unfold = Ix.fixM-unfold <-wf F
