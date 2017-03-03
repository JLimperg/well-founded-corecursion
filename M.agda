module M where


open import Data.Unit
open import Induction.WellFounded using (Well-founded)
open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.Indexed using (_at_)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Size using (Size ; Size<_ ; ∞)


open import Data.Container public using (Container ; _▷_ ; ⟦_⟧)

open import M.Indexed as Ix public using (funext⇒F-ext ; inf)
-- TODO While defining the following notions via their generalisations in
-- M.Indexed is elegant, it also litters goals with garbage if Agda gets
-- simplification wrong. Thus, we should probably reimplement everything
-- independent of M.Indexed, then provide conversion lemmas if necessary.


container⇒indexedContainer : ∀ {l} → Container l → Ix.Container ⊤ ⊤ _ _
container⇒indexedContainer (Shape ▷ Position)
    = (λ _ → Shape) Ix.◃ (λ {_} → Position) / (λ _ _ → tt)


M : ∀ {l} → Container l → Size → Set _
M C s = Ix.M (container⇒indexedContainer C) s tt


≅F-setoid : ∀ {l} (C : Container l) (s : Size) → Setoid _ _
≅F-setoid C s = (Ix.≅F-setoid (container⇒indexedContainer C) s) at tt


_≅F_ : ∀ {l} {C : Container l} {s} → Rel (⟦ C ⟧ (M C s)) _
_≅F_ {C = C} {s} = Setoid._≈_ (≅F-setoid C s)


≅M-setoid :  ∀ {l} (C : Container l) (s : Size) {t : Size< s} → Setoid _ _
≅M-setoid C s = (Ix.≅M-setoid (container⇒indexedContainer C) s) at tt


_≅M_ : ∀ {l} {C : Container l} {s} {t : Size< s} → Rel (M C s) _
_≅M_ {C = C} {s} = Setoid._≈_ (≅M-setoid C s)



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
        → (∀ y y<x → g y y<x ≅F g' y y<x)
        → F x f g ≅F F x f' g')
    → ∀ x
    → inf (fixM x) ≅F F x fixM (λ y _ → inf (fixM y))
  fixM-unfold = Ix.fixM-unfold <-wf F
