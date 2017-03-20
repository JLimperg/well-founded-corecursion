module M where


open import Data.Unit
open import Induction.WellFounded using (Well-founded)
open import Level using (Level) renaming (suc to lsuc)
open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.Indexed using (_at_)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Relation.Binary.HeterogeneousEquality as Het using
  (_≅_ ; ≅-to-≡ ; ≡-ext-to-≅-ext)
open import Size using (Size ; Size<_ ; ∞)


open import Data.Container public using (Container ; _▷_ ; ⟦_⟧)

open import M.Indexed as Ix public using (inf)
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


≅F⇒≡ : ∀ {l} {C : Container l} {s} {x y : ⟦ C ⟧ (M C s)}
  → Extensionality l (lsuc l)
  → x ≅F y
  → x ≡ y
≅F⇒≡ ≡-ext eq = ≅-to-≡ (Ix.≅F⇒≅ (≡-ext-to-≅-ext ≡-ext) eq)


≅M-setoid :  ∀ {l} (C : Container l) (s : Size) {t : Size< s} → Setoid _ _
≅M-setoid C s = (Ix.≅M-setoid (container⇒indexedContainer C) s) at tt


_≅M_ : ∀ {l} {C : Container l} {s} {t : Size< s} → Rel (M C s) _
_≅M_ {C = C} {s} = Setoid._≈_ (≅M-setoid C s)


M-Extensionality : ∀ l → Set (lsuc l)
M-Extensionality l
    = ∀ {C : Container l} {s} {t : Size< s}
    → {x y : M C s}
    → inf x ≡ inf y
    → x ≡ y


≅M⇒≡ : ∀ {l} {C : Container l} {s} {t : Size< s} {x y : M C s}
  → M-Extensionality l
  → Extensionality l (lsuc l)
  → x ≅M y
  → x ≡ y
≅M⇒≡ M-ext ≡-ext eq = M-ext (≅F⇒≡ ≡-ext eq)


module _
  {l lin} {C : Container l} {In : Set lin}
  (F : ∀ {t}
     → (x : In)
     → (In → M C t)
     → ⟦ C ⟧ (M C t))
  where

  cofix : ∀ {s} → In → M C s
  cofix x .inf = F x cofix


  cofix-unfold : ∀ x
    → inf (cofix x) ≡ F x cofix
  cofix-unfold _ = refl


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
  fixM = Ix.fixM <-wf (λ _ → tt) F


  fixM-unfold
    : (∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≅F g' y y<x)
        → F x f g ≅F F x f' g')
    → ∀ x
    → inf (fixM x) ≅F F x fixM (λ y _ → inf (fixM y))
  fixM-unfold = Ix.fixM-unfold <-wf (λ _ → tt) F


  fixM-unfold′
    : (∀ {a b} → Extensionality a b)
    → ∀ x
    → inf (fixM x) ≡ F x fixM (λ y _ → inf (fixM y))
  fixM-unfold′ ≡-ext = Ix.fixM-unfold′ <-wf (λ _ → tt) F (≡-ext-to-≅-ext ≡-ext)
