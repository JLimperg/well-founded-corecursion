module Coinduction.WellFounded.Internal where

open import Data.Container using (Container ; _▷_ ; ⟦_⟧)
open import Data.Unit
open import Induction.WellFounded using (Well-founded)
open import Level using (Level) renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.Indexed using (_at_)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Relation.Binary.HeterogeneousEquality as Het using
  (_≅_ ; ≅-to-≡ ; ≡-ext-to-≅-ext ; ≡-to-≅)
open import Size using (Size ; Size<_ ; ∞)

open import Coinduction.WellFounded.Indexed as Ix public
  using (inf ; M-Extensionality)
-- TODO While defining the following notions via their generalisations in
-- Ix is elegant, it also litters goals with garbage if Agda gets
-- simplification wrong. Thus, we should probably reimplement everything
-- independent of Ix, then provide conversion lemmas if necessary.


container⇒indexedContainer : ∀ {l} → Container l → Ix.Container ⊤ ⊤ _ _
container⇒indexedContainer (Shape ▷ Position)
    = (λ _ → Shape) Ix.◃ (λ {_} → Position) / (λ _ _ → tt)


M : ∀ {l} → Container l → Size → Set _
M C s = Ix.M (container⇒indexedContainer C) s tt


-- TODO We should probably switch to the ≡ setoid rather than using the
-- ≅ setoid (which does nothing for us). Part of the 'reimplement everything'
-- plan.
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


M-Extensionality-from-Ix : ∀ {l s} {t : Size< s}
  → Ix.M-Extensionality lzero l l s
  → {C : Container l} {x y : M C s}
  → inf x ≡ inf y
  → x ≡ y
M-Extensionality-from-Ix M-ext eq = ≅-to-≡ (M-ext (≡-to-≅ eq))


≅M⇒≡ : ∀ {l} {C : Container l} {s} {t : Size< s} {x y : M C s}
  → M-Extensionality lzero l l s
  → Extensionality l (lsuc l)
  → x ≅M y
  → x ≡ y
≅M⇒≡ M-ext ≡-ext eq = M-Extensionality-from-Ix M-ext (≅F⇒≡ ≡-ext eq)


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

  cofixWf : In → M C ∞
  cofixWf = Ix.cofixWf <-wf F


  cofixWf-unfold
    : (∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≅F g' y y<x)
        → F x f g ≅F F x f' g')
    → ∀ x
    → inf (cofixWf x) ≅F F x cofixWf (λ y _ → inf (cofixWf y))
  cofixWf-unfold = Ix.cofixWf-unfold <-wf F


  cofixWf-unfold′
    : (∀ {a b} → Extensionality a b)
    → ∀ x
    → inf (cofixWf x) ≡ F x cofixWf (λ y _ → inf (cofixWf y))
  cofixWf-unfold′ ≡-ext = Ix.cofixWf-unfold′ <-wf F (≡-ext-to-≅-ext ≡-ext)