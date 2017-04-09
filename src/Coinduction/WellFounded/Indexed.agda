module Coinduction.WellFounded.Indexed where

open import Coinduction.WellFounded.Internal.Relation using
  (Rel ; Setoid ; on-setoid)
open import Data.Product
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Well-founded ; Acc ; acc)
open import Level using (_⊔_ ; Level)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Relation.Binary.HeterogeneousEquality as Het using
  (_≅_ ; refl ; ≅-to-≡ ; ≡-to-≅)
open import Size using (Size ; Size<_ ; ∞)

open import Coinduction.WellFounded.Internal.Container as Cont public using
  (Container ; _◃_/_ ; ⟦_⟧)


record M
  {lo lc lr}
  {O : Set lo}
  (C : Container O O lc lr)
  (s : Size)
  (o : O)
  : Set (lo ⊔ lc ⊔ lr) where
  coinductive
  field
    inf : {t : Size< s} → ⟦ C ⟧ (M C t) o

open M public


-- We could generalise this from (M C s) to an arbitray (A : O → Set la), but
-- for some reason this kills type inference.
-- TODO In the following, we hardcode heterogeneous equality as the underlying
-- equivalence relation. This is sufficient for the purposes of fixM-unfold, but
-- we may need the generalisation to an arbitrary setoid later.
≅F-setoid : ∀ {lo lc lr} {O : Set lo} (C : Container O O lc lr) (s : Size)
  → Setoid O _ _
≅F-setoid C s = Cont.setoid C (Het.indexedSetoid (M C s))


≅M-setoid : ∀ {lo lc lr} {O : Set lo} (C : Container O O lc lr) s {t : Size< s}
  → Setoid O _ _
≅M-setoid C _ {t} = on-setoid (≅F-setoid C t) (λ x → inf x {t})


-- We could make s an index of this relation (and _≅M_ below) to allow equality
-- between objects of different sizes. I haven't needed this yet and it would
-- complicate matters somewhat, so I'm leaving the definition as is for now.
_≅F_ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s}
  → Rel (⟦ C ⟧ (M C s)) _
_≅F_ {C = C} {s} = Setoid._≈_ (≅F-setoid C s)


module Internal₁ where

  -- Copied the following from Data.Container.Indexed, where it is sadly
  -- private.
  Eq⇒≅ : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
    → {C : Container I O c r} {X : I → Set ℓ} {o₁ o₂ : O}
    → {xs : ⟦ C ⟧ X o₁} {ys : ⟦ C ⟧ X o₂}
    → Het.Extensionality r ℓ
    → Cont.Eq C X X (λ x₁ x₂ → x₁ ≅ x₂) xs ys
    → xs ≅ ys
  Eq⇒≅ {xs = c , k} {.c , k′} ext (refl , refl , k≈k′) =
    Het.cong (_,_ c) (ext (λ _ → refl) (λ r → k≈k′ r r refl))


≅F⇒≅ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s} {o₁ o₂}
  → {x : ⟦ C ⟧ (M C s) o₁} {y : ⟦ C ⟧ (M C s) o₂}
  → Het.Extensionality lr (lo ⊔ lc ⊔ lr)
  → x ≅F y
  → x ≅ y
≅F⇒≅ {C = C} {s} = Internal₁.Eq⇒≅ {X = M C s}


_≅M_ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s} {t : Size< s}
  → Rel (M C s) _
_≅M_ {C = C} {s} = Setoid._≈_ (≅M-setoid C s)


-- s and t are arguments of this definition rather than appearing on the
-- right-hand side because otherwise using a (p : M-Extensionality lo lc lr)
-- in ≅M⇒≅ below fails due to the type (Size< s) potentially being empty. I'm
-- not entirely sure why that is.
-- Maybe we don't actually care about sizes other than ∞, but since I'm not
-- certain, I prefer the more general version for now.
M-Extensionality : (lo lc lr : Level) (s : Size) {t : Size< s} → Set _
M-Extensionality lo lc lr s
    = ∀ {O : Set lo} {C : Container O O lc lr} {o₁ o₂}
    → {x : M C s o₁} {y : M C s o₂}
    → inf x ≅ inf y
    → x ≅ y


≅M⇒≅ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s} {t : Size< s}
  → ∀ {o₁ o₂} {x : M C s o₁} {y : M C s o₂}
  → M-Extensionality lo lc lr s
  → Het.Extensionality lr (lo ⊔ lc ⊔ lr)
  → x ≅M y
  → x ≅ y
≅M⇒≅ M-ext ≅-ext eq = M-ext (≅F⇒≅ ≅-ext eq)


module _
  {lo lc lr} {O : Set lo} {C : Container O O lc lr}
  {lin} {In : Set lin}
  (P : In → O)
  (F : ∀ {t}
     → (x : In)
     → ((y : In) → M C t (P y))
     → ⟦ C ⟧ (M C t) (P x))
  where

  cofix : ∀ {s} → (x : In) → M C s (P x)
  cofix x .inf = F x cofix


  cofix-unfold : ∀ x
    → inf (cofix x) ≡ F x cofix
  cofix-unfold _ = refl


module Internal₂
  {lo lc lr} {O : Set lo} {C : Container O O lc lr}
  {lin l<} {In : Set lin}
  {_<_ : In → In → Set l<} (<-wf : Well-founded _<_)
  (P : In → O)
  (F : ∀ {t}
     → (x : In)
     → ((y : In) → M C t (P y))
     → ((y : In) → y < x → ⟦ C ⟧ (M C t) (P y))
     → ⟦ C ⟧ (M C t) (P x))
  where


  fixM' : ∀ {s} → (x : In) → Acc _<_ x → M C s (P x)
  fixM' x (acc rs) .inf
      = F x (λ y → fixM' y (<-wf y)) (λ y y<x → inf (fixM' y (rs y y<x)))


  fixM : (x : In) → M C ∞ (P x)
  fixM x = fixM' x (<-wf x)


  module _
    (F-ext : ∀ x {f f' g g'}
       → (∀ y → f y ≡ f' y)
       → (∀ y y<x → g y y<x ≅F g' y y<x)
       →  F x f g ≅F F x f' g')
    where

    fixM'-Acc-irrelevant : ∀ {x} (acc acc' : Acc _<_ x)
      → fixM' x acc ≅M fixM' x acc'
    fixM'-Acc-irrelevant (acc rs) (acc rs')
        = F-ext _
            (λ _ → refl)
            (λ y y<x → fixM'-Acc-irrelevant (rs y y<x) (rs' y y<x))


    fixM-unfold : ∀ x
      → inf (fixM x) ≅F F x fixM (λ y _ → inf (fixM y))
    fixM-unfold x with (<-wf x)
    ... | (acc rs)
        = F-ext _
            (λ _ → refl)
            (λ y y<x → fixM'-Acc-irrelevant (rs y y<x) (<-wf y))


  ≅-ext-to-≡-ext : ∀ {a b} → Het.Extensionality a b → Extensionality a b
  ≅-ext-to-≡-ext ≅-ext f-eq
      = ≅-to-≡ (≅-ext (λ _ → refl) (λ x → ≡-to-≅ (f-eq x)))


  -- We could change F-ext to require extensionality only at specific levels
  -- (namely some upper bound of lo, lc, lr, lin, and l<). However, this
  -- complicates the implementation considerably, and I don't see a reason for
  -- users to postulate extensionality only at specific levels.
  F-ext
    : (∀ {a b} → Het.Extensionality a b)
    → ∀ x {f f' g g'}
    → (∀ y → f y ≡ f' y)
    → (∀ y y<x → g y y<x ≅F g' y y<x)
    → F x f g ≅F F x f' g'
  F-ext ≅-ext x {f} {f'} {g} {g'} eq-f eq-g = go
    where
      module S = Setoid (≅F-setoid C ∞)

      ≡-ext : ∀ {a b} → Extensionality a b
      ≡-ext = ≅-ext-to-≡-ext ≅-ext

      f≡f' : f ≡ f'
      f≡f' = ≡-ext eq-f

      g≡g' : g ≡ g'
      g≡g' = ≡-ext (λ y → ≡-ext (λ y<x → ≅-to-≡ (≅F⇒≅ ≅-ext (eq-g y y<x))))

      go : F x f g ≅F F x f' g'
      go rewrite f≡f' | g≡g' = S.refl


  fixM-unfold′
    : (∀ {a b} → Het.Extensionality a b)
    → ∀ x
    → inf (fixM x) ≡ F x fixM (λ y _ → inf (fixM y))
  fixM-unfold′ ≅-ext x = ≅-to-≡ (≅F⇒≅ ≅-ext (fixM-unfold (F-ext ≅-ext) x))


open Internal₂ public using (fixM ; fixM-unfold ; fixM-unfold′)
