module Coinduction.WellFounded.Indexed.Internal where

open import Coinduction.WellFounded.Internal.Relation using
  (IRel ; IndexedSetoid ; on-setoid)
open import Data.Container.Indexed as Cont using
  (Container ; _◃_/_ ; ⟦_⟧)
open import Data.Product
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (WellFounded ; Acc ; acc)
open import Level using (_⊔_ ; Level)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Relation.Binary.HeterogeneousEquality as Het using
  (_≅_ ; refl ; ≅-to-≡ ; ≡-to-≅)
open import Size using (Size ; Size<_ ; ∞)



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
-- We hardcode heterogeneous equality as the underlying equivalence relation.
-- This is sufficient for the purposes of fixM-unfold, but we may need the
-- generalisation to an arbitrary setoid later.
≅F-setoid : ∀ {lo lc lr} {O : Set lo} (C : Container O O lc lr) (s : Size)
  → IndexedSetoid O _ _
≅F-setoid C s = Cont.setoid C (Het.indexedSetoid (M C s))


≅M-setoid : ∀ {lo lc lr} {O : Set lo} (C : Container O O lc lr) s {t : Size< s}
  → IndexedSetoid O _ _
≅M-setoid C _ {t} = on-setoid (≅F-setoid C t) (λ x → inf x {t})


-- We could make s an index of this relation (and _≅M_ below) to allow equality
-- between objects of different sizes. I haven't needed this yet and it would
-- complicate matters somewhat, so I'm leaving the definition as is for now.
_≅F_ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s}
  → IRel (⟦ C ⟧ (M C s)) _
_≅F_ {C = C} {s} = IndexedSetoid._≈_ (≅F-setoid C s)


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
≅F⇒≅ {C = C} {s} = Eq⇒≅ {X = M C s}


_≅M_ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s} {t : Size< s}
  → IRel (M C s) _
_≅M_ {C = C} {s} = IndexedSetoid._≈_ (≅M-setoid C s)


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


≅-ext-to-≡-ext : ∀ {a b} → Het.Extensionality a b → Extensionality a b
≅-ext-to-≡-ext ≅-ext f-eq
    = ≅-to-≡ (≅-ext (λ _ → refl) (λ x → ≡-to-≅ (f-eq x)))


module _
  {lo lc lr} {O : Set lo} {C : Container O O lc lr}
  {lin} {In : Set lin}
  {P : In → O}
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


module _
  {lo lc lr} {O : Set lo} {C : Container O O lc lr}
  {lin l<} {In : Set lin}
  {_<_ : In → In → Set l<} (<-wf : WellFounded _<_)
  {P : In → O}
  (F : ∀ {t}
     → (x : In)
     → ((y : In) → M C t (P y))
     → ((y : In) → y < x → ⟦ C ⟧ (M C t) (P y))
     → ⟦ C ⟧ (M C t) (P x))
  where


  cofixWf′ : ∀ {s} → (x : In) → Acc _<_ x → M C s (P x)
  cofixWf′ x (acc rs) .inf
      = F x (λ y → cofixWf′ y (<-wf y)) (λ y y<x → inf (cofixWf′ y (rs y y<x)))


  cofixWf : (x : In) → M C ∞ (P x)
  cofixWf x = cofixWf′ x (<-wf x)


  module _
    (F-ext : ∀ x {f f' g g'}
       → (∀ y → f y ≡ f' y)
       → (∀ y y<x → g y y<x ≅F g' y y<x)
       →  F x f g ≅F F x f' g')
    where

    cofixWf′-Acc-irrelevant : ∀ {x} (acc acc' : Acc _<_ x)
      → cofixWf′ x acc ≅M cofixWf′ x acc'
    cofixWf′-Acc-irrelevant (acc rs) (acc rs')
        = F-ext _
            (λ _ → refl)
            (λ y y<x → cofixWf′-Acc-irrelevant (rs y y<x) (rs' y y<x))


    cofixWf-unfold : ∀ x
      → inf (cofixWf x) ≅F F x cofixWf (λ y _ → inf (cofixWf y))
    cofixWf-unfold x with (<-wf x)
    ... | (acc rs)
        = F-ext _
            (λ _ → refl)
            (λ y y<x → cofixWf′-Acc-irrelevant (rs y y<x) (<-wf y))


  -- We could change cofixWf-unfold′ to require extensionality only at specific
  -- levels (namely some upper bound of lo, lc, lr, lin, and l<). However, this
  -- complicates the implementation considerably, and I don't see a reason for
  -- users to postulate extensionality only at specific levels.
  cofixWf-unfold′
    : (∀ {a b} → Het.Extensionality a b)
    → ∀ x
    → inf (cofixWf x) ≡ F x cofixWf (λ y _ → inf (cofixWf y))
  cofixWf-unfold′ ≅-ext x = ≅-to-≡ (≅F⇒≅ ≅-ext (cofixWf-unfold F-ext x))
    where
      F-ext
        : ∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≅F g' y y<x)
        → F x f g ≅F F x f' g'
      F-ext x {f} {f'} {g} {g'} eq-f eq-g = go
        where
          module S = IndexedSetoid (≅F-setoid C ∞)

          ≡-ext : ∀ {a b} → Extensionality a b
          ≡-ext = ≅-ext-to-≡-ext ≅-ext

          f≡f' : f ≡ f'
          f≡f' = ≡-ext eq-f

          g≡g' : g ≡ g'
          g≡g' = ≡-ext (λ y → ≡-ext (λ y<x → ≅-to-≡ (≅F⇒≅ ≅-ext (eq-g y y<x))))

          go : F x f g ≅F F x f' g'
          go rewrite f≡f' | g≡g' = S.refl
