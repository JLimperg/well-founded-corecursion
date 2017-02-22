module M.Indexed where

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

open import Data.Container.Indexed public using
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
    inf : ∀ {t : Size< s} → ⟦ C ⟧ (M C t) o

open M public


module Internal
  {lo lc lr} {O : Set lo} {C : Container O O lc lr}
  {lin l<} {In : Set lin} {o : O}
  {_<_ : Rel In l<} (<-wf : Well-founded _<_)
  (F : ∀ {t}
     → (x : In)
     → (In → M C t o)
     → ((y : In) → y < x → ⟦ C ⟧ (M C t) o)
     → ⟦ C ⟧ (M C t) o)
  where


  fixM' : ∀ {s} → (x : In) → Acc _<_ x → M C s o
  fixM' x (acc rs) .inf
      = F x (λ y → fixM' y (<-wf y)) (λ y y<x → inf (fixM' y (rs y y<x)))


  fixM : In → M C ∞ o
  fixM x = fixM' x (<-wf x)


  module _
    (F-ext : ∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≡ g' y y<x)
        → F x f g ≡ F x f' g')
    where

    fixM'-Acc-irrelevant : ∀ {x} (acc acc' : Acc _<_ x)
      → inf (fixM' x acc) ≡ inf (fixM' x acc')
    fixM'-Acc-irrelevant (acc rs) (acc rs') = F-ext _ (λ _ → refl) lem
      where
        lem : ∀ y y<x
          → inf (fixM' y (rs y y<x)) ≡ inf (fixM' y (rs' y y<x))
        lem y y<x rewrite fixM'-Acc-irrelevant (rs y y<x) (rs' y y<x) = refl


    fixM-unfold : ∀ x → inf (fixM x) ≡ F x fixM (λ y _ → inf (fixM y))
    fixM-unfold x with (<-wf x)
    ... | (acc rs)
        = F-ext _
            (λ _ → refl)
            (λ y y<x → fixM'-Acc-irrelevant (rs y y<x) (<-wf y))


open Internal public using (fixM ; fixM-unfold)


funext⇒F-ext
  : (∀ {a b} → Extensionality a b)
  → ∀ {a b c d e g h} {A : Set a} {B : A → Set b} {C : ∀ a → B a → Set c}
      {D : A → Set d} {E : ∀ a → D a → Set e}
      {G : ∀ a (d : D a) → E a d → Set g} {H : Set h}
      (F : ∀ a
         → ((b : B a) → C a b)
         → ((d : D a) → (e : E a d) → G a d e)
         → H)
      x {f f' g g'}
  → (∀ y → f y ≡ f' y)
  → (∀ y z → g y z ≡ g' y z)
  → F x f g ≡ F x f' g'
funext⇒F-ext funext F x {f} {f'} {g} {g'} eq-f eq-g = lem
  where
    f≡f' : f ≡ f'
    f≡f' = funext eq-f

    g≡g' : g ≡ g'
    g≡g' = funext (λ y → funext (eq-g y))

    lem : F x f g ≡ F x f' g'
    lem rewrite f≡f' | g≡g' = refl
