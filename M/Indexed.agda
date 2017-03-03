module M.Indexed where

open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Well-founded ; Acc ; acc)
open import Level using (_⊔_)
open import Relation.Binary.Indexed.Extra using (Rel ; Setoid ; on-setoid)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; Extensionality)
open import Relation.Binary.HeterogeneousEquality as Het using
  (_≅_ ; refl)
open import Size using (Size ; Size<_ ; ∞)

open import Data.Container.Indexed.Extra as Cont public using
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


≅F-setoid : ∀ {lo lc lr} {O : Set lo} (C : Container O O lc lr) (s : Size)
  → Setoid O _ _
≅F-setoid C s = Cont.setoid C (Het.indexedSetoid (M C s))


≅M-setoid : ∀ {lo lc lr} {O : Set lo} (C : Container O O lc lr) (s : Size)
  → {t : Size< s}
  → Setoid O _ _
≅M-setoid C _ {t} = on-setoid (≅F-setoid C t) (λ x → inf x {t})


_≅F_ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s}
  → Rel (⟦ C ⟧ (M C s)) _
_≅F_ {C = C} {s} = Setoid._≈_ (≅F-setoid C s)


_≅M_ : ∀ {lo lc lr} {O : Set lo} {C : Container O O lc lr} {s} {t : Size< s}
  → Rel (M C s) _
_≅M_ {C = C} {s} = Setoid._≈_ (≅M-setoid C s)


module Internal
  {lo lc lr} {O : Set lo} {C : Container O O lc lr}
  {lin l<} {In : Set lin} {o : O}
  {_<_ : In → In → Set l<} (<-wf : Well-founded _<_)
  (F : ∀ {t}
     → (x : In)
     → (In → M C t o)
     → ((y : In) → y < x → ⟦ C ⟧ (M C t) o)
     → ⟦ C ⟧ (M C t) o)
  where
  -- TODO Can we generalise o?


  fixM' : ∀ {s} → (x : In) → Acc _<_ x → M C s o
  fixM' x (acc rs) .inf
      = F x (λ y → fixM' y (<-wf y)) (λ y y<x → inf (fixM' y (rs y y<x)))


  fixM : In → M C ∞ o
  fixM x = fixM' x (<-wf x)


  module _
    (F-ext : ∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≅F g' y y<x)
        → F x f g ≅F F x f' g')
    where

    fixM'-Acc-irrelevant : ∀ {x} (acc acc' : Acc _<_ x)
      → fixM' x acc ≅M fixM' x acc'
    fixM'-Acc-irrelevant (acc rs) (acc rs')
        = F-ext _
            (λ _ → refl)
            (λ y y<x → fixM'-Acc-irrelevant (rs y y<x) (rs' y y<x))


    fixM-unfold : ∀ x → inf (fixM x) ≅F F x fixM (λ y _ → inf (fixM y))
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
