module Graph.Special where


open import Induction.WellFounded
open import Relation.Binary
open import Size


data Graph : Size → Set
record Graph∞ (s : Size) : Set


data Graph where
  tip : ∀ {s} → Graph s
  branch : ∀ {s} → Graph∞ s → Graph∞ s → Graph s


record Graph∞ (s : Size) where
  coinductive
  field
    force : ∀ {t : Size< s} → Graph t

open Graph∞


module _
  {lin l<} {In : Set lin} {_<_ : Rel In l<}
  (<-wf : Well-founded _<_)
  (F : ∀ {t}
    → (x : In)
    → (In → Graph∞ t)
    → ((y : In) → y < x → Graph t)
    → Graph t)
  where


  fixGraph' : ∀ {s} → (x : In) → Acc _<_ x → Graph∞ s
  fixGraph' x (acc rs) .force
      = F x
          (λ y → fixGraph' y (<-wf y))
          (λ y y<x → force (fixGraph' y (rs y y<x)))


  fixGraph : ∀ {s} → In → Graph∞ s
  fixGraph x = fixGraph' x (<-wf x)
