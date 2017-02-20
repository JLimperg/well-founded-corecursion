module M where


import Data.Container as NI
import Data.Container.Indexed as I
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Size

module Indexed where

  open I public using
    (Container ; _◃_/_ ; Command ; Response ; next ; ⟦_⟧)


  record M
    {lo lc lr}
    {O : Set lo}
    (C : Container O O lc lr)
    (s : Size)
    (o : O)
    : Set (lo ⊔ lc ⊔ lr) where
    coinductive
    field
      inf : ∀ {t : Size< s} -> ⟦ C ⟧ (M C t) o

  open M public


  module _ {lo lc lr} {O : Set lo} {C : Container O O lc lr} where

    head : ∀ {s} {t : Size< s} {o} -> M C s o -> Command C o
    head x = proj₁ (inf x)


    tail : ∀ {s} {t : Size< s} {o}
      -> (m : M C s o)
      -> (r : Response C (head m))
      -> M C t (next C (head m) r)
    tail x = proj₂ (inf x)


    module _
      {lin l<} {In : Set lin} {o : O} {_<_ : Rel In l<} (<-wf : Well-founded _<_)
      (F : ∀ {t}
        -> (x : In)
        -> (In -> M C t o)
        -> ((y : In) -> y < x -> ⟦ C ⟧ (M C t) o)
        -> ⟦ C ⟧ (M C t) o)
      where

      fixM' : ∀ {s} -> (x : In) -> Acc _<_ x -> M C s o
      fixM' x (acc rs) .inf = F x (λ y -> fixM' y (<-wf y)) (λ y y<x -> inf (fixM' y (rs y y<x)))


      fixM : In -> M C ∞ o
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
            lem y y<x rewrite fixM'-Acc-irrelevant (rs y y<x) (rs' y y<x)
                = refl


        fixM-unfold : ∀ x → inf (fixM x) ≡ F x fixM (λ y _ → inf (fixM y))
        fixM-unfold x with (<-wf x)
        ... | (acc rs)
            = F-ext _
                (λ _ → refl)
                (λ y y<x → fixM'-Acc-irrelevant (rs y y<x) (<-wf y))


      funext-to-F-ext
        : (∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
           → (∀ x → f x ≡ g x)
           → f ≡ g)
        → (∀ x {f f' g g'}
           → (∀ y → f y ≡ f' y)
           → (∀ y y<x → g y y<x ≡ g' y y<x)
           → F x f g ≡ F x f' g')
      funext-to-F-ext funext x {f} {f'} {g} {g'} eq-f eq-g = lem
        where
          f≡f' : f ≡ f'
          f≡f' = funext eq-f

          g≡g' : g ≡ g'
          g≡g' = funext (λ y → funext (eq-g y))

          lem : F x f g ≡ F x f' g'
          lem rewrite f≡f' | g≡g' = refl


module NonIndexed where

  open NI public using
    (Container ; _▷_ ; Shape ; Position ; ⟦_⟧)

  open Indexed.M public
  open Indexed public using (funext-to-F-ext)


  container⇒indexedContainer : ∀ {l} -> Container l -> I.Container ⊤ ⊤ _ _
  container⇒indexedContainer (Shape ▷ Position) = (λ _ -> Shape) I.◃ (λ {_} -> Position) / (λ _ _ -> tt)


  M : ∀ {l} -> Container l -> Size -> Set _
  M C s = Indexed.M (container⇒indexedContainer C) s tt


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
    fixM = Indexed.fixM <-wf F


    fixM-unfold
      : (F-ext : ∀ x {f f' g g'}
            → (∀ y → f y ≡ f' y)
            → (∀ y y<x → g y y<x ≡ g' y y<x)
            → F x f g ≡ F x f' g')
      → ∀ x
      → inf (fixM x) ≡ F x fixM (λ y _ → inf (fixM y))
    fixM-unfold = Indexed.fixM-unfold <-wf F


open Indexed public
