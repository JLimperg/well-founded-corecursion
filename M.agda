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


module NonIndexed where

  open NI public using
    (Container ; _▷_ ; Shape ; Position ; ⟦_⟧)

  open Indexed.M public


  container⇒indexedContainer : ∀ {l} -> Container l -> I.Container ⊤ ⊤ _ _
  container⇒indexedContainer (Shape ▷ Position) = (λ _ -> Shape) I.◃ (λ {_} -> Position) / (λ _ _ -> tt)


  M : ∀ {l} -> Container l -> Size -> Set _
  M C s = Indexed.M (container⇒indexedContainer C) s tt


  fixM : ∀ {l lin l<} {C : Container l} {In : Set lin} {_<_ : Rel In l<} (<-wf : Well-founded _<_)
    -> (∀ {t}
        -> (x : In)
        -> (In -> M C t)
        -> ((y : In) -> y < x -> ⟦ C ⟧ (M C t))
        -> ⟦ C ⟧ (M C t))
    -> In
    -> M C ∞
  fixM <-wf F x = Indexed.fixM <-wf F x


open Indexed public
