module Filter.M where

open import Data.Bool
open import Data.Empty
open import Data.Nat using (_<′_)
open import Data.Product
open import Function
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Well-founded ; module Inverse-image)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; inspect ; [_] ; Extensionality)
open import Size using (∞)

open import Filter.Base

import M

open M.NonIndexed


module _ {a} {A : Set a} where

  _<[_]_ : Stream A ∞ → (A → Set) → Stream A ∞ → Set
  xs <[ p ] ys = dist p xs <′ dist p ys


  <[p]-wf : ∀ {p} → Well-founded _<[ p ]_
  <[p]-wf {p} = Inverse-image.well-founded (dist p) <-well-founded


  module _ (p : A → Bool) where

    tail-< : ∀ {xs} → p (head xs) ≡ false → tail xs <[ T ∘ p ] xs
    tail-< {xs} eq-p-head = dist-monotone (¬p-head ∘ dist-0)
      where
        ¬p-head : T (p (head xs)) → ⊥
        ¬p-head c rewrite eq-p-head = c


    filterF : ∀ {t}
      → (xs : Stream A ∞)
      → (Stream A ∞ → Stream A t)
      → (∀ ys → ys <[ T ∘ p ] xs → ⟦ StreamC A ⟧ (Stream A t))
      → ⟦ StreamC A ⟧ (Stream A t)
    filterF xs corec wfrec
      with p (head xs) | inspect p (head xs)
    ...  | true        | _                   = head xs , λ _ → corec (tail xs)
    ...  | false       | [ p≡false ]         = wfrec (tail xs) (tail-< p≡false)


    filter : Stream A ∞ → Stream A ∞
    filter = fixM <[p]-wf filterF


    postulate
      funext : ∀ {a b} → Extensionality a b


    filter-unfold : ∀ xs
      → inf (filter xs)
      ≡ inf (if p (head xs)
               then cons (head xs) (filter (tail xs))
               else filter (tail xs))
    filter-unfold xs
      rewrite fixM-unfold <[p]-wf filterF (funext⇒F-ext funext filterF) xs
      with p (head xs) | inspect p (head xs)
    ...  | true        | _                   = refl
    ...  | false       | _                   = refl
