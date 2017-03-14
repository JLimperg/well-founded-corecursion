module Filter.M where

open import Data.Bool
open import Data.Empty
open import Data.Nat using (_<′_)
open import Data.Product
open import Function
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Well-founded ; module Inverse-image)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; inspect ; [_] ; Extensionality)
open import Relation.Binary.HeterogeneousEquality using
  (_≅_ ; refl ; ≡-to-≅)
open import Size using (∞)

open import Filter.Base
open import M


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


    filter-body : Stream A ∞ → Stream A ∞
    filter-body xs
        = if p (head xs)
            then cons (head xs) (filter (tail xs))
            else filter (tail xs)


    module Internal where

      filterF-ext : ∀ x {f f' g g'}
        → (∀ y → f y ≡ f' y)
        → (∀ y y<x → g y y<x ≅F g' y y<x)
        → filterF x f g ≅F filterF x f' g'
      filterF-ext x f-eq g-eq with p (head x) | inspect p (head x)
      ... | true  | _ = refl , refl , (λ _ _ _ → ≡-to-≅ (f-eq _))
      ... | false | _
          = refl , proj₁ (proj₂ (g-eq _ _)) , proj₂ (proj₂ (g-eq _ _))


      filter-unfold′ : ∀ xs
        → inf (filter xs) ≅F filterF xs filter (λ x _ → inf (filter x))
      filter-unfold′ = fixM-unfold <[p]-wf filterF filterF-ext

      filter-unfold″ : ∀ xs
        → filterF xs filter (λ x _ → inf (filter x)) ≡ inf (filter-body xs)
      filter-unfold″ xs with p (head xs) | inspect p (head xs)
      ... | true  | _ = refl
      ... | false | _ = refl


    filter-unfold : ∀ xs → filter xs ≅M filter-body xs
    filter-unfold xs
        = S.trans (Internal.filter-unfold′ xs)
            (S.reflexive (Internal.filter-unfold″ xs))
      where
        module S = Setoid (≅F-setoid (StreamC A) ∞)
