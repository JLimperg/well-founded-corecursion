module Graph.List where


open import Data.List public
open import Data.List.Any public using (module Membership-≡ ; here ; there)
open import Relation.Binary.PropositionalEquality using (refl)

open Membership-≡ public


∷-⊆ : ∀ {a} {A : Set a} {xs ys} {x : A} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
∷-⊆ _ (here px) = here px
∷-⊆ xs⊆ys (there In) = there (xs⊆ys In)


⊆-duplicate : ∀ {a} {A : Set a} {x : A} {xs} → x ∷ x ∷ xs ⊆ x ∷ xs
⊆-duplicate (here px) rewrite px = here refl
⊆-duplicate (there In) = In


⊆-swap : ∀ {a} {A : Set a} {x y : A} {xs} → x ∷ y ∷ xs ⊆ y ∷ x ∷ xs
⊆-swap (here px) rewrite px = there (here refl)
⊆-swap (there (here px)) rewrite px = here refl
⊆-swap (there (there In)) = there (there In)
