module Data.List.Extra where


open import Data.List
open import Data.List.Any
open import Relation.Binary.PropositionalEquality


open Membership-≡


∷-⊆ : ∀ {a} {A : Set a} {xs ys} {x : A} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)
∷-⊆ _ (Any.here px) = Any.here px
∷-⊆ xs⊆ys (there In) = there (xs⊆ys In)


⊆-duplicate : ∀ {a} {A : Set a} {x : A} {xs} -> x ∷ x ∷ xs ⊆ x ∷ xs
⊆-duplicate (Any.here px) rewrite px = Any.here refl
⊆-duplicate (there In) = In


⊆-swap : ∀ {a} {A : Set a} {x y : A} {xs} -> x ∷ y ∷ xs ⊆ y ∷ x ∷ xs
⊆-swap (Any.here px) rewrite px = there (Any.here refl)
⊆-swap (there (Any.here px)) rewrite px = Any.here refl
⊆-swap (there (there In)) = there (there In)
