module Filter.Properties where


open import Data.Bool
open import Data.Product
open import Data.Unit
open import Size using (Size ; Size<_ ; ∞)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Filter.Base
open import Filter.M
open import M.Indexed


postulate
  Stream-ext : ∀ {a} {A : Set a} {xs ys : Stream A ∞}
    → inf xs ≡ inf ys → xs ≡ ys


module Direct {a} {A : Set a} where

  data SubstreamF (Substream : Rel (Stream A ∞) a) : Rel (Stream A ∞) a where
    take : ∀ {xs ys}
      → head xs ≡ head ys
      → Substream (tail xs) (tail ys)
      → SubstreamF Substream xs ys
    skip : ∀ {xs ys}
      → Substream xs (tail ys)
      → SubstreamF Substream xs ys


  record Substream (s : Size) (xs ys : Stream A ∞) : Set a where
    coinductive
    field
      force : ∀ {t : Size< s} → SubstreamF (Substream t) xs ys

  open Substream


  filter-Substream : ∀ {s} p (xs : Stream A ∞) → Substream s (filter p xs) xs
  filter-Substream p xs .force
    rewrite Stream-ext
      {xs = filter p xs}
      {if p (head xs)
         then (cons (head xs) (filter p (tail xs)))
         else filter p (tail xs)}
      (filter-unfold p xs)
    with p (head xs)
  ...  | true  = take refl (filter-Substream p (tail xs))
  ...  | false = skip (filter-Substream p (tail xs))
  -- Why can't the implicit arguments of Stream-ext be inferred?


module WithM {a} {A : Set a} where

  ⊆-C : (A : Set a)
    → Container (Stream A ∞ × Stream A ∞) (Stream A ∞ × Stream A ∞) _ _
  ⊆-C A = Command ◃ Response / next
    module ⊆-C where
      data Command (xs×ys : Stream A ∞ × Stream A ∞) : Set a where
        take : head (proj₁ xs×ys) ≡ head (proj₂ xs×ys) → Command xs×ys
        skip : Command xs×ys

      Response : ∀ {o} → Command o → Set
      Response (take _) = ⊤
      Response skip = ⊤

      next : ∀ {o} (c : Command o) → Response c → Stream A ∞ × Stream A ∞
      next {xs , ys} (take _) _ = tail xs , tail ys
      next {xs , ys} skip     _ = xs , tail ys


  _⊆[_]_ : Stream A ∞ → Size → Stream A ∞ → Set _
  xs ⊆[ s ] ys = M (⊆-C A) s (xs , ys)


  filter-Substream : ∀ {s} p (xs : Stream A ∞) → filter p xs ⊆[ s ] xs
  filter-Substream p xs .inf
    rewrite Stream-ext
      {xs = filter p xs}
      {if p (head xs)
         then (cons (head xs) (filter p (tail xs)))
         else filter p (tail xs)}
      (filter-unfold p xs)
    with p (head xs)
  ...  | true  = ⊆-C.take refl , λ _ → filter-Substream p (tail xs)
  ...  | false = ⊆-C.skip      , λ _ → filter-Substream p (tail xs)
