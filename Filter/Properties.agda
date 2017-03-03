module Filter.Properties where


open import Data.Bool
open import Data.Product
open import Data.Unit
open import Size using (Size ; Size<_ ; ∞)
open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; refl ; ≅-to-≡)
open import Level using (lift)

open import Filter.Base
open import Filter.M


module Direct {a} {A : Set a} where

  open import M

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


  substream-respects-≅M : ∀ {s xs xs' ys ys'}
    → xs ≅M xs'
    → ys ≅M ys'
    → Substream s xs ys
    → Substream s xs' ys'
  substream-respects-≅M
    {_} {xs} {xs'} {ys} {ys'}
    eq-xs@(_ , eq-head-xs , eq-tail-xs) eq-ys@(_ , eq-head-ys , eq-tail-ys) sub
    .force {t}
    with force sub
  ... | take head-eq tail-sub = go
    where
      go : SubstreamF (Substream t) xs' ys'
      go
        rewrite ≅-to-≡ eq-head-xs
              | ≅-to-≡ eq-head-ys
              | ≅-to-≡ (eq-tail-xs _ _ refl)
              | ≅-to-≡ (eq-tail-ys _ _ refl)
        = take head-eq tail-sub
  ... | skip tail-sub
      = skip
          (substream-respects-≅M eq-xs
             (reflexive (≅-to-≡ (eq-tail-ys _ _ refl))) tail-sub)
    where
      open Setoid (≅M-setoid (StreamC A) ∞) using (reflexive)


  filter-Substream : ∀ {s} p (xs : Stream A ∞) → Substream s (filter p xs) xs
  filter-Substream {s} p xs
      = substream-respects-≅M
          (S.sym {filter p xs} {filter-p-xs} (filter-unfold p xs)) (S.refl {xs})
          go
    where
      module S = Setoid (≅M-setoid (StreamC A) ∞)

      filter-p-xs : Stream A ∞
      filter-p-xs
          = if p (head xs)
              then (cons (head xs) (filter p (tail xs)))
              else (filter p (tail xs))

      go : Substream s filter-p-xs xs
      go .force with p (head xs)
      ... | true  = take refl (filter-Substream p (tail xs))
      ... | false = skip (filter-Substream p (tail xs))


module WithM {a} {A : Set a} where

  open import M.Indexed

  ⊆-C : (A : Set a)
    → Container (Stream A ∞ × Stream A ∞) (Stream A ∞ × Stream A ∞) _ _
  ⊆-C A = Command ◃ Response / next
    module ⊆-C where
      data Command (xs×ys : Stream A ∞ × Stream A ∞) : Set a where
        take : head (proj₁ xs×ys) ≡ head (proj₂ xs×ys) → Command xs×ys
        skip : Command xs×ys

      Response : ∀ {o} → Command o → Set
      Response _ = ⊤

      next : ∀ {o} (c : Command o) → Response c → Stream A ∞ × Stream A ∞
      next {xs , ys} (take _) _ = tail xs , tail ys
      next {xs , ys} skip     _ = xs , tail ys


  _⊆[_]_ : Stream A ∞ → Size → Stream A ∞ → Set _
  xs ⊆[ s ] ys = M (⊆-C A) s (xs , ys)


  -- TODO If we are to eat our own dog food, we should reimplement the above.
  -- Not sure I have the stomach though.

  -- filter-Substream : ∀ {s} p (xs : Stream A ∞) → filter p xs ⊆[ s ] xs
  -- filter-Substream p xs .inf = ?
  --   rewrite Stream-ext
  --     {xs = filter p xs}
  --     {if p (head xs)
  --        then (cons (head xs) (filter p (tail xs)))
  --        else filter p (tail xs)}
  --     (filter-unfold p xs)
  --   with p (head xs)
  -- ...  | true  = ⊆-C.take refl , λ _ → filter-Substream p (tail xs)
  -- ...  | false = ⊆-C.skip      , λ _ → filter-Substream p (tail xs)
