module Filter.Properties where


open import Data.Bool
open import Data.Product
open import Data.Unit
open import Size using (Size ; Size<_ ; ∞)
open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Binary.HeterogeneousEquality as Het
  using (_≅_ ; refl ; ≅-to-≡)
open import Level using (lift) renaming (zero to lzero)

open import Filter.Base
open import Filter.M


module Direct {a} {A : Set a} where

  open import M

  data ⊆-F (_⊆_ : Rel (Stream A ∞) a) : Rel (Stream A ∞) a where
    take : ∀ {xs ys}
      → head xs ≡ head ys
      → tail xs ⊆ tail ys
      → ⊆-F _⊆_ xs ys
    skip : ∀ {xs ys}
      → xs ⊆ tail ys
      → ⊆-F _⊆_ xs ys


  record _⊆[_]_ (xs : Stream A ∞) (s : Size) (ys : Stream A ∞) : Set a where
    coinductive
    field
      force : ∀ {t : Size< s} → ⊆-F (_⊆[ t ]_) xs ys

  open _⊆[_]_


  substream-respects-≅M : ∀ {s xs xs' ys ys'}
    → xs ≅M xs'
    → ys ≅M ys'
    → xs ⊆[ s ] ys
    → xs' ⊆[ s ] ys'
  substream-respects-≅M
    {_} {xs} {xs'} {ys} {ys'}
    eq-xs@(_ , eq-head-xs , eq-tail-xs) eq-ys@(_ , eq-head-ys , eq-tail-ys) sub
    .force {t}
    with force sub
  ... | take head-eq tail-sub = go
    where
      go : ⊆-F (_⊆[ t ]_) xs' ys'
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


  filter-⊆ : ∀ {s} p (xs : Stream A ∞) → filter p xs ⊆[ s ] xs
  filter-⊆ {s} p xs
      = substream-respects-≅M filter-eq (S.refl {xs}) go
    where
      module S = Setoid (≅M-setoid (StreamC A) ∞)


      filter-eq : filter-body p xs ≅M filter p xs
      filter-eq = S.sym {filter p xs} {filter-body p xs} (filter-unfold p xs)
      -- Why can't the implicit arguments be inferred?


      go : filter-body p xs ⊆[ s ] xs
      go .force with p (head xs)
      ... | true  = take refl (filter-⊆ p (tail xs))
      ... | false = skip (filter-⊆ p (tail xs))


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


  filter-unfold′ : ∀ p (xs : Stream A ∞) → filter p xs ≡ filter-body p xs
  filter-unfold′ p xs = ≅-to-≡ (≅M⇒≅ M-ext ≅-ext (filter-unfold p xs))
    where
      postulate M-ext : M-Extensionality lzero a a ∞
      postulate ≅-ext : Het.Extensionality a a


  filter-Substream : ∀ {s} p (xs : Stream A ∞) → filter p xs ⊆[ s ] xs
  filter-Substream p xs .inf
    rewrite filter-unfold′ p xs
    with p (head xs)
  ...  | true  = ⊆-C.take refl , λ _ → filter-Substream p (tail xs)
  ...  | false = ⊆-C.skip      , λ _ → filter-Substream p (tail xs)
