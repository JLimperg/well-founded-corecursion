module Filter.Base where

open import Data.Nat using (ℕ ; _<′_)
open import Data.Product
open import Data.Unit
open import Level using (Lift ; lift)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_)
open import Size using (Size ; ↑_)

open import M


StreamC : ∀ {a} → Set a → Container a
StreamC A = A ▷ (λ _ → Lift ⊤)


Stream : ∀ {a} → Set a → Size → Set a
Stream A s = M (StreamC A) s


module _ {a} {A : Set a} where

  head : ∀ {s} → Stream A (↑ s) → A
  head xs = proj₁ (inf xs)


  tail : ∀ {s} → Stream A (↑ s) → Stream A s
  tail xs = proj₂ (inf xs) (lift tt)


  cons : ∀ {s} → A → Stream A s → Stream A (↑ s)
  cons x xs .inf = x , λ _ → xs


  postulate
    dist : ∀ {s} → (A → Set) → Stream A s → ℕ
    dist-0 : ∀ {p s} → dist p s ≡ 0 → p (head s)
    dist-monotone : ∀ {p s}
      → dist p s ≢ 0
      → dist p (tail s) <′ dist p s
