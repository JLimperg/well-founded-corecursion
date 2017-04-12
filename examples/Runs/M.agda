module Runs.M where

open import Data.Bool using (if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; [_] ; _∷ʳ_)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Nat
open import Data.Product
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _on_)
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Well-founded ; module Inverse-image)
open import Level using () renaming (zero to lzero ; suc to lsuc)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl; Extensionality)
open import Size

open import Coinduction.WellFounded
open import Runs.Nat


-- Basic data structures etc.


StreamC : Set → Container lzero
StreamC A = A ▷ (λ _ → ⊤)


Stream : Set → Size → Set
Stream A = M (StreamC A)


StreamWhnf : ∀ A → Size → Set
StreamWhnf A s = ⟦ StreamC A ⟧ (Stream A s)


whnf : ∀ {s} {t : Size< s} {A} → Stream A s → StreamWhnf A t
whnf xs = inf xs


head : ∀ {s} {t : Size< s} {A} → Stream A s → A
head xs = proj₁ (whnf xs)


tail : ∀ {s} {t : Size< s} {A} → Stream A s → Stream A t
tail xs = proj₂ (whnf xs) tt


cons : ∀ {s A} → A → Stream A s → Stream A (↑ s)
cons x xs .inf = x , λ _ → xs


_<<_ : ∀ {a} {A : Set a} → Rel (A × Stream ℕ ∞) lzero
_<<_ =  _<′_ on (head ∘ proj₂)


<<-wf : ∀ {a} {A : Set a} → Well-founded (_<<_ {A = A})
<<-wf = Inverse-image.well-founded _ <-well-founded


-- Definition of runs


runs′F : ∀ {t}
  → (x : List ℕ × Stream ℕ ∞)
  → (List ℕ × Stream ℕ ∞ → Stream (List ℕ) t)
  → (∀ y → y << x → StreamWhnf (List ℕ) t)
  → StreamWhnf (List ℕ) t
runs′F (run , xs) corec rec with head (tail xs) <′? head xs
... | yes lt = rec (run ∷ʳ head xs , tail xs) lt
... | no  _  = run ∷ʳ head xs , λ _ → corec ([] , tail xs)


runs′ : List ℕ × Stream ℕ ∞ → Stream (List ℕ) ∞
runs′ = fixM <<-wf runs′F


runs : Stream ℕ ∞ → Stream (List ℕ) ∞
runs xs = runs′ ([] , xs)


-- A simple 'unit test':


take : ∀ {A} → ℕ → Stream A ∞ → List A
take zero xs = []
take (suc n) xs = head xs ∷ take n (tail xs)


cycle : ∀ {A n} → Vec A (1 + n) → Stream A ∞
cycle xs = go xs xs
  where
    go : ∀ {A n m} → Vec A (1 + n) → Vec A (1 + m) → Stream A ∞
    go xs (x ∷ []    ) .inf = x , λ _ → go xs xs
    go xs (x ∷ y ∷ ys) .inf = x , λ _ → go xs (y ∷ ys)


test : List (List ℕ)
test = take 10 (runs (cycle (0 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ [])))


-- Unfolding runs′


runs′-body
  : List ℕ
  → Stream ℕ ∞
  → Stream (List ℕ) ∞
runs′-body run xs
    = if ⌊ head (tail xs) <′? head xs ⌋
        then runs′ ((run ∷ʳ head xs) ,  (tail xs))
        else cons (run ∷ʳ head xs) (runs′ ([] , (tail xs)))


runs′-unfold : ∀ run xs → runs′ (run , xs) ≡ runs′-body run xs
runs′-unfold run xs = M-ext go
  where
    postulate
      ≡-ext : ∀ {a b} → Extensionality a b
      M-ext : ∀ {a} → M-Extensionality a

    go : inf (runs′ (run , xs))
       ≡ inf (runs′-body run xs)
    go rewrite fixM-unfold′ <<-wf runs′F ≡-ext (run , xs)
       with head (tail xs) <′? head xs
    ... | yes _ = refl
    ... | no  _ = refl
