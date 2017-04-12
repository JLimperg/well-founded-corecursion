module Runs.M where

open import Data.Bool using (if_then_else_)
open import Data.List using (List ; [] ; _∷_)
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


_<<_ : Rel (ℕ × Stream ℕ ∞) lzero
_<<_ =  _<′_ on (head ∘ proj₂)


<<-wf : Well-founded _<<_
<<-wf = Inverse-image.well-founded _ <-well-founded


runLengths′F : ∀ {t}
  → (x : ℕ × Stream ℕ ∞)
  → (ℕ × Stream ℕ ∞ → Stream ℕ t)
  → (∀ y → y << x → StreamWhnf ℕ t)
  → StreamWhnf ℕ t
runLengths′F (n , xs) corec rec with head (tail xs) <′? head xs
... | yes lt = rec (suc n , tail xs) lt
... | no  _  = n , λ _ → corec (1 , tail xs)


runLengths′ : ℕ × Stream ℕ ∞ → Stream ℕ ∞
runLengths′ = fixM <<-wf runLengths′F


runLengths : Stream ℕ ∞ → Stream ℕ ∞
runLengths xs = runLengths′ (1 , xs)


runLengths′-body
  : (ℕ → Stream ℕ ∞ → Stream ℕ ∞)
  → ℕ
  → Stream ℕ ∞
  → Stream ℕ ∞
runLengths′-body runLengths′ n xs
    = if ⌊ head (tail xs) <′? head xs ⌋
        then runLengths′ (suc n) (tail xs)
        else cons n (runLengths′ 1 (tail xs))


runLenghts′-unfold : ∀ n xs →
  runLengths′ (n , xs) ≡ runLengths′-body (λ n xs → runLengths′ (n , xs)) n xs
runLenghts′-unfold n xs = M-ext go
  where
    postulate
      ≡-ext : ∀ {a b} → Extensionality a b
      M-ext : ∀ {a} → M-Extensionality a

    go : inf (runLengths′ (n , xs))
       ≡ inf (runLengths′-body (λ n xs → runLengths′ (n , xs)) n xs)
    go rewrite fixM-unfold′ <<-wf runLengths′F ≡-ext (n , xs)
       with head (tail xs) <′? head xs
    ... | yes _ = refl
    ... | no  _ = refl


take : ∀ {A} → ℕ → Stream A ∞ → List A
take zero xs = []
take (suc n) xs = head xs ∷ take n (tail xs)


cycle : ∀ {A n} → Vec A (1 + n) → Stream A ∞
cycle xs = go xs xs
  where
    go : ∀ {A n m} → Vec A (1 + n) → Vec A (1 + m) → Stream A ∞
    go xs (x ∷ []    ) .inf = x , λ _ → go xs xs
    go xs (x ∷ y ∷ ys) .inf = x , λ _ → go xs (y ∷ ys)


test : List ℕ
test = take 10 (runLengths (cycle (0 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ [])))
