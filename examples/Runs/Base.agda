module Runs.Base where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Size


-- Utilities

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl x = x


-- Streams

module Stream where

  open import Coinduction.WellFounded


  StreamC : Set → Container lzero lzero
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

open Stream public


module All where

  open import Coinduction.WellFounded.Indexed


  module _ {A : Set} (P : A → Set) where

    AllC : Container (Stream A ∞) (Stream A ∞) lzero lzero
    AllC = Command ◃ (λ {i} → Response {i}) / (λ {i} → next {i})
      module AllC where
        Command : Stream A ∞ → Set
        Command xs = P (head xs)

        Response : ∀ {i} → Command i → Set
        Response _ = ⊤

        next : ∀ {i} c → Response {i} c → Stream A ∞
        next {xs} _ _ = tail xs


    AllF : (Stream A ∞ → Set) → Stream A ∞ → Set
    AllF = ⟦ AllC ⟧


    All : Size → Stream A ∞ → Set
    All = M AllC


    AllWhnf : Size → Stream A ∞ → Set
    AllWhnf s = AllF (All s)

open All public
