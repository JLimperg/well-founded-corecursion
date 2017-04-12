module Runs.Nat where

open import Data.Nat public
open import Relation.Nullary using (Dec ; yes ; no)


≤′-zero : ∀ n → 0 ≤′ n
≤′-zero zero = ≤′-refl
≤′-zero (suc n) = ≤′-step (≤′-zero n)


≤′-suc : ∀ {n m} → n ≤′ m → suc n ≤′ suc m
≤′-suc ≤′-refl = ≤′-refl
≤′-suc (≤′-step leq) = ≤′-step (≤′-suc leq)


≤⇒≤′ : ∀ {n m} → n ≤ m → n ≤′ m
≤⇒≤′ z≤n = ≤′-zero _
≤⇒≤′ (s≤s leq) = ≤′-suc (≤⇒≤′ leq)


≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)


≤-step : ∀ {n m} → n ≤ m → n ≤ (suc m)
≤-step z≤n = z≤n
≤-step (s≤s leq) = s≤s (≤-step leq)


≤′⇒≤ : ∀ {n m} → n ≤′ m → n ≤ m
≤′⇒≤ ≤′-refl = ≤-refl _
≤′⇒≤ (≤′-step leq) = ≤-step (≤′⇒≤ leq)


mapDec : ∀ {p q} {P : Set p} {Q : Set q}
  → (P → Q) → (Q → P)
  → Dec P → Dec Q
mapDec f g (yes p) = yes (f p)
mapDec f g (no ¬p) = no (λ z → ¬p (g z))


_≤′?_ : ∀ n m → Dec (n ≤′ m)
n ≤′? m = mapDec ≤⇒≤′ ≤′⇒≤ (n ≤? m)


_<′?_ : ∀ n m → Dec (n <′ m)
n <′? m = suc n ≤′? m
