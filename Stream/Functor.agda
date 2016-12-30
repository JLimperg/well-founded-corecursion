module Stream.Functor where


open import Data.Bool
open import Data.List using (List ; _∷_) renaming ([] to nil)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Size


open import Functor


StreamF : Set -> Functor
StreamF A = |K| A |×| |Id|


Stream : Set -> Size -> Set
Stream A = ν (StreamF A)


id-Stream : ∀ {i A} -> Stream A i -> Stream A i
unν (id-Stream s) = unν s


head : ∀ {i A} -> Stream A (↑ i) -> A
head s = proj₁ (unν s)


tail : ∀ {i A} -> Stream A i -> ∀ {j : Size< i} -> Stream A j
tail s = proj₂ (unν s)


StreamSF : Set -> Functor
StreamSF A = StreamF A |+| |Id|


StreamS : Set -> Size -> Set
StreamS A = ν (StreamSF A)


step : ∀ {i A} -> A -> (∀ {j : Size< i} -> StreamS A j) -> StreamS A i
unν (step x xs) = inj₁ (x , xs)


wait : ∀ {i A} -> (∀ {j : Size< i} -> StreamS A j) -> StreamS A i
unν (wait s) = inj₂ s


is-step : ∀ {i F} -> ν (F |+| |Id|) (↑ i) -> Bool
is-step s = is-just (isInj₁ (unν s))


is-wait : ∀ {i F} -> ν (F |+| |Id|) (↑ i) -> Bool
is-wait s = is-just (isInj₂ (unν s))


data Eventually {A} (P : A -> Set) : Size -> Stream A ∞ -> Set where
  now : ∀ {j} s -> P (head s) -> Eventually P j s
  later : ∀ {j} s -> Eventually P j (tail s) -> Eventually P (↑ j) s

open Eventually public


InfinitelyOften : ∀ {A} (P : A -> Set) -> Size -> Stream A ∞ -> Set
InfinitelyOften P j = Always (Eventually P ∞) j


extract-step : ∀ {i F} (s : ν (F |+| |Id|) (↑ i)) -> T (is-step s) -> [ F ] (ν (F |+| |Id|) i)
extract-step s p with unν s | p
... | inj₁ x | _ = x
... | inj₂ _ | ()


data WaitFinite {F} : ∀ {i : Size} -> Size -> ν (F |+| |Id|) i -> Set where
  immediate : ∀ {i j} (s : ν (F |+| |Id|) (↑ i)) -> T (is-step s) -> WaitFinite j s
  later : ∀ {i j} (s : ν (F |+| |Id|) (↑ i)) -> T (is-wait s) -> ForSubterms (F |+| |Id|) (WaitFinite j) (unν s) -> WaitFinite (↑ j) s


Productive : ∀ {F} -> Size -> (ν (F |+| |Id|) ∞) -> Set
Productive = Always (WaitFinite ∞)


trues : ∀ {i} -> Stream Bool i
unν trues = true , trues


mutual
  truesS : ∀ {i} -> StreamS Bool i
  unν truesS {j} = inj₂ truesS'

  truesS' : ∀ {i} -> StreamS Bool i
  unν truesS' = inj₁ (true , truesS)


take : ∀ {A} -> ℕ -> Stream A ∞ -> List A
take zero _ = nil
take (suc n) s = head s ∷ take n (tail s)


integersFrom : ℕ -> Stream ℕ ∞
unν (integersFrom n) = n , integersFrom (suc n)


integers : Stream ℕ ∞
integers = integersFrom 0
