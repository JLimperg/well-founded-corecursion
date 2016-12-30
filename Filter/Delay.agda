module Filter.Delay where


open import Data.Bool
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Function
open import Size


record Stream (A : Set) (i : Size) : Set where
  coinductive
  constructor _::_
  field
    head : A
    tail : {j : Size< i} -> Stream A j

open Stream


record Always {A} (P : Stream A ∞ -> Set) (i : Size) (s : Stream A ∞) : Set where
  coinductive
  field
    current : P s
    substreams : ∀ {j : Size< i} -> Always P j (tail s)

open Always


data Eventually {A} (P : A -> Set) : ∀ (i : Size) -> Stream A ∞ -> Set where
  here : ∀ i s -> P (head s) -> Eventually P i s
  later : ∀ i s -> Eventually P i (tail s) -> Eventually P (↑ i) s

open Eventually


InfinitelyOften : ∀ {A} -> (A -> Set) -> Size -> Stream A ∞ -> Set
InfinitelyOften P i = Always (Eventually P ∞) i


isTrue : Bool -> Set
isTrue true = ⊤ 
isTrue false = ⊥


mutual
  data Delay (i : Size) (A : Set) : Set where
    now : A -> Delay i A
    later : Delay∞ i A -> Delay i A

  record Delay∞ (i : Size) (A : Set) : Set where
    coinductive
    field
      undelay : ∀ {j : Size< i} -> Delay j A

open Delay∞
open Delay


pure : ∀ {A i} -> A -> Delay i A
pure = now


mutual
  _>>=_ : ∀ {A B i} -> Delay i A -> (A -> Delay i B) -> Delay i B
  (now x) >>= f = f x
  (later x) >>= f = later (x ∞>>= f)

  _∞>>=_ : ∀ {A B i} -> Delay∞ i A -> (A -> Delay i B) -> Delay∞ i B
  undelay (x ∞>>= f) = undelay x >>= f


fmap : ∀ {A B i} -> (A -> B) -> Delay i A -> Delay i B
fmap f x = x >>= λ x' -> now (f x')


sfilter : ∀ {A i} -> (A -> Bool) -> Stream A ∞ -> Delay i (Stream A ∞)
sfilter {A} {i} P xs = later fxs
  where
    fxs : Delay∞ i (Stream A ∞)
    undelay fxs {j} with P (head xs)
    ... | true = fmap (λ (xs' : Stream A ∞) -> head xs :: xs') (sfilter P (tail xs))
    ... | false = sfilter P (tail xs)


data _⇓_ {A} : Delay ∞ A -> A -> Set where
  now⇓ : ∀ a -> (now a) ⇓ a
  later⇓ : ∀ {a? a} -> undelay a? ⇓ a -> later a? ⇓ a


sfilter⇓ : ∀ {A i} {P : A -> Bool} {xs : Stream A ∞} -> InfinitelyOften (isTrue ∘ P) i xs -> Σ (Stream A ∞) (sfilter P xs ⇓_)
sfilter⇓ = {!!}
