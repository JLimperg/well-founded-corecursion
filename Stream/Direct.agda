module Stream.Direct where

open import Size
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality


record StreamF A (i : Size) (Stream : Size -> Set) : Set where
  constructor _::_
  field
    head : A
    tail : Stream i

open StreamF


record Stream A (i : Size) : Set where
  coinductive
  field
    force : ∀ (j : Size< i) -> StreamF A j (Stream A)


record StreamS A (i : Size) : Set where
  coinductive
  field
    force : ∀ (j : Size< i) -> StreamF A j (StreamS A) ⊎ StreamS A j


open Stream


smap : ∀ {A B} i -> (A -> B) -> Stream A i -> Stream B i
head (force (smap i f s) j) = f (head (force s j))
tail (force (smap i f s) j) = smap j f (tail (force s j))


zipWith : ∀ {A B C} i -> (A -> B -> C) -> Stream A i -> Stream B i -> Stream C i
head (force (zipWith i f s t) j) = f (head (force s j)) (head (force t j))
tail (force (zipWith i f s t) j) = zipWith j f (tail (force s j)) (tail (force t j))


repeat : ∀ {A} i -> A -> Stream A i
head (force (repeat i x) j) = x
tail (force (repeat i x) j) = repeat j x


unfold : ∀ {A B : Set} i -> (B -> A × B) -> B -> Stream A i
head (force (unfold i step x) j) = proj₁ (step x)
tail (force (unfold i step x) j) = unfold j step (proj₂ (step x))


interleave : ∀ {A} i -> Stream A i -> Stream A i -> Stream A i
head (force (interleave _ xs ys) j) = head (force xs j)
tail (force (interleave _ xs ys) j) = interleave j ys xs


record Always {A} (P : Stream A ∞ -> Set) (i : Size) (s : Stream A ∞) : Set where
  coinductive
  field
    current : P s
    substreams : ∀ (j : Size< i) -> Always P j (tail (force s ∞))

open Always


id-Always : ∀ {A P i s} -> Always {A} P i s -> Always P i s
current (id-Always p) = current p
substreams (id-Always p) = substreams p


data Eventually {A} (P : A -> Set) : ∀ (i : Size) -> Stream A ∞ -> Set where
  here : ∀ i s -> P (head (force s ∞)) -> Eventually P i s
  later : ∀ i s -> Eventually P i (tail (force s ∞)) -> Eventually P (↑ i) s

open Eventually


id-Eventually : ∀ {A} {P : A -> Set} {i} {s : Stream A ∞} -> Eventually P i s -> Eventually P i s
id-Eventually (here i s p) = here i s p
id-Eventually (later i s p) = later i s p


Eventually-step : ∀ {A} i {P : A -> Set} {s : Stream A ∞} -> Eventually P i s -> Σ A P × Stream A ∞
Eventually-step .j (here j s x) = (head (force s ∞) , x) , tail (force s ∞)
Eventually-step .(↑ j) (later j s p) = Eventually-step j p


InfinitelyOften : ∀ {A} -> (A -> Set) -> Size -> Size -> Stream A ∞ -> Set
InfinitelyOften P i j = Always (Eventually P j) i


InfinitelyOften-step' : ∀ {A} i -> {P : A -> Set} {s : Stream A ∞} -> Eventually P i s -> InfinitelyOften P ∞ ∞ s -> Σ A P × Σ (Stream A ∞) (InfinitelyOften P ∞ ∞)
InfinitelyOften-step' .j (here j s p) pInf = (head (force s ∞) , p) , ((tail (force s ∞)) , (substreams pInf ∞))
InfinitelyOften-step' .(↑ j) (later j s p) pInf = InfinitelyOften-step' j p (substreams pInf ∞)


InfinitelyOften-step : ∀ {A} -> {P : A -> Set} {s : Stream A ∞} -> InfinitelyOften P ∞ ∞ s -> Σ A P × Σ (Stream A ∞) (InfinitelyOften P ∞ ∞)
InfinitelyOften-step p = InfinitelyOften-step' ∞ (current p) p


alternate : ∀ {A} -> A -> A -> Stream A ∞
alternate x y = interleave ∞ (repeat ∞ x) (repeat ∞ y)


lem1' : ∀ {A} i (x y : A) -> Eventually (_≡ x) i (alternate x y)
lem1' i x y = here i (alternate x y) refl


lem1 : ∀ {A} i (x y : A) -> Eventually (_≡ y) (↑ i) (alternate x y)
lem1 i x y = later i (alternate x y) (lem1' i y x)


lem2 : ∀ {A} i (x : A) -> Always (λ _ -> ⊤) i (repeat ∞ x)
current (lem2 _ _) = tt
substreams (lem2 _ x) j = lem2 j x


mutual
  lem3 : ∀ {A} i (x y : A) -> InfinitelyOften (_≡ x) i ∞ (alternate x y)
  current (lem3 _ x y) = lem1' ∞ x y
  substreams (lem3 _ x y) j = lem4 j y x

  lem4 : ∀ {A} i (x y : A) -> InfinitelyOften (_≡ y) i ∞ (alternate x y)
  current (lem4 _ x y) = lem1 ∞ x y
  substreams (lem4 _ x y) j = lem3 j y x


isTrue : Bool -> Set
isTrue true = ⊤ 
isTrue false = ⊥
