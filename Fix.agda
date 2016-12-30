module Fix where


open import Data.Bool
open import Data.Empty
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Function
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Size

open import Functor
open import Stream.Functor


fixν-simple : ∀ {a} {A : Set a} {i F} -> (∀ {j} -> (A -> ν F j) -> A -> [ F ] (ν F j)) -> A -> ν F i
unν (fixν-simple F x) = F (fixν-simple F) x


mapF : ∀ {i A B} -> (A -> B) -> (Stream A ∞ -> Stream B i) -> Stream A ∞ -> [ StreamF B ] (Stream B i)
mapF f map s with unν s
... | (x , s') = f x , map s'


map : ∀ {A B} -> (A -> B) -> Stream A ∞ -> Stream B ∞
map f = fixν-simple (mapF f)


fixν' : ∀ {i a} {A : Set a} {F : Functor} {_<_ : Rel A a} (<-wf : Well-founded _<_)
  -> (f : ∀ {j} -> (x : A) -> (A -> ν F j) -> ((y : A) -> y < x -> [ F ] (ν F j)) -> [ F ] (ν F j))
  -> (x : A)
  -> Acc _<_ x
  -> ν F i
unν (fixν' <-wf f x (acc rs)) = f x (λ y -> fixν' <-wf f y (<-wf y)) (λ y y<x -> unν (fixν' <-wf f y (rs y y<x)))


fixν : ∀ {i a} {A : Set a} {F : Functor} {_<_ : Rel A a} (<-wf : Well-founded _<_)
  -> (f : ∀ {j} -> (x : A) -> (A -> ν F j) -> ((y : A) -> y < x -> [ F ] (ν F j)) -> [ F ] (ν F j))
  -> A
  -> ν F i
fixν <-wf f x = fixν' <-wf f x (<-wf x) 



every-nth : ∀ {i A} -> ℕ -> ℕ -> Stream A ∞ -> Stream A i
unν (every-nth n zero s) = head s , every-nth n n (tail s)
unν (every-nth n (suc k) s) = unν (every-nth n k (tail s))


_<<_ : ∀ {A} -> Rel (ℕ × Stream A ∞) lzero
_<<_ = _<′_ on proj₁


<<-wf : ∀ {A} -> Well-founded (_<<_ {A})
<<-wf = Inverse-image.well-founded proj₁ <-well-founded


every-nthF : ∀ {A}
  -> ℕ
  -> ∀ {i}
  -> (x : ℕ × Stream A ∞)
  -> (ℕ × Stream A ∞ -> Stream A i)
  -> ((y : ℕ × Stream A ∞) -> y << x -> [ StreamF A ] (Stream A i))
  -> [ StreamF A ] (Stream A i)
every-nthF n (zero , s) every-nth₁ every-nth₂ = head s , every-nth₁ (n , tail s)
every-nthF n (suc k , s) every-nth₁ every-nth₂ = every-nth₂ (k , tail s) ≤′-refl


every-nth' : ∀ {A} -> ℕ -> ℕ -> Stream A ∞ -> Stream A ∞
every-nth' n k s = fixν <<-wf (every-nthF n) (k , s)


test = take 10 (every-nth' 9 10 integers)
