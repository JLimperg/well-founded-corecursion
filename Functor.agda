module Functor where


open import Data.Empty
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Size


infixr 50 _|+|_
infixr 60 _|×|_


data Functor : Set₁ where
  |Id| : Functor
  |K| : Set -> Functor
  _|+|_ : Functor -> Functor -> Functor
  _|×|_ : Functor -> Functor -> Functor


[_] : Functor -> Set -> Set
[ |Id| ] X = X
[ |K| A ] _ = A
[ F |+| G ] X = [ F ] X ⊎ [ G ] X
[ F |×| G ] X = [ F ] X × [ G ] X


fmap : ∀ {A B} (F : Functor) -> (A -> B) -> [ F ] A -> [ F ] B
fmap |Id| f x = f x
fmap (|K| _) _ x = x
fmap (F |+| G) f (inj₁ x) = inj₁ (fmap F f x)
fmap (F |+| G) f (inj₂ x) = inj₂ (fmap G f x)
fmap (F |×| G) f (x , y) = fmap F f x , fmap G f y


ForSubterms : ∀ {A} (F : Functor) -> (A -> Set) -> [ F ] A -> Set
ForSubterms |Id| P x = P x
ForSubterms (|K| _) P x = ⊤
ForSubterms (F |+| G) P (inj₁ x) = ForSubterms F P x
ForSubterms (F |+| G) P (inj₂ x) = ForSubterms G P x
ForSubterms (F |×| G) P (x , y) = ForSubterms F P x × ForSubterms G P y


apply-ForSubterms : ∀ {A P} F x -> ForSubterms {A} F P x -> [ F ] (Σ A P)
apply-ForSubterms |Id| x p = x , p
apply-ForSubterms (|K| B) x _ = x
apply-ForSubterms (F |+| G) (inj₁ x) p = inj₁ (apply-ForSubterms F x p)
apply-ForSubterms (F |+| G) (inj₂ x) p = inj₂ (apply-ForSubterms G x p)
apply-ForSubterms (F |×| G) (x , y) (px , py) = apply-ForSubterms F x px , apply-ForSubterms G y py


data μ (F : Functor) : ∀ Size -> Set where
  <_> : ∀ {i} -> [ F ] (μ F i) -> μ F (↑ i)

open μ public


foldμ : ∀ {i A} (F : Functor) -> ([ F ] A -> A) -> μ F i -> A
foldμ F f < x > = f (fmap F (foldμ F f) x)


record ν (F : Functor) (i : Size) : Set where
  coinductive
  field
    unν : ∀ {j : Size< i} -> [ F ] (ν F j)

open ν public


record Always {F} (P : ν F ∞ -> Set) (i : Size) (s : ν F ∞) : Set where
  coinductive
  field
    here : P s
    further : ∀ {j : Size< i} -> ForSubterms F (Always P j) (unν s)

open Always public
