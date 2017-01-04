module M where


open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Binary.HeterogeneousEquality as Het using (_≅_ ; ≅-to-≡)
open import Size


record Container la lb : Set (lsuc (la ⊔ lb)) where
  field
    A : Set la
    B : A -> Set lb

open Container


record ContainerI li la lb : Set (lsuc (li ⊔ la ⊔ lb)) where
  field
    I : Set li
    A : I -> Set la
    B : ∀ {i} -> A i -> Set lb
    r : ∀ {i} -> {a : A i} -> B a -> I

open ContainerI


Container⇒ContainerI : ∀ {la lb} -> Container la lb -> ContainerI lzero la lb
Container⇒ContainerI record { A = A ; B = B } = record { I = ⊤ ; A = λ _ -> A ; B = B ; r = λ _ -> tt }


record MI
  {li la lb}
  (c : ContainerI li la lb)
  (i : I c)
  (s : Size)
  : Set (la ⊔ lb) where
  coinductive
  field
    -- TODO Shouldn't we make a available without t < s?
    inf : ∀ {t : Size< s}
      -> Σ[ a ∈ A c i ] ((b : B c a) -> MI c (r c b) t)

open MI public


module _ {li la lb} {c : ContainerI li la lb} where

  head : ∀ {s} {t : Size< s} {i} -> MI c i s -> A c i
  head x = proj₁ (inf x)


  tail : ∀ {s} {t : Size< s} {i}
    -> (x : MI c i s)
    -> (b : B c (head x))
    -> MI c (r c b) t
  tail x = proj₂ (inf x)


M : ∀ {la lb} (c : Container la lb) (s : Size) -> Set (la ⊔ lb)
M c s = MI (Container⇒ContainerI c) tt s


-- TODO What is the correct level for _<_?
fixM' : ∀ {s li la lb lc} {c : ContainerI li la lb} {i : I c} {C : Set lc} {_<_ : Rel C lc} (<-wf : Well-founded _<_)
  -> (∀ {t}
      -> (x : C)
      -> (C -> MI c i t)
      -> ((y : C) -> y < x -> Σ[ a ∈ A c i ] ((b : B c a) -> MI c (r c b) t))
      -> Σ[ a ∈ A c i ] ((b : B c a) -> MI c (r c b) t))
  -> (x : C)
  -> Acc _<_ x
  -> MI c i s
inf (fixM' <-wf F x (acc rs)) = F x (λ y -> fixM' <-wf F y (<-wf y)) (λ y y<x -> inf (fixM' <-wf F y (rs y y<x)))


fixM : ∀ {s li la lb lc} {c : ContainerI li la lb} {i : I c} {C : Set lc} {_<_ : Rel C lc} (<-wf : Well-founded _<_)
  -> (∀ {t}
      -> (x : C)
      -> (C -> MI c i t)
      -> ((y : C) -> y < x -> Σ[ a ∈ A c i ] ((b : B c a) -> MI c (r c b) t))
      -> Σ[ a ∈ A c i ] ((b : B c a) -> MI c (r c b) t))
  -> C
  -> MI c i s
fixM <-wf F x = fixM' <-wf F x (<-wf x) 
