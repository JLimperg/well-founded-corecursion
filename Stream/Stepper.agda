module Stream.Stepper where


open import Data.Bool
open import Data.Empty
open import Data.List hiding ([_])
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Size

open import Functor
open import Stream.Functor


lem-truesS : WaitFinite ∞ truesS
lem-truesS = later truesS tt (immediate truesS' tt)


convStep : ∀ {F} {s : ν (F |+| |Id|) ∞} -> WaitFinite ∞ s -> [ F ] (ν (F |+| |Id|) ∞)
convStep (immediate s s-is-step) with unν s | s-is-step
... | inj₁ x | _ = x
... | inj₂ x | ()
convStep (later s s-is-wait p) with unν s | s-is-wait
... | inj₁ _ | ()
... | inj₂ s' | _ = convStep p


mutual
  lem-truesS∞ : ∀ {i} -> Productive i truesS
  here lem-truesS∞ = lem-truesS
  further lem-truesS∞ = lem-truesS'∞

  lem-truesS'∞ : ∀ {i} -> Productive i truesS'
  here lem-truesS'∞ = immediate _ _
  further lem-truesS'∞ = _ , lem-truesS∞


convStep∞ : ∀ {F} {s : ν (F |+| |Id|) ∞} -> WaitFinite ∞ s -> Productive ∞ s -> [ F ] (Σ (ν (F |+| |Id|) ∞) (Productive ∞))
convStep∞ {F} (immediate s s-is-step) pprod with unν s | s-is-step | further pprod
... | inj₁ x | _ | p = apply-ForSubterms F x p
... | inj₂ _ | () | _
convStep∞ (later s s-is-wait p) pprod with unν s | s-is-wait | further pprod
... | inj₁ _ | () | _
... | inj₂ _ | _ | p' = convStep∞ p p'


-- We have to define a specialised fmap (conv') along with the conversion function
-- to please the termination checker. If convStep∞ had a more precise type,
-- we might be able to use regular fmap like in fold.
conv : ∀ {F} -> {s : ν (F |+| |Id|) ∞} -> (Productive ∞ s) -> ν F ∞
-- unν (conv {F} sprod) = fmap F conv (convStep∞ (here sprod) sprod)
unν (conv {F} sprod) = conv' F (convStep∞ (here sprod) sprod)
  where
    conv' : ∀ F {G} -> [ F ] (Σ (ν (G |+| |Id|) ∞) (Productive ∞)) -> [ F ] (ν G ∞)
    -- conv' F = fmap F conv
    conv' |Id| (_ , p) = conv p
    conv' (|K| _) x = x
    conv' (F |+| G) (inj₁ x) = inj₁ (conv' F x)
    conv' (F |+| G) (inj₂ x) = inj₂ (conv' G x)
    conv' (F |×| G) (x , y) = conv' F x , conv' G y


takes : ∀ {A} -> ℕ -> Stream A ∞ -> List A
takes zero _ = []
takes (suc n) s with unν s
... | (x , s') = x ∷ takes n s'


test = takes 10 (conv lem-truesS∞)


rew : ∀ {a b} {A : Set a} {x y : A} (P : A -> Set b) -> (x ≡ y) -> P x -> P y
rew _ eq px rewrite eq = px


filterS : ∀ {A} -> (p : A -> Bool) -> (s : Stream A ∞) -> StreamS A ∞
unν (filterS p s) with p (proj₁ (unν s))
... | true = inj₁ (proj₁ (unν s) , filterS p (proj₂ (unν s)))
... | false = inj₂ (filterS p (proj₂ (unν s)))


-- TODO There has to be a more elegant formulation of the below.
filterS-WaitFinite : ∀ {A} {p : A -> Bool} {s} -> Eventually (T ∘ p) ∞ s -> WaitFinite ∞ (filterS p s)
filterS-WaitFinite {p = p} {s} prf with p (proj₁ (unν s)) | inspect p (proj₁ (unν s))
... | true | ⟨ eq ⟩ = immediate _ prf'
  where
    prf' : T (is-step (filterS p s))
    prf' rewrite eq = tt
filterS-WaitFinite {p = p} (now s prf') | false | ⟨ eq ⟩ rewrite eq = ⊥-elim prf'
filterS-WaitFinite {A} {p} (later s prf') | false | ⟨ eq ⟩ = later _ prf'' prf'''
  where
    prf'' : T (is-wait (filterS p s))
    prf'' rewrite eq = tt

    prf''' : ForSubterms (StreamSF A) (WaitFinite ∞) (unν (filterS p s))
    prf''' rewrite eq = filterS-WaitFinite prf'


filterS-Productive : ∀ {A} {p : A -> Bool} {s} -> InfinitelyOften (T ∘ p) ∞ s -> Productive ∞ (filterS p s)
here (filterS-Productive pinf) = filterS-WaitFinite (here pinf)
further (filterS-Productive {p = p} {s} pinf) with p (proj₁ (unν s))
... | true = _ , filterS-Productive (proj₂ (further pinf))
... | false = filterS-Productive (proj₂ (further pinf))


filters : ∀ {A} {p : A -> Bool} {s} -> InfinitelyOften (T ∘ p) ∞ s -> Stream A ∞
filters pinf = conv (filterS-Productive pinf)
