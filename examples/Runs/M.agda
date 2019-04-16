module Runs.M where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool using (true ; false ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; [_] ; _∷ʳ_)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Nat
open import Data.Product
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; _on_)
open import Induction.Nat using (<-wellFounded)
open import Induction.WellFounded using (WellFounded ; module Inverse-image)
open import Level using () renaming (zero to lzero ; suc to lsuc)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Rel ; Setoid ; Decidable)
open import Relation.Binary.PropositionalEquality as ≡ using
  (_≡_ ; refl)
open import Relation.Binary.HeterogeneousEquality using
  (≡-to-≅ ; ≅-to-≡)
open import Size

open import Coinduction.WellFounded
import Coinduction.WellFounded.Indexed as Ix
open import Runs.Base


-- # Well-founded relation


_<<_ : ∀ {A : Set} → Rel (Stream ℕ ∞ × A) lzero
_<<_ (xs , _) (ys , _) = head xs < head ys


<<-wf : ∀ {A} → WellFounded (_<<_ {A = A})
<<-wf = Inverse-image.wellFounded _ <-wellFounded


-- # Definition of runs


runs′F : ∀ {t}
  → (x : Stream ℕ ∞ × List ℕ)
  → (Stream ℕ ∞ × List ℕ → Stream (List ℕ) t)
  → (∀ y → y << x → StreamWhnf (List ℕ) t)
  → StreamWhnf (List ℕ) t
runs′F (xs , run) corec rec with head (tail xs) <? head xs
... | yes lt = rec (tail xs , run ∷ʳ head xs) lt
... | no  _  = run ∷ʳ head xs
             , λ _ → corec (tail xs , [])

runs′ : Stream ℕ ∞ × List ℕ → Stream (List ℕ) ∞
runs′ = cofixWf <<-wf runs′F


runs : Stream ℕ ∞ → Stream (List ℕ) ∞
runs xs = runs′ (xs , [])


-- # A simple 'unit test':


take : ∀ {A} → ℕ → Stream A ∞ → List A
take zero xs = []
take (suc n) xs = head xs ∷ take n (tail xs)


cycle : ∀ {A n} → Vec A (1 + n) → Stream A ∞
cycle xs = go xs xs
  where
    go : ∀ {A n m} → Vec A (1 + n) → Vec A (1 + m) → Stream A ∞
    go xs (x ∷ []    ) .inf = x , λ _ → go xs xs
    go xs (x ∷ y ∷ ys) .inf = x , λ _ → go xs (y ∷ ys)


test : take 6 (runs (cycle (0 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ [])))
     ≡ ([ 0 ] ∷ [ 0 ] ∷ (1 ∷ 0 ∷ []) ∷ (2 ∷ 1 ∷ 0 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ [ 0 ] ∷ [])
test = refl


-- # Unfolding runs′


runs′-body
  : (Stream ℕ ∞ × List ℕ)
  → Stream (List ℕ) ∞
runs′-body (xs , run)
    = if ⌊ head (tail xs) <? head xs ⌋
        then runs′ (tail xs , run ∷ʳ head xs)
        else cons (run ∷ʳ head xs) (runs′ (tail xs , []))


runs′-unfold : ∀ xs run → runs′ (xs , run) ≡ runs′-body (xs , run)
runs′-unfold xs run = M-Extensionality-from-Ix M-ext go
  where
    postulate
      ≡-ext : ∀ {a b} → Extensionality a b
      M-ext : ∀ {a b c s} {t : Size< s} → M-Extensionality a b c s

    go : inf (runs′ (xs , run))
       ≡ inf (runs′-body (xs , run))
    go rewrite cofixWf-unfold′ <<-wf runs′F ≡-ext (xs , run)
       with head (tail xs) <? head xs
    ... | yes _ = refl
    ... | no  _ = refl


-- # A simple property of runs


-- We will prove that for all streams xs, the lists in `runs xs` contain only
-- elements of `xs`. This holds by parametricity, but the proof is still
-- interesting because we need indexed well-founded coinduction for it.


data _∈_ {A} : A → Stream A ∞ → Set where
  here : ∀ xs → head xs ∈ xs
  there : ∀ {x xs} → x ∈ tail xs → x ∈ xs


_⊂L_ : ∀ {A} → List A → Stream A ∞ → Set
[] ⊂L ys = ⊤
(x ∷ xs) ⊂L ys = x ∈ ys × xs ⊂L ys


⊂L-∷ʳ : ∀ {A} {xs} {x : A} {ys}
  → xs ⊂L ys
  → x ∈ ys
  → (xs ∷ʳ x) ⊂L ys
⊂L-∷ʳ {xs = []} sub-xs elem = elem , tt
⊂L-∷ʳ {xs = x ∷ xs} (elem′ , sub-xs) elem = elem′ , ⊂L-∷ʳ sub-xs elem


_⊆[_]_ : ∀ {A} → Stream A ∞ → Size → Stream A ∞ → Set
xs ⊆[ s ] ys = All (_∈ ys) s xs


_⊆_ : ∀ {A} → Rel (Stream A ∞) _
_⊆_ = _⊆[ ∞ ]_


⊆-head : ∀ {s} {t : Size< s} {A} {xs ys : Stream A ∞}
  → xs ⊆[ s ] ys → head xs ∈ ys
⊆-head sub = proj₁ (inf sub)


⊆-tail : ∀ {s} {t : Size< s} {A} {xs ys : Stream A ∞}
  → xs ⊆[ s ] ys → tail xs ⊆[ t ] ys
⊆-tail sub = proj₂ (inf sub) tt


⊆-fromTail : ∀ {s A} {xs ys : Stream A ∞}
  → xs ⊆[ s ] tail ys → xs ⊆[ s ] ys
⊆-fromTail sub .inf = there (⊆-head sub) , λ _ → ⊆-fromTail (⊆-tail sub)


⊆-refl : ∀ {s A} {xs : Stream A ∞} → xs ⊆[ s ] xs
⊆-refl {xs = xs} .inf = here xs , λ _ → ⊆-fromTail ⊆-refl


module Internal₁ where

  record In (ys : Stream ℕ ∞) : Set where
    constructor build-In
    field
      xs : Stream ℕ ∞
      run : List ℕ
      sub-xs : xs ⊆ ys
      sub-run : run ⊂L ys

  _<<<_ : ∀ {ys ys′} → In ys → In ys′ → Set
  x <<< y = head (In.xs x) < head (In.xs y)

  <<<-wf : ∀ {ys} → WellFounded {A = In ys} _<<<_
  <<<-wf = Inverse-image.wellFounded _ <-wellFounded

  Out : ∀ {ys} → In ys → Stream (List ℕ) ∞
  Out (build-In xs run _ _) = runs′ (xs , run)

  runs′-⊂LF : ∀ ys {t}
    → (x : In ys)
    → (∀ y → All (_⊂L ys) t (Out y))
    → (∀ y → y <<< x → AllWhnf (_⊂L ys) t (Out y))
    → AllWhnf (_⊂L ys) t (Out x)
  runs′-⊂LF ys {t} (build-In xs run sub-xs sub-run) corec rec
      = cast (≡.cong (AllWhnf (_⊂L ys) t) (≡.sym (runs′-unfold xs run))) go
      -- TODO For some reason, the following doesn't work.
      -- rewrite runs′-unfold xs run = go
    where
      sub-run′ : (run ∷ʳ head xs) ⊂L ys
      sub-run′ = ⊂L-∷ʳ sub-run (⊆-head sub-xs)

      sub-tail-xs : tail xs ⊆ ys
      sub-tail-xs = ⊆-tail sub-xs

      go : AllWhnf (_⊂L ys) t (runs′-body (xs , run))
      go with head (tail xs) <? head xs
      ... | yes p = rec (build-In _ _ sub-tail-xs sub-run′) p
      ... | no  _ = sub-run′ , λ _ → corec (build-In _ _ sub-tail-xs tt)


  runs′-⊂L : ∀ ys (x : In ys) → All (_⊂L ys) ∞ (Out x)
  runs′-⊂L ys = Ix.cofixWf <<<-wf (runs′-⊂LF ys)


  runs-⊂L : ∀ xs → All (_⊂L xs) ∞ (runs xs)
  runs-⊂L xs = runs′-⊂L xs (build-In xs [] ⊆-refl tt)

open Internal₁ public using (runs-⊂L)
