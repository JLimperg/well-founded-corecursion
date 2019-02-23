module Graph.Base where


open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Function
open import Induction
open import Induction.Nat
open import Induction.WellFounded
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Size

open import Graph.List
open import Coinduction.WellFounded


-- LoopyTree data type and operations


Var : Set
Var = ℕ


data LoopyTree : Set where
  tip : LoopyTree
  branch : (l r : LoopyTree) → LoopyTree
  var : (x : Var) → LoopyTree
  nu : (x : Var) → (t : LoopyTree) → LoopyTree


_[_⇒_] : LoopyTree → Var → LoopyTree → LoopyTree
tip [ x ⇒ s ] = tip
branch l r [ x ⇒ s ] = branch (l [ x ⇒ s ]) (r [ x ⇒ s ])
var x [ y ⇒ s ] with x ≟ y
... | yes _ = s
... | no _ = var x
nu x t [ y ⇒ s ] with x ≟ y
... | yes _ = nu x t
... | no _ = nu x (t [ y ⇒ s ])


var? : (t : LoopyTree) → Dec (Σ[ x ∈ Var ] (t ≡ var x))
var? tip = no (λ { (_ , ()) })
var? (branch t t₁) = no (λ { (_ , ()) })
var? (var x) = yes (x , refl)
var? (nu x t) = no (λ { (_ , ()) })


nu-unfold : LoopyTree → LoopyTree
nu-unfold (nu x t) = t [ x ⇒ nu x t ]
nu-unfold t = t


subst-preserves-not-var : ∀ {t x s}
  → False (var? t)
  → False (var? (t [ x ⇒ s ]))
subst-preserves-not-var {tip} t-novar = _
subst-preserves-not-var {branch l r} t-novar = _
subst-preserves-not-var {var x} ()
subst-preserves-not-var {nu x t} {y} with x ≟ y
... | yes _ = _
... | no _ = _


-- Contractiveness


data Contractive : LoopyTree → Set where
  tip : Contractive tip
  branch : ∀ {l r} → Contractive l → Contractive r → Contractive (branch l r)
  var : ∀ x → Contractive (var x)
  nu : ∀ {x t} → False (var? t) → Contractive t → Contractive (nu x t)


subst-preserves-Contractive : ∀ {t x s}
  → Contractive t
  → Contractive s
  → Contractive (t [ x ⇒ s ])
subst-preserves-Contractive {tip} contr-t contr-s = tip
subst-preserves-Contractive {branch l r} (branch contr-l contr-r) contr-s
    = branch
       (subst-preserves-Contractive contr-l contr-s)
       (subst-preserves-Contractive contr-r contr-s)
subst-preserves-Contractive {var x} {y} contr-t contr-s with x ≟ y
... | yes _ = contr-s
... | no _ = var x
subst-preserves-Contractive {nu x t} {y} nuxt-contr@(nu t-novar t-contr) s-contr
  with x ≟ y
... | yes eq = nuxt-contr
... | no neq
    = nu
        (subst-preserves-not-var t-novar)
        (subst-preserves-Contractive t-contr s-contr)


nu-unfold-contractive : ∀ {t} → Contractive t → Contractive (nu-unfold t)
nu-unfold-contractive c@tip = c
nu-unfold-contractive c@(branch _ _) = c
nu-unfold-contractive c@(var _) = c
nu-unfold-contractive c@(nu _ c') = subst-preserves-Contractive c' c


-- Closedness


data ClosedWrt : List Var → LoopyTree → Set where
  tip : ∀ {xs} → ClosedWrt xs tip
  branch : ∀ {xs l r}
    → ClosedWrt xs l
    → ClosedWrt xs r
    → ClosedWrt xs (branch l r)
  var : ∀ {xs x} → x ∈ xs → ClosedWrt xs (var x)
  nu : ∀ {xs x t} → ClosedWrt (x ∷ xs) t → ClosedWrt xs (nu x t)


Closed : LoopyTree → Set
Closed = ClosedWrt []


Closed-absurd-var : ∀ {a} {A : Set a} {x} → Closed (var x) → A
Closed-absurd-var (var ())


ClosedWrt-⊆ : ∀ {xs ys t} → xs ⊆ ys → ClosedWrt xs t → ClosedWrt ys t
ClosedWrt-⊆ _ tip = tip
ClosedWrt-⊆ sub (branch l r) = branch (ClosedWrt-⊆ sub l) (ClosedWrt-⊆ sub r)
ClosedWrt-⊆ sub (var elem) = var (sub elem)
ClosedWrt-⊆ sub (nu cl) = nu (ClosedWrt-⊆ (∷-⊆ sub) cl)


Closed-subst : ∀ {xs x t s}
  → ClosedWrt (x ∷ xs) t
  → ClosedWrt xs s
  → ClosedWrt xs (t [ x ⇒ s ])
Closed-subst tip _ = tip
Closed-subst (branch l r) s-closed
    = branch (Closed-subst l s-closed) (Closed-subst r s-closed)
Closed-subst {x = y} (var {x = x} elem) s-closed with x ≟ y | elem
... | yes x≡y | _ rewrite x≡y = s-closed
... | no x≢y | here x≡y = ⊥-elim (x≢y x≡y)
... | no x≢y | there elem' = var elem'
Closed-subst {x = y} (nu {xs} {x} {t} cl) s-closed with x ≟ y
... | yes x≡y rewrite x≡y = nu (ClosedWrt-⊆ ⊆-duplicate cl)
... | no x≢y
    = nu (Closed-subst (ClosedWrt-⊆ ⊆-swap cl) (ClosedWrt-⊆ there s-closed))


nu-unfold-closed : ∀ {t} → Closed t → Closed (nu-unfold t)
nu-unfold-closed tip = tip
nu-unfold-closed cl@(branch _ _) = cl
nu-unfold-closed cl@(var _) = cl
nu-unfold-closed (nu cl) = Closed-subst cl (nu cl)


-- Nu Prefix length


nu-prefix-length : LoopyTree → ℕ
nu-prefix-length (nu x t) = 1 + nu-prefix-length t
nu-prefix-length _ = 0


subst-preserves-nu-prefix-length : ∀ t x s
  → Contractive t
  → False (var? t)
  → nu-prefix-length (t [ x ⇒ s ]) ≡ nu-prefix-length t
subst-preserves-nu-prefix-length tip _ _ _ _ = refl
subst-preserves-nu-prefix-length (branch _ _) _ _ _ _ = refl
subst-preserves-nu-prefix-length (var _) _ _ _ ()
subst-preserves-nu-prefix-length (nu x t) y s (nu t-novar t-contr) _ with x ≟ y
... | yes eq = refl
... | no _ rewrite subst-preserves-nu-prefix-length t y s t-contr t-novar = refl


-- Wellformed LoopyTrees and operations


record LoopyTreeWf : Set where
  constructor mkLoopyTreeWf
  field
    tree : LoopyTree
    contractive : Contractive tree
    closed : Closed tree


map-LoopyTreeWf
  : (f : LoopyTree → LoopyTree)
  → (∀ {t} → Contractive t → Contractive (f t))
  → (∀ {t} → Closed t → Closed (f t))
  → LoopyTreeWf
  → LoopyTreeWf
map-LoopyTreeWf f f-contr f-closed t
    = mkLoopyTreeWf (f tree) (f-contr contractive) (f-closed closed)
  where
    open LoopyTreeWf t


_<<<_ : Rel LoopyTreeWf lzero
_<<<_ = _<_ on nu-prefix-length ∘ LoopyTreeWf.tree


<<<-wf : WellFounded _<<<_
<<<-wf = Inverse-image.wellFounded _ <-wellFounded


nu-unfold-wf : LoopyTreeWf → LoopyTreeWf
nu-unfold-wf = map-LoopyTreeWf nu-unfold nu-unfold-contractive nu-unfold-closed


nu-unfold-wf-<<< : ∀ x t contr closed
  → let t' = (mkLoopyTreeWf (nu x t) contr closed)
    in nu-unfold-wf t' <<< t'
nu-unfold-wf-<<< x t (nu novar contr) closed
    rewrite subst-preserves-nu-prefix-length t x (nu x t) contr novar
    = ≤-refl


-- Graphs directly


data GraphF (A : Set) : Set where
  tip : GraphF A
  branch : A → A → GraphF A


record Graph (s : Size) : Set where
  coinductive
  field
    force : ∀ {t : Size< s} → GraphF (Graph t)


fmap-GraphF : ∀ {A B} → (A → B) → GraphF A → GraphF B
fmap-GraphF f tip = tip
fmap-GraphF f (branch l r) = branch (f l) (f r)


-- Graphs via M-types


GraphMF : Container _ _
GraphMF = Shape ▷ Position
  module _ where
    data Shape : Set where
      tip branch : Shape

    Position : Shape → Set
    Position tip = ⊥
    Position branch = ⊤ ⊎ ⊤


GraphM : Size → Set
GraphM = M GraphMF


tipM : ∀ {A : Set} → ⟦ GraphMF ⟧ A
tipM = tip , λ()


branchM : ∀ {A : Set} → A → A → ⟦ GraphMF ⟧ A
branchM l r
    = branch ,
      λ where
        (inj₁ _) → l
        (inj₂ _) → r
