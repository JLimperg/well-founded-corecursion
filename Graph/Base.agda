module Graph.Base where


open import Data.Empty
open import Data.Nat
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

open import Functor


Var : Set
Var = ℕ


data LoopyTree : Set where
  tip : LoopyTree
  branch : (l r : LoopyTree) -> LoopyTree
  var : (x : Var) -> LoopyTree
  nu : (x : Var) -> (t : LoopyTree) -> LoopyTree


var? : (t : LoopyTree) -> Dec (Σ[ x ∈ Var ] (t ≡ var x))
var? tip = no (λ { (_ , ()) })
var? (branch t t₁) = no (λ { (_ , ()) })
var? (var x) = yes (x , refl)
var? (nu x t) = no (λ { (_ , ()) })


data Contractive : LoopyTree -> Set where
  tip : Contractive tip
  branch : ∀ {l r} -> Contractive l -> Contractive r -> Contractive (branch l r)
  var : ∀ x -> Contractive (var x)
  nu : ∀ {x t} -> False (var? t) -> Contractive t -> Contractive (nu x t)


Contractive? : (t : LoopyTree) -> Dec (Contractive t)
Contractive? tip = yes tip
Contractive? (branch l r) with Contractive? l | Contractive? r
... | yes c-l | yes c-r = yes (branch c-l c-r)
... | no c-l | _ = no λ { (branch c-l' _) -> c-l c-l'}
... | _ | no c-r = no λ { (branch _ c-r') -> c-r c-r'}
Contractive? (var x) = yes (var x)
Contractive? (nu x t) with var? t | Contractive? t
... | yes (y , eq) | _ rewrite eq = no (λ {(nu contra _) → contra})
... | no t-novar | yes t-contr = yes (nu (fromWitnessFalse t-novar) t-contr)
... | no _ | no t-nocontr = no (λ { (nu _ t-contr) -> t-nocontr t-contr })


data Free : Var -> LoopyTree -> Set where
  branch : ∀ {x l r} -> Free x l ⊎ Free x r -> Free x (branch l r)
  var : ∀ {x} -> Free x (var x)
  nu : ∀ {x y t} -> x ≢ y -> Free x t -> Free x (nu y t)


Free? : (x : Var) -> (t : LoopyTree) -> Dec (Free x t)
Free? x tip = no λ()
Free? x (branch l r) with Free? x l | Free? x r
... | yes l! | _ = yes (branch (inj₁ l!))
... | _ | yes r! = yes (branch (inj₂ r!))
... | no l! | no r! = no λ { (branch (inj₁ l!!)) -> l! l!! ; (branch (inj₂ r!!)) -> r! r!! }
Free? x (var y) with x ≟ y
... | yes eq rewrite eq = yes var
... | no neq = no λ { var -> neq refl }
Free? x (nu y t) with x ≟ y | Free? x t
... | yes x≡y | _ = no λ { (nu x≢y _) -> x≢y x≡y }
... | _ | no unfree = no λ { (nu _ free) -> unfree free }
... | no x≢y | yes free = yes (nu x≢y free)


Closed : LoopyTree -> Set
Closed t = ∀ x -> ¬ Free x t


_[_⇒_] : LoopyTree -> Var -> LoopyTree -> LoopyTree
tip [ x ⇒ s ] = tip
branch l r [ x ⇒ s ] = branch (l [ x ⇒ s ]) (r [ x ⇒ s ])
var x [ y ⇒ s ] with x ≟ y
... | yes _ = s
... | no _ = var x
nu x t [ y ⇒ s ] with x ≟ y
... | yes _ = nu x t
... | no _ = nu x (t [ y ⇒ s ])


nu-unfold : LoopyTree -> LoopyTree
nu-unfold (nu x t) = t [ x ⇒ nu x t ]
nu-unfold t = t


nu-prefix-length : LoopyTree -> ℕ
nu-prefix-length (nu x t) = 1 + nu-prefix-length t
nu-prefix-length _ = 0


subst-preserves-nu-prefix-length : ∀ t x s
  -> Contractive t
  -> False (var? t)
  -> nu-prefix-length (t [ x ⇒ s ]) ≡ nu-prefix-length t
subst-preserves-nu-prefix-length tip _ _ _ _ = refl
subst-preserves-nu-prefix-length (branch _ _) _ _ _ _ = refl
subst-preserves-nu-prefix-length (var _) _ _ _ ()
subst-preserves-nu-prefix-length (nu x t) y s (nu t-novar t-contr) _ with x ≟ y
... | yes eq = refl
... | no neq rewrite subst-preserves-nu-prefix-length t y s t-contr t-novar = refl


subst-preserves-not-var : ∀ {t x s}
  -> False (var? t)
  -> False (var? (t [ x ⇒ s ]))
subst-preserves-not-var {tip} t-novar = _
subst-preserves-not-var {branch l r} t-novar = _
subst-preserves-not-var {var x} ()
subst-preserves-not-var {nu x t} {y} with x ≟ y 
... | yes _ = _
... | no _ = _


subst-preserves-Contractive : ∀ {t x s}
  -> Contractive t
  -> Contractive s
  -> Contractive (t [ x ⇒ s ])
subst-preserves-Contractive {tip} contr-t contr-s = tip
subst-preserves-Contractive {branch l r} (branch contr-l contr-r) contr-s
    = branch (subst-preserves-Contractive contr-l contr-s) (subst-preserves-Contractive contr-r contr-s)
subst-preserves-Contractive {var x} {y} contr-t contr-s with x ≟ y
... | yes _ = contr-s
... | no _ = var x
subst-preserves-Contractive {nu x t} {y} nu-x-t-contr@(nu t-novar t-contr) s-contr with x ≟ y
... | yes eq = nu-x-t-contr
... | no neq = nu (subst-preserves-not-var t-novar) (subst-preserves-Contractive t-contr s-contr)


GraphF : Functor
GraphF = (|K| ⊤) |+| (|Id| |×| |Id|)


Graph : Size -> Set
Graph i = ν GraphF i


pattern tipP = inj₁ tt

tipG : ∀ {i} -> Graph i
unν tipG = tipP


pattern branchP l r = inj₂ (l , r)

branchG : ∀ {i} -> Graph i -> Graph i -> Graph (↑ i)
unν (branchG l r) = branchP l r


expand-input : Set
expand-input = Σ[ t ∈ LoopyTree ] (Contractive t × Closed t)


_<<<_ : Rel expand-input lzero
_<<<_ = _<′_ on nu-prefix-length ∘ proj₁


<<<-wf : Well-founded _<<<_
<<<-wf = Inverse-image.well-founded _ <-well-founded


Closed-absurd-var : ∀ {a} {A : Set a} {x} -> Closed (var x) -> A
Closed-absurd-var {x = x} cl = ⊥-elim (cl x var)


Closed-branch-inv : ∀ l r -> Closed (branch l r) -> Closed l × Closed r
Closed-branch-inv l r cl = (λ x xfree -> cl x (branch (inj₁ xfree))) , (λ x xfree -> cl x (branch (inj₂ xfree)))


Free-subst-inv : ∀ x t y s
  -> Free x (t [ y ⇒ s ])
  -> Free x s ⊎ (x ≢ y × Free x t)

Free-subst-inv _ tip _ _ ()

Free-subst-inv x (branch l r) y s (branch (inj₁ hyp)) with Free-subst-inv x l y s hyp
... | (inj₁ hyp') = inj₁ hyp'
... | (inj₂ (hyp₁ , hyp₂)) = inj₂ (hyp₁ , branch (inj₁ hyp₂))
Free-subst-inv x (branch l r) y s (branch (inj₂ hyp)) with Free-subst-inv x r y s hyp
... | (inj₁ hyp') = inj₁ hyp'
... | (inj₂ (hyp₁ , hyp₂)) = inj₂ (hyp₁ , branch (inj₂ hyp₂))

Free-subst-inv x (var v) y s hyp with v ≟ y
... | yes v≡y rewrite v≡y = inj₁ hyp
Free-subst-inv x (var v) y s var | no v≢y = inj₂ (v≢y , var)

Free-subst-inv x (nu v t) y s hyp with v ≟ y
Free-subst-inv x (nu v t) y s (nu x≢y free) | yes v≡y rewrite v≡y = inj₂ (x≢y , nu x≢y free)
Free-subst-inv x (nu v t) y s (nu x≢v free) | no v≢y with Free-subst-inv x t y s free
... | inj₁ free' = inj₁ free'
... | inj₂ (x≢y , free') = inj₂ (x≢y , nu x≢v free')


Closed-nu : ∀ {t x} -> Closed (nu x t) -> Closed (t [ x ⇒ nu x t ])
Closed-nu {t} {x} cl y free with Free-subst-inv y t x (nu x t) free
... | inj₁ free' = cl y free'
... | inj₂ (eq , free') = cl y (nu eq free')


nu-unfold' : expand-input -> expand-input
nu-unfold' (nu x t , nu-x-t-contr@(nu t-novar t-contr) , closed)
    = nu-unfold (nu x t) , subst-preserves-Contractive t-contr nu-x-t-contr , Closed-nu closed
nu-unfold' (t , contr , closed) = (t , contr , closed)


nu-unfold'-<<< : ∀ x t contr closed -> nu-unfold' (nu x t , contr , closed) <<< (nu x t , contr , closed)
nu-unfold'-<<< x t (nu t-novar t-contr) closed
  rewrite subst-preserves-nu-prefix-length t x (nu x t) t-contr t-novar
  = ≤′-refl
