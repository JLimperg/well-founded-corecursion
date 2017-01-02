module Graph.Direct where


open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Induction.WellFounded
open import Level renaming (zero to lzero ; suc to lsuc)
open import Size

open import Graph.Base
open import Functor


expand'F :
  ∀ (t : expand-input)
  -> ((s : expand-input) -> s <<< t -> [ GraphF ] expand-input)
  -> [ GraphF ] expand-input
expand'F (tip , _) _ = tipP
expand'F (branch l r , branch contr-l contr-r , closed) _
    = let closed-l , closed-r = Closed-branch-inv _ _ closed
      in branchP (l , contr-l , closed-l) (r , contr-r , closed-r)
expand'F (var _ , _ , closed) _ = ⊥-elim (Closed-absurd-var closed)
expand'F t@(nu x s , contr , closed) expand' = expand' (nu-unfold' t) (nu-unfold'-<<< x s contr closed)


expand' : expand-input -> [ GraphF ] expand-input
expand' = All.wfRec <<<-wf lzero (λ _ ->  _) expand'F


expand : ∀ {i} -> expand-input -> Graph i
unν (expand t) = fmap GraphF expand (expand' t)
