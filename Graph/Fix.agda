module Graph.Fix where


open import Data.Product
open import Size

open import Graph.Base
open import Fix
open import Functor


expandF : ∀ {i}
  -> (t : expand-input)
  -> (expand-input -> Graph i)
  -> ((s : expand-input) -> s <<< t -> [ GraphF ] (Graph i))
  -> [ GraphF ] (Graph i)
expandF (tip , p) expand₁ expand₂ = tipP
expandF (branch l r , (branch contr-l contr-r , closed)) expand₁ expand₂
    = let closed-l , closed-r = Closed-branch-inv l r closed in
      branchP (expand₁ (l , contr-l , closed-l)) (expand₁ (r , contr-r , closed-r))
expandF (var x , (_ , closed)) expand₁ expand₂ = Closed-absurd-var closed
expandF t@(nu x s , contr , closed) expand₁ expand₂
    = expand₂ (nu-unfold' t) (nu-unfold'-<<< x s contr closed)


expand : ∀ {i} (t : expand-input) -> Graph i
expand = fixν <<<-wf expandF
