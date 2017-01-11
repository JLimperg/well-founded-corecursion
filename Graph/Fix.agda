module Graph.Fix where


open import Data.Product
open import Size

open import Graph.Base
open import Fix
open import Functor


expandF : ∀ {i}
  -> (t : LoopyTreeWf)
  -> (LoopyTreeWf -> Graph i)
  -> ((s : LoopyTreeWf) -> s <<< t -> [ GraphF ] (Graph i))
  -> [ GraphF ] (Graph i)
expandF (mkLoopyTreeWf tip _ _) _ _ = tipP
expandF (mkLoopyTreeWf (branch l r) (branch l-contr r-contr) (branch l-closed r-closed)) expand₁ _
    = branchP (expand₁ (mkLoopyTreeWf l l-contr l-closed)) (expand₁ (mkLoopyTreeWf r r-contr r-closed))
expandF (mkLoopyTreeWf (var _) _ closed) _ _ = Closed-absurd-var closed
expandF t@(mkLoopyTreeWf (nu x s) contr closed) _ expand₂
    = expand₂ (nu-unfold-wf t) (nu-unfold-wf-<<< x s contr closed)


expand : ∀ {i} (t : LoopyTreeWf) -> Graph i
expand = fixν <<<-wf expandF
