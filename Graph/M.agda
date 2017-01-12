module Graph.M where


open import Data.Product
open import Data.Sum

open import Graph.Base
import M

open M.NonIndexed


expandF
  : ∀ {t}
  -> (x : LoopyTreeWf)
  -> (LoopyTreeWf -> GraphM t)
  -> ((y : LoopyTreeWf) -> y <<< x -> ⟦ GraphMF ⟧ (GraphM t))
  -> ⟦ GraphMF ⟧ (GraphM t)
expandF (mkLoopyTreeWf tip _ _) _ _ = tipM
expandF (mkLoopyTreeWf (branch l r) (branch l-contr r-contr) (branch l-closed r-closed)) expand₁ _
    = branchM (expand₁ (mkLoopyTreeWf l l-contr l-closed)) (expand₁ (mkLoopyTreeWf r r-contr r-closed))
expandF (mkLoopyTreeWf (var _) _ closed) _ _ = Closed-absurd-var closed
expandF t@(mkLoopyTreeWf (nu x t₁) contr closed) _ expand₂
    = expand₂ (nu-unfold-wf t) (nu-unfold-wf-<<< x t₁ contr closed)


expand : ∀ {s} -> LoopyTreeWf -> GraphM s
expand = fixM <<<-wf expandF
