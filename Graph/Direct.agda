module Graph.Direct where


open import Data.Container using () renaming (map to fmap)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Induction.WellFounded
open import Level renaming (zero to lzero ; suc to lsuc)
open import Size

open import Graph.Base
import M

open M.NonIndexed


expand'F :
  ∀ (t : LoopyTreeWf)
  -> ((s : LoopyTreeWf) -> s <<< t -> ⟦ GraphMF ⟧ LoopyTreeWf)
  -> ⟦ GraphMF ⟧ LoopyTreeWf
expand'F (mkLoopyTreeWf tip _ _) _ = tipM
expand'F (mkLoopyTreeWf (branch l r) (branch l-contr r-contr) (branch l-closed r-closed)) _
    = branchM (mkLoopyTreeWf l l-contr l-closed) (mkLoopyTreeWf r r-contr r-closed)
expand'F (mkLoopyTreeWf (var _) _ closed) _ = Closed-absurd-var closed
expand'F t@(mkLoopyTreeWf (nu x s) contr closed) expand'
    = expand' (nu-unfold-wf t) (nu-unfold-wf-<<< x s contr closed)


expand' : LoopyTreeWf -> ⟦ GraphMF ⟧ LoopyTreeWf
expand' = All.wfRec <<<-wf lzero (λ _ ->  _) expand'F


expand : ∀ {i} -> LoopyTreeWf -> GraphM i
expand t .M.inf = fmap expand (expand' t) 
