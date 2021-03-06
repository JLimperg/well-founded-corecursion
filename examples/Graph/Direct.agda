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

expand'F :
  (t : LoopyTreeWf)
  → ((s : LoopyTreeWf) → s <<< t → GraphF LoopyTreeWf)
  → GraphF LoopyTreeWf
expand'F (mkLoopyTreeWf tip _ _) _ = tip
expand'F (mkLoopyTreeWf (branch l r)
  (branch l-contr r-contr)
  (branch l-closed r-closed)) _
    = branch
        (mkLoopyTreeWf l l-contr l-closed)
        (mkLoopyTreeWf r r-contr r-closed)
expand'F (mkLoopyTreeWf (var _) _ closed) _ = Closed-absurd-var closed
expand'F t@(mkLoopyTreeWf (nu x s) contr closed) expand'
    = expand' (nu-unfold-wf t) (nu-unfold-wf-<<< x s contr closed)


expand' : LoopyTreeWf → GraphF LoopyTreeWf
expand' = All.wfRec <<<-wf lzero (λ _ → _) expand'F


expand : ∀ {i} → LoopyTreeWf → Graph i
expand t .Graph.force = fmap-GraphF expand (expand' t)
