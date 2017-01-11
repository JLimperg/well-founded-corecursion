module Graph.M where


open import Data.Product
open import Data.Sum

open import Graph.Base
open import M


expandF
  : ∀ {t}
  -> (x : LoopyTreeWf)
  -> (LoopyTreeWf -> GraphM t)
  -> ((y : LoopyTreeWf) -> y <<< x -> Σ[ a ∈ GraphMA ] (GraphMB a -> GraphM t))
  -> Σ[ a ∈ GraphMA ] (GraphMB a -> GraphM t)
expandF (mkLoopyTreeWf tip _ _) _ _ = tip , λ()
expandF (mkLoopyTreeWf (branch l r) contr closed) expand₁ _
    = let l' , r' = branch-inv-wf contr closed in
      branch ,
      λ where
        (inj₁ _) -> expand₁ l'
        (inj₂ _) -> expand₁ r'
expandF (mkLoopyTreeWf (var _) _ closed) _ _ = Closed-absurd-var closed
expandF t@(mkLoopyTreeWf (nu x t₁) contr closed) _ expand₂
    = expand₂ (nu-unfold-wf t) (nu-unfold-wf-<<< x t₁ contr closed)


expand : ∀ {s} -> LoopyTreeWf -> GraphM s
expand = fixM <<<-wf expandF
