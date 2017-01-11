module Graph.M where


open import Data.Product
open import Data.Sum

open import Graph.Base
open import M


expandF
  : ∀ {t}
  -> (x : expand-input)
  -> (expand-input -> GraphM t)
  -> ((y : expand-input) -> y <<< x -> Σ[ a ∈ GraphMA ] (GraphMB a -> GraphM t))
  -> Σ[ a ∈ GraphMA ] (GraphMB a -> GraphM t)
expandF (tip , t-contr , t-closed) expand₁ expand₂ = tip , λ()
expandF (branch l r , branch l-contr r-contr , t-closed) expand₁ expand₂
    = let l-closed , r-closed = Closed-branch-inv l r t-closed in
      branch ,
      λ where
        (inj₁ _) -> expand₁ (l , l-contr , l-closed)
        (inj₂ _) -> expand₁ (r , r-contr , r-closed)
expandF (var x , t-contr , t-closed) expand₁ expand₂ = Closed-absurd-var t-closed
expandF t@(nu x t₁ , t-contr , t-closed) expand₁ expand₂
    = expand₂ (nu-unfold' t) (nu-unfold'-<<< x t₁ t-contr t-closed)


expand : ∀ {s} -> expand-input -> GraphM s
expand = fixM <<<-wf expandF
