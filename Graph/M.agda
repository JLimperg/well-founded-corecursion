module Graph.M where


open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

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
expandF (mkLoopyTreeWf (branch l r)
  (branch l-contr r-contr)
  (branch l-closed r-closed))
  expand₁ _
    = branchM
        (expand₁ (mkLoopyTreeWf l l-contr l-closed))
        (expand₁ (mkLoopyTreeWf r r-contr r-closed))
expandF (mkLoopyTreeWf (var _) _ (var ()))
expandF t@(mkLoopyTreeWf (nu x t₁) contr closed) _ expand₂
    = expand₂ (nu-unfold-wf t) (nu-unfold-wf-<<< x t₁ contr closed)


expand : ∀ {s} -> LoopyTreeWf -> GraphM s
expand = fixM <<<-wf expandF


expandF-ext : ∀ x {corec corec' rec rec'}
  → (∀ y → corec y ≡ corec' y)
  → (∀ y y<x → rec y y<x ≡ rec' y y<x)
  → expandF x corec rec ≡ expandF x corec' rec'
expandF-ext (mkLoopyTreeWf tip contractive closed) eq-corec eq-rec = refl
expandF-ext
  (mkLoopyTreeWf (branch tree tree₁)
  (branch contractive contractive₁)
  (branch closed closed₁))
  eq-corec eq-rec
  rewrite eq-corec (mkLoopyTreeWf tree contractive closed)
  |       eq-corec (mkLoopyTreeWf tree₁ contractive₁ closed₁)
  = refl
expandF-ext (mkLoopyTreeWf (var x) contractive (var ()))
expandF-ext t@(mkLoopyTreeWf (nu x tree) contractive closed) eq-corec eq-rec
  rewrite eq-rec (nu-unfold-wf t) (nu-unfold-wf-<<< x tree contractive closed)
  = refl


expand-unfold : ∀ x → inf (expand x) ≡ expandF x expand (λ y _ → inf (expand y))
expand-unfold = fixM-unfold <<<-wf expandF expandF-ext
