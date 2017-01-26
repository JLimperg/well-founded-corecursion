module Generic where


open import Category.Monad
open import Data.List
open import Data.String
open import Data.Unit
open import Induction.WellFounded
open import Level
open import Reflection
open import Relation.Binary
open import Size


private
  instance TC-Monad : ∀ {f} → RawMonad {f} TC
  TC-Monad = record { return = returnTC ; _>>=_ = bindTC }


  open RawMonad {{...}}


  arg' : ∀ {A} → A → Arg A
  arg' = arg (arg-info visible relevant)


  argH : ∀ {A} → A → Arg A
  argH = arg (arg-info hidden relevant)


fixG
  : Name {- single record field -}
  → Name {- function name -}
  → TC ⊤
fixG force fix
    = defineFun fix
      [ clause
          ( arg' (var "<-wf") {- 0 -}
          ∷ arg' (var "F") {- 1 -}
          ∷ arg' (var "x") {- 2 -}
          ∷ arg' (con (quote acc) [ arg' (var "rs") ]) {- 3 -}
          ∷ arg' (proj force)
          ∷ [])
          (var 2
            ( arg' (var 1 [])
            ∷ arg' (lam visible (abs "y"
                (def fix
                  ( arg' (var 4 [])
                  ∷ arg' (var 3 [])
                  ∷ arg' (var 0 [])
                  ∷ arg' (var 4 [ arg' (var 0 []) ])
                  ∷ []))))
            ∷ arg' ((lam visible (abs "y" (lam visible (abs "y<x"
                (def force
                  [ arg' (def fix
                      ( arg' (var 5 [])
                      ∷ arg' (var 4 [])
                      ∷ arg' (var 1 [])
                      ∷ arg' (var 2
                          ( arg' (var 1 [])
                          ∷ arg' (var 0 [])
                          ∷ []))
                      ∷ []))
                  ]))))))
            ∷ []))
      ]


data Graph : Size → Set
record Graph∞ Size : Set


data Graph where
  tip : ∀ {s} → Graph s
  branch : ∀ {s} → Graph∞ s → Graph∞ s → Graph s


record Graph∞ (s : Size) where
  coinductive
  field
    force : ∀ {t : Size< s} → Graph t

open Graph∞


fixGraph' : ∀ {lin l<} {In : Set lin} {_<_ : Rel In l<}
  → (<-wf : Well-founded _<_)
  → (F : ∀ {t}
      → (x : In)
      → (In → Graph∞ t)
      → ((y : In) → y < x → Graph t)
      → Graph t)
  → ∀ {s}
  → (x : In)
  → Acc _<_ x
  → Graph∞ s

unquoteDef fixGraph' = fixG (quote force) fixGraph'
