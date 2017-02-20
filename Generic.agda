module Generic where


open import Category.Monad using (RawMonad)
open import Data.List
open import Data.String using (String)
open import Data.Unit
open import Induction.WellFounded using (Well-founded ; Acc ; acc)
open import Level using (Level)
open import Reflection
open import Relation.Binary using (Rel)
open import Size using (Size ; Size<_)


private
  instance TC-Monad : ∀ {f} → RawMonad {f} TC
  TC-Monad = record { return = returnTC ; _>>=_ = bindTC }


  open RawMonad {{...}}


  arg' : ∀ {A} → A → Arg A
  arg' = arg (arg-info visible relevant)


  argH : ∀ {A} → A → Arg A
  argH = arg (arg-info hidden relevant)


  lam' : String → Term → Term
  lam' s t = lam visible (abs s t)


  piH : String → Term → Term
  piH s t = pi (argH unknown) (abs s t)


fixGtype : ∀ {li lc}
  → (la l< : Level) → (Size → Set li) → (Size → Set lc) → Set _
fixGtype la l< Ind Coind
    = ∀ {A : Set la} {_<_ : Rel A l<}
      → (<-wf : Well-founded _<_)
      → (F : ∀ {t}
          → (x : A)
          → (A → Coind t)
          → (∀ y → y < x → Ind t)
          → Ind t)
      → ∀ {s}
      → (x : A)
      → Acc _<_ x
      → Coind s


fixG : ∀ {li lc}
  → (Size → Set li) {- inductive type -}
  → (Size → Set lc) {- coinductive record -}
  → Name            {- single record field -}
  → Name            {- function name -}
  → TC ⊤
fixG Ind Coind force fix
    = quoteTC Ind >>= λ Ind →
      quoteTC Coind >>= λ Coind →
      declareDef (arg' fix) (type Ind Coind) >>
      defineFun fix
        [ clause
            ( arg' (var "<-wf")
            ∷ arg' (var "F")
            ∷ arg' (var "x")
            ∷ arg' (con (quote acc) [ arg' (var "rs") ])
            ∷ arg' (proj force)
            ∷ [])
            (var 2
              ( arg' (var 1 [])
              ∷ arg' (lam' "y"
                  (def fix
                    ( arg' (var 4 [])                  {- <-wf -}
                    ∷ arg' (var 3 [])                  {- F -}
                    ∷ arg' (var 0 [])                  {- y -}
                    ∷ arg' (var 4 [ arg' (var 0 []) ]) {- <-wf y -}
                    ∷ [])))
              ∷ arg' ((lam' "y" (lam' "y<x"
                  (def force
                    [ arg' (def fix
                        ( arg' (var 5 [])     {- <-wf -}
                        ∷ arg' (var 4 [])     {- F -}
                        ∷ arg' (var 1 [])     {- y -}
                        ∷ arg' (var 2         {- rs -}
                            ( arg' (var 1 []) {- y -}
                            ∷ arg' (var 0 []) {- y<x -}
                            ∷ []))
                        ∷ []))
                    ]))))
              ∷ []))
        ]
  where
    type : Term → Term → Type
    type Ind Coind
        = piH "la" (piH  "l<"
            (def (quote fixGtype)
              ( arg' (var 1 [])
              ∷ arg' (var 0 [])
              ∷ arg' Ind
              ∷ arg' Coind
              ∷ [])))


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


unquoteDecl fixGraph = fixG Graph Graph∞ (quote force) fixGraph

{-
fixGraph : ∀ {la l<} → fixGtype la l< Graph Graph∞

fixGraph : ∀ {la l<} {A : Set la} {_<_ : Rel A l<}
  → Well-founded _<_
  → (∀ {t}
     → (x : A)
     → (A → Graph∞ t)
     → (∀ y → y < x → Graph t)
     → Graph t)
  → ∀ {s}
  → (x : A)
  → Acc _<_ x
  → Graph∞ s
-}


data GraphF (Graph : Set) : Set where
  tip : GraphF Graph
  branch : Graph → Graph → GraphF Graph


record Graph′ (s : Size) : Set where
  coinductive
  field
    force′ : ∀ {t : Size< s} → GraphF (Graph′ t)

open Graph′


unquoteDecl fixGraph′
    = fixG (λ s → GraphF (Graph′ s)) Graph′ (quote force′) fixGraph′

{-
fixGraph′ : ∀ {la l<} → fixGtype la l< (λ s → GraphF (Graph′ s)) Graph′

fixGraph′ : ∀ {la l<} {A : Set la} {_<_ : Rel A l<}
  → Well-founded _<_
  → (∀ {t}
     → (x : A)
     → (A → Graph′ t)
     → (∀ y → y < x → GraphF (Graph′ t))
     → GraphF (Graph′ t))
  → ∀ {s}
  → (x : A)
  → Acc _<_ x
  → Graph′ s
-}
