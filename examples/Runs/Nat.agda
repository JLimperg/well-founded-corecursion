module Runs.Nat where

open import Data.Nat public
open import Relation.Nullary using (yes ; no)
open import Relation.Binary using (Decidable)


_<?_ : Decidable _<_
zero <? zero = no (λ ())
zero <? suc _ = yes (s≤s z≤n)
suc x <? zero = no (λ ())
suc x <? suc y with x <? y
... | yes p = yes (s≤s p)
... | no ¬p = no λ { (s≤s contra) → ¬p contra }
