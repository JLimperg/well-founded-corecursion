module Coinduction.WellFounded.Indexed where

open import Data.Container.Indexed public using
  ( Container
  ; _◃_/_
  ; ⟦_⟧
  )

open import Coinduction.WellFounded.Indexed.Internal public using
  ( M
  ; inf
  ; ≅F-setoid
  ; ≅M-setoid
  ; _≅F_
  ; ≅F⇒≅
  ; _≅M_
  ; M-Extensionality
  ; ≅M⇒≅
  ; cofix
  ; cofix-unfold
  ; cofixWf
  ; cofixWf-unfold
  ; cofixWf-unfold′
  )
