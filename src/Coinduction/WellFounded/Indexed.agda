module Coinduction.WellFounded.Indexed where

open import Coinduction.WellFounded.Internal.Container public using
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
  ; fixM
  ; fixM-unfold
  ; fixM-unfold′
  )
