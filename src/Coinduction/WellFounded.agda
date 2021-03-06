module Coinduction.WellFounded where

open import Data.Container public using
  ( Container
  ; _▷_
  ; ⟦_⟧
  )

open import Coinduction.WellFounded.Internal public using
  ( M
  ; inf
  ; ≅F-setoid
  ; _≅F_
  ; ≅F⇒≡
  ; ≅M-setoid
  ; _≅M_
  ; M-Extensionality
  ; M-Extensionality-from-Ix
  ; ≅M⇒≡
  ; cofix
  ; cofix-unfold
  ; cofixWf
  ; cofixWf-unfold
  ; cofixWf-unfold′
  )
