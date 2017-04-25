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
  ; ≅M⇒≡
  ; cofix
  ; cofix-unfold
  ; fixM
  ; fixM-unfold
  ; fixM-unfold′
  )
