module 01-Prelude where

open import Agda.Primitive public
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to UU)

variable i j k l : Level
