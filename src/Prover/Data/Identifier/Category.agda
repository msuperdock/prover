module Prover.Data.Identifier.Category where

open import Prover.Category
  using (Category)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Data.Identifier
  using (Identifier)

-- ## Category

category-identifier
  : Category
category-identifier
  = category-unit Identifier

