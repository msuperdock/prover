module Prover.Data.Variables.Category where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; chain₁-category)
open import Prover.Category.Collection.Unit
  using (category-collection-unit)
open import Prover.Data.Variable
  using (Variable)
open import Prover.Prelude

-- ## Category

category-variables
  : Category
category-variables
  = category-collection-unit (Equal Variable)

module CategoryVariables
  = Category category-variables

-- ## ChainCategory

chain-category-variables
  : ChainCategory (suc zero)
chain-category-variables
  = chain₁-category category-variables

