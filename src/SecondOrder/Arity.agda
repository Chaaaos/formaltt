open import Agda.Primitive using (lzero; lsuc; _⊔_)

module SecondOrder.Arity where

  -- We work over a given notion of arity
  record Arity : Set₁ where
    field
      arity : Set -- the set of permissible arities, e.g., ℕ for finitary arities
      arg : arity → Set -- every arity gives a set of argument (position), e.g. Fin
