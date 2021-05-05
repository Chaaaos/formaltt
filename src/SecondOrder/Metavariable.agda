open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Signature

module SecondOrder.Metavariable
  {ℓs ℓo}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓs ℓo 𝔸)
  where

  open SecondOrder.Signature.Signature Σ

  -- A metavariable context
  record MetaContext : Set (lsuc ℓs) where
    field
      mv : Set -- the metavariables
      mv-arity : mv → Context -- the arity of a metavariable
      mv-sort : mv → sort -- the sort of a metavariable

  open MetaContext public

  mv-arg : ∀ (Θ : MetaContext) → MetaContext.mv Θ → sort → Set ℓs
  mv-arg Θ M A = A ∈ (MetaContext.mv-arity Θ M)
