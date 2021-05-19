open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Signature

module SecondOrder.Metavariable
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Signature.Signature Σ

  -- A metavariable context
  record MetaContext : Set (lsuc ℓ) where
    field
      mv : Set -- the metavariables
      mv-arity : mv → Context -- the arity of a metavariable
      mv-sort : mv → sort -- the sort of a metavariable

  open MetaContext public

  mv-arg : ∀ (Θ : MetaContext) → MetaContext.mv Θ → sort → Set ℓ
  mv-arg Θ M A = A ∈ (MetaContext.mv-arity Θ M)
