open import Agda.Primitive using (lzero; lsuc; _⊔_)

import SecondOrder.Arity
import SecondOrder.Signature
import SecondOrder.Metavariable
import SecondOrder.VRenaming
import SecondOrder.Term

module SecondOrder.Theory
  {ℓ}
  {𝔸 : SecondOrder.Arity.Arity}
  (Σ : SecondOrder.Signature.Signature ℓ 𝔸)
  where

  open SecondOrder.Metavariable Σ public
  open SecondOrder.Term Σ public
  open SecondOrder.Signature.Signature Σ public
  open SecondOrder.VRenaming Σ

  record Axiom : Set ℓ where
    constructor make-ax
    field
      ax-mv-ctx : MContext -- metavariable context of an equation
      ax-sort : sort -- sort of an equation
      ax-lhs : Term ax-mv-ctx ctx-empty ax-sort -- left-hand side
      ax-rhs : Term ax-mv-ctx ctx-empty ax-sort -- right-hand side

  record Theory ℓa : Set (lsuc (ℓ ⊔ ℓa)) where
    field
      ax : Set ℓa -- the axioms
      ax-eq : ax → Axiom -- each axiom has a corresponding Axiom

    ax-mv-ctx : ax → MContext -- the meta-context of each axiom
    ax-mv-ctx ε = Axiom.ax-mv-ctx (ax-eq ε)

    ax-sort : ax → sort -- the sort of each axiom
    ax-sort ε = Axiom.ax-sort (ax-eq ε)

    -- the left- and right-hand side of each axiom s ≈ t, promoted to any context
    ax-lhs : ∀ (ε : ax) {Γ} → Term (ax-mv-ctx ε) Γ (ax-sort ε)
    ax-lhs ε =  [ inʳ ]ʳ Axiom.ax-lhs (ax-eq ε)

    ax-rhs : ∀ (ε : ax) {Γ} → Term (ax-mv-ctx ε) Γ (ax-sort ε)
    ax-rhs ε = [ inʳ ]ʳ Axiom.ax-rhs (ax-eq ε)
