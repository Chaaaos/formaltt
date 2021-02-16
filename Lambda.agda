module Lambda where
  -- The typed λ-calculus

  -- The type of types
  data ty : Set where
     ι : ty                   -- the base type
     _⇒_ : ty → ty → ty      -- function type

  -- A typing context, there are no variable names because we use de Bruijn indices.
  data ctx : Set where
     • : ctx                  -- empty context
     _,_ : ctx → ty → ctx     -- context extension

  -- A variable is a natural number (de Bruijn index, position in the context),
  -- but at the same time a proof that a type appears in the context.
  -- We write Γ ∋ A for the type of variables in Γ of type A.
  data _∋_ : (Γ : ctx) (B : ty) → Set where
     Z : {Γ : ctx} {B : ty} → (Γ , B) ∋ B              -- zero
     S : {Γ : ctx} {A B : ty} → Γ ∋ B → (Γ , A) ∋ B    -- successor


  -- The type of terms in context Γ of type A
  data tm (Γ : ctx) : (A : ty) → Set where
     tm-var : {A : ty} → Γ ∋ A → tm Γ A
     tm-λ : {B : ty} {A : ty} → tm (Γ , A) B → tm Γ (A ⇒ B)
     tm-app : {A B : ty} → tm Γ (A ⇒ B) → tm Γ A → tm Γ B

  -- We need serveral boring auxiliary functions whose
  -- purpose is to define substitution

  -- A variable renaming is a type-preserving map from variables in Γ to variables in Δ
  -- (In Agda "renaming" is a reserved word.)
  variable-renaming = λ Γ Δ → ∀ {A} → Γ ∋ A → Δ ∋ A

  -- we may extend a renaming by one more variable (which does not get renamed)
  extend-renaming : ∀ {Γ Δ A} → variable-renaming Γ Δ → variable-renaming (Γ , A) (Δ , A)
  extend-renaming ρ Z = Z
  extend-renaming ρ (S x) = S (ρ x)

  -- the action of a renaming on a term
  term-rename : ∀ {Γ Δ} → variable-renaming Γ Δ → (∀ {A} → tm Γ A → tm Δ A)
  term-rename ρ (tm-var x) = tm-var (ρ x)
  term-rename ρ (tm-λ t) = tm-λ (term-rename (extend-renaming ρ) t)
  term-rename ρ (tm-app s t) = tm-app (term-rename ρ s) (term-rename ρ t)

  -- a special kind of renaming is weakening by a variable, which we write as ↑
  ↑ : ∀ {Γ A B} → tm Γ A → tm (Γ , B) A
  ↑ = term-rename S

  -- a substitution from Γ to Δ takes variables in Γ to terms in Δ
  substitution = λ Γ Δ → (∀ {A} → Γ ∋ A → tm Δ A)

  extend-substutition : ∀ {Γ Δ A} → substitution Γ Δ → substitution (Γ , A) (Δ , A)
  extend-substutition σ Z = tm-var Z
  extend-substutition σ (S x) = ↑ (σ x)

  -- The action of a substitution on a term
  term-substitute : ∀ {Γ Δ} → substitution Γ Δ → ∀ {A} → tm Γ A → tm Δ A
  term-substitute σ (tm-var x) = σ x
  term-substitute σ (tm-λ t) = tm-λ (term-substitute (extend-substutition σ) t)
  term-substitute σ (tm-app s t) = tm-app (term-substitute σ s) (term-substitute σ t)

  -- A common kind of substitution only replaces the 0-th variable with a term
  -- and leaves all the others intact, so we define its action as a shorthand
  _[_] : ∀ {Γ A B} → tm (Γ , A) B → tm Γ A → tm Γ B
  _[_] {Γ} {A} {B} s t = term-substitute σ s where
    σ : substitution (Γ , A) Γ
    σ Z = t
    σ (S x) = tm-var x

  -- Judgemental equality
  data _≡_ {Γ : ctx} : {A : ty} (t s : tm Γ A) → Set where
    -- general rules
    eq-refl : {A : ty} {t : tm Γ A} → t ≡ t
    eq-tran : {A : ty} {t s u : tm Γ A} → t ≡ s → s ≡ u → t ≡ u
    eq-sym :  {A : ty} {t s : tm Γ A} → t ≡ s → s ≡ t
    -- congruence rules
    eq-congr-app : ∀ {A B} {t₁ t₂ : tm Γ (A ⇒ B)} {s₁ s₂ : tm Γ A} →
                   t₁ ≡ t₂ → s₁ ≡ s₂ → tm-app t₁ s₁ ≡ tm-app t₂ s₂
    eq-congr-λ : ∀ {A B} {t₁ t₂ : tm (Γ , A) B} →
                   t₁ ≡ t₂ → tm-λ t₁ ≡ tm-λ t₂
    -- computation rules
    eq-β : ∀ {A B} {t : tm (Γ , A) B} {s : tm Γ A} → (tm-app (tm-λ t) s) ≡ (t [ s ])
    -- extensionality rules
    eq-ext : ∀ {A B} {s t : tm Γ (A ⇒ B)} →
             (tm-app (↑ s) (tm-var Z)) ≡ (tm-app (↑ t) (tm-var Z))
             → s ≡ t

  -- Example: the identity function
  -- Note that we actually define a family of terms, indexed by a context
  -- and a type, but the family is constant, i.e., it is always the same term.
  tm-id : ∀ {Γ A} → tm Γ (A ⇒ A)
  tm-id = tm-λ (tm-var Z)

  -- Appying the identity function twice does nothing
  app-id-id : ∀ {Γ A} {t : tm Γ A} → tm-app tm-id (tm-app tm-id t) ≡ t
  -- app-id-id = eq-tran (eq-congr-app eq-refl eq-β) eq-β
  app-id-id = eq-tran eq-β eq-β

  -- Eta-rule

  eq-η : ∀ {Γ A B} {t : tm Γ (A ⇒ B)} → tm-λ (tm-app (↑ t) (tm-var Z)) ≡ t
  eq-η = eq-ext (eq-tran eq-β (eq-congr-app {!!} eq-refl))

  -- natural numbers
  data N : Set where
    zero : N
    succ : N → N

  -- church numerals

  nat = (ι ⇒ ι) ⇒ (ι ⇒ ι)

  tm-numeral : ∀ {Γ} → N → tm Γ nat
  tm-numeral zero = tm-id
  tm-numeral (succ n) = tm-λ (tm-λ (tm-app (tm-app (tm-numeral n) (tm-var (S Z))) (tm-app (tm-var (S Z)) (tm-var Z))))

  -- normalization (this is problematic because Agda does not see that it terminates)
  -- normalize : ∀ {Γ A} → tm Γ A → tm Γ A
  -- normalize (tm-var x) = tm-var x
  -- normalize (tm-λ t) = tm-λ (normalize t)
  -- normalize {Γ} {A} (tm-app s t) = apply-normalized (normalize s) (normalize t) where
  --   apply-normalized : ∀ {B} → tm Γ (B ⇒ A) → tm Γ B → tm Γ A
  --   apply-normalized (tm-λ u) v = normalize (u [ v ])
  --   apply-normalized (tm-var x) v = (tm-app (tm-var x) v)
  --   apply-normalized (tm-app u₁ u₂) v = (tm-app (tm-app u₁ u₂) v)

  -- -- normalization works correctly
  -- normalize-correct : ∀ {Γ A} (t : tm Γ A) → normalize t ≡ t
  -- normalize-correct (tm-var x) = {!!}
  -- normalize-correct (tm-λ t) = {!!}
  -- normalize-correct (tm-app s t) with normalize s
  -- normalize-correct (tm-app s t)    | (tm-λ u) = {!!}
  -- normalize-correct (tm-app s t)    | (tm-var x) = {!!}
  -- normalize-correct (tm-app s t)    | (tm-app u₁ u₂) = {!!}
