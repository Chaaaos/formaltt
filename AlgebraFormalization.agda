open import Agda.Primitive
open import Agda.Builtin.Equality  renaming (_≡_ to _==_) --(( If I want to rename the built-in equality ))

module AlgebraFormalization where

  -- Here is an attempt to translate (part of) the Coq formalization. I did not translate the definition of the free algebra, the proof, and the part concerning the groups yet. I hope I did not do too weird things with the levels.


  -- ** Formalization of single-sorted algebraic theories **

  -- Function extensionality
  postulate
    funext : ∀ {X : Set} {Y : X → Set} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) == (g x))) → (f == g)
  -- Operation Signature
  record OpSignature {l : Level} : Set (lsuc l) where
    field
      operation : Set l
      arity : operation → Set l
  -- I used the things with the levels of the hierachy of types because Agda was unhappy with what I was doing (and I did not want to define it only with Set₀ and Set₁ beacause I wanted to avoid weird things if we then want to define an OpSignature with an operation OpSignature)


-- Here is a attempt (partial for the moment) to add context and terms, based on the same principles as in the file "ManySortedAlgebra.agda"
  -- Contexts
  record Context {l : Level} (Σ : OpSignature {l}) : Set (lsuc l) where
    field
      var : Set l

  open Context

  -- Terms on an operation signature
  data Term {l : Level} {Σ : OpSignature {l}} (Γ : Context Σ) : Set l  where
    tm-var : ∀ (x : var Γ) → Term Γ
    tm-op : ∀ (f : OpSignature.operation Σ) → (OpSignature.arity Σ f → Term Γ) → Term Γ

  substitution : ∀ {l : Level} {Σ : OpSignature {l}} (Γ Δ : Context Σ) → Set l
  substitution Γ Δ = ∀ (x : var Γ) → Term Δ


  -- the action of a substitution on a term
  _·_ : ∀ {l : Level} {Σ : OpSignature {l}} {Γ Δ : Context Σ} → substitution Γ Δ  → Term Γ → Term Δ
  σ · (tm-var x) = σ x
  σ · (tm-op f x) = tm-op f (λ i → σ · x i)

  infixr 6 _·_

  -- composition of substitutions
  _○_ : ∀ {l : Level} {Σ : OpSignature {l}} {Γ Δ Θ : Context Σ} → substitution Δ Θ → substitution Γ Δ → substitution Γ Θ
  (σ ○ τ) x = σ · τ x

  infixl 7 _○_

-- End of the attempt






  -- Operation Algebra
  record OpAlgebra {l : Level} (S : OpSignature {l}) : Set (lsuc l) where
    field
      carrier : Set l
      op : ∀ (o : OpSignature.operation S) (f : OpSignature.arity S o → carrier) → carrier

  -- Homomorphisms
  record Hom {l : Level} {S : OpSignature {l}} (A : OpAlgebra {l} S) (B : OpAlgebra {l} S) : Set (lsuc l) where
    field
      map : (OpAlgebra.carrier A) → (OpAlgebra.carrier B)
      op-commute : ∀ (o : OpSignature.operation S) (args : OpSignature.arity S o → OpAlgebra.carrier A) → (map (OpAlgebra.op A o args) == OpAlgebra.op B o (λ x → map (args x) ))

  -- For the moment I skip the translation of the part concerning the free algebra







-- Attempt to formalize the Equational theories diffenrently, based on what is done in the file "ManySortedAglebra.agda"

  -- Equational Theory (equations are seen as "in a context" and not with arities anymore)
  record EquationalTheory {l : Level} (Σ : OpSignature {l}) : Set (lsuc l) where
    field
      eq : Set l
      eq-ctx : ∀ (ε : eq) → Context {l} Σ
      eq-lhs : ∀ (ε : eq) → Term (eq-ctx ε)
      eq-rhs : ∀ (ε : eq) → Term (eq-ctx ε)

  open EquationalTheory

  -- Equality of terms
  infix 4 _≡_

  data _≡_ {l : Level} {Σ : OpSignature {l}} {T : EquationalTheory {l} Σ } : {Γ : Context Σ} → Term Γ → Term Γ → Set (lsuc l) where
    -- general rules
    eq-refl : ∀ {Γ} {t : Term Γ } → t ≡ t
    eq-symm : ∀ {Γ} {s t : Term {l} {Σ} Γ } → _≡_ {T = T} s t → t ≡ s
    eq-tran : ∀ {Γ} {s t u : Term Γ } → _≡_ {T = T} s t → _≡_ {T = T} t u → s ≡ u
    -- congruence rule
    eq-congr : ∀ {Γ} {f : OpSignature.operation Σ} (x y : ∀ (i : OpSignature.arity Σ f) → Term Γ) → (∀ i → _≡_ {_} {_} {T} (x i) (y i)) → ((tm-op f x) ≡ (tm-op f y))
    -- equational axiom
    eq-axiom : ∀ (ε : eq T) {Δ : Context {l} Σ} (σ : substitution (eq-ctx T ε) Δ) →
               ((σ · eq-lhs T ε) ≡ (σ · eq-rhs T ε))


  -- composition is functorial
  subst-○ : ∀ {l : Level} {Σ : OpSignature {l}} {T : EquationalTheory Σ} {Γ Δ Θ : Context Σ}
              (σ : substitution Δ Θ) (τ : substitution Γ Δ) →
              ∀ (t : Term Γ ) → _≡_ {T = T} (σ · τ · t)  (σ ○ τ · t)
  subst-○ σ τ (tm-var x) = eq-refl
  subst-○ σ τ (tm-op f x) = eq-congr (λ i → σ · τ · x i) (λ i → σ ○ τ · x i) λ i → subst-○ σ τ (x i)

  -- substitution preserves equality
  eq-subst : ∀ {l : Level} {Σ : OpSignature {l}} {T : EquationalTheory Σ} {Γ Δ : Context Σ} (σ : substitution Γ Δ)
               {s t : Term Γ}  → _≡_ {T = T} s t → _≡_ {T = T} (σ · s) (σ · t)
  eq-subst σ eq-refl = eq-refl
  eq-subst σ (eq-symm ξ) = eq-symm (eq-subst σ ξ)
  eq-subst σ (eq-tran ζ ξ) = eq-tran (eq-subst σ ζ) (eq-subst σ ξ)
  eq-subst σ (eq-congr x y ξ) = eq-congr (λ i → σ · x i) (λ i → σ · y i) λ i → eq-subst σ (ξ i)
  eq-subst {T = T} σ (eq-axiom ε τ) =
    eq-tran (subst-○ σ τ (eq-lhs T ε))
            (eq-tran (eq-axiom ε (σ ○ τ)) (eq-symm (subst-○ σ τ (eq-rhs T ε))))


-- End of the attempt





  -- Equation Signature
  record EqSignature {l : Level} (S : OpSignature {l}) : Set (lsuc l) where
    field
      eq : Set l
      eq-arity : eq → Set l
      -- the two sides of the equation
      lhs : ∀ {A : OpAlgebra {l} S} {e : eq} → ((eq-arity e) → (OpAlgebra.carrier A)) → (OpAlgebra.carrier A)
      rhs : ∀ {A : OpAlgebra {l} S} {e : eq} → ((eq-arity e) → (OpAlgebra.carrier A)) → (OpAlgebra.carrier A)
      -- naturality / commutation
      lhs-natural : ∀ (A B : OpAlgebra {l} S) (f : Hom A B) (e : eq) (args : eq-arity e → OpAlgebra.carrier A) → ( (Hom.map f) (lhs {A} {e} args) == lhs {B} {e} (λ i → (Hom.map f) (args i)))
      rhs-natural : ∀ (A B : OpAlgebra {l} S) (f : Hom A B) (e : eq) (args : eq-arity e → OpAlgebra.carrier A) → ( (Hom.map f) (rhs {A} {e} args) == rhs {B} {e} (λ i → (Hom.map f) (args i)))

  --  Algebra
  record Algebra {l : Level} (S : OpSignature {l}) (E : EqSignature {l} S) : Set (lsuc l) where
    field
      alg : OpAlgebra S
      equations : ∀ (e : EqSignature.eq E) (args : EqSignature.eq-arity E e → OpAlgebra.carrier  alg) → (EqSignature.rhs E {alg} {e} args == EqSignature.lhs E {alg} {e} args)


   -- For the moment, I think that we did not talk about terms in contexts, did we ? Should we generalize the things we did in Lambda.agda (using De Bruijn indices for the variables) ? -> I tried things







  -- ** Other things **

  -- Useful arities
  data nullary : Set where
  data unary : Set where
    only : unary
  data binary : Set where
    fst : binary
    snd : binary


  -- Definition of groups
  data GroupOperation : Set where
    one : GroupOperation
    mul : GroupOperation
    inv : GroupOperation

  GroupArity : (o : GroupOperation) → Set
  GroupArity one = nullary
  GroupArity mul = binary
  GroupArity inv = unary

  GroupOp : OpSignature
  GroupOp = record { operation = GroupOperation ;  arity = GroupArity}



