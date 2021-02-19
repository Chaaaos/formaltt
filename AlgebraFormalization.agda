open import Agda.Primitive
open import Agda.Builtin.Equality -- renaming (_≡_ to _==_) (( If I want to rename the built-in equality ))

module AlgebraFormalization where

  -- Here is an attempt to translate (part of) the Coq formalization. I did not translate the definition of the free algebra, the proof, and the part concerning the groups yet. I hope I did not do too weird things with the levels.

  -- Function extensionality
  postulate
    funext : ∀ {X : Set} {Y : X → Set} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) ≡ (g x))) → (f ≡ g)
  -- Operation Signature
  record OpSignature {l : Level} : Set (lsuc l) where
    field
      operation : Set l
      arity : operation → Set l
  -- I used the things with the levels of the hierachy of types because Agda was unhappy with what I was doing (and I did not want to define it only with Set₀ and Set₁ beacause I wanted to avoid weird things if we then want to define an OpSignature with an operation OpSignature)

  -- Operation Algebra
  record OpAlgebra {l : Level} (S : OpSignature {l}) : Set (lsuc l) where
    field
      carrier : Set l
      op : ∀ (o : OpSignature.operation S) (f : OpSignature.arity S o → carrier) → carrier

  -- Homomorphisms
  record Hom {l : Level} {S : OpSignature {l}} (A : OpAlgebra {l} S) (B : OpAlgebra {l} S) : Set (lsuc l) where
    field
      map : (OpAlgebra.carrier A) → (OpAlgebra.carrier B)
      op-commute : ∀ (o : OpSignature.operation S) (args : OpSignature.arity S o → OpAlgebra.carrier A) → (map (OpAlgebra.op A o args) ≡ OpAlgebra.op B o (λ x → map (args x) ))

  -- For the moment I skip the translation of the part concerning the free algebra

  -- Equation Signature
  record Eqsignature {l : Level} (S : OpSignature {l}) : Set (lsuc l) where
    field
      eq : Set l
      eq-arity : eq → Set l
      -- the two sides of the equation
      lhs : ∀ {A : OpAlgebra {l} S} {e : eq} → ((eq-arity e) → (OpAlgebra.carrier A)) → (OpAlgebra.carrier A)
      rhs : ∀ {A : OpAlgebra {l} S} {e : eq} → ((eq-arity e) → (OpAlgebra.carrier A)) → (OpAlgebra.carrier A)
      -- naturality / commutation
      lhs-natural : ∀ (A B : OpAlgebra {l} S) (f : Hom A B) (e : eq) (args : eq-arity e → OpAlgebra.carrier A) → ( (Hom.map f) (lhs {A} {e} args) ≡ lhs {B} {e} (λ i → (Hom.map f) (args i)))
      rhs-natural : ∀ (A B : OpAlgebra {l} S) (f : Hom A B) (e : eq) (args : eq-arity e → OpAlgebra.carrier A) → ( (Hom.map f) (rhs {A} {e} args) ≡ rhs {B} {e} (λ i → (Hom.map f) (args i)))

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



