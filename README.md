# Formalization of simple type theory

## Coding standards

We collect here some coding standards.

1. Only `import` what is necessary.
2. Avoid global `open` and prefer local `open` statements.
3. Do not have excessively long lines.
4. Do not rename things in the standard library without a very good reason.
   If you discover that something already exists in the library, use it directly, not via renaming.
   Yes, that means more work with renaming things in your code, but it also avoids creating spaghetti.

## Outline of the ideas we are pursing

In this project we are aiming to formalize simple type theories in Agda. We may proceed along two axes, **generality** and **meta-analysis**.

### Generality

Generality is about how large a class of type theories we encompass. There are many ways to measure "generality", but
here is one that ought to work well and allow us to proceed in steps.

#### Single-sorted algebraic theory

**Parameterized by:**

* a family of **term symbols**, each having an arity (a set, or a number)
* a family of **equational axioms** `Γ ⊢ ℓ ≡ r`, see below

**Expressions:**

* **terms `s`, `t`:**

**Judgement forms:**

| Form | Intent |
|:----:|:------:|
| `Γ ⊢ t`      | `t` is a term in context `Γ = (x₁, ..., xᵢ)` |
| `Γ ⊢ s ≡ t`  | `s` and `t` are equal terms in context `Γ`  |

**Examples:** monoid, group, (fintarily branching) inductive types, ring, `R`-module (for a fixed `R`).


#### Multi-sorted algebraic theory

Parameterized by:

* a set of **sorts**
* a family of **term symbols**, each having an arity `(σ₁, ..., σᵢ) → τ` where `σ`'s and `τ` are sorts.
* a family of **equational axioms** `Γ ⊢ ℓ ≡ r : σ`, see below


**Expressions:**

* **terms `s`, `t`**

**Judgement forms:**

| Form | Intent |
|:----:|:------:|
| `Γ ⊢ t`          | `t` is a term in context `Γ = (x₁, ..., xᵢ)` |
| `Γ ⊢ s ≡ t : σ`  | `s` and `t` are equal terms of sort `σ` in context `Γ`  |

**Examples:** module, directed graph, mutually recursive (finitarily branching) inductive types.


#### Simple type theory I

These extend many-sorted algebraic theory in two ways:

* instead of having an amorphous set of sorts, we have types which are generated using type symbols
* term symbols may bind variables (e.g., `λ`-abstraction)

Parameterized by:

* a family of **type symbols**, each having an arity (a number, or a set)
* a family of **term symbols**, each having a formation rule (to be determined precisely what that is)
* a family of **equational axioms** `Γ ⊢ ℓ ≡ r : σ`, see below

**Syntactic classes:**

* **types `σ`, `τ`**, generated by type symbols
* **terms `s`, `t`** generated by variables, and term symbols applied to arguments
* **arguments** are types and (possibly abstracted) terms

**Judgement forms:**

| Form | Intent |
|:----:|:------:|
| `Γ ⊢ t : τ`      | `t` is a term of type `τ` in context `Γ = (x₁:σ₁, …, xᵢ:σᵢ)` |
| `Γ ⊢ s ≡ t : τ`  | `s` and `t` are equal terms of type `τ` in context `Γ`  |


**Example:** untyped λ-calculus, simply typed λ-calculus


#### Simple type theory II

These are like simple type theories, but we also allow types to take term arguments. However, types may not contain any free variables. This allows us to form types that depende on terms, such as a subtype `{ x : τ | ϕ }` where `x : τ ⊢ ϕ : bool` -- here `x` is bound in the type.

Parameterized by:

* a family of **type symbols**, each having a formation rule (to be determined)
* a family of **term symbols**, each having a formation rule (to be determined)
* a family of **equational term axioms** `Γ ⊢ ℓ ≡ r : σ`, see below
* a family of **equational type axioms** `Γ ⊢ σ ≡ τ`, see below

**Syntactic classes:**

* **types `σ`, `τ`**, generated by type symbols appied to arguments
* **terms `s`, `t`** generated by variables, and term symbols applied to term arguments
* **arguments** are types and (possibly abstracted) terms

Important: types may *not* contain any free variables!


**Judgement forms:**

| Form | Intent |
|:----:|:------:|
| `σ ≡ τ`          | `σ` and `τ` are equal types |
| `Γ ⊢ t : τ`      | `t` is a term of type `τ` in context `Γ = (x₁:σ₁, …, xᵢ:σᵢ)` |
| `Γ ⊢ s ≡ t : τ`  | `s` and `t` are equal terms of type `τ` in context `Γ`  |

**Example:** internal logic of an elementary topos


### Meta-analysis

We may pursue several directions of study.

#### Concreteness of definition

Definitions can be given at different levels of concreteness. For example, we may have raw terms and types, and a
separate judgement that such raw entities are well formed, or we have a single definition of terms and types that
prevents us from ever generating an ill-typed term.


#### Syntactic meta-theorems

We can prove theorems, such as uniqueness of typing, substitution lemmas, admissibility of substitutions, etc.


#### Semantics


We can define categorical semantics and show it to be sound.

#### Semantic completeness

We can show that the semantics is complete by constructing the initial models.
