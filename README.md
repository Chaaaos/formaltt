# Formalization of simple type theory

## Coding standards

We collect here some coding standards.

#### `import` and `open`

Only `import` what is necessary. Avoid global `open` and prefer local `open` statements.

#### Standard and categories libraries

Use the standard and categories libraries instead of reinventing the wheel.

#### Indentation level and line length

Use indentation level 2. Instead of

```
    Functor-Jⱽ.F-resp-≈  (Monad.F₀ VMonad Γ A) {ψ} {Ω} {Δ} {Ξ} {ρ} {τ} {ι} {μ} ξᵛʳ ξᵐʳ {t} {u} ξ  =
                                                          begin⟨ Term-setoid Θ _ _ ⟩
                                                          ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ ]ᵛʳ t) ≈⟨ []ᵛʳ-resp-≈ ξ ⟩
                                                          ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ ]ᵛʳ u)
                                                                                   ≈⟨ []ᵛʳ-resp-≡ᵛʳ ([,]ᵛʳ-resp-≡ᵛʳ (λ x → refl) λ x → ρ-resp-≡ {ρ = var-inr} (ξᵛʳ x)) ⟩
                                                          ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ ]ᵛʳ u) ∎
```

you should write

```
    Functor-Jⱽ.F-resp-≈  (Monad.F₀ VMonad Γ A) {ψ} {Ω} {Δ} {Ξ} {ρ} {τ} {ι} {μ} ξᵛʳ ξᵐʳ {t} {u} ξ  =
      begin⟨ Term-setoid Θ _ _ ⟩
        ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ ]ᵛʳ t)
          ≈⟨ []ᵛʳ-resp-≈ ξ ⟩
        ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (ρ x₁)) ]ᵛʳ ]ᵛʳ u)
          ≈⟨ []ᵛʳ-resp-≡ᵛʳ ([,]ᵛʳ-resp-≡ᵛʳ (λ x → refl) λ x → ρ-resp-≡ {ρ = var-inr} (ξᵛʳ x)) ⟩
      ([ [ (λ x₁ → var-inl x₁) , (λ x₁ → var-inr (τ x₁)) ]ᵛʳ ]ᵛʳ u) ∎
```

or something similar that doesn't produce exceedingly long lines with unecessary indentation.


#### Naming conventions

1. Use full names: `RelativeMonad` instead of `RelMon`, `RelativeMorphism` instead of `RelMorph`. Abbreviations should be use very sparingly.
2. We use subscripts to indicate entities, as follows:
   * `ᵛ` for *variable renaming*
   * `ᵐ` for *metavariable renaming*
   * `ˢ` for *substitition*
   * `ⁱ` for *instantiation*
3. Composition of entities is written as `∘ˣ` where `x` is a supscript indicating the kind, e.g.,
   `σ ∘ˢ τ` is composition of subtitutions. There are also mixed compositions `ʸ∘ˣ` which compose
   an entity of kind `y` with an entitiy of kind `x`.
4. The action of `f` on a term `t` is written as `[ f ]ˣ t` where `x` is a supscript indicating the kind of `f`.
   For example, `[ σ ]ˢ t` is the action of the substitution `σ` on term `t`.
5. A theorem explaining how an action interacts with composition are named `[∘ˣ]` or `[ˣ∘ʸ]`.
6. A theorem stating that an action `[]ˣ` respects equality `≈ʸ` are named `[]ˣ-resp-≈ʸ`.


## The categorical structure of second-order syntax

Given functors `I F : ℂ → 𝔻`, let `RelativeMonad I F` be the category whose objects are
relative monad structures on `(I, F)` and the morphisms are relative monad morphisms between them.

The ingridients:
* A set of types `Ty`.
* A category `VCtx` of variable contexts and renamings. The category has finite coproducts.
* A category `MCtx` of metavariable contexts and renamings. The category has finite coproducts.
* A coproduct-preserving functor `Jᵛ : VCtx → Set^Ty` where `Jᵛ Γ A` is thought of as variables of type `A` in context `Γ`
* A coproduct-preserving functor `Jᵐ : VCtx → Set^(VCtx × Ty)`, where `Jᵐ Θ (Δ, A)` is thought of as metavariables of arity `Δ` and type `A` in metacontext `Θ`.
* A functor `Term : MCtx → VCtx → Set^Ty`, where `Term Θ Γ A` is thought of as the set of terms of type `A` in metacontext `Θ` and context `Γ`.
* A functor `MCtx → RelativeMonad Jᵛ Tᵛ` where `Tᵛ : MCtx → VCtx → Set^Ty` is `Tᵛ Θ Γ A := Term Θ Γ A`.
* A functor `VCtx → RelativeMonad Jᵐ Tᵐ` where `Tᵐ : VCtx → MCtx → Set^(VCtx × Ty)` is `Tᵐ Θ Γ (Δ, A) = Term Θ (Γ + Δ) A`.
* For every `f : Jⱽ Γ → Tᵛ Θ Γ'` we can define `hat f : Tᵐ Γ → Tᵐ Γ'` and it is a `Jᵐ`-relative monad morphism
* For every `I : Jᵐ Θ → Tᵐ Θ'` we can define `hat I : Tᵛ Θ → Tᵛ Θ'` and it is a `Jᵛ`-relative monad morphism

The syntactic structure is recovered from the above category-theoretic ingridients as follows:

* Types are the elements of `Ty`.
* Variable contexts are the objects of `VCtx`, variable renamings are the morphisms.
* Metavariable contexts are the objects of `MCtx`, metavariable renamings are the morphisms.
* `x : A ∈ Γ` is `x ∈ Jⱽ Γ A`
* `M : [ Δ , A ]∈ Θ` is `M ∈ Jᴹ Θ (Δ, A)`
* `Θ ; Γ ⊢ t : A` is `t ∈ Term Θ Γ A`
* a substitution `σ : Γ ⇒ˢ Θ ⊕ Δ` is a morphism `σ : Jᵛ Γ → Tᵛ Θ Δ` in `Set^Ty`.
* the renaming action `[ ρ ]ʳ : Term Θ Γ → Term Θ Δ` is `Term Θ ρ`
* the substitution action `[ σ ]ˢ : Term Θ Γ → Term Θ Δ` is the Kleisli extension of `σ`
* an instantiation `I : Θ ⇒ⁱ Ξ ⊕ Γ` is a morphism `I : Jᵐ Θ → Tᵐ Γ Ξ` in `Set^(VCtx × Ty)`
* the instantiation action `[ I ]ⁱ : Term Θ Γ → Term Ξ Γ` is **(please fill in)**
* extension `⇑ʳ` arises from the coproduct structure on `VCtx`
* extension `⇑ˢ` arises from **(please fill in)**
* extension `⇑ⁱ` arises from **(please fill in)**



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
