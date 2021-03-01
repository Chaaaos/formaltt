open import Agda.Primitive
open import Agda.Builtin.Equality   renaming (_≡_ to _==_) --(( If I want to rename the built-in equality ))

-- What follows is an attempt to formalize multicategories. For this purpose, we also need to define lists, since the source of a multimap in a multicategory is a list.
-- For the moment, I do not try to prove that the lists an the associated concatenation form a monoid (because I do not know if this is useful or not).

module MultiCategories where

  -- ** Function extensionality **
  postulate
    funext : ∀ {X : Set} {Y : X → Set} {f g : ∀ (x : X) → (Y x)} → (∀ (x : X) → ((f x) == (g x))) → (f == g)



  -- ** Lists **

  -- We first define lists
  data List {l : Level} (A : Set l) : Set l where
    [] : List A
    _::_ : A → List A → List A

  infixr 30 _::_

  open List

  -- We define equality on lists, that extends the built-in equality (since for the moment, we dont need other definitions of equality → but maybe we could do something more general by asking the "equality" as a parameter ?)
  data _≡ᴸ_ {l : Level} {A : Set l} : (u v : List {l} A) → Set (lsuc l) where
    eq-nil : [] ≡ᴸ []
    eq-cons : ∀ (x y : A) (su sv : List A) → (x == y) → (su ≡ᴸ sv) → ( (x :: su) ≡ᴸ (y :: sv))

  -- We define the mapping of lists
  list-map : ∀ {l : Level} {A B : Set l} → (f : A → B) → List A → List B
  list-map f [] = []
  list-map f (x :: u) = ((f x) :: (list-map f u))

  -- We define the concatenation of lists
  _++_ : ∀ {l}{A : Set l} → List A → List A → List A
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  -- We define a fold function
  fold : ∀ {l : Level} {A B : Set l} → (A → B → B) → B → List A → B
  fold _⊗_ e [] =  e
  fold _⊗_ e (x :: xs)  =  x ⊗ (fold _⊗_ e xs)

  -- We define a flatten function
  flatten : ∀ {l : Level} {A : Set l} → (u : List ( List A)) → (List A)
  flatten [] = []
  flatten (x :: xs) = x ++ (flatten xs)
  --  (I wanted to do this with the above fold function, which would be more elegant, but I don't know why, I miserably failed at it - must be tired)

  -- We define a function that takes a list of functions and a list of arguments and apply the functions point to point
  list-apply : ∀ {l : Level} {A B : Set l} → (list-f : List (A → B)) → (list-arg : List A) → List B
  list-apply [] [] = []
  list-apply (f :: fs) [] = []
  list-apply [] (x :: xs) = []
  list-apply (f :: fs) (x :: xs) = (f x) :: (list-apply fs xs)
  -- The two cases in the middle should be forbidden, but I don't know how to do this


  -- ** Multicategories **

  -- -- We first define the multimaps on a set
  -- data Multimap {l : Level} {O : Setl l} : Set l where
  --   map : ()

  record MultiCategory {l : Level} : Set (lsuc l) where
    field
      -- Objects and maps
      object : Set l
      multimap : Set l
      sources : ∀ (m : multimap) → List object
      target : ∀ (m : multimap) → object
      -- Composition and associated equations / conditions
      _∘_ : ∀ (f : multimap) → (list : List multimap) → multimap
      plug : ∀ {g : multimap} → {f : multimap} → {list : List multimap} → {g == (f ∘ list)} →  (sources f) ≡ᴸ (list-map target list)
      dom-comp : ∀ {f : multimap} → {list : List multimap} → ((flatten (list-map sources list)) ≡ᴸ (sources (f ∘ list)))
      comp-codom : ∀ (f : multimap) → (list : List multimap) → (target f == target (f ∘ list))
      -- Identities and associated equations / conditions
      id : ∀ (o : object) → multimap
      id-dom-codom : ∀ (o : object) → (sources (id o) == o :: [] )
      id-codom :  ∀ (o : object) → (target (id o) == o)
      id-left : ∀ {o : object} {f : multimap} → {f == id o} → (list : List multimap) → ( (f ∘ list) == f)
      id-rigth : ∀ {f : multimap} {list : List multimap} → {list ≡ᴸ (list-map id (sources f))} → ((f ∘ list) == f)
      -- Associativity
      assoc : ∀ {f : multimap} {list-g : List multimap} {list-h : List (List multimap)} → (f ∘ (list-apply (list-map _∘_ list-g) list-h)) == ( (f ∘ list-g) ∘ (flatten list-h))

  open MultiCategory

  -- List over a list
  data ListOver {l : Level} {A : Set l} (B : A → Set l) : List A → Set l where
    [[]] : ListOver B []
    _:::_ : ∀ {x xs} → (y : B x) → (ys : ListOver B xs) → ListOver B (x :: xs)

  infixr 25 _:::_

  over-map : ∀ {l : Level} {A : Set l} {B : A → Set l} {xs} {C : Set l} → (∀ {x} → B x → C) → ListOver B xs → List C
  over-map f [[]] = []
  over-map f (y ::: ys) = f y :: over-map f ys

  over-over-map : ∀ {l : Level} {A : Set l} {B : A → Set l} {xs} {C : A → Set l} → (∀ {x} → B x → C x) → ListOver B xs → ListOver C xs
  over-over-map f [[]] = [[]]
  over-over-map f (y ::: ys) = f y ::: over-over-map f ys

  over-lift : ∀ {l : Level} {A : Set l} (list : List A) → ListOver (λ x → A) list
  over-lift [] = [[]]
  over-lift (y :: ys) = y ::: (over-lift ys)

  over-flatten : ∀ {l : Level} {A B : Set l} {list : List A} (list-ov : ListOver (λ x → List B) list) → List B
  over-flatten [[]] = []
  over-flatten (x ::: xs) = x ++ (over-flatten xs)

  -- Dependent sum
  record Σ {l} (A : Set l) (B : A → Set l) : Set l where
    constructor ⟨_,_⟩
    field
      π₁ : A
      π₂ : B π₁

  open Σ

  -- Shortcuts to map the projections on lists when the dependent sum is a "product"
  list-π₁ : ∀ {l : Level} {A : Set l} {B} (list : List ( Σ {l} A B)) → List A
  list-π₁ list = list-map π₁ list

  list-π₂ : ∀ {l : Level} {A C : Set l} (list : List ( Σ {l} A ( λ x → C))) → List C
  list-π₂ list = list-map π₂ list



  -- A more dependent attempt at multicategories
  record MultiCategory2 {l : Level} : Set (lsuc l) where
    field
      object : Set l
      multimap : List object → object → Set l
      𝟙 : ∀ {x} → multimap (x :: []) x
      _•_ : ∀ {ys x} → multimap ys x → ∀ (gs : ListOver (λ y → Σ (List object) (λ zs → multimap zs y)) ys) →
            multimap (flatten (over-map π₁ gs)) x
      -- Another attempt to define multimaps, "putting the dependance elsewhere"
      _●_ : ∀ {x : object} {ys : List (Σ (List object) (λ x → object))} → multimap (list-π₂ ys) x → ListOver (λ y → multimap (π₁ y) (π₂ y)) ys → multimap (flatten (list-π₁ ys)) x
      -- here complications start
      -- 𝟙-left : ∀ {ys x} → (f : multimap ys x) → 𝟙 • (⟨ ys , f ⟩ ::: [[]]) == f
      -- 𝟙-right : ∀ {ys x} → (f : multimap ys x) → f • (over-over-map ? (over-lift ys)) == f
      --(ListOver ( λ y → ⟨ x ::: [[]] , 𝟙 ⟩ ) ys) == f
      -- Attempt with the alternative composition
      𝟙-left-● : ∀ {x ys} → (f : multimap ys x) → 𝟙 ● (f ::: [[]]) == f -- Here it seems that we have a lemma to prove to say that ys = (ys ++ flatten (list-map π₁ [])). Do we do it locally or would it be useful to have a more genral lemma ?

-- Here I tried to fix 𝟙-left and to define 𝟙-right, but I did not manage to do it, it both cases. Maybe we should revise the definition of _•_ ?
-- Agda seems to struggle with the fact that thnigs that should be equal are not equal by definition (conversion/reduction problems). Maybe there are some lemmas to prove here.
-- Also, I do not understand why we use the "over-map" : it would feel more natural to me if, once we lift a list to a dependent one, and use dependant lists, we only use dependeant lists, that's why I defined over-lift and over-over-map. (I also defined an "over-flatten" but don't know if it's useful)
