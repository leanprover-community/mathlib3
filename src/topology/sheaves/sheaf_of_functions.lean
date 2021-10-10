/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import topology.sheaves.presheaf_of_functions
import topology.sheaves.sheaf_condition.unique_gluing
import category_theory.limits.shapes.types
import topology.local_homeomorph

/-!
# Sheaf conditions for presheaves of (continuous) functions.

We show that
* `Top.sheaf_condition.to_Type`: not-necessarily-continuous functions into a type form a sheaf
* `Top.sheaf_condition.to_Types`: in fact, these may be dependent functions into a type family

For
* `Top.sheaf_condition.to_Top`: continuous functions into a topological space form a sheaf
please see `topology/sheaves/local_predicate.lean`, where we set up a general framework
for constructing sub(pre)sheaves of the sheaf of dependent functions.

## Future work
Obviously there's more to do:
* sections of a fiber bundle
* various classes of smooth and structure preserving functions
* functions into spaces with algebraic structure, which the sections inherit
-/

open category_theory
open category_theory.limits
open topological_space
open topological_space.opens

universe u

noncomputable theory

variables (X : Top.{u})

open Top

namespace Top.presheaf

/--
We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a type family `T`,
so we do the more general case.
-/
def to_Types (T : X → Type u) : sheaf_condition (presheaf_to_Types X T) :=
sheaf_condition_of_exists_unique_gluing _ $ λ ι U sf hsf,
-- We use the sheaf condition in terms of unique gluing
-- U is a family of open sets, indexed by `ι` and `sf` is a compatible family of sections.
-- In the informal comments below, I'll just write `U` to represent the union.
begin
  -- Our first goal is to define a function "lifted" to all of `U`.
  -- We do this one point at a time. Using the axiom of choice, we can pick for each
  -- `x : supr U` an index `i : ι` such that `x` lies in `U i`
  let index : supr U → ι := λ ⟨x,mem⟩, classical.some (opens.mem_supr.mp mem),
  have index_spec : ∀ x : supr U, x.1 ∈ U (index x) := by {
      rintro ⟨x,mem⟩,
      exact classical.some_spec (opens.mem_supr.mp mem), },
  -- Using this data, we can glue our functions together to a single section
  let s : Π x : supr U, T x := λ x, sf (index x) ⟨x.1, index_spec x⟩,
  refine ⟨s,_,_⟩,
  { intro i,
    ext x,
    -- Now we need to verify that this lifted function restricts correctly to each set `U i`.
    -- Of course, the difficulty is that at any given point `x ∈ U i`,
    -- we may have used the axiom of choice to pick a different `j` with `x ∈ U j`
    -- when defining the function.
    -- Thus we'll need to use the fact that the restrictions are compatible.
    convert congr_fun (hsf (index ⟨x,_⟩) i) ⟨x,⟨index_spec ⟨x.1,_⟩,x.2⟩⟩,
    ext,
    refl },
  { -- Now we just need to check that the lift we picked was the only possible one.
    -- So we suppose we had some other gluing `t` of our sections
    intros t ht,
    -- and observe that we need to check that it agrees with our choice
    -- for each `f : s .X` and each `x ∈ supr U`.
    ext x,
    convert congr_fun (ht (index x)) ⟨x.1,index_spec x⟩,
    ext,
    refl }
end

-- We verify that the non-dependent version is an immediate consequence:
/--
The presheaf of not-necessarily-continuous functions to
a target type `T` satsifies the sheaf condition.
-/
def to_Type (T : Type u) : sheaf_condition (presheaf_to_Type X T) :=
to_Types X (λ _, T)

end Top.presheaf

namespace Top

/--
The sheaf of not-necessarily-continuous functions on `X` with values in type family
`T : X → Type u`.
-/
def sheaf_to_Types (T : X → Type u) : sheaf (Type u) X :=
{ presheaf := presheaf_to_Types X T,
  sheaf_condition := presheaf.to_Types _ _, }

/--
The sheaf of not-necessarily-continuous functions on `X` with values in a type `T`.
-/
def sheaf_to_Type (T : Type u) : sheaf (Type u) X :=
{ presheaf := presheaf_to_Type X T,
  sheaf_condition := presheaf.to_Type _ _, }

end Top
