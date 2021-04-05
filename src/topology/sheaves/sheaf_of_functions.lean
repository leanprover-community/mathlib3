/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import topology.sheaves.presheaf_of_functions
import topology.sheaves.sheaf
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
λ ι U,
-- U is a family of open sets, indexed by `ι`.
-- In the informal comments below, I'll just write `U` to represent the union.
begin
  refine fork.is_limit.mk _ _ _ _,
  { -- Our first goal is to define a function "lifted" to all of `U`, given
    -- `s`, some cone over the sheaf condition diagram
    -- (which we can think of as some type `s.X` which we know nothing about,
    -- except how to restrict terms to each of the `U i`, obtaining a function there,
    -- and that these restrictions are compatible), and
    -- `f`, a term of `s.X`.
    -- We do this one point at a time, so we also pick some `x` and the evidence `mem : x ∈ supr U`.
    rintros s f ⟨x, mem⟩,
    change x ∈ supr U at mem, -- FIXME there is a stray `has_coe_t_aux.coe` here
    -- Since `x ∈ supr U`, there must be some `i` so `x ∈ U i`:
    simp [opens.mem_supr] at mem,
    choose i hi using mem,
    -- We define out function to be the restriction of `f` to that `U i`, evaluated at `x`.
    exact ((s.ι ≫ pi.π _ i) f) ⟨x, hi⟩, },
  { -- Now we need to verify that this lifted function restricts correctly to each set `U i`.
    -- Of course, the difficulty is that at any given point `x ∈ U i`,
    -- we may have used the axiom of choice to pick a differnt `j` with `x ∈ U j`
    -- when defining the function.
    -- This we'll need to use the fact that the restrictions are compatible.

    -- Again, we begin with some `s`, a cone over the sheaf condition diagram.
    intros s,
    -- The goal at this point is fairly inscrutable,
    -- but we know we're trying two functions are equal, so we call `ext` and see what we get:
    ext i f ⟨x, mem⟩,
    dsimp at mem,
    -- We now have `i : ι`, a term `f : s.X`, and a point `x` with `mem : x ∈ U i`.

    -- We clean up the goal a little,
    simp only [exists_prop, set.mem_range, set.mem_image, exists_exists_eq_and, category.assoc],
    simp only [limit.lift_π, types_comp_apply, fan.mk_π_app, presheaf_to_Type],
    dsimp,
    -- although you still need to be ambitious to read it.
    -- The mathematical content, of course, is that the lifted function we constructed from `f`,
    -- when restricted to `U i` and evaluated at `x`,
    -- has the same value as `f` restricted to to `U i` and evaluated at `x`.

    -- We have a slightly annoying issue at this point,
    -- that we're not really sure which `j : ι` was used to define the lifted function
    -- and this point `x`, because we used choice.
    -- As a trick, we create a new metavariable `j` to represent this choice,
    -- and later in the proof it will be solved by unification.
    let j : ι := _,

    -- Now, we assert that the two restrictions of `f` to `U i` and `U j` coincide on `U i ⊓ U j`,
    -- and in particular coincide there after evaluating at `x`.
    have s₀ := s.condition =≫ pi.π _ (j, i),
    simp only [sheaf_condition_equalizer_products.left_res,
      sheaf_condition_equalizer_products.right_res] at s₀,
    have s₁ := congr_fun s₀ f,
    have s₂ := congr_fun s₁ ⟨x, _⟩, clear s₀ s₁,
    -- Notice at this point we've spun after an additional goal:
    -- that `x ∈ U j ⊓ U i` to begin with! Let's get that out of the way.
    swap,
    { -- We knew `x ∈ U i` right from the start:
      refine ⟨_, mem⟩,
      -- Notice that when we introduced `j`, we just introduced it as some metavariable.
      -- However at this point it's received a concrete value,
      -- because Lean's unification has worked out that this `j` must have been the index
      -- that we picked using choice back when constructing the lift.
      -- From this, we can extract the evidence that `x ∈ U j`:
      convert @classical.some_spec _ (λ i, x ∈ (U i : set X)) _, },
    -- Now, we can just assert that `s₂` is the droid you are looking for,
    -- and do a little patching up afterwards.
    convert s₂,
    { simp only [sheaf_condition_equalizer_products.res, presheaf_to_Types_map,
        types.pi_lift_π_apply, types_comp_apply],
      dsimp [inf_le_left_apply],
      simp,
      refl, },
    { simp,
      refl, }, },
  { -- On the home stretch now,
    -- we just need to check that the lift we picked was the only possible one.

    -- So we suppose we had some other way `m` of choosing lifts,
    intros s m w,
    -- and observe that we need to check that it agrees with our choice
    -- for each `f : s .X` and each `x ∈ supr U`.
    ext f ⟨x, mem⟩,

    -- Now `w` is the evidence that other choice of lift agrees either on the `U i`s,
    -- or on the `U i ⊓ U j`s.
    -- We'll need the later,
    specialize w walking_parallel_pair.zero,
    -- because we're not sure which arbitrary `j : ι` we used to define our lift.

    let j : ι := _,

    -- Now it's just a matter of plugging in all the values;
    -- `j` gets solved for during unification.
    convert congr_fun (congr_fun (w =≫ pi.π _ j) f) ⟨x, _⟩,
    simp [sheaf_condition_equalizer_products.res],
    refl, }
end.

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
