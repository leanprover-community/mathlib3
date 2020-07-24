/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import topology.sheaves.presheaf_of_functions
import topology.sheaves.sheaf
import category_theory.limits.types

open category_theory
open category_theory.limits
open topological_space

noncomputable theory

universe u

variables (X : Top.{u})

open Top

/--
We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.
-/
def sheaf_condition_presheaf_to_Type (T : Type u) : sheaf_condition (presheaf_to_Type X T) :=
λ ι U,
-- U is a family of open sets, indexed by `i`.
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
    change x ∈ supr U at mem, -- needs some lemmas!
    -- Since `x ∈ supr U`, there must be some `i` so `x ∈ U i`:
    choose Ui H using mem,
    simp only [set.mem_range, set.mem_image, exists_exists_eq_and] at H,
    choose i hi using H.1,
    -- We define out function to be the restriction of `f` to that `U i`, evaluated at `x`.
    exact ((s.ι ≫ pi.π _ i) f) ⟨x, by { subst hi, exact  H.2, }⟩, },
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
    -- TODO make proper simp lemmas
    simp [sheaf_condition.left_res, sheaf_condition.right_res] at s₀,
    have s₁ := congr_fun s₀ f,
    have s₂ := congr_fun s₁ ⟨x, _⟩,
    -- Notice at this point we've spun after an additional goal:
    -- that `x ∈ U j ⊓ U i` to begin with! We'll postpone that.

    -- In the meantime, we can just assert that `s₂` is the droid you are looking for.
    -- (We relying shamefacedly on Lean's unification understanding this,
    -- even though the type of the goal is still fairly messy. "It's obvious.")
    simp [presheaf_to_Type] at s₂,
    convert s₂,

    -- At this point we've ended up with two copies of the "left over" goal `x ∈ U j ⊓ U i`.
    -- We just throw one out; Lean is clever enough to sort this out later.
    (do [g₁, g₂] ← tactic.get_goals, tactic.set_goals [g₁]),

    -- We've got half of this: we knew `x ∈ U i` right from the start:
    refine ⟨_, mem⟩,
    dsimp,

    -- We now do a ridiculous ninja move.
    -- Notice that when we introduced `j`, we just introduced it as some metavariable.
    -- However at this point it's received a concrete value,
    -- because Lean's unification has worked out that this `j` must have been the index
    -- that we picked using choice back when constructing the lift.
    -- From this, we can extract the evidence that `x ∈ U j`:
    obtain ⟨_, x_mem⟩ := classical.spec_of_eq_some (subtype.val_prop _ : j ∈ _),
    exact x_mem, },
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
    convert congr_fun (congr_fun (w =≫ pi.π _ j) f) ⟨x, _⟩, }
end

/-
TODO: next we need to do this for continuous functions.

In fact, I'd like to do it for any "functions satisfying a local condition",
for which there's a sketch at https://github.com/leanprover-community/mathlib/issues/1462

But it's probably worth doing this as a warm-up first.
The idea, of course, is to first lift to the underlying function,
using the fact that the presheaf of functions is a sheaf.
Because continuous functions are determined by their underlying functions,
this takes care of our factorisation and uniqueness obligations in the sheaf condition.

To show continuity, we already know that our lifted function restricted to any `U i` is the
original continuous function we had here,
and since continuity is a local condition we should be done!
-/
-- example (T : Top.{u}) : sheaf_condition (presheaf_to_Top X T) :=
