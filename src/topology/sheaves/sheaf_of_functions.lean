/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import topology.sheaves.presheaf_of_functions
import topology.sheaves.sheaf
import category_theory.limits.types
import topology.local_homeomorph

open category_theory
open category_theory.limits
open topological_space

universe u

lemma open_embedding.continuous_at_iff {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  {f : X → Y} {g : Y → Z} (hf : open_embedding f) {x : X} :
  continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
begin
  haveI : nonempty X := ⟨x⟩,
  convert ((hf.to_local_homeomorph.continuous_at_iff_continuous_at_comp_right) _).symm,
  { apply (local_homeomorph.left_inv _ _).symm,
    simp, },
  { simp, },
end

@[simp] lemma classical.indefinite_description_val {α : Sort u} (p : α → Prop) (h : ∃ x, p x) :
  (classical.indefinite_description p h).val = classical.some h := rfl

@[simp] lemma classical.indefinite_description_property {α : Sort u} (p : α → Prop) (h : ∃ x, p x) :
  (classical.indefinite_description p h).property = classical.some_spec h := rfl

noncomputable theory


variables (X : Top.{u})

open Top

namespace Top.sheaf_condition

/--
We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a type family `T`,
so we do the more general case.
-/
def to_Types (T : X → Type u) : sheaf_condition (presheaf_to_Types X T) :=
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
    change x ∈ supr U at mem, -- FIXME needs some lemmas!
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
    -- FIXME make proper simp lemmas
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
    clear s₀ s₁,

    -- We've got half of this: we knew `x ∈ U i` right from the start:
    refine ⟨_, mem⟩,
    dsimp,

    -- We now do a ridiculous ninja move.
    -- Notice that when we introduced `j`, we just introduced it as some metavariable.
    -- However at this point it's received a concrete value,
    -- because Lean's unification has worked out that this `j` must have been the index
    -- that we picked using choice back when constructing the lift.
    -- From this, we can extract the evidence that `x ∈ U j`:

    -- FIXME this is surely unnecessarily cumbersome:
    have := classical.spec_of_eq_some (rfl : j = j),
    exact this, },
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
end.

-- We verify that the non-dependent version is an immediate consequence:
def to_Type (T : Type u) : sheaf_condition (presheaf_to_Type X T) :=
to_Types X (λ _, T)

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

/--
The natural transformation from the sheaf condition diagram for continuous functions
to the sheaf condition diagram for arbitrary functions,
given by forgetting continuity everywhere.
-/
def forget_continuity (T : Top.{u}) {ι : Type u} (U : ι → opens X) :
  diagram (presheaf_to_Top X T) U ⟶ diagram (presheaf_to_Type X T) U :=
{ app :=
  begin
    rintro ⟨_|_⟩,
    exact (pi.map (λ i f, f.to_fun)),
    exact (pi.map (λ p f, f.to_fun)),
  end,
  naturality' := by rintro ⟨_|_⟩ ⟨_|_⟩ f; cases f; refl, }

example (T : Top.{u}) : sheaf_condition (presheaf_to_Top X T) :=
λ ι U,
-- U is a family of open sets, indexed by `i`.
-- In the informal comments below, I'll just write `U` to represent the union.
begin
  refine fork.is_limit.mk _ _ _ _,
  { intros s f,
    fsplit,
    -- First, we use the fact that not necessarily continuous functions form a sheaf,
    -- to provide the lift.
    { let s' := (cones.postcompose (forget_continuity.{u u} X T U)).obj s,
      exact (to_Type X T U).lift s' f, },
    -- Second, we need to do the actual work, proving this lift is continuous.
    { dsimp,
      apply continuous_iff_continuous_at.2,
      rintro ⟨x, mem⟩,
      change x ∈ supr U at mem, -- FIXME needs some lemmas!
      simp only [opens.mem_supr] at mem,
      choose i hi using mem,

      let s' := (cones.postcompose (forget_continuity.{u u} X T U)).obj s,
      have := (to_Type X T U).fac s' walking_parallel_pair.zero,
      have := this =≫ pi.π _ i,
      simp only [sheaf_condition.res, limit.lift_π, cones.postcompose_obj_π, sheaf_condition.fork_π_app_walking_parallel_pair_zero,
 fan.mk_π_app, nat_trans.comp_app, category.assoc] at this,
      have := congr_fun this f,
      simp only [forget_continuity, discrete.nat_trans_app, types_comp_apply, presheaf_to_Type_map, limit.map_π] at this,

      have : continuous ((to_Type X ↥T U).lift s' f ∘ ((opens.le_supr U i).op)),
      { rw this, continuity, },

      rw continuous_iff_continuous_at at this,
      specialize this ⟨x, hi⟩,

      exact (opens.hom_open_embedding (opens.le_supr U i)).continuous_at_iff.1 this,

     },
    },
  { -- Proving the factorisation condition is straightforward:
    -- we observe that checking equality of continuous functions reduces to
    -- checking equality of the underlying functions,
    -- and use the factorisation condition for the sheaf condition for functions.
    intros s,
    ext i f : 2,
    apply continuous_map.coe_inj,
    exact congr_fun (((to_Type X T U).fac _ walking_parallel_pair.zero) =≫ pi.π _ i) _, },
  { -- Similarly for proving the uniqueness condition, after a certain amount of bookkeeping.
    intros s m w,
    ext f : 1,
    apply continuous_map.coe_inj,
    let s' := (cones.postcompose (forget_continuity.{u u} X T U)).obj s,
    refine congr_fun ((to_Type X T U).uniq s' _ _) f,
    -- We "just" need to fix up our `w` to match the missing `w` argument.
    -- Unfortunately, it's really gross.
    intro j,
    specialize w j,
    dsimp [s'],
    rw ←w, clear w,
    simp only [category.assoc],
    rcases j with ⟨_|_⟩,
    { apply limit.hom_ext,
      intro i,
      simp only [category.assoc, limit.map_π, forget_continuity],
      ext f' ⟨x, mem⟩,
      simp [presheaf_to_Top, presheaf_to_Type, res],
      refl, },
    { apply limit.hom_ext,
      intro i,
      simp only [category.assoc, limit.map_π, forget_continuity],
      ext f' ⟨x, mem⟩,
      simp [presheaf_to_Top, presheaf_to_Type, res, left_res],
      refl, }, },
end

end Top.sheaf_condition
