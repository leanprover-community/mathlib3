/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.sites.sheaf_of_types


/-!
# The canonical topology on a category

We define the finest (largest) Grothendieck topology for which a given presheaf `P` is a sheaf.
This is well defined since if `P` is a sheaf for a topology `J`, then it is a sheaf for any
coarser (smaller) topology. Nonetheless we define the topology explicitly by specifying its sieves:
A sieve `S` on `X` is covering for `finest_topology_single P` iff
  for any `f : Y ⟶ X`, `P` satisfies the sheaf axiom for `S.pullback f`.
Showing that this is a genuine Grothendieck topology (namely that it satisfies the transitivity
axiom) forms the bulk of this file.

This generalises to a set of presheaves, giving the topology `finest_topology Ps` which is the
finest topology for which every presheaf in `Ps` is a sheaf.
Using `Ps` as the set of representable presheaves defines the `canonical_topology`: the finest
topology for which every representable is a sheaf.

A Grothendieck topology is called `subcanonical` if it is smaller than the canonical topology,
equivalently it is subcanonical iff every representable presheaf is a sheaf.

## References
* https://ncatlab.org/nlab/show/canonical+topology
* https://ncatlab.org/nlab/show/subcanonical+coverage
* https://stacks.math.columbia.edu/tag/00Z9
* https://math.stackexchange.com/a/358709/
-/

universes v u
namespace category_theory

open category_theory category limits sieve classical

variables {C : Type u} [category.{v} C]

namespace sheaf

variables {P : Cᵒᵖ ⥤ Type v}
variables {X Y : C} {S : sieve X} {R : presieve X}
variables (J J₂ : grothendieck_topology C)

/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `is_sheaf_for_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
lemma is_sheaf_for_bind (P : Cᵒᵖ ⥤ Type v) (U : sieve X)
  (B : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → sieve Y)
  (hU : presieve.is_sheaf_for P U)
  (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), presieve.is_sheaf_for P (B hf))
  (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y),
              presieve.is_separated_for P ((B h).pullback g)) :
  presieve.is_sheaf_for P (sieve.bind U B) :=
begin
  intros s hs,
  let y : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), presieve.family_of_elements P (B hf) :=
    λ Y f hf Z g hg, s _ (presieve.bind_comp _ _ hg),
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).compatible,
  { intros Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm,
    apply hs,
    apply reassoc_of comm },
  let t : presieve.family_of_elements P U := λ Y f hf, (hB hf).amalgamate (y hf) (hy hf),
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).is_amalgamation (t f hf) :=
    λ Y f hf, (hB hf).is_amalgamation _,
  have hT : t.compatible,
  { rw presieve.compatible_iff_sieve_compatible,
    intros Z W f h hf,
    apply (hB (U.downward_closed hf h)).is_separated_for.ext,
    intros Y l hl,
    apply (hB' hf (l ≫ h)).ext,
    intros M m hm,
    have : bind U B (m ≫ l ≫ h ≫ f),
    { have : bind U B _ := presieve.bind_comp f hf hm,
      simpa using this },
    transitivity s (m ≫ l ≫ h ≫ f) this,
    { have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m),
      rw [op_comp, functor_to_types.map_comp_apply] at this,
      rw this,
      change s _ _ = s _ _,
      simp },
    { have : s _ _ = _ := (ht hf _ hm).symm,
      simp only [assoc] at this,
      rw this,
      simp } },
  refine ⟨hU.amalgamate t hT, _, _⟩,
  { rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩,
    rw [op_comp, functor_to_types.map_comp_apply, presieve.is_sheaf_for.valid_glue _ _ _ hg],
    apply ht hg _ hf },
  { intros y hy,
    apply hU.is_separated_for.ext,
    intros Y f hf,
    apply (hB hf).is_separated_for.ext,
    intros Z g hg,
    rw [←functor_to_types.map_comp_apply, ←op_comp, hy _ (presieve.bind_comp _ _ hg),
        hU.valid_glue _ _ hf, ht hf _ hg] }
end

/--
Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `finest_topology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
lemma is_sheaf_for_trans (P : Cᵒᵖ ⥤ Type v) (R S : sieve X)
  (hR : presieve.is_sheaf_for P R)
  (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S f), presieve.is_separated_for P (R.pullback f))
  (hS : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : R f), presieve.is_sheaf_for P (S.pullback f)) :
  presieve.is_sheaf_for P S :=
begin
  have : (bind R (λ Y f hf, S.pullback f) : presieve X) ≤ S,
  { rintros Z f ⟨W, f, g, hg, (hf : S _), rfl⟩,
    apply hf },
  apply presieve.is_sheaf_for_subsieve_aux P this,
  apply is_sheaf_for_bind _ _ _ hR hS,
  { intros Y f hf Z g,
    dsimp,
    rw ← pullback_comp,
    apply (hS (R.downward_closed hf _)).is_separated_for },
  { intros Y f hf,
    have : (sieve.pullback f (bind R (λ T (k : T ⟶ X) (hf : R k), pullback k S))) = R.pullback f,
    { ext Z g,
      split,
      { rintro ⟨W, k, l, hl, _, comm⟩,
        rw [pullback_apply, ← comm],
        simp [hl] },
      { intro a,
        refine ⟨Z, 𝟙 Z, _, a, _⟩,
        simp [hf] } },
    rw this,
    apply hR' hf },
end

/--
Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf.

This is a special case of https://stacks.math.columbia.edu/tag/00Z9, but following a different
proof (see the comments there).
-/
def finest_topology_single (P : Cᵒᵖ ⥤ Type v) : grothendieck_topology C :=
{ sieves := λ X S, ∀ Y (f : Y ⟶ X), presieve.is_sheaf_for P (S.pullback f),
  top_mem' := λ X Y f,
  begin
    rw sieve.pullback_top,
    exact presieve.is_sheaf_for_top_sieve P,
  end,
  pullback_stable' := λ X Y S f hS Z g,
  begin
    rw ← pullback_comp,
    apply hS,
  end,
  transitive' := λ X S hS R hR Z g,
  begin
    -- This is the hard part of the construction, showing that the given set of sieves satisfies
    -- the transitivity axiom.
    refine is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _,
    { intros Y f hf,
      rw ← pullback_comp,
      apply (hS _ _).is_separated_for },
    { intros Y f hf,
      have := hR hf _ (𝟙 _),
      rw [pullback_id, pullback_comp] at this,
      apply this },
  end }

/--
Construct the finest (largest) Grothendieck topology for which all the given presheaves are sheaves.

This is equal to the construction of https://stacks.math.columbia.edu/tag/00Z9.
-/
def finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) : grothendieck_topology C :=
Inf (finest_topology_single '' Ps)

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
lemma sheaf_for_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) (h : P ∈ Ps) :
  presieve.is_sheaf (finest_topology Ps) P :=
λ X S hS, by simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finest_topology Ps`.
-/
lemma le_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) (J : grothendieck_topology C)
  (hJ : ∀ P ∈ Ps, presieve.is_sheaf J P) : J ≤ finest_topology Ps :=
begin
  rintro X S hS _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩,
  intros Y f, -- this can't be combined with the previous because the `subst` is applied at the end
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS),
end

/--
The `canonical_topology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf.

See https://stacks.math.columbia.edu/tag/00ZA
-/
def canonical_topology (C : Type u) [category.{v} C] : grothendieck_topology C :=
finest_topology (set.range yoneda.obj)

/-- `yoneda.obj X` is a sheaf for the canonical topology. -/
lemma is_sheaf_yoneda_obj (X : C) : presieve.is_sheaf (canonical_topology C) (yoneda.obj X) :=
λ Y S hS, sheaf_for_finest_topology _ (set.mem_range_self _) _ hS

/-- A representable functor is a sheaf for the canonical topology. -/
lemma is_sheaf_of_representable (P : Cᵒᵖ ⥤ Type v) [P.representable] :
  presieve.is_sheaf (canonical_topology C) P :=
presieve.is_sheaf_iso (canonical_topology C) P.repr_w (is_sheaf_yoneda_obj _)

/--
A subcanonical topology is a topology which is smaller than the canonical topology.
Equivalently, a topology is subcanonical iff every representable is a sheaf.
-/
def subcanonical (J : grothendieck_topology C) : Prop :=
J ≤ canonical_topology C

namespace subcanonical

/-- If every functor `yoneda.obj X` is a `J`-sheaf, then `J` is subcanonical. -/
lemma of_yoneda_is_sheaf (J : grothendieck_topology C)
  (h : ∀ X, presieve.is_sheaf J (yoneda.obj X)) :
  subcanonical J :=
le_finest_topology _ _ (by { rintro P ⟨X, rfl⟩, apply h })

/-- If `J` is subcanonical, then any representable is a `J`-sheaf. -/
lemma is_sheaf_of_representable {J : grothendieck_topology C} (hJ : subcanonical J)
  (P : Cᵒᵖ ⥤ Type v) [P.representable] :
  presieve.is_sheaf J P :=
presieve.is_sheaf_of_le _ hJ (is_sheaf_of_representable P)

end subcanonical

end sheaf

end category_theory
