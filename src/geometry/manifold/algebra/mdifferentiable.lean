/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.algebra.structures
import geometry.manifold.local_invariant_properties_aux

/-! supplement to `geometry.manifold.algebra.*` -/

noncomputable theory
open topological_space

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [_i : smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}

section /-! # general facts -/

/-- For `φ : A → B` and a group `G`, the "right-composition" homomorphism from `B → G` to `A → G`.
-/
@[to_additive]
def monoid_hom.comp_right {A B G : Type*} [group G] (φ : A → B) : (B → G) →* (A → G) :=
{ to_fun := λ f, f ∘ φ,
  map_one' := rfl,
  map_mul' := λ f g, rfl }

/-- For `φ : A → B` and a ring `R`, the "right-composition" homomorphism from `B → R` to `A → R`. -/
def ring_hom.comp_right {A B R : Type*} [ring R] (φ : A → B) : (B → R) →+* (A → R) :=
{ to_fun := λ f, f ∘ φ,
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl }

end

section /-! # general facts for `mdfderiv` file -/
include _i

lemma mdifferentiable_inclusion {U V : opens M} (h : U ≤ V) :
  mdifferentiable I I (set.inclusion h : U → V) :=
begin
  rintros ⟨x, hx : x ∈ U⟩,
  rw mdifferentiable_at_iff_lift_prop_at,
  apply (differentiable_within_at_local_invariant_prop I I).bar',
  { intros y,
    dsimp [differentiable_within_at_prop],
    rw [set.univ_inter],
    refine differentiable_within_at_id.congr _ _,
    { exact I.right_inv_on },
    { exact congr_arg I (I.left_inv y) } },
  apply_instance
end

end

section lie_group
variables (G : Type*) [group G] [topological_space G] [charted_space H' G] [lie_group I' G]
include _i

variables (I I' M)

/-- For a Lie group `G`, the subring of `M → G` consisting of the `mdifferentiable` functions.
-/
@[to_additive] def mdifferentiable_subgroup : subgroup (M → G) :=
{ carrier := {f | mdifferentiable I I' f},
  mul_mem' := λ f g hf hg, mdifferentiable.mul' hf hg,
  one_mem' := (mdifferentiable_const I I' : mdifferentiable I I' (λ _, (1:G))),
  inv_mem' := λ f hf, mdifferentiable.inv' hf }

/-- For a `I'`-Lie group `G` and `I`-smooth manifold `M`, the subring of `M → G` consisting of
the `lift_prop (differentiable_within_at_prop I I')` functions. -/
@[to_additive] def differentiable_within_at_local_invariant_prop_subgroup : subgroup (M → G) :=
(mdifferentiable_subgroup I M I' G).copy
  {f | lift_prop (differentiable_within_at_prop I I') f}
  begin
    ext f,
    apply forall_congr,
    intros x,
    exact (mdifferentiable_at_iff_lift_prop_at I I' f x).symm
  end

variables {M}

/-- For a Lie group `G`, the "restriction" group homomorphism from
`mdifferentiable_subgroup I V I' G` to `mdifferentiable_subgroup I U I' G`. -/
@[to_additive] def mdifferentiable_subgroup_restrict {U V : opens M} (h : U ≤ V) :
  mdifferentiable_subgroup I V I' G →* mdifferentiable_subgroup I U I' G :=
monoid_hom.cod_restrict
  (monoid_hom.restrict
    (monoid_hom.comp_right (set.inclusion h) : (V → G) →* (U → G))
    (mdifferentiable_subgroup I V I' G))
  (mdifferentiable_subgroup I U I' G)
  (λ f, mdifferentiable.comp f.prop (mdifferentiable_inclusion h))

/-- For a Lie group `G`, the "restriction" group homomorphism from
`mdifferentiable_subgroup I V I' G` to `mdifferentiable_subgroup I U I' G`. -/
@[to_additive]
def differentiable_within_at_local_invariant_prop_subgroup_restrict {U V : opens M} (h : U ≤ V) :
  differentiable_within_at_local_invariant_prop_subgroup I V I' G
  →* differentiable_within_at_local_invariant_prop_subgroup I U I' G :=
monoid_hom.cod_restrict
  (monoid_hom.restrict
    (monoid_hom.comp_right (set.inclusion h) : (V → G) →* (U → G))
    (differentiable_within_at_local_invariant_prop_subgroup I V I' G))
  (differentiable_within_at_local_invariant_prop_subgroup I U I' G)
  begin
    let i : U → V := set.inclusion h,
    rintros ⟨f : V → G, hf⟩ x,
    change lift_prop_at (differentiable_within_at_prop I I')  _ _,
    have H : lift_prop_at (differentiable_within_at_prop I I') (f : V → G) (i x) := hf (i x),
    rw ← mdifferentiable_at_iff_lift_prop_at at *,
    exact H.comp x (mdifferentiable_inclusion h x),
  end

end lie_group

section smooth_ring
variables (R : Type*) [ring R] [topological_space R] [charted_space H' R] [smooth_ring I' R]
include _i

variables (I I' M)

/-- For a smooth ring `R`, the subring of `M → R` consisting of the `mdifferentiable` functions.
-/
def mdifferentiable_subring : subring (M → R) :=
{ carrier := {f | mdifferentiable I I' f},
  mul_mem' := λ f g hf hg, mdifferentiable.mul' hf hg,
  one_mem' := (mdifferentiable_const I I' : mdifferentiable I I' (λ _, (1:R))),
  add_mem' := λ f g hf hg, mdifferentiable.add' hf hg,
  zero_mem' := (mdifferentiable_const I I' : mdifferentiable I I' (λ _, (0:R))),
  neg_mem' := λ f hf, mdifferentiable.neg' hf }

/-- For a `I'`-smooth ring `R` and `I`-smooth manifold `M`, the subring of `M → R` consisting of
the `lift_prop (differentiable_within_at_prop I I')` functions. -/
def differentiable_within_at_local_invariant_prop_subring : subring (M → R) :=
(mdifferentiable_subring I M I' R).copy
  {f | lift_prop (differentiable_within_at_prop I I') f}
  begin
    ext f,
    apply forall_congr,
    intros x,
    exact (mdifferentiable_at_iff_lift_prop_at I I' f x).symm
  end

variables {M}

/-- For a smooth ring `R`, the "restriction" ring homomorphism from
`mdifferentiable_subring I V I' R` to `mdifferentiable_subring I U I' R`. -/
def mdifferentiable_subring_restrict {U V : opens M} (h : U ≤ V) :
  mdifferentiable_subring I V I' R →+* mdifferentiable_subring I U I' R :=
ring_hom.cod_restrict
  (ring_hom.dom_restrict
    (ring_hom.comp_right (set.inclusion h) : (V → R) →+* (U → R))
    (mdifferentiable_subring I V I' R))
  (mdifferentiable_subring I U I' R)
  (λ f, mdifferentiable.comp f.prop (mdifferentiable_inclusion h))

/-- For a smooth ring `R`, the "restriction" ring homomorphism from
`mdifferentiable_subring I V I' R` to `mdifferentiable_subring I U I' R`. -/
def differentiable_within_at_local_invariant_prop_subring_restrict {U V : opens M} (h : U ≤ V) :
  differentiable_within_at_local_invariant_prop_subring I V I' R
  →+* differentiable_within_at_local_invariant_prop_subring I U I' R :=
ring_hom.cod_restrict
  (ring_hom.dom_restrict
    (ring_hom.comp_right (set.inclusion h) : (V → R) →+* (U → R))
    (differentiable_within_at_local_invariant_prop_subring I V I' R))
  (differentiable_within_at_local_invariant_prop_subring I U I' R)
  begin
    let i : U → V := set.inclusion h,
    rintros ⟨f : V → R, hf⟩ x,
    change lift_prop_at (differentiable_within_at_prop I I')  _ _,
    have H : lift_prop_at (differentiable_within_at_prop I I') (f : V → R) (i x) := hf (i x),
    rw ← mdifferentiable_at_iff_lift_prop_at at *,
    exact H.comp x (mdifferentiable_inclusion h x),
  end

end smooth_ring
