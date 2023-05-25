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
{HM : Type*} [topological_space HM]
{EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM] {IM : model_with_corners 𝕜 EM HM}
{M : Type*} [topological_space M] [charted_space HM M] [_i : smooth_manifold_with_corners IM M]
{E E' : Type*} [normed_add_comm_group E] [normed_add_comm_group E'] [normed_space 𝕜 E]
  [normed_space 𝕜 E']
{H H' : Type*} [topological_space H] [topological_space H'] {I : model_with_corners 𝕜 E H}
  {I' : model_with_corners 𝕜 E' H'}

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
  mdifferentiable IM IM (set.inclusion h : U → V) :=
begin
  rintros ⟨x, hx : x ∈ U⟩,
  rw mdifferentiable_at_iff_lift_prop_at,
  apply (differentiable_within_at_local_invariant_prop IM IM).bar',
  { intros y,
    dsimp [differentiable_within_at_prop],
    rw [set.univ_inter],
    refine differentiable_within_at_id.congr _ _,
    { exact IM.right_inv_on },
    { exact congr_arg IM (IM.left_inv y) } },
  apply_instance
end

end

section lie_group
variables (G G' : Type*) [group G] [group G'] [topological_space G] [topological_space G']
  [charted_space H G] [charted_space H' G'] [lie_group I G] [lie_group I' G']
include _i

variables (IM I M)

/-- For a Lie group `G`, the subring of `M → G` consisting of the `mdifferentiable` functions.
-/
@[to_additive] def mdifferentiable_subgroup : subgroup (M → G) :=
{ carrier := {f | mdifferentiable IM I f},
  mul_mem' := λ f g hf hg, mdifferentiable.mul' hf hg,
  one_mem' := (mdifferentiable_const IM I : mdifferentiable IM I (λ _, (1:G))),
  inv_mem' := λ f hf, mdifferentiable.inv' hf }

/-- For a `I`-Lie group `G` and `I`-smooth manifold `M`, the subring of `M → G` consisting of
the `lift_prop (differentiable_within_at_prop IM I)` functions. -/
@[to_additive] def differentiable_within_at_local_invariant_prop_subgroup : subgroup (M → G) :=
(mdifferentiable_subgroup IM M I G).copy
  {f | lift_prop (differentiable_within_at_prop IM I) f}
  begin
    ext f,
    apply forall_congr,
    intros x,
    exact (mdifferentiable_at_iff_lift_prop_at IM I f x).symm
  end

@[to_additive] instance :
  has_coe_to_fun (differentiable_within_at_local_invariant_prop_subgroup IM M I G) (λ _, M → G) :=
⟨λ f, f.1⟩

variables {IM I M G}

@[to_additive] lemma differentiable_within_at_local_invariant_prop_subgroup.mdifferentiable
  (f : differentiable_within_at_local_invariant_prop_subgroup IM M I G) :
  mdifferentiable IM I f :=
begin
  intro x,
  rw mdifferentiable_at_iff_lift_prop_at,
  exact f.prop x,
end

variables (IM M) (φ : G →* G') (hφ : smooth I I' φ)

@[to_additive] def monoid_hom.comp_right_mdifferentiable (φ : G →* G') (hφ : smooth I I' φ) :
  differentiable_within_at_local_invariant_prop_subgroup IM M I G
  →* differentiable_within_at_local_invariant_prop_subgroup IM M I' G' :=
{ to_fun := λ f,
  begin
    refine ⟨φ ∘ f, _⟩,
    intro x,
    have : lift_prop_at _ _ x := f.prop x,
    rw [←mdifferentiable_at_iff_lift_prop_at] at ⊢ this,
    exact (hφ.mdifferentiable _).comp _ this,
  end,
  map_one' := by ext x; show φ 1 = 1; simp,
  map_mul' := λ f g, by ext x; show φ (f x * g x) = φ (f x) * φ (g x); simp }

variables (I G) {M}

/-- For a Lie group `G`, the "restriction" group homomorphism from
`mdifferentiable_subgroup IM V I G` to `mdifferentiable_subgroup IM U I G`. -/
@[to_additive] def mdifferentiable_subgroup_restrict {U V : opens M} (h : U ≤ V) :
  mdifferentiable_subgroup IM V I G →* mdifferentiable_subgroup IM U I G :=
monoid_hom.cod_restrict
  (monoid_hom.restrict
    (monoid_hom.comp_right (set.inclusion h) : (V → G) →* (U → G))
    (mdifferentiable_subgroup IM V I G))
  (mdifferentiable_subgroup IM U I G)
  (λ f, mdifferentiable.comp f.prop (mdifferentiable_inclusion h))

/-- For a Lie group `G`, the "restriction" group homomorphism from
`mdifferentiable_subgroup IM V I G` to `mdifferentiable_subgroup IM U I G`. -/
@[to_additive]
def differentiable_within_at_local_invariant_prop_subgroup_restrict {U V : opens M} (h : U ≤ V) :
  differentiable_within_at_local_invariant_prop_subgroup IM V I G
  →* differentiable_within_at_local_invariant_prop_subgroup IM U I G :=
monoid_hom.cod_restrict
  (monoid_hom.restrict
    (monoid_hom.comp_right (set.inclusion h) : (V → G) →* (U → G))
    (differentiable_within_at_local_invariant_prop_subgroup IM V I G))
  (differentiable_within_at_local_invariant_prop_subgroup IM U I G)
  begin
    let i : U → V := set.inclusion h,
    rintros ⟨f : V → G, hf⟩ x,
    change lift_prop_at (differentiable_within_at_prop IM I)  _ _,
    have H : lift_prop_at (differentiable_within_at_prop IM I) (f : V → G) (i x) := hf (i x),
    rw ← mdifferentiable_at_iff_lift_prop_at at *,
    exact H.comp x (mdifferentiable_inclusion h x),
  end

end lie_group

section smooth_ring
variables (R : Type*) [ring R] [topological_space R] [charted_space H R] [smooth_ring I R]
include _i

variables (IM I M)

/-- For a smooth ring `R`, the subring of `M → R` consisting of the `mdifferentiable` functions.
-/
def mdifferentiable_subring : subring (M → R) :=
{ carrier := {f | mdifferentiable IM I f},
  mul_mem' := λ f g hf hg, mdifferentiable.mul' hf hg,
  one_mem' := (mdifferentiable_const IM I : mdifferentiable IM I (λ _, (1:R))),
  add_mem' := λ f g hf hg, mdifferentiable.add' hf hg,
  zero_mem' := (mdifferentiable_const IM I : mdifferentiable IM I (λ _, (0:R))),
  neg_mem' := λ f hf, mdifferentiable.neg' hf }

/-- For a `I`-smooth ring `R` and `I`-smooth manifold `M`, the subring of `M → R` consisting of
the `lift_prop (differentiable_within_at_prop IM I)` functions. -/
def differentiable_within_at_local_invariant_prop_subring : subring (M → R) :=
(mdifferentiable_subring IM M I R).copy
  {f | lift_prop (differentiable_within_at_prop IM I) f}
  begin
    ext f,
    apply forall_congr,
    intros x,
    exact (mdifferentiable_at_iff_lift_prop_at IM I f x).symm
  end

variables {M}

/-- For a smooth ring `R`, the "restriction" ring homomorphism from
`mdifferentiable_subring IM V I R` to `mdifferentiable_subring IM U I R`. -/
def mdifferentiable_subring_restrict {U V : opens M} (h : U ≤ V) :
  mdifferentiable_subring IM V I R →+* mdifferentiable_subring IM U I R :=
ring_hom.cod_restrict
  (ring_hom.dom_restrict
    (ring_hom.comp_right (set.inclusion h) : (V → R) →+* (U → R))
    (mdifferentiable_subring IM V I R))
  (mdifferentiable_subring IM U I R)
  (λ f, mdifferentiable.comp f.prop (mdifferentiable_inclusion h))

/-- For a smooth ring `R`, the "restriction" ring homomorphism from
`mdifferentiable_subring IM V I R` to `mdifferentiable_subring IM U I R`. -/
def differentiable_within_at_local_invariant_prop_subring_restrict {U V : opens M} (h : U ≤ V) :
  differentiable_within_at_local_invariant_prop_subring IM V I R
  →+* differentiable_within_at_local_invariant_prop_subring IM U I R :=
ring_hom.cod_restrict
  (ring_hom.dom_restrict
    (ring_hom.comp_right (set.inclusion h) : (V → R) →+* (U → R))
    (differentiable_within_at_local_invariant_prop_subring IM V I R))
  (differentiable_within_at_local_invariant_prop_subring IM U I R)
  begin
    let i : U → V := set.inclusion h,
    rintros ⟨f : V → R, hf⟩ x,
    change lift_prop_at (differentiable_within_at_prop IM I)  _ _,
    have H : lift_prop_at (differentiable_within_at_prop IM I) (f : V → R) (i x) := hf (i x),
    rw ← mdifferentiable_at_iff_lift_prop_at at *,
    exact H.comp x (mdifferentiable_inclusion h x),
  end

end smooth_ring
