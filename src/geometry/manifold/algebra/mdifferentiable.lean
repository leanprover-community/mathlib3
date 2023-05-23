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

/-- For `φ : A → B` and a ring `R`, the "right-composition" homomorphism from `B → R` to `A → R`. -/
def ring_hom.comp_right {A B R : Type*} [ring R] (φ : A → B) : (B → R) →+* (A → R) :=
{ to_fun := λ f, f ∘ φ,
  map_one' := rfl,
  map_mul' := λ f g, rfl,
  map_zero' := rfl,
  map_add' := λ f g, rfl }

end

section /-! # general facts for `mdfderiv` file -/

variables {M' : Type*} [topological_space M'] [charted_space H' M']
  {f g : M → M'} {s : set M} {x : M}

lemma mdifferentiable_within_at.prod_mk
  (hf : mdifferentiable_within_at I I' f s x) (hg : mdifferentiable_within_at I I' g s x) :
  mdifferentiable_within_at I (I'.prod I') (λ x, (f x, g x)) s x :=
⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

lemma mdifferentiable_at.prod_mk
  (hf : mdifferentiable_at I I' f x) (hg : mdifferentiable_at I I' g x) :
  mdifferentiable_at I (I'.prod I') (λ x, (f x, g x)) x :=
⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

include _i

lemma mdifferentiable_inclusion {U V : opens M} (h : U ≤ V) :
  mdifferentiable I I (set.inclusion h : U → V) :=
begin
  rintros ⟨x, hx : x ∈ U⟩,
  rw mdifferentiable_at_iff_lift_prop_at,
  apply (differentiable_within_at_local_invariant_prop I I).bar',
  apply_instance,
end

end

section has_smooth_mul
variables {G : Type*} [has_mul G] [topological_space G] [charted_space H' G] [has_smooth_mul I' G]
variables {f g : M → G} {s : set M} {x : M}
include _i

@[to_additive]
lemma mdifferentiable_within_at.mul
  (hf : mdifferentiable_within_at I I' f s x)
  (hg : mdifferentiable_within_at I I' g s x) : mdifferentiable_within_at I I' (f * g) s x :=
((smooth_mul I').smooth_at.mdifferentiable_within_at le_top).comp x (hf.prod_mk hg) le_top

@[to_additive]
lemma mdifferentiable_at.mul
  (hf : mdifferentiable_at I I' f x)
  (hg : mdifferentiable_at I I' g x) : mdifferentiable_at I I' (f * g) x :=
((smooth_mul I').smooth_at.mdifferentiable_at le_top).comp x (hf.prod_mk hg)

@[to_additive]
lemma mdifferentiable.mul
  (hf : mdifferentiable I I' f)
  (hg : mdifferentiable I I' g) : mdifferentiable I I' (f * g) :=
λ x, (hf x).mul (hg x)

end has_smooth_mul


section smooth_ring
variables {R : Type*} [ring R] [topological_space R] [charted_space H' R] [smooth_ring I' R]
variables {f g : M → R} {s : set M} {x : M}
include _i

lemma mdifferentiable_within_at.neg
  (hf : mdifferentiable_within_at I I' f s x) : mdifferentiable_within_at I I' (-f) s x :=
((smooth_neg I').smooth_at.mdifferentiable_within_at le_top).comp x hf le_top

lemma mdifferentiable_at.neg
  (hf : mdifferentiable_at I I' f x) : mdifferentiable_at I I' (-f) x :=
((smooth_neg I').smooth_at.mdifferentiable_at le_top).comp x hf

lemma mdifferentiable.neg
  (hf : mdifferentiable I I' f) : mdifferentiable I I' (-f) :=
λ x, (hf x).neg

variables (I I' M R)

/-- For a smooth ring `R`, the subring of `M → R` consisting of the `mdifferentiable` functions.
-/
def mdifferentiable_subring : subring (M → R) :=
{ carrier := {f | mdifferentiable I I' f},
  mul_mem' := λ f g hf hg, mdifferentiable.mul hf hg,
  one_mem' := (mdifferentiable_const I I' : mdifferentiable I I' (λ _, (1:R))),
  add_mem' := λ f g hf hg, mdifferentiable.add hf hg,
  zero_mem' := (mdifferentiable_const I I' : mdifferentiable I I' (λ _, (0:R))),
  neg_mem' := λ f hf, mdifferentiable.neg hf }

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
def mdifferentiable_restrict {U V : opens M} (h : U ≤ V) :
  mdifferentiable_subring I V I' R →+* mdifferentiable_subring I U I' R :=
ring_hom.cod_restrict
  (ring_hom.restrict
    (ring_hom.comp_right (set.inclusion h) : (V → R) →+* (U → R))
    (mdifferentiable_subring I V I' R))
  (mdifferentiable_subring I U I' R)
  (λ f, mdifferentiable.comp f.prop (mdifferentiable_inclusion h))

/-- For a smooth ring `R`, the "restriction" ring homomorphism from
`mdifferentiable_subring I V I' R` to `mdifferentiable_subring I U I' R`. -/
def differentiable_within_at_local_invariant_prop_restrict {U V : opens M} (h : U ≤ V) :
  differentiable_within_at_local_invariant_prop_subring I V I' R
  →+* differentiable_within_at_local_invariant_prop_subring I U I' R :=
ring_hom.cod_restrict
  (ring_hom.restrict
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
