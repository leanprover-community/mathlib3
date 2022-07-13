/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Vincent Beffara
-/
import linear_algebra.finite_dimensional
import topology.algebra.group_with_zero
import topology.algebra.group
import topology.constructions
import topology.separation

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is notation for `projectivization K V`, the projectivization of a `K`-vector space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `projectivization.mk'' H h` where `H : submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `projectivization.equiv_submodule` is the equivalence between `ℙ K V`
  and `{ H : submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

## Projects
Everything in this file can be done for `division_ring`s instead of `field`s, but
this would require a significant refactor of the results from
`linear_algebra.finite_dimensional` and its imports.

-/

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivization_setoid : setoid { v : V // v ≠ 0 } :=
(mul_action.orbit_rel Kˣ V).comap coe

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
@[nolint has_inhabited_instance]
def projectivization := quotient (projectivization_setoid K V)

notation `ℙ` := projectivization

namespace projectivization

variables {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : ℙ K V := quotient.mk' ⟨v,hv⟩

/-- A variant of `projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V := quotient.mk' v

@[simp]
lemma mk'_eq_mk (v : { v : V // v ≠ 0}) :
  mk' K v = mk K v v.2 :=
by { dsimp [mk, mk'], congr' 1, simp }

@[simp]
lemma quotient_mk_eq_mk (z : V) (h : z ≠ 0) :
  @quotient.mk _ (projectivization_setoid _ _) ⟨z, h⟩ = mk K z h := rfl

@[simp]
lemma quotient_mk'_eq_mk {z : V} (h : z ≠ 0) :
  @quotient.mk' _ (projectivization_setoid _ _) ⟨z, h⟩ = mk K z h := rfl

instance [nontrivial V] : nonempty (ℙ K V) :=
let ⟨v, hv⟩ := exists_ne (0 : V) in ⟨mk K v hv⟩

instance [topological_space V] : topological_space (ℙ K V) :=
quotient.topological_space

variable {K}

/-- Choose a representative of `v : projectivization K V` in `V`. -/
protected noncomputable def rep (v : ℙ K V) : V := v.out'

lemma rep_nonzero (v : ℙ K V) : v.rep ≠ 0 := v.out'.2

@[simp]
lemma mk_rep (v : ℙ K V) :
  mk K v.rep v.rep_nonzero = v :=
by simp only [projectivization.rep, mk, subtype.coe_eta, quotient.out_eq']

/-- Wrapper around `quotient.lift_on' with more convenient interface in terms of `mk`. -/
def lift_on {K V α : Type*} [field K] [add_comm_group V] [module K V]
  (z : ℙ K V) (f : {w : V // w ≠ 0} → α)
  (hf : ∀ (x y : V) (hx : x ≠ 0) (hy : y ≠ 0), mk K x hx = mk K y hy → f ⟨x,hx⟩ = f ⟨y,hy⟩) : α :=
quotient.lift_on' z f (λ ⟨x, hx⟩ ⟨y, hy⟩ h, hf x y hx hy (quotient.eq'.mpr h))

@[simp]
lemma lift_on_mk {α : Type*} {z : V} (h : z ≠ 0) (f : {w : V // w ≠ 0} → α) (hf) :
  lift_on (mk K z h) f hf = f ⟨z, h⟩ := rfl

@[simp]
lemma lift_on_mk' {α : Type*} {z : V} (h : z ≠ 0) (f : {w : V // w ≠ 0} → α) (hf) :
  quotient.lift_on' (mk K z h) f hf = f ⟨z, h⟩ := rfl

open finite_dimensional

/-- Consider an element of the projectivization as a submodule of `V`. -/
protected def submodule (v : ℙ K V) : submodule K V :=
quotient.lift_on' v (λ v, K ∙ (v : V)) $ begin
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, (rfl : x • b = a)⟩,
  exact (submodule.span_singleton_group_smul_eq _ x _),
end

variable (K)

lemma mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
  mk K v hv = mk K w hw ↔ ∃ (a : Kˣ), a • w = v :=
quotient.eq'

/-- A specialization of `mk_eq_mk_iff` that is sometimes more convenient to use. -/
lemma mk_eq_mk_iff_mul_eq_mul {x y : K × K} (hx : x ≠ 0) (hy : y ≠ 0) :
  mk K x hx = mk K y hy ↔ x.1 * y.2 = x.2 * y.1 :=
begin
  rw [mk_eq_mk_iff],
  split,
  { rintro ⟨a, rfl⟩,
    simp [units.smul_def, mul_assoc, mul_comm y.1 _] },
  { intro hxy,
    rcases x with ⟨x1, x2⟩,
    rcases y with ⟨y1, y2⟩,
    rcases eq_or_ne y1 0 with (rfl | h),
    { simp only [ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hy,
      simp only [hy, mul_zero, mul_eq_zero, or_false] at hxy,
      simp only [hxy, ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hx,
      use units.mk0 (x2/y2) (div_ne_zero hx hy),
      simp [units.smul_def, hy, hxy] },
    { rcases eq_or_ne x1 0 with (rfl | h'),
      { simp only [ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hx,
        simp only [hx, h, zero_mul, zero_eq_mul, false_or] at hxy,
        contradiction },
      { use units.mk0 (x1/y1) (div_ne_zero h' h),
        simp [units.smul_def, div_mul_cancel, h, mul_comm_div', ← mul_div_assoc, hxy] } } }
end

lemma exists_smul_eq_mk_rep
  (v : V) (hv : v ≠ 0) : ∃ (a : Kˣ), a • v = (mk K v hv).rep :=
show (projectivization_setoid K V).rel _ _, from quotient.mk_out' ⟨v, hv⟩

variable {K}

/-- Define a function on the projective line from a function of the ratio of projective
coordinates. -/
def lift_of_div {α K : Type*} [field K] (f : K → α) (z : ℙ K (K × K)) : α :=
lift_on z (λ w, f (w.val.1 / w.val.2))
begin
  intros x y hx hy hxy,
  obtain ⟨a, rfl⟩ := (mk_eq_mk_iff _ _ _ _ _).mp hxy,
  exact congr_arg f (mul_div_mul_left y.1 y.2 a.ne_zero)
end

/-- An induction principle for `projectivization`.
Use as `induction v using projectivization.ind`. -/
@[elab_as_eliminator]
lemma ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) :
  ∀ p, P p :=
quotient.ind' $ subtype.rec $ by exact h

instance [topological_space K] [t1_space K] [has_continuous_sub K] [has_continuous_mul K] :
  t1_space (ℙ K (K × K)) :=
begin
  refine ⟨λ x, _⟩,
  induction x using projectivization.ind with x hx,
  have hc : continuous (λ z : {w : K × K // w ≠ 0}, z.val.1 * x.2 - z.val.2 * x.1) :=
    ((continuous_fst.comp continuous_induced_dom).mul continuous_const).sub
    ((continuous_snd.comp continuous_induced_dom).mul continuous_const),
  apply is_open_compl_iff.mp,
  change is_open {z | ¬ mk' K z = mk K x hx},
  simp_rw [mk'_eq_mk, mk_eq_mk_iff_mul_eq_mul],
  convert ← is_open_compl_singleton.preimage hc,
  ext,
  exact sub_ne_zero
end

@[continuity]
lemma continuous_lift_of_div {K α : Type*} [field K]
  [topological_space K] [t1_space K] [has_continuous_inv₀ K] [has_continuous_mul K]
  [topological_space α] {f : K → α} (hf : continuous f) :
  continuous_on (lift_of_div f) {mk K (1,0) (by simp)}ᶜ :=
begin
  rw continuous_on_iff,
  intros z hz t ht hzt,
  refine ⟨lift_of_div f ⁻¹' t ∩ {mk K (1,0) (by simp)}ᶜ, _, ⟨hzt, hz⟩,
    by simp [set.inter_assoc, set.inter_subset_left]⟩,
  refine ⟨{z | z.2 ≠ 0 ∧ f (z.1 / z.2) ∈ t}, _, _⟩,
  { suffices : continuous_on (λ z : K × K, f (z.1 / z.2)) {z | z.2 ≠ 0},
      exact this.preimage_open_of_open (is_open_compl_singleton.preimage continuous_snd) ht,
    refine continuous.comp_continuous_on hf _,
    exact continuous_fst.continuous_on.div continuous_snd.continuous_on (λ _, id) },
  { ext ⟨x, hx⟩,
    simp [lift_of_div, mk_eq_mk_iff_mul_eq_mul, and_comm, eq_comm] }
end

@[simp]
lemma submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).submodule = K ∙ v := rfl

lemma submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep :=
by { conv_lhs { rw ← v.mk_rep }, refl }

lemma finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 :=
begin
  rw submodule_eq,
  exact finrank_span_singleton v.rep_nonzero,
end

instance (v : ℙ K V) : finite_dimensional K v.submodule :=
by { rw ← v.mk_rep, change finite_dimensional K (K ∙ v.rep), apply_instance }

lemma submodule_injective : function.injective
  (projectivization.submodule : ℙ K V → submodule K V) :=
begin
  intros u v h, replace h := le_of_eq h,
  simp only [submodule_eq] at h,
  rw submodule.le_span_singleton_iff at h,
  rw [← mk_rep v, ← mk_rep u],
  apply quotient.sound',
  obtain ⟨a,ha⟩ := h u.rep (submodule.mem_span_singleton_self _),
  have : a ≠ 0 := λ c, u.rep_nonzero (by simpa [c] using ha.symm),
  use [units.mk0 a this, ha],
end

variables (K V)
/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
noncomputable
def equiv_submodule : ℙ K V ≃ { H : submodule K V // finrank K H = 1 } :=
equiv.of_bijective (λ v, ⟨v.submodule, v.finrank_submodule⟩)
begin
  split,
  { intros u v h, apply_fun (λ e, e.val) at h,
    apply submodule_injective h },
  { rintros ⟨H, h⟩,
    rw finrank_eq_one_iff' at h,
    obtain ⟨v, hv, h⟩ := h,
    have : (v : V) ≠ 0 := λ c, hv (subtype.coe_injective c),
    use mk K v this,
    symmetry,
    ext x, revert x, erw ← set.ext_iff, ext x,
    dsimp [-set_like.mem_coe],
    rw [submodule.span_singleton_eq_range],
    refine ⟨λ hh, _, _⟩,
    { obtain ⟨c,hc⟩ := h ⟨x,hh⟩,
      exact ⟨c, congr_arg coe hc⟩ },
    { rintros ⟨c,rfl⟩,
      refine submodule.smul_mem _ _ v.2 } }
end
variables {K V}

/-- Construct an element of the projectivization from a subspace of dimension 1. -/
noncomputable
def mk'' (H : _root_.submodule K V) (h : finrank K H = 1) : ℙ K V :=
(equiv_submodule K V).symm ⟨H,h⟩

@[simp]
lemma submodule_mk'' (H : _root_.submodule K V) (h : finrank K H = 1) :
  (mk'' H h).submodule = H :=
begin
  suffices : (equiv_submodule K V) (mk'' H h) = ⟨H,h⟩, by exact congr_arg coe this,
  dsimp [mk''],
  simp
end

@[simp]
lemma mk''_submodule (v : ℙ K V) : mk'' v.submodule v.finrank_submodule = v :=
show (equiv_submodule K V).symm (equiv_submodule K V _) = _, by simp

section map

variables {L W : Type*} [field L] [add_comm_group W] [module L W]

/-- An injective semilinear map of vector spaces induces a map on projective spaces. -/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : function.injective f) :
  ℙ K V → ℙ L W :=
quotient.map' (λ v, ⟨f v, λ c, v.2 (hf (by simp [c]))⟩)
begin
  rintros ⟨u,hu⟩ ⟨v,hv⟩ ⟨a,ha⟩,
  use units.map σ.to_monoid_hom a,
  dsimp at ⊢ ha,
  erw [← f.map_smulₛₗ, ha],
end

@[simp]
lemma map_mk {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : function.injective f) (u : V) (hu : u ≠ 0) :
  map f hf (mk K u hu) = mk L (f u) ((map_ne_zero_iff f hf).mpr hu) :=
rfl

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
lemma map_injective {σ : K →+* L} {τ : L →+* K} [ring_hom_inv_pair σ τ]
  (f : V →ₛₗ[σ] W) (hf : function.injective f) :
  function.injective (map f hf) :=
begin
  intros u v,
  induction u using projectivization.ind with u hu,
  induction v using projectivization.ind with v hv,
  simp only [map_mk, mk_eq_mk_iff, units.smul_def],
  rintro ⟨a, ha⟩,
  refine ⟨units.map τ.to_monoid_hom a, hf _⟩,
  simpa only [units.map, ring_hom.coe_monoid_hom, ring_hom.to_monoid_hom_eq_coe,
    monoid_hom.mk'_apply, units.coe_mk, linear_map.map_smulₛₗ, ring_hom_inv_pair.comp_apply_eq₂]
end

@[simp]
lemma map_id : map
  (linear_map.id : V →ₗ[K] V)
  (linear_equiv.refl K V).injective = id :=
by { ext v, induction v using projectivization.ind, refl }

@[simp]
lemma map_comp {F U : Type*} [field F] [add_comm_group U] [module F U]
  {σ : K →+* L} {τ : L →+* F} {γ : K →+* F} [ring_hom_comp_triple σ τ γ]
  (f : V →ₛₗ[σ] W) (hf : function.injective f)
  (g : W →ₛₗ[τ] U) (hg : function.injective g) :
  map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf :=
by { ext v, induction v using projectivization.ind, refl }

end map

end projectivization
