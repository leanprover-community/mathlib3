/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import linear_algebra.finite_dimensional

/-!

# Projective Spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

-/

variables (K V : Type*) [division_ring K] [add_comm_group V] [module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivization_setoid : setoid { v : V // v ≠ 0 } :=
(mul_action.orbit_rel Kˣ V).comap coe

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
@[nolint has_nonempty_instance]
def projectivization := quotient (projectivization_setoid K V)

notation `ℙ` := projectivization

namespace projectivization

variables {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : ℙ K V := quotient.mk' ⟨v,hv⟩

/-- A variant of `projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V := quotient.mk' v

@[simp] lemma mk'_eq_mk (v : { v : V // v ≠ 0}) :
  mk' K v = mk K v v.2 :=
by { dsimp [mk, mk'], congr' 1, simp }

instance [nontrivial V] : nonempty (ℙ K V) :=
let ⟨v, hv⟩ := exists_ne (0 : V) in ⟨mk K v hv⟩

variable {K}

/-- Choose a representative of `v : projectivization K V` in `V`. -/
protected noncomputable def rep (v : ℙ K V) : V := v.out'

lemma rep_nonzero (v : ℙ K V) : v.rep ≠ 0 := v.out'.2

@[simp]
lemma mk_rep (v : ℙ K V) :
  mk K v.rep v.rep_nonzero = v :=
by { dsimp [mk, projectivization.rep], simp }

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

/-- Two nonzero vectors go to the same point in projective space if and only if one is
a scalar multiple of the other. -/
lemma mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) : mk K v hv = mk K w hw ↔
  ∃ (a : K), a • w = v :=
begin
  rw mk_eq_mk_iff K v w hv hw,
  split,
  { rintro ⟨a, ha⟩, exact ⟨a, ha⟩ },
  { rintro ⟨a, ha⟩, refine ⟨units.mk0 a (λ c, hv.symm _), ha⟩, rwa [c, zero_smul] at ha }
end

lemma exists_smul_eq_mk_rep
  (v : V) (hv : v ≠ 0) : ∃ (a : Kˣ), a • v = (mk K v hv).rep :=
show (projectivization_setoid K V).rel _ _, from quotient.mk_out' ⟨v, hv⟩

variable {K}

/-- An induction principle for `projectivization`.
Use as `induction v using projectivization.ind`. -/
@[elab_as_eliminator]
lemma ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) :
  ∀ p, P p :=
quotient.ind' $ subtype.rec $ by exact h

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

variables {L W : Type*} [division_ring L] [add_comm_group W] [module L W]

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

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
lemma map_injective {σ : K →+* L} {τ : L →+* K} [ring_hom_inv_pair σ τ]
  (f : V →ₛₗ[σ] W) (hf : function.injective f) :
  function.injective (map f hf) :=
begin
  intros u v h,
  rw [← u.mk_rep, ← v.mk_rep] at *,
  apply quotient.sound',
  dsimp [map, mk] at h,
  simp only [quotient.eq'] at h,
  obtain ⟨a,ha⟩ := h,
  use units.map τ.to_monoid_hom a,
  dsimp at ⊢ ha,
  have : (a : L) = σ (τ a), by rw ring_hom_inv_pair.comp_apply_eq₂,
  change (a : L) • f v.rep = f u.rep at ha,
  rw [this, ← f.map_smulₛₗ] at ha,
  exact hf ha,
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
