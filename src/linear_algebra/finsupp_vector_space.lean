/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.mv_polynomial
import linear_algebra.dimension
import linear_algebra.direct_sum.finsupp
import linear_algebra.finite_dimensional

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

Furthermore, it contains some facts about isomorphisms of vector spaces from equality of dimension
as well as the cardinality of finite dimensional vector spaces.

## TODO

Move the second half of this file to more appropriate other files.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open set linear_map submodule

namespace finsupp

section ring
variables {R : Type*} {M : Type*} {ι : Type*}
variables [ring R] [add_comm_group M] [module R M]

lemma linear_independent_single {φ : ι → Type*}
  {f : Π ι, φ ι → M} (hf : ∀i, linear_independent R (f i)) :
  linear_independent R (λ ix : Σ i, φ i, single ix.1 (f ix.1 ix.2)) :=
begin
  apply @linear_independent_Union_finite R _ _ _ _ ι φ (λ i x, single i (f i x)),
  { assume i,
    have h_disjoint : disjoint (span R (range (f i))) (ker (lsingle i)),
    { rw ker_lsingle,
      exact disjoint_bot_right },
    apply (hf i).map h_disjoint },
  { intros i t ht hit,
    refine (disjoint_lsingle_lsingle {i} t (disjoint_singleton_left.2 hit)).mono _ _,
    { rw span_le,
      simp only [supr_singleton],
      rw range_coe,
      apply range_comp_subset_range },
    { refine supr_le_supr (λ i, supr_le_supr _),
      intros hi,
      rw span_le,
      rw range_coe,
      apply range_comp_subset_range } }
end

open linear_map submodule

lemma is_basis_single {φ : ι → Type*} (f : Π ι, φ ι → M)
  (hf : ∀i, is_basis R (f i)) :
  is_basis R (λ ix : Σ i, φ i, single ix.1 (f ix.1 ix.2)) :=
begin
  split,
  { apply linear_independent_single,
    exact λ i, (hf i).1 },
  { rw [range_sigma_eq_Union_range, span_Union],
    simp only [image_univ.symm, λ i, image_comp (single i) (f i), span_single_image],
    simp only [image_univ, (hf _).2, map_top, supr_lsingle_range] }
end

lemma is_basis_single_one : is_basis R (λ i : ι, single i (1 : R)) :=
by convert (is_basis_single (λ (i : ι) (x : unit), (1 : R)) (λ i, is_basis_singleton_one R)).comp
  (λ i : ι, ⟨i, ()⟩) ⟨λ _ _, and.left ∘ sigma.mk.inj, λ ⟨i, ⟨⟩⟩, ⟨i, rfl⟩⟩

end ring

section comm_ring
variables {R : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
variables [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N]

/-- If b : ι → M and c : κ → N are bases then so is λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N. -/
lemma is_basis.tensor_product {b : ι → M} (hb : is_basis R b) {c : κ → N} (hc : is_basis R c) :
  is_basis R (λ i : ι × κ, b i.1 ⊗ₜ[R] c i.2) :=
by { convert linear_equiv.is_basis is_basis_single_one
  ((tensor_product.congr (module_equiv_finsupp hb) (module_equiv_finsupp hc)).trans $
    (finsupp_tensor_finsupp _ _ _ _ _).trans $
    lcongr (equiv.refl _) (tensor_product.lid R R)).symm,
  ext ⟨i, k⟩, rw [function.comp_apply, linear_equiv.eq_symm_apply], simp }

end comm_ring

section dim
universes u v
variables {K : Type u} {V : Type v} {ι : Type v}
variables [field K] [add_comm_group V] [vector_space K V]

lemma dim_eq : vector_space.dim K (ι →₀ V) = cardinal.mk ι * vector_space.dim K V :=
begin
  rcases exists_is_basis K V with ⟨bs, hbs⟩,
  rw [← cardinal.lift_inj, cardinal.lift_mul, ← hbs.mk_eq_dim,
      ← (is_basis_single _ (λa:ι, hbs)).mk_eq_dim, ← cardinal.sum_mk,
      ← cardinal.lift_mul, cardinal.lift_inj],
  { simp only [cardinal.mk_image_eq (single_injective.{u u} _), cardinal.sum_const] }
end

end dim

end finsupp

section vector_space
/- We use `universe variables` instead of `universes` here because universes introduced by the
   `universes` keyword do not get replaced by metavariables once a lemma has been proven. So if you
   prove a lemma using universe `u`, you can only apply it to universe `u` in other lemmas of the
   same section. -/
universe variables u v w
variables {K : Type u} {V V₁ V₂ : Type v} {V' : Type w}
variables [field K]
variables [add_comm_group V] [vector_space K V]
variables [add_comm_group V₁] [vector_space K V₁]
variables [add_comm_group V₂] [vector_space K V₂]
variables [add_comm_group V'] [vector_space K V']

open vector_space


lemma equiv_of_dim_eq_lift_dim
  (h : cardinal.lift.{v w} (dim K V) = cardinal.lift.{w v} (dim K V')) :
  nonempty (V ≃ₗ[K] V') :=
begin
  haveI := classical.dec_eq V,
  haveI := classical.dec_eq V',
  rcases exists_is_basis K V with ⟨m, hm⟩,
  rcases exists_is_basis K V' with ⟨m', hm'⟩,
  rw [←cardinal.lift_inj.1 hm.mk_eq_dim, ←cardinal.lift_inj.1 hm'.mk_eq_dim] at h,
  rcases quotient.exact h with ⟨e⟩,
  let e := (equiv.ulift.symm.trans e).trans equiv.ulift,
  exact ⟨((module_equiv_finsupp hm).trans
      (finsupp.dom_lcongr e)).trans
      (module_equiv_finsupp hm').symm⟩,
end

/-- Two `K`-vector spaces are equivalent if their dimension is the same. -/
def equiv_of_dim_eq_dim (h : dim K V₁ = dim K V₂) : V₁ ≃ₗ[K] V₂ :=
begin
  classical,
  exact classical.choice (equiv_of_dim_eq_lift_dim (cardinal.lift_inj.2 h))
end

/-- An `n`-dimensional `K`-vector space is equivalent to `fin n → K`. -/
def fin_dim_vectorspace_equiv (n : ℕ)
  (hn : (dim K V) = n) : V ≃ₗ[K] (fin n → K) :=
begin
  have : cardinal.lift.{v u} (n : cardinal.{v}) = cardinal.lift.{u v} (n : cardinal.{u}),
    by simp,
  have hn := cardinal.lift_inj.{v u}.2 hn,
  rw this at hn,
  rw ←@dim_fin_fun K _ n at hn,
  exact classical.choice (equiv_of_dim_eq_lift_dim hn),
end

end vector_space

section vector_space
universes u

open vector_space

variables (K V : Type u) [field K] [add_comm_group V] [vector_space K V]

lemma cardinal_mk_eq_cardinal_mk_field_pow_dim [finite_dimensional K V] :
  cardinal.mk V = cardinal.mk K ^ dim K V :=
begin
  rcases exists_is_basis K V with ⟨s, hs⟩,
  have : nonempty (fintype s),
  { rw [← cardinal.lt_omega_iff_fintype, cardinal.lift_inj.1 hs.mk_eq_dim],
    exact finite_dimensional.dim_lt_omega K V },
  cases this with hsf, letI := hsf,
  calc cardinal.mk V = cardinal.mk (s →₀ K) : quotient.sound ⟨(module_equiv_finsupp hs).to_equiv⟩
    ... = cardinal.mk (s → K) : quotient.sound ⟨finsupp.equiv_fun_on_fintype⟩
    ... = _ : by rw [← cardinal.lift_inj.1 hs.mk_eq_dim, cardinal.power_def]
end

lemma cardinal_lt_omega_of_finite_dimensional [fintype K] [finite_dimensional K V] :
  cardinal.mk V < cardinal.omega :=
begin
  rw cardinal_mk_eq_cardinal_mk_field_pow_dim K V,
  exact cardinal.power_lt_omega (cardinal.lt_omega_iff_fintype.2 ⟨infer_instance⟩)
    (finite_dimensional.dim_lt_omega K V),
end

end vector_space
