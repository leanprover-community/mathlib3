/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.mv_polynomial
import linear_algebra.dimension
import linear_algebra.direct_sum.finsupp
import linear_algebra.finite_dimensional
import linear_algebra.std_basis

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
open_locale cardinal

universes u v w

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

/-- The basis on `ι →₀ M` with basis vectors `λ ⟨i, x⟩, single i (b i x)`. -/
protected def basis {φ : ι → Type*} (b : ∀ i, basis (φ i) R M) :
  basis (Σ i, φ i) R (ι →₀ M) :=
basis.of_repr
  { to_fun := λ g,
      { to_fun := λ ix, (b ix.1).repr (g ix.1) ix.2,
        support := g.support.sigma (λ i, ((b i).repr (g i)).support),
        mem_support_to_fun := λ ix,
          by { simp only [finset.mem_sigma, mem_support_iff, and_iff_right_iff_imp, ne.def],
               intros b hg,
               simpa [hg] using b } },
    inv_fun := λ g,
      { to_fun := λ i, (b i).repr.symm (g.comap_domain _
                          (set.inj_on_of_injective sigma_mk_injective _)),
        support := g.support.image sigma.fst,
        mem_support_to_fun := λ i,
          by { rw [ne.def, ← (b i).repr.injective.eq_iff, (b i).repr.apply_symm_apply, ext_iff],
               simp only [exists_prop, linear_equiv.map_zero, comap_domain_apply, zero_apply,
                  exists_and_distrib_right, mem_support_iff, exists_eq_right, sigma.exists,
                  finset.mem_image, not_forall] } },
    left_inv := λ g,
      by { ext i, rw ← (b i).repr.injective.eq_iff, ext x,
           simp only [coe_mk, linear_equiv.apply_symm_apply, comap_domain_apply] },
    right_inv := λ g,
      by { ext ⟨i, x⟩,
           simp only [coe_mk, linear_equiv.apply_symm_apply, comap_domain_apply] },
    map_add' := λ g h, by { ext ⟨i, x⟩, simp only [coe_mk, add_apply, linear_equiv.map_add] },
    map_smul' := λ c h, by { ext ⟨i, x⟩, simp only [coe_mk, smul_apply, linear_equiv.map_smul,
                                                    ring_hom.id_apply] } }

@[simp] lemma basis_repr {φ : ι → Type*} (b : ∀ i, basis (φ i) R M)
  (g : ι →₀ M) (ix) :
  (finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
rfl

@[simp] lemma coe_basis {φ : ι → Type*} (b : ∀ i, basis (φ i) R M) :
  ⇑(finsupp.basis b) = λ (ix : Σ i, φ i), single ix.1 (b ix.1 ix.2) :=
funext $ λ ⟨i, x⟩, basis.apply_eq_iff.mpr $
begin
  ext ⟨j, y⟩,
  by_cases h : i = j,
  { cases h,
    simp only [basis_repr, single_eq_same, basis.repr_self,
               basis.finsupp.single_apply_left sigma_mk_injective] },
  simp only [basis_repr, single_apply, h, false_and, if_false, linear_equiv.map_zero, zero_apply]
end

/-- The basis on `ι →₀ M` with basis vectors `λ i, single i 1`. -/
@[simps]
protected def basis_single_one :
  basis ι R (ι →₀ R) :=
basis.of_repr (linear_equiv.refl _ _)

@[simp] lemma coe_basis_single_one :
  (finsupp.basis_single_one : ι → (ι →₀ R)) = λ i, finsupp.single i 1 :=
funext $ λ i, basis.apply_eq_iff.mpr rfl

end ring

section dim
variables {K : Type u} {V : Type v} {ι : Type v}
variables [field K] [add_comm_group V] [module K V]

lemma dim_eq : module.rank K (ι →₀ V) = #ι * module.rank K V :=
begin
  let bs := basis.of_vector_space K V,
  rw [← cardinal.lift_inj, cardinal.lift_mul, ← bs.mk_eq_dim,
      ← (finsupp.basis (λa:ι, bs)).mk_eq_dim, ← cardinal.sum_mk,
      ← cardinal.lift_mul, cardinal.lift_inj],
  { simp only [cardinal.mk_image_eq (single_injective.{u u} _), cardinal.sum_const] }
end

end dim

end finsupp

section module
variables {K : Type u} {V V₁ V₂ : Type v} {V' : Type w}
variables [field K]
variables [add_comm_group V] [module K V]
variables [add_comm_group V₁] [module K V₁]
variables [add_comm_group V₂] [module K V₂]
variables [add_comm_group V'] [module K V']

open module


lemma equiv_of_dim_eq_lift_dim
  (h : cardinal.lift.{w} (module.rank K V) = cardinal.lift.{v} (module.rank K V')) :
  nonempty (V ≃ₗ[K] V') :=
begin
  haveI := classical.dec_eq V,
  haveI := classical.dec_eq V',
  let m := basis.of_vector_space K V,
  let m' := basis.of_vector_space K V',
  rw [←cardinal.lift_inj.1 m.mk_eq_dim, ←cardinal.lift_inj.1 m'.mk_eq_dim] at h,
  rcases quotient.exact h with ⟨e⟩,
  let e := (equiv.ulift.symm.trans e).trans equiv.ulift,
  exact ⟨(m.repr ≪≫ₗ (finsupp.dom_lcongr e)) ≪≫ₗ m'.repr.symm⟩
end

/-- Two `K`-vector spaces are equivalent if their dimension is the same. -/
def equiv_of_dim_eq_dim (h : module.rank K V₁ = module.rank K V₂) : V₁ ≃ₗ[K] V₂ :=
begin
  classical,
  exact classical.choice (equiv_of_dim_eq_lift_dim (cardinal.lift_inj.2 h))
end

/-- An `n`-dimensional `K`-vector space is equivalent to `fin n → K`. -/
def fin_dim_vectorspace_equiv (n : ℕ)
  (hn : (module.rank K V) = n) : V ≃ₗ[K] (fin n → K) :=
begin
  have : cardinal.lift.{u} (n : cardinal.{v}) = cardinal.lift.{v} (n : cardinal.{u}),
    by simp,
  have hn := cardinal.lift_inj.{v u}.2 hn,
  rw this at hn,
  rw ←@dim_fin_fun K _ n at hn,
  exact classical.choice (equiv_of_dim_eq_lift_dim hn),
end

end module

section module

open module

variables (K V : Type u) [field K] [add_comm_group V] [module K V]

lemma cardinal_mk_eq_cardinal_mk_field_pow_dim [finite_dimensional K V] :
  #V = #K ^ module.rank K V :=
begin
  let s := basis.of_vector_space_index K V,
  let hs := basis.of_vector_space K V,
  calc #V = #(s →₀ K) : quotient.sound ⟨hs.repr.to_equiv⟩
    ... = #(s → K) : quotient.sound ⟨finsupp.equiv_fun_on_fintype⟩
    ... = _ : by rw [← cardinal.lift_inj.1 hs.mk_eq_dim, cardinal.power_def]
end

lemma cardinal_lt_omega_of_finite_dimensional [fintype K] [finite_dimensional K V] :
  #V < ω :=
begin
  rw cardinal_mk_eq_cardinal_mk_field_pow_dim K V,
  exact cardinal.power_lt_omega (cardinal.lt_omega_iff_fintype.2 ⟨infer_instance⟩)
    (is_noetherian.dim_lt_omega K V),
end

end module
