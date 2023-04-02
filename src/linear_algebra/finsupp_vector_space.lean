/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import linear_algebra.std_basis

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

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
    { refine supr₂_mono (λ i hi, _),
      rw [span_le, range_coe],
      apply range_comp_subset_range } }
end

end ring

section semiring
variables {R : Type*} {M : Type*} {ι : Type*}
variables [semiring R] [add_comm_monoid M] [module R M]

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
               finsupp.single_apply_left sigma_mk_injective] },
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

end semiring

end finsupp

namespace basis

variables {R M n : Type*}
variables [decidable_eq n] [fintype n]
variables [semiring R] [add_comm_monoid M] [module R M]

lemma _root_.finset.sum_single_ite (a : R) (i : n) :
  finset.univ.sum (λ (x : n), finsupp.single x (ite (i = x) a 0)) = finsupp.single i a :=
begin
  rw finset.sum_congr_set {i} (λ (x : n), finsupp.single x (ite (i = x) a 0))
    (λ _, finsupp.single i a),
  { simp },
  { intros x hx,
    rw set.mem_singleton_iff at hx,
    simp [hx] },
  intros x hx,
  have hx' : ¬i = x :=
  begin
    refine ne_comm.mp _,
    rwa mem_singleton_iff at hx,
  end,
  simp [hx'],
end

@[simp] lemma equiv_fun_symm_std_basis (b : basis n R M) (i : n) :
  b.equiv_fun.symm (linear_map.std_basis R (λ _, R) i 1) = b i :=
begin
  have := equiv_like.injective b.repr,
  apply_fun b.repr,
  simp only [equiv_fun_symm_apply, std_basis_apply', linear_equiv.map_sum,
    linear_equiv.map_smulₛₗ, ring_hom.id_apply, repr_self, finsupp.smul_single', boole_mul],
  exact finset.sum_single_ite 1 i,
end

end basis
