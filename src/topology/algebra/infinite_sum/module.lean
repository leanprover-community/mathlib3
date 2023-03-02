/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov, Frédéric Dupuis
-/
import topology.algebra.infinite_sum.basic
import topology.algebra.module.basic

/-! # Infinite sums in topological vector spaces -/

variables {ι R R₂ M M₂ : Type*}

section smul_const
variables [semiring R] [topological_space R] [topological_space M] [add_comm_monoid M] [module R M]
  [has_continuous_smul R M] {f : ι → R}

lemma has_sum.smul_const {r : R} (hf : has_sum f r) (a : M) : has_sum (λ z, f z • a) (r • a) :=
hf.map ((smul_add_hom R M).flip a) (continuous_id.smul continuous_const)

lemma summable.smul_const (hf : summable f) (a : M) : summable (λ z, f z • a) :=
(hf.has_sum.smul_const _).summable

lemma tsum_smul_const [t2_space M] (hf : summable f) (a : M) : ∑' z, f z • a = (∑' z, f z) • a :=
(hf.has_sum.smul_const _).tsum_eq

end smul_const

section has_sum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.

variables [semiring R] [semiring R₂] [add_comm_monoid M] [module R M]
  [add_comm_monoid M₂] [module R₂ M₂] [topological_space M] [topological_space M₂]
  {σ : R →+* R₂} {σ' : R₂ →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected lemma continuous_linear_map.has_sum {f : ι → M} (φ : M →SL[σ] M₂) {x : M}
  (hf : has_sum f x) :
  has_sum (λ (b:ι), φ (f b)) (φ x) :=
by simpa only using hf.map φ.to_linear_map.to_add_monoid_hom φ.continuous

alias continuous_linear_map.has_sum ← has_sum.mapL

protected lemma continuous_linear_map.summable {f : ι → M} (φ : M →SL[σ] M₂) (hf : summable f) :
  summable (λ b:ι, φ (f b)) :=
(hf.has_sum.mapL φ).summable

alias continuous_linear_map.summable ← summable.mapL

protected lemma continuous_linear_map.map_tsum [t2_space M₂] {f : ι → M}
  (φ : M →SL[σ] M₂) (hf : summable f) : φ (∑' z, f z) = ∑' z, φ (f z) :=
(hf.has_sum.mapL φ).tsum_eq.symm

include σ'
/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected lemma continuous_linear_equiv.has_sum {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
  has_sum (λ (b:ι), e (f b)) y ↔ has_sum f (e.symm y) :=
⟨λ h, by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →SL[σ'] M),
  λ h, by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →SL[σ] M₂).has_sum h⟩

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected lemma continuous_linear_equiv.has_sum' {f : ι → M} (e : M ≃SL[σ] M₂) {x : M} :
  has_sum (λ (b:ι), e (f b)) (e x) ↔ has_sum f x :=
by rw [e.has_sum, continuous_linear_equiv.symm_apply_apply]

protected lemma continuous_linear_equiv.summable {f : ι → M} (e : M ≃SL[σ] M₂) :
  summable (λ b:ι, e (f b)) ↔ summable f :=
⟨λ hf, (e.has_sum.1 hf.has_sum).summable, (e : M →SL[σ] M₂).summable⟩


lemma continuous_linear_equiv.tsum_eq_iff [t2_space M] [t2_space M₂] {f : ι → M}
  (e : M ≃SL[σ] M₂) {y : M₂} : ∑' z, e (f z) = y ↔ ∑' z, f z = e.symm y :=
begin
  by_cases hf : summable f,
  { exact ⟨λ h, (e.has_sum.mp ((e.summable.mpr hf).has_sum_iff.mpr h)).tsum_eq,
      λ h, (e.has_sum.mpr (hf.has_sum_iff.mpr h)).tsum_eq⟩ },
  { have hf' : ¬summable (λ z, e (f z)) := λ h, hf (e.summable.mp h),
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf'],
    exact ⟨by { rintro rfl, simp }, λ H, by simpa using (congr_arg (λ z, e z) H)⟩ }
end

protected lemma continuous_linear_equiv.map_tsum [t2_space M] [t2_space M₂] {f : ι → M}
  (e : M ≃SL[σ] M₂) : e (∑' z, f z) = ∑' z, e (f z) :=
by { refine symm (e.tsum_eq_iff.mpr _), rw e.symm_apply_apply _ }

end has_sum
