/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.localization.at_prime
import ring_theory.valuation.basic
import tactic.field_simp

/-!

# Extending valuations in a localization

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.prime_compl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/

variables {A : Type*} [comm_ring A] (S : submonoid A)
  (B : Type*) [comm_ring B] [algebra A B] [is_localization S B]
variables {Γ : Type*} [linear_ordered_comm_group_with_zero Γ] (v : valuation A Γ)

variable {S}

lemma valuation.ne_zero_of_mem_of_le_prime_compl_supp (s : A) (hs : s ∈ S)
  (hS : S ≤ v.supp.prime_compl) : v s ≠ 0 :=
λ  c, hS hs c

variable (S)

/-- We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`. -/
def valuation.extend_to_localization (hS : S ≤ v.supp.prime_compl):
  valuation (localization S) Γ :=
{ to_fun := λ t, localization.lift_on t (λ a s, v a * (v s)⁻¹) begin
    rintros a a' s s' h, rw localization.r_iff_exists at h,
    obtain ⟨t,ht⟩ := h, dsimp at ht ⊢,
    apply_fun v at ht, apply_fun (λ e, e * (v t)⁻¹) at ht,
    simp only [valuation.map_mul, mul_assoc,
      mul_inv_cancel (v.ne_zero_of_mem_of_le_prime_compl_supp t t.2 hS),
      mul_one] at ht,
    rw [mul_inv_eq_iff_eq_mul₀ (v.ne_zero_of_mem_of_le_prime_compl_supp s s.2 hS),
      mul_assoc, mul_comm _ (v s), ← mul_assoc],
    symmetry,
    rw mul_inv_eq_iff_eq_mul₀ (v.ne_zero_of_mem_of_le_prime_compl_supp s' s'.2 hS),
    exact ht.symm,
  end,
  map_zero' := by simp [localization.lift_on_zero],
  map_one' := by simp only [← localization.mk_one, localization.lift_on_mk, v.map_one,
    submonoid.coe_one, valuation.map_one, inv_one, mul_one],
  map_mul' := begin
    intros x y,
    obtain ⟨a,s,rfl⟩ := is_localization.mk'_surjective S x,
    obtain ⟨b,t,rfl⟩ := is_localization.mk'_surjective S y,
    rw ← is_localization.mk'_mul,
    dsimp [is_localization.mk'],
    simp_rw [localization.lift_on_mk', submonoid.coe_mul, v.map_mul, mul_inv₀, mul_assoc,
      mul_comm (v s)⁻¹, mul_assoc],
  end,
  map_add_le_max' := begin
    intros x y,
    obtain ⟨a,s,rfl⟩ := is_localization.mk'_surjective S x,
    obtain ⟨b,t,rfl⟩ := is_localization.mk'_surjective S y,
    dsimp,
    rw ← is_localization.mk'_add,
    dsimp [is_localization.mk'],
    simp_rw [localization.lift_on_mk'],
    rw mul_inv_le_iff₀ (v.ne_zero_of_mem_of_le_prime_compl_supp ↑(s * t) (s * t).2 hS),
    convert v.map_add (a * t) (b * s),
    simp only [submonoid.coe_mul, valuation.map_mul],
    rw [← max_mul_mul_right, mul_assoc (v a), ← mul_assoc (v s)⁻¹,
      inv_mul_cancel (v.ne_zero_of_mem_of_le_prime_compl_supp s s.2 hS), one_mul,
      mul_assoc (v b), mul_comm (v t)⁻¹, mul_assoc,
      mul_inv_cancel (v.ne_zero_of_mem_of_le_prime_compl_supp t t.2 hS), mul_one],
  end }

@[simp]
lemma valuation.extend_to_localization_apply_map_apply (hS : S ≤ v.supp.prime_compl)
  (a : A) : v.extend_to_localization S hS (algebra_map A (localization S) a) = v a :=
begin
  change _ * _ = _,
  simp,
end

/-- We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`. -/
noncomputable
def valuation.extend_to_is_localization (hS : S ≤ v.supp.prime_compl) :
  valuation B Γ :=
let e : B ≃ₐ[A] localization S := (localization.alg_equiv S B).symm in
valuation.comap e.to_alg_hom.to_ring_hom (v.extend_to_localization S hS)

@[simp]
lemma valuation.extend_to_is_localization_algebra_map_apply (hS : S ≤ v.supp.prime_compl)
  (a : A) : v.extend_to_is_localization S B hS (algebra_map A B a) = v a :=
begin
  dsimp only [valuation.extend_to_is_localization, valuation.comap_apply],
  convert v.extend_to_localization_apply_map_apply S hS a,
  apply_fun (localization.alg_equiv S B),
  swap, { apply alg_equiv.injective },
  erw alg_equiv.apply_symm_apply,
  simp only [localization.alg_equiv_apply],
  dsimp [is_localization.map],
  simp only [is_localization.lift_eq, ring_hom.coe_comp,
    ring_equiv.coe_to_ring_hom, function.comp_app, ring_equiv.refl_apply],
end
