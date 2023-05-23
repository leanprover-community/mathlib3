/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import topology.metric_space.algebra
import analysis.normed.field.basic

/-!
# Lemmas for `has_bounded_smul` over normed additive groups

Lemmas which hold only in `normed_space α β` are provided in another file.

Notably we prove that `non_unital_semi_normed_ring`s have bounded actions by left- and right-
multiplication. This allows downstream files to write general results about `bounded_smul`, and then
deduce `const_mul` and `mul_const` results as an immediate corollary.
-/

variables {α β : Type*}

section seminormed_add_group
variables [seminormed_add_group α] [seminormed_add_group β] [smul_zero_class α β]
variables [has_bounded_smul α β]

lemma norm_smul_le (r : α) (x : β) : ‖r • x‖ ≤ ‖r‖ * ‖x‖ :=
by simpa [smul_zero] using dist_smul_pair r 0 x

lemma nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ ≤ ‖r‖₊ * ‖x‖₊ :=
norm_smul_le _ _

lemma dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) ≤ ‖s‖ * dist x y :=
by simpa only [dist_eq_norm, sub_zero] using dist_smul_pair s x y

lemma nndist_smul_le (s : α) (x y : β) : nndist (s • x) (s • y) ≤ ‖s‖₊ * nndist x y :=
dist_smul_le s x y

lemma edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) ≤ ‖s‖₊ • edist x y :=
by simpa only [edist_nndist, ennreal.coe_mul] using ennreal.coe_le_coe.mpr (nndist_smul_le s x y)

lemma lipschitz_with_smul (s : α) : lipschitz_with ‖s‖₊ ((•) s : β → β) :=
lipschitz_with_iff_dist_le_mul.2 $ dist_smul_le _

end seminormed_add_group

/-- Left multiplication is bounded. -/
instance non_unital_semi_normed_ring.to_has_bounded_smul [non_unital_semi_normed_ring α] :
  has_bounded_smul α α :=
{ dist_smul_pair' := λ x y₁ y₂, by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂),
  dist_pair_smul' := λ x₁ x₂ y, by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y, }

/-- Right multiplication is bounded. -/
instance non_unital_semi_normed_ring.to_has_bounded_op_smul [non_unital_semi_normed_ring α] :
  has_bounded_smul αᵐᵒᵖ α :=
{ dist_smul_pair' := λ x y₁ y₂,
    by simpa [sub_mul, dist_eq_norm, mul_comm] using norm_mul_le (y₁ - y₂) x.unop,
  dist_pair_smul' := λ x₁ x₂ y,
    by simpa [mul_sub, dist_eq_norm, mul_comm] using norm_mul_le y (x₁ - x₂).unop, }

section semi_normed_ring
variables [semi_normed_ring α] [seminormed_add_comm_group β] [module α β]

lemma has_bounded_smul.of_norm_smul_le (h : ∀ (r : α) (x : β), ‖r • x‖ ≤ ‖r‖ * ‖x‖) :
  has_bounded_smul α β :=
{ dist_smul_pair' := λ a b₁ b₂, by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂),
  dist_pair_smul' := λ a₁ a₂ b, by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }

end semi_normed_ring

section normed_division_ring
variables [normed_division_ring α] [seminormed_add_group β]
variables [mul_action_with_zero α β] [has_bounded_smul α β]

lemma norm_smul (r : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖ :=
begin
  by_cases h : r = 0,
  { simp [h, zero_smul α x] },
  { refine le_antisymm (norm_smul_le r x) _,
    calc ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖     : by rw [inv_smul_smul₀ h]
               ... ≤ ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) :
      mul_le_mul_of_nonneg_left (norm_smul_le _ _) (norm_nonneg _)
               ... = ‖r • x‖                 :
      by rw [norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul] }
end

lemma nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊ :=
nnreal.eq $ norm_smul r x

end normed_division_ring

section normed_division_ring_module
variables [normed_division_ring α] [seminormed_add_comm_group β]
variables [module α β] [has_bounded_smul α β]

lemma dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * dist x y :=
by simp_rw [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

lemma nndist_smul₀ (s : α) (x y : β) : nndist (s • x) (s • y) = ‖s‖₊ * nndist x y :=
nnreal.eq $ dist_smul₀ s x y

lemma edist_smul₀ (s : α) (x y : β) : edist (s • x) (s • y) = ‖s‖₊ • edist x y :=
by simp only [edist_nndist, nndist_smul₀, ennreal.coe_mul, ennreal.smul_def, smul_eq_mul]

end normed_division_ring_module
