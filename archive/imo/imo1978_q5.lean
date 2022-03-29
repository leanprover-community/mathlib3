/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.order.rearrangement
import data.nat.interval
import data.real.basic


open_locale big_operators

variables (n : ℕ) (a : ℕ ↪ ℕ) (ha0 : a 0 = 0)
include ha0

lemma to_name {ι α : Type*} [preorder ι] [linear_order α] {f : ι → α} (s : finset ι) :
  ∃ σ : equiv.perm ι, {x | σ x ≠ x} ⊆ s ∧ monotone_on (f ∘ σ) s :=
begin
  classical,
  apply s.induction_on,
  { use equiv.refl ι,
    simp only [equiv.coe_refl, id.def, ne.def, eq_self_iff_true, not_true, set.set_of_false,
    finset.coe_empty, set.empty_subset, true_and, monotone_on, set.mem_empty_eq, forall_false_left,
    implies_true_iff] },
  { intros a s has hind,
    sorry}
end



theorem IMO_1978_Q5 : (∑ k in finset.Icc 1 n, 1 / k : ℚ) ≤ ∑ k in finset.Icc 1 n, a k / k ^ 2 :=
begin
  set g : ℕ → ℚ := λ k, 1 / k ^ 2 with hg,
  have hga : antitone_on g (finset.Icc 1 n),
  { intros i hi j hj hij,
    simp only [hg, one_div],
    simp only [finset.coe_Icc, set.mem_Icc] at *,
    replace hi : (0 : ℚ) < i, {norm_cast, exact nat.succ_le_iff.mp hi.1 },
    replace hj : (0 : ℚ) < j, {norm_cast, exact nat.succ_le_iff.mp hj.1 },
    rw inv_le_inv (pow_pos hj 2) (pow_pos hi 2),
    norm_cast,
    simp only [sq],
    apply mul_le_mul hij hij (zero_le i) (zero_le j) },
  have : ∃ σ : equiv.perm ℕ, {x | σ x ≠ x} ⊆ finset.Icc 1 n ∧
    monotone_on (λ (k : ℕ), ((a (σ k)) : ℚ)) (finset.Icc 1 n),
  { sorry },
  rcases this with ⟨σ, hσ, hσn⟩,
  have htemp : (∑ k in finset.Icc 1 n, a (σ k) / k ^ 2 : ℚ) ≤
    ∑ k in finset.Icc 1 n, (a k) / k ^ 2,
  { have hσ1 : {x | σ⁻¹ x ≠ x} ⊆ finset.Icc 1 n,
    { convert hσ,
      simp only [ne.def, equiv.perm.inv_eq_iff_eq],
      ext,
      exact ne_comm },
    convert antivary_on.sum_mul_le_sum_comp_perm_mul _ hσ1,
    { simp only [equiv.perm.apply_inv_self, div_eq_mul_inv],
      refl },
    { convert monotone_on.antivary_on hσn hga,
      simp only [hg, one_div],
      refl }},
  apply le_trans (finset.sum_le_sum _) htemp,
  intros i hi,
  rw le_div_iff _,
  { simp only [sq, one_div, ←mul_assoc, inv_mul_mul_self, nat.cast_le],
    induction i with d hd,
    { exfalso,
      simp only [finset.mem_Icc, nonpos_iff_eq_zero, nat.one_ne_zero, false_and] at hi,
      assumption },
    { sorry }},
  { simp only [finset.mem_Icc] at hi,
    norm_cast,
    rw sq,
    apply mul_pos;
    linarith }
end
