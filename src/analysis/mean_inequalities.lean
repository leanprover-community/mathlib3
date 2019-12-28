/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.mean_value data.nat.parity analysis.complex.exponential

/-! # Mean values inequalities
-/

universes u v

open real finset
open_locale classical nnreal

lemma convex_on_exp : convex_on set.univ exp :=
convex_on_univ_of_deriv2_nonneg differentiable_exp
  (deriv_exp.symm ▸ differentiable_exp)
  (assume x, (iter_deriv_exp 2).symm ▸ le_of_lt (exp_pos x))

variables {α : Type u} (s : finset α)

/-- Geometric mean is less than or equal to the arithmetic mean, weighted version
for functions on `finset`s. -/
theorem real.am_gm_weighted (w z : α → ℝ)
  (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : s.sum w = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
  s.prod (λ i, (z i) ^ (w i)) ≤ s.sum (λ i, w i * z i) :=
begin
  let s' := s.filter (λ i, w i ≠ 0),
  have A : ∀ i ∈ s, i ∉ s' → w i = 0, by { intros i hi hi', simpa [hi] using hi' },
  rw [← sum_subset s.filter_subset A] at hw',
  suffices : s'.prod (λ i, (z i) ^ (w i)) ≤ s'.sum (λ i, w i * z i),
  { have B : ∀ i ∈ s, i ∉ s' → (z i) ^ (w i) = 1, by { intros, simp [*] },
    have C : ∀ i ∈ s, i ∉ s' → w i * z i = 0, by { intros, simp [*] },
    rwa [← prod_subset s.filter_subset B, ← sum_subset s.filter_subset C] },
  replace A : ∀ i ∈ s', i ∈ s ∧ w i ≠ 0, from λ i hi, mem_filter.1 hi,
  replace hz : ∀ i ∈ s', 0 ≤ z i := λ i hi, hz i (A i hi).1,
  replace hw : ∀ i ∈ s', 0 ≤ w i := λ i hi, hw i (A i hi).1,
  by_cases B : ∃ i ∈ s', z i = 0,
  { rcases B with ⟨i, imem, hzi⟩,
    rw [prod_eq_zero imem],
    { exact sum_nonneg (λ j hj, mul_nonneg (hw j hj) (hz j hj)) },
    { rw hzi, exact zero_rpow (A i imem).2 } },
  { replace hz : ∀ i ∈ s', 0 < z i,-- by simpa only [not_exists, not_not] using B,
      from λ i hi, lt_of_le_of_ne (hz _ hi)
        (ne.symm $ by { simp only [not_exists, ne.def] at B, exact B i hi }),
    have := convex_on_exp.map_sum_le s' w (log ∘ z) hw hw' (λ _ _, trivial),
    simp only [exp_sum] at this,
    convert this using 1; simp only [function.comp],
    { apply prod_congr rfl,
      intros i hi,
      rw [smul_eq_mul, mul_comm],
      exact rpow_def_of_pos (hz i hi) _ },
    { apply sum_congr rfl,
      intros i hi,
      rw [exp_log (hz i hi)] } }
end

lemma fin.succ_univ (n : ℕ) :
  (univ : finset (fin n.succ)) = insert 0 ((univ : finset (fin n)).image fin.succ) :=
begin
  ext m,
  simp only [mem_univ, mem_insert, true_iff, mem_image, exists_prop, true_and],
  by_cases m = 0,
  { exact or.inl h },
  { exact or.inr ⟨m.pred h, m.succ_pred h⟩ }
end

theorem finset.prod_fin_succ {α} [comm_monoid α] {n} (f : fin (n+1) → α) :
  univ.prod f = f 0 * univ.prod (λ i:fin n, f i.succ) :=
begin
  rw [fin.succ_univ, prod_insert, prod_image],
  { intros x _ y _ hxy, exact fin.succ.inj hxy },
  { simpa using fin.succ_ne_zero }
end

theorem finset.sum_fin_succ {α} [add_comm_monoid α] {n} (f : fin (n+1) → α) :
  univ.sum f = f 0 + univ.sum (λ i:fin n, f i.succ) :=
begin
  rw [fin.succ_univ, sum_insert, sum_image],
  { intros x _ y _ hxy, exact fin.succ.inj hxy },
  { simpa using fin.succ_ne_zero }
end

noncomputable instance nnreal.rpow : has_pow ℝ≥0 ℝ :=
⟨λ x y, ⟨(x:ℝ)^y, rpow_nonneg_of_nonneg x.2 _⟩⟩

@[move_cast] lemma nnreal.coe_rpow {p : ℝ≥0} {r : ℝ} : ↑(p^r) = (p:ℝ)^r := rfl

theorem nnreal.am_gm_weighted (w z : α → ℝ≥0) (hw' : s.sum w = 1) :
  s.prod (λ i, (z i) ^ (w i : ℝ)) ≤ s.sum (λ i, w i * z i) :=
begin
  rw [← nnreal.coe_le],
  push_cast,
  refine real.am_gm_weighted _ _ _ (λ i _, (w i).coe_nonneg) _ (λ i _, (z i).coe_nonneg),
  norm_cast,
  assumption
end

theorem nnreal.am_gm2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) (hw : w₁ + w₂ = 1) :
  p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) ≤ w₁ * p₁ + w₂ * p₂ :=
begin
  have := nnreal.am_gm_weighted (univ : finset (fin 2)) (fin.cons w₁ (λ _, w₂))
    (fin.cons p₁ (λ _, p₂)),
  simpa [finset.prod_fin_succ, finset.sum_fin_succ, hw] using this
end

theorem nnreal.am_gm3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) (hw : w₁ + w₂ + w₃ = 1) :
  p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃:=
begin
  have := nnreal.am_gm_weighted (univ : finset (fin 3))
    (fin.cons w₁ $ fin.cons w₂ $ λ _, w₃)
    (fin.cons p₁ $ fin.cons p₂ $ λ _, p₃),
  simp only [add_assoc] at hw,
  simpa [finset.prod_fin_succ, finset.sum_fin_succ, hw, add_assoc, mul_assoc] using this
end
