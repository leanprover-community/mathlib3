/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.polynomial.basic
--import data.polynomial.derivative
--import data.polynomial.ring_division
import data.set.intervals.infinite
import topology.instances.real
import topology.algebra.polynomial
import analysis.calculus.mean_value
--import topology.bounded_continuous_function  -- why?

/-!
This file contains some lemmas about real polynomials and their derivatives
-/

open_locale classical

open polynomial real set


/-
lemma Ioo_of_open (x : ℝ) (U : set ℝ) (oU : is_open U) (xU : x ∈ U) :
  ∃ (e : ℝ), 0 < e ∧ Ioo x (x + e) ⊆ U := sorry

lemma Ioo_infinite (x e : ℝ) (e0 : 0 < e) : (set.Ioo (x - e) (x + e)).infinite :=
Ioo.infinite $ sub_pos.mp (by { rw add_sub_sub_cancel, exact add_pos e0 e0 })
-/

lemma exists_forall_ge_of_polynomial_Ioo_for (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ N, N ≥ M → ∀ y ∈ Icc (α - 1) (α + 1), abs (eval y f) ≤ N :=
begin
  obtain ⟨x, ⟨_, hy⟩⟩ :=
    is_compact.exists_forall_ge (@compact_Icc (α - 1) (α + 1))
      ⟨α - 1, ⟨rfl.le, sub_le_iff_le_add.mpr
        (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg rfl.le zero_le_one) zero_le_one)⟩⟩
    (continuous_abs.comp f.continuous_eval).continuous_on,
  refine ⟨abs (f.eval x), λ N hN y hy1, le_trans (hy y hy1) hN⟩,
end

lemma exists_forall_ge_of_polynomial_Ioo (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ y ∈ Icc (α - 1) (α + 1), abs (eval y f) ≤ M :=
begin
  obtain ⟨x, ⟨_, hy⟩⟩ :=
    is_compact.exists_forall_ge (@compact_Icc (α - 1) (α + 1))
      ⟨α - 1, ⟨rfl.le, sub_le_iff_le_add.mpr
        (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg rfl.le zero_le_one) zero_le_one)⟩⟩
    (continuous_abs.comp (continuous_eval f)).continuous_on,
  exact ⟨abs (f.eval x), λ y h, hy y h⟩,
end

lemma exists_forall_ge_of_polynomial_deriv_Ioo (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ y ∈ Icc (α - 1) (α + 1), abs (eval y f.derivative) ≤ M :=
exists_forall_ge_of_polynomial_Ioo α f.derivative

lemma sub_mem_Icc_iff (α i y : ℝ) : (y - α ∈ Icc (- i) i ↔ y ∈ Icc (α - i) (α + i)) :=
⟨λ a,
  ⟨sub_le_iff_le_add.mpr (neg_le_sub_iff_le_add.mp a.1), sub_le_iff_le_add.mp (sub_le.mpr a.2)⟩,
  λ a, ⟨neg_le_sub_iff_le_add.mpr (sub_le_iff_le_add.mp a.1) , sub_le_iff_le_add'.mpr a.2⟩⟩

lemma abs_le_iff_mem_Icc (α i y : ℝ) : (abs (y - α) ≤ i ↔ y ∈ Icc (α - i) (α + i)) :=
⟨λ h, ⟨sub_le_of_abs_sub_le_left h, sub_le_iff_le_add'.mp (abs_le.mp h).2⟩,
  λ h, abs_le.mpr ((sub_mem_Icc_iff α i y).mpr h)⟩


lemma exists_forall_ge_of_polynomial_deriv_zero_allowed (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f.derivative) ≤ M :=
begin
  simp_rw abs_le_iff_mem_Icc,
  exact exists_forall_ge_of_polynomial_Ioo _ _,
end


lemma zero_le_add_abs_self (a : ℝ) : 0 ≤ a + abs a :=
begin
  by_cases h : a < 0,
  { rw [abs_of_neg h, add_right_neg] },
  { rw abs_of_nonneg (not_lt.mp h),
    exact le_trans (not_lt.mp h) (le_add_of_nonneg_left (not_lt.mp h)) },
end

lemma exists_forall_ge_of_polynomial_deriv (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, 0 < M ∧ ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f.derivative) ≤ M :=
begin
  obtain ⟨M, xx⟩ := exists_forall_ge_of_polynomial_Ioo_for α f.derivative,
  refine ⟨M + abs M + 1,
    lt_of_lt_of_le zero_lt_one ((le_add_iff_nonneg_left 1).mpr (zero_le_add_abs_self M)), λ y, _⟩,
  rw abs_le_iff_mem_Icc,
  refine λ (hy : y ∈ Icc (α - 1) (α + 1)), xx (M + abs M + 1) (ge_iff_le.mpr _) y hy,
  rw add_assoc,
  apply (le_add_iff_nonneg_right M).mpr,
  apply le_trans (abs_nonneg M) ((le_add_iff_nonneg_right (abs M)).mpr zero_le_one),
end

/-
lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0) :
  ∃ B : ℝ, 0 < B ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := f_roots.image (λ x, abs (α - x)),
--  have h_nonempty : distances.nonempty := ⟨M, finset.mem_insert_self _ _⟩,
  set B := dite (distances.nonempty) (λ d, distances.min' d) (λ d, 1),
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx, rw [finset.mem_image] at hx,
    rcases hx with ⟨α₀, ⟨h, rfl⟩⟩,
--    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
--    { exact hM },
    { apply abs_pos.mpr (sub_ne_zero.mpr (ne.symm (ne_of_mem_of_not_mem h _))),
      exact finset.not_mem_erase α (roots f).to_finset } },
  refine ⟨B, (h_allpos B _), _⟩,
  exact finset.min'_le _ _ (finset.mem_insert.mpr (or.inl rfl)),

  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_image],
      exact or.inr (bex.intro x h₁ rfl), },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂,
end
-/

--this one has 1/M instead of M
lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ M ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (M : ℝ) (f_roots.image (λ x, abs (α - x))),
  have h_nonempty : distances.nonempty := ⟨M, finset.mem_insert_self _ _⟩,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx,
    rw [finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact hM },
    { apply abs_pos.mpr (sub_ne_zero.mpr (ne.symm (ne_of_mem_of_not_mem h _))),
      exact finset.not_mem_erase α (roots f).to_finset } },
  refine ⟨distances.min' h_nonempty, (h_allpos _ (distances.min'_mem _)), _, _⟩,
  { exact finset.min'_le _ _ (finset.mem_insert.mpr (or.inl rfl)) },
  intros x hx hxα,
  rw [ne.def, ← is_root.def, ← mem_roots h_f_nonzero, ← multiset.mem_to_finset],
  intro h,
  have h₂ : abs (α - x) ∈ distances :=
    finset.mem_insert.mpr (or.inr (finset.mem_image.mpr
      (bex.intro x (finset.mem_erase.mpr ⟨hxα, h⟩) rfl))),
  exact h_f_nonzero (false.rec _ ((not_le.mpr hx) (finset.min'_le distances (abs (α - x)) h₂))),
end

lemma non_root_small_interval_of_polynomial_MM (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1 ∧
  ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain ⟨B, B0, BM, xx⟩ :=
    non_root_small_interval_of_polynomial α f h_f_nonzero (1 / M) (one_div_pos.mpr hM),
  by_cases B1 : B ≤ 1,
  { exact ⟨B, B0, BM, B1, xx⟩ },
  refine ⟨1, zero_lt_one, _, rfl.le, λ x hx xa, xx _ (lt_trans hx (not_le.mp B1)) xa⟩,
  apply le_of_lt (lt_of_lt_of_le (not_le.mp B1) BM),
end

--this one has 1/M instead of M
lemma non_root_small_interval_of_polynomial_M (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (1 : ℝ) (insert (1 / M : ℝ) (f_roots.image (λ x, abs (α - x)))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx, rw [finset.mem_insert, finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact zero_lt_one },
    { apply inv_pos.mp,
      simp only [*, one_div, inv_inv'] },
      rcases hx with ⟨x, hx, rfl⟩,
      apply abs_pos.mpr (sub_ne_zero.mpr _),
      symmetry,
      apply ne_of_mem_of_not_mem hx (finset.not_mem_erase α (roots f).to_finset), },
  refine ⟨B, (h_allpos B (distances.min'_mem h_nonempty)), _, _, _⟩,
  exact finset.min'_le _ _ (finset.mem_insert_of_mem (finset.mem_insert.mpr (or.inl rfl))),
  exact finset.min'_le _ _ (finset.mem_insert.mpr (or.inl rfl)),

  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_insert, finset.mem_image],
      exact or.inr (or.inr (Exists.intro x (Exists.intro h₁ rfl))) },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂,
end



lemma exists_deriv_eq_slope_of_polynomial_root (α : ℝ) (f : polynomial ℝ) (h_α_root : f.eval α = 0)
  (x : ℝ) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  have h₀ : x ≠ α, { intro h₁, rw ← h₁ at h_α_root, rw h_α_root at h, tauto },
  rcases ne_iff_lt_or_gt.1 h₀ with h_α_gt | h_α_lt,
  { -- When `x < α`
    have h_cont : continuous_on (λ x, f.eval x) (Icc x α) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo x α) :=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_gt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval α f - eval x f) / (α - x) at hx₀,
    rw [h_α_root, zero_sub] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin
      rwa [hc, neg_div, neg_eq_zero, div_eq_iff (show α - x ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢, rwa mul_comm,
      exact h_Df_nonzero,
      rw sub_ne_zero, exact h₀.symm },
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_pos (sub_pos.mpr h_α_gt), abs_of_pos (sub_pos.mpr x₀_range.2),
      abs_of_neg (sub_lt_zero.mpr x₀_range.1)],
lemma exists_forall_ge_of_polynomial_eval (α : ℝ) (f : polynomial ℝ)
  (h_f_deg : 0 < f.nat_degree) :
  ∃ M : ℝ, 0 < M ∧ ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f) ≤ M :=
begin
  have h_f_nonzero : f ≠ 0 := ne_zero_of_nat_degree_gt h_f_deg,
  obtain ⟨x_max, ⟨h_x_max_range, hM⟩⟩ := is_compact.exists_forall_ge (@compact_Icc (α-1) (α+1))
    begin rw set.nonempty, use α, rw set.mem_Icc, split; linarith end
    (continuous_abs.comp f.continuous_eval).continuous_on,
  replace hM : ∀ (y : ℝ), y ∈ Icc (α - 1) (α + 1) →
    abs (eval y f) ≤ abs (eval x_max f),
    { simpa only [function.comp_app abs] },
  set M := abs (f.eval x_max),
  use M,
  split,
  { apply lt_of_le_of_ne (abs_nonneg _),
    intro hM0, change 0 = M at hM0, rw hM0.symm at hM,
    { refine h_f_nonzero (f.eq_zero_of_infinite_is_root _),
      refine infinite_mono (λ y hy, _) (Icc.infinite (show α - 1 < α + 1, by linarith)),
      simp only [mem_set_of_eq, is_root.def],
      exact abs_nonpos_iff.1 (hM y hy) }},
  intros y hy,
  have hy' : y ∈ Icc (α - 1) (α + 1),
  { apply mem_Icc.mpr,
    have h1 := le_abs_self (y - α),
    have h2 := neg_le_abs_self (y - α),
    split; linarith },
  { -- When `α < x`
    have h_cont : continuous_on (λ x, f.eval x) (Icc α x) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo α x):=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_lt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval x f - eval α f) / (x - α) at hx₀,
    rw [h_α_root, sub_zero] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin rwa [hc, div_eq_iff (show x - α ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢,
      {rw hx₀, ring },
      { exact h_Df_nonzero },
      { rwa sub_ne_zero }},
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_neg (sub_lt_zero.mpr x₀_range.1), abs_of_neg (sub_lt_zero.mpr h_α_lt),
      abs_of_pos (sub_pos.mpr x₀_range.2)],
    split; linarith }
end

#exit








lemma non_root_small_interval_of_polynomial_al (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ ∀ C : ℝ, 0 < C → C ≤ B → ∀ x (hr : abs (α - x) < C) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (1 : ℝ) (f_roots.image (λ x, abs (α - x))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  use distances.min' ⟨1, finset.mem_insert_self _ _⟩,
  refine ⟨lt_of_le_of_ne _ _, _⟩,
--  apply @lt_of_lt_of_le ℝ _ 0 (distances.min' ⟨1, finset.mem_insert_self _ _⟩) _ ,
    { apply finset.le_min',
      intros y hy,
      rw finset.mem_insert at hy,
      rcases hy with ⟨rfl⟩,
      { exact zero_le_one },
      rw finset.mem_image at hy,
      rcases hy with ⟨hy, hj, rfl⟩,
      exact abs_nonneg (α - _) },
    {
      symmetry,
      apply @ne_of_mem_of_not_mem _ _ _ distances _ 0 (finset.min'_mem _ _) _,
      simp only [not_exists, and_imp, abs_eq_zero, false_or, multiset.mem_to_finset, finset.mem_image, finset.mem_insert,
  zero_ne_one, finset.mem_erase],
  intros x hx xr xa,
  rw sub_eq_zero at xa,
  apply hx,
  subst xa },
  intros C C0 Cd x xaC xa fa,
  apply xa,
  dsimp only at *, simp only [ne.def, finset.insert_nonempty] at *,

  fsplit, work_on_goal 1 { intros C ᾰ ᾰ_1 x hr hn ᾰ_2 },

  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { rintros x hx,
    apply @lt_of_lt_of_le _ _ 0 B _ _ (finset.min'_le _ _ hx),
    apply lt_of_le_of_ne,
    { apply finset.le_min',
      intros y hy,
      simp only [one_div, exists_prop, multiset.mem_to_finset, finset.mem_image, ne.def, finset.mem_insert, finset.mem_erase] at hy,
      rcases hy with ⟨rfl⟩,
      exact zero_le_one,
      rcases hy with ⟨rfl⟩,
      exact le_of_lt (inv_pos.mpr hM),
      rcases hy with ⟨xx, yy, rfl⟩,
      exact abs_nonneg (α - xx) },
      symmetry,
    apply @ne_of_mem_of_not_mem _ _ _ distances B 0 (finset.min'_mem _ _) _,
    simp only [one_div, exists_prop, abs_eq_zero, false_or, multiset.mem_to_finset, finset.mem_image, ne.def, finset.mem_insert,
  zero_eq_inv, zero_ne_one, finset.mem_erase],
  intros hH,
  rcases hH with ⟨rfl⟩,
  apply @false_of_ne ℝ 0 (ne_of_lt hM),
  rcases hH with ⟨a, ⟨nb, bb⟩, cc⟩,
  apply nb,
  apply sub_eq_zero.mp,
  apply neg_eq_zero.mp,
  rw neg_sub,
  exact cc, },

   sorry,












end
#exit

  set distances := insert (1 : ℝ) (insert (1 / M : ℝ) (f_roots.image (λ x, abs (α - x)))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { rintros x hx,
    apply @lt_of_lt_of_le _ _ 0 B _ _ (finset.min'_le _ _ hx),
    apply lt_of_le_of_ne,
    { apply finset.le_min',
      intros y hy,
      simp only [one_div, exists_prop, multiset.mem_to_finset, finset.mem_image, ne.def, finset.mem_insert, finset.mem_erase] at hy,
      rcases hy with ⟨rfl⟩,
      exact zero_le_one,
      rcases hy with ⟨rfl⟩,
      exact le_of_lt (inv_pos.mpr hM),
      rcases hy with ⟨xx, yy, rfl⟩,
      exact abs_nonneg (α - xx) },
      symmetry,
    apply @ne_of_mem_of_not_mem _ _ _ distances B 0 (finset.min'_mem _ _) _,
    simp only [one_div, exists_prop, abs_eq_zero, false_or, multiset.mem_to_finset, finset.mem_image, ne.def, finset.mem_insert,
  zero_eq_inv, zero_ne_one, finset.mem_erase],
  intros hH,
  rcases hH with ⟨rfl⟩,
  apply @false_of_ne ℝ 0 (ne_of_lt hM),
  rcases hH with ⟨a, ⟨nb, bb⟩, cc⟩,
  apply nb,
  apply sub_eq_zero.mp,
  apply neg_eq_zero.mp,
  rw neg_sub,
  exact cc, },

   sorry,
end

#exit
   rw [finset.mem_insert, finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact zero_lt_one },
    { apply inv_pos.mp,
      convert hM,
      finish },
      rcases hx with ⟨x, hx, rfl⟩,
      apply abs_pos.mpr,
      apply sub_ne_zero.mpr,
      symmetry,
      apply ne_of_mem_of_not_mem hx (finset.not_mem_erase α (roots f).to_finset), },
  refine ⟨B, (h_allpos B (distances.min'_mem h_nonempty)), _⟩,
  intros C C0 CB y hx ya,

  exact finset.min'_le _ _ (finset.mem_insert_of_mem (finset.mem_insert.mpr (or.inl rfl))),
  exact finset.min'_le _ _ (finset.mem_insert.mpr (or.inl rfl)),

  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_insert, finset.mem_image], right, right, exact ⟨x, ⟨h₁, rfl⟩⟩ },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂
end

lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (1 : ℝ) (insert (1 / M : ℝ) (f_roots.image (λ x, abs (α - x)))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx, rw [finset.mem_insert, finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact zero_lt_one },
    { apply inv_pos.mp,
      convert hM,
      finish },
      rcases hx with ⟨x, hx, rfl⟩,
      apply abs_pos.mpr,
      apply sub_ne_zero.mpr,
      symmetry,
      apply ne_of_mem_of_not_mem hx (finset.not_mem_erase α (roots f).to_finset), },
  refine ⟨B, (h_allpos B (distances.min'_mem h_nonempty)), _, _, _⟩,
  exact finset.min'_le _ _ (finset.mem_insert_of_mem (finset.mem_insert.mpr (or.inl rfl))),
  exact finset.min'_le _ _ (finset.mem_insert.mpr (or.inl rfl)),

  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_insert, finset.mem_image], right, right, exact ⟨x, ⟨h₁, rfl⟩⟩ },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂
end

/-
lemma non_root_interval_of_polynomial_vec (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0) :
  ∃ B : ℝ, 0 < B ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (1 : ℝ) (f_roots.image (λ x, abs (α - x))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx, rw [finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact zero_lt_one },
    { rw [finset.mem_erase] at h,
      rw [abs_pos, sub_ne_zero], exact h.1.symm }},
  use [B, (h_allpos B (distances.min'_mem h_nonempty))],
  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_image], right, exact ⟨x, ⟨h₁, rfl⟩⟩ },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂
end

lemma non_root_small_interval_of_polynomial_ve (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain ⟨B0, ⟨h_B0_pos, h_B0_root⟩⟩ := non_root_interval_of_polynomial α f h_f_nonzero,
--  refine ⟨B0, h_B0_pos, _⟩,

  have h1M : 0 < 1 / M := one_div_pos.mpr hM,
  obtain ⟨B1, ⟨hB11, hB12, hB13⟩⟩ : ∃ B1 : ℝ, 0 < B1 ∧ B1 ≤ 1 / M ∧ B1 ≤ B0,
  { cases le_or_gt (1 / M) B0,
    { use 1 / M, tauto },
    { exact ⟨B0, h_B0_pos, le_of_lt h, le_refl B0⟩ }},
  obtain ⟨B, ⟨hB1, hB2, hB3, hB4⟩⟩ : ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1 ∧ B ≤ B0,
  { cases le_or_gt 1 B1,
    { use 1, split, norm_num, split, linarith, split, norm_num, linarith },
    { use B1, exact ⟨hB11, ⟨hB12, ⟨le_of_lt h, hB13⟩⟩⟩ }},
  refine ⟨B, hB1, hB2, hB3, λ (x : ℝ) (hx : abs (α - x) < B), h_B0_root x _ ⟩,
  linarith
end
-/

lemma exists_deriv_eq_slope_of_polynomial_root (α : ℝ) (f : polynomial ℝ) (h_α_root : f.eval α = 0)
  (x : ℝ) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  have h₀ : x ≠ α, { intro h₁, rw ← h₁ at h_α_root, rw h_α_root at h, tauto },
  rcases ne_iff_lt_or_gt.1 h₀ with h_α_gt | h_α_lt,
  { -- When `x < α`
    have h_cont : continuous_on (λ x, f.eval x) (Icc x α) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo x α) :=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_gt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval α f - eval x f) / (α - x) at hx₀,
    rw [h_α_root, zero_sub] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin
      rwa [hc, neg_div, neg_eq_zero, div_eq_iff (show α - x ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢, rwa mul_comm,
      exact h_Df_nonzero,
      rw sub_ne_zero, exact h₀.symm },
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_pos (sub_pos.mpr h_α_gt), abs_of_pos (sub_pos.mpr x₀_range.2),
      abs_of_neg (sub_lt_zero.mpr x₀_range.1)],
    split; linarith },
  { -- When `α < x`
    have h_cont : continuous_on (λ x, f.eval x) (Icc α x) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo α x):=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_lt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval x f - eval α f) / (x - α) at hx₀,
    rw [h_α_root, sub_zero] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin rwa [hc, div_eq_iff (show x - α ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢,
      {rw hx₀, ring },
      { exact h_Df_nonzero },
      { rwa sub_ne_zero }},
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_neg (sub_lt_zero.mpr x₀_range.1), abs_of_neg (sub_lt_zero.mpr h_α_lt),
      abs_of_pos (sub_pos.mpr x₀_range.2)],
    split; linarith }
end
