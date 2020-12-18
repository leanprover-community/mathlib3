/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.set.intervals.infinite
import topology.algebra.polynomial
import analysis.calculus.mean_value
import topology.separation

/-!
This file contains some lemmas about real polynomials and their derivatives
-/

open_locale classical big_operators

open polynomial real set

section intervals

/-- A lemma relating a compact interval and its shifts. -/
lemma sub_mem_Icc_iff (α i y : ℝ) : (y - α ∈ Icc (- i) i ↔ y ∈ Icc (α - i) (α + i)) :=
⟨λ a,
  ⟨sub_le_iff_le_add.mpr (neg_le_sub_iff_le_add.mp a.1), sub_le_iff_le_add.mp (sub_le.mpr a.2)⟩,
  λ a, ⟨neg_le_sub_iff_le_add.mpr (sub_le_iff_le_add.mp a.1) , sub_le_iff_le_add'.mpr a.2⟩⟩

/-- A lemma describing a compact interval via absolute values. -/
lemma abs_le_iff_mem_Icc (α i y : ℝ) : (abs (y - α) ≤ i ↔ y ∈ Icc (α - i) (α + i)) :=
⟨λ h, ⟨sub_le_of_abs_sub_le_left h, sub_le_iff_le_add'.mp (abs_le.mp h).2⟩,
  λ h, abs_le.mpr ((sub_mem_Icc_iff α i y).mpr h)⟩

/-- An element of an open interval is closer to the left end-point than
the length of the interval. -/
lemma abs_lt_abs_left {a b c : ℝ} (hc : b ∈ Ioo a c) :
  abs (a - b) < abs (a - c) :=
begin
  rw [abs_lt, neg_lt, lt_abs, lt_abs, neg_sub, neg_sub],
  exact ⟨or.inr (sub_lt_sub_right hc.2 a), or.inr (sub_lt_sub (lt_trans hc.1 hc.2) hc.1)⟩,
end

/-- An element of an open interval is closer to the right end-point than
the length of the interval. -/
lemma abs_lt_abs_right {a b c : ℝ} (hc : b ∈ Ioo a c) :
  abs (c - b) < abs (a - c) :=
begin
  rw [abs_sub, sub_eq_neg_add, sub_eq_neg_add, ← neg_neg b, ← neg_neg a],
  exact abs_lt_abs_left ⟨neg_lt_neg_iff.mpr hc.2, neg_lt_neg_iff.mpr hc.1⟩,
end

end intervals

/-- A polynomial is bounded on a compact interval. In this formulation, there is the
flexibility of using a larger-than-optimal bound. -/
lemma exists_forall_ge_of_polynomial_Ioo (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ N, N ≥ M → ∀ y ∈ Icc (α - 1) (α + 1), abs (eval y f) ≤ N :=
begin
  obtain ⟨x, ⟨-, hy⟩⟩ := is_compact.exists_forall_ge compact_Icc ⟨α - 1, ⟨rfl.le,
    sub_le_iff_le_add.mpr (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg rfl.le zero_le_one)
    zero_le_one)⟩⟩ (continuous_abs.comp (polynomial.continuous f)).continuous_on,
  exact ⟨abs (f.eval x), λ N hN y hy1, le_trans (hy y hy1) hN⟩,
end

/-- Similar to `exists_forall_ge_of_polynomial_Ioo`, except no freedom on the bound. -/
lemma exists_forall_ge_of_polynomial_Ioo_M_alone (α : ℝ) (f : polynomial ℝ) :
  ∃ M : ℝ, ∀ y ∈ Icc (α - 1) (α + 1), abs (eval y f) ≤ M :=
begin
  obtain ⟨M, F⟩ := exists_forall_ge_of_polynomial_Ioo α f,
  exact ⟨M, F M rfl.le⟩,
end

/-- A lemma in the original PR, now a consequence of `exists_forall_ge_of_polynomial_Ioo`. -/
lemma exists_forall_ge_of_polynomial_eval (α : ℝ) (f : polynomial ℝ):
  ∃ M : ℝ, 0 < M ∧ ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f) ≤ M :=
begin
  obtain ⟨M, F⟩ := exists_forall_ge_of_polynomial_Ioo α f,
  simp_rw ← abs_le_iff_mem_Icc at F,
  by_cases M0 : M ≤ 0,
  { exact ⟨1, zero_lt_one, λ y h, F 1 (le_trans M0 zero_le_one) y h⟩ },
  { exact ⟨M, not_le.mp M0, F M rfl.ge⟩ },
end

/-- A `finset` in a `t1_space` is closed. -/
lemma finset_closed_of_t1 {α : Type*} [topological_space α] [t1_space α] (s : finset α) :
  is_closed (s : set α) :=
begin
  have : (s : set α) = ⋃ a ∈ s, {a}:= by { ext,
    simp only [exists_prop, mem_Union, mem_singleton_iff, exists_eq_right', finset.mem_coe] },
  rw this,
  exact is_closed_bUnion (finite_mem_finset s) (λ i hi, t1_space.t1 i),
end

/-- There is an open interval around any point in the complement of a closed set,
missing the closed set. -/
lemma Ioo_disjoint_of_not_mem_finset (x : ℝ) (C : finset ℝ) :
  ∃ l m : ℝ, x ∈ Ioo l m ∧ ∀ y (yI : y ∈ Ioo l m) (yx : y ≠ x), y ∉ C :=
begin
  obtain oU := is_open_compl_iff.mpr (finset_closed_of_t1 (finset.erase C x)),
  rcases (mem_nhds_iff_exists_Ioo_subset.mp (@mem_nhds_sets _ _ x _ oU _)) with ⟨l, m, aI, IU⟩,
  { refine ⟨l, m, aI, λ y Iy yx yC, mem_of_mem_of_subset Iy IU (finset.mem_coe.mpr _)⟩,
    exact finset.mem_erase.mpr ⟨yx, yC⟩ },
  { exact λ xh, finset.ne_of_mem_erase xh rfl },
end

lemma Ioo_eval_ne_zero (α : ℝ) (f : polynomial ℝ) (f0 : f ≠ 0) :
  ∃ l m : ℝ, α ∈ Ioo l m ∧ ∀ x (xI : x ∈ Ioo l m) (xa : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain oU := is_open_compl_iff.mpr (finset_closed_of_t1 ((roots f).to_finset.erase α)),
  rcases (mem_nhds_iff_exists_Ioo_subset.mp (@mem_nhds_sets _ _ α _ oU _)) with ⟨l, m, aI, IU⟩,
  { refine ⟨l, m, aI, λ x Ix xa xr, _⟩,
    apply @mem_of_mem_of_subset ℝ x (Ioo l m) (↑(f.roots.to_finset.erase α))ᶜ Ix (by convert IU),
    rw [finset.coe_erase, mem_diff],
    refine ⟨_, xa⟩,
    apply multiset.mem_to_finset.mpr,
    exact (mem_roots f0).mpr (is_root.def.mpr xr) },
  { rw [mem_compl_iff, finset.coe_erase, mem_diff],
    exact (λ ff, ff.right (mem_singleton α)) },
end

lemma non_root_small_interval_of_polynomial_good_statement_use_closed
  (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0) (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), x ∉ f.roots.to_finset :=
begin
  obtain ⟨l, m, I, F⟩ := Ioo_disjoint_of_not_mem_finset α f.roots.to_finset,
  refine ⟨min 1 (min (1 / M) (min (α - l) (m - α))), _, _, _, λ x hx, _⟩,
  { rw [lt_min_iff, lt_min_iff, lt_min_iff, one_div, inv_pos],
    refine ⟨zero_lt_one, hM, sub_pos.mpr I.1, sub_pos.mpr I.2⟩ },
  { exact (min_le_iff.mpr (or.inr (min_le_iff.mpr (or.inl rfl.le)))) },
  { exact min_le_iff.mpr (or.inl rfl.le) },
  {
    have H : (x < α + (α - l) ∧ l < x) ∧ x < m ∧ α - x < m - α,
      { simp only [abs_lt, neg_lt_sub_iff_lt_add, lt_min_iff, sub_lt_sub_iff_left,
          add_sub_cancel'_right] at hx,
        exact hx.2.2 },
    exact λ xa, F x (mem_Ioo.mpr ⟨H.1.2, H.2.1⟩) xa,
--    simp only [lt_min_iff, abs_lt, neg_sub, sub_lt_sub_iff_left] at H,
    clear hx,
    exact ⟨H.1.2, H.2.1⟩,

--    rw [abs_lt, neg_lt_sub_iff_lt_add, lt_min_iff,
--      sub_lt_sub_iff_left, add_sub_cancel'_right] at hx,
    simp only [abs_lt, neg_lt_sub_iff_lt_add, lt_min_iff,
      sub_lt_sub_iff_left, add_sub_cancel'_right] at hx,
    exact λ xa, F x (mem_Ioo.mpr ⟨hx.2.2.1.2, hx.2.2.2.1⟩) xa
     }
end


lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain ⟨l, m, I, F⟩ := Ioo_eval_ne_zero α f h_f_nonzero,
  refine ⟨min 1 (min (1 / M) (min (α - l) (m - α))), _, _, _, λ x hx, _⟩,
  { rw [lt_min_iff, lt_min_iff, lt_min_iff, one_div, inv_pos],
    refine ⟨zero_lt_one, hM, sub_pos.mpr I.1, sub_pos.mpr I.2⟩ },
  { exact (min_le_iff.mpr (or.inr (min_le_iff.mpr (or.inl rfl.le)))) },
  { exact min_le_iff.mpr (or.inl rfl.le) },
  { simp only [abs_lt, neg_lt_sub_iff_lt_add, lt_min_iff,
      sub_lt_sub_iff_left, add_sub_cancel'_right] at hx,
    exact F x (mem_Ioo.mpr ⟨hx.2.2.1.2, hx.2.2.2.1⟩) },
end


/-- For any real number `α`, the roots of a non-zero polynomial that are different from `α`
are a positive distance away from `α`.  The parameter `M` gives the flexibility of choosing a
smaller distance than the minimal one required. -/
lemma non_root_small_interval_of_polynomial_my (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
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

section from_topology_separation

/-- The definition of `separated` and the lemma `finset_disjoint_finset_opens_of_ts`
from `topology/separation`. -/
def separated {α : Type*} [topological_space α] : set α → set α → Prop :=
  λ (s t : set α), ∃ U V : (set α), (is_open U) ∧ is_open V ∧
  (∀ a : α, a ∈ s → a ∈ U) ∧ (∀ a : α, a ∈ t → a ∈ V) ∧ disjoint U V

lemma finset_disjoint_finset_opens_of_t2 {α : Type*} [topological_space α] [t2_space α] :
  ∀ (s t : finset α), disjoint s t → separated (s : set α) t := sorry

end from_topology_separation

lemma sep (α : ℝ) (f : polynomial ℝ) :
  separated ({α} : set ℝ) (finset.erase f.roots.to_finset α) :=
begin
  convert finset_disjoint_finset_opens_of_t2 ({α} : finset ℝ) (finset.erase f.roots.to_finset α) _,
  { exact (finset.coe_singleton _).symm },
  { apply disjoint.symm (finset.disjoint_singleton.mpr _),
    exact finset.not_mem_erase α (roots f).to_finset },
end

lemma sep_top {R : Type*} [topological_space R] [t1_space R] [integral_domain R]
  (α : R) (f : polynomial R) : ∃ U : set R, is_open U ∧ α ∈ U
  ∧ disjoint U (finset.erase f.roots.to_finset α) :=
begin
  refine ⟨(finset.erase f.roots.to_finset α)ᶜ, _, _, disjoint_compl_left⟩,
  { exact is_open_compl_iff.mpr (finset_closed_of_t1 (f.roots.to_finset.erase α)) },
  { exact finset.not_mem_erase α f.roots.to_finset },
end

--def roos {R : Type*} [integral_domain R] (f : polynomial R) : set R := f.roots.to_finset

lemma compl_roots_open {R : Type*} [topological_space R] [t1_space R] [integral_domain R]
  (α : R) (f : polynomial R) : is_open (finset.erase f.roots.to_finset α : set R)ᶜ :=
is_open_compl_iff.mpr (finset_closed_of_t1 ((roots f).to_finset.erase α))

lemma roots_closed {R : Type*} [topological_space R] [t1_space R] [integral_domain R]
  (α : R) (f : polynomial R) : is_closed (finset.erase f.roots.to_finset α : set R) :=
finset_closed_of_t1 ((roots f).to_finset.erase α)



lemma interval_roots_open (α : ℝ) (f : polynomial ℝ) (f0 : f ≠ 0) :
  ∃ l m : ℝ, α ∈ Ioo l m ∧ ∀ x (xI : x ∈ Ioo l m) (xa : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain oU := compl_roots_open α f,
  rcases (mem_nhds_iff_exists_Ioo_subset.mp (@mem_nhds_sets _ _ α _ oU _)) with ⟨l, m, aI, IU⟩,
  { refine ⟨l, m, aI, λ x Ix xa xr, _⟩,
    apply @mem_of_mem_of_subset ℝ x (Ioo l m) (↑(f.roots.to_finset.erase α))ᶜ Ix (by convert IU),
    rw [finset.coe_erase, mem_diff],
    refine ⟨_, xa⟩,
    apply multiset.mem_to_finset.mpr,
    exact (mem_roots f0).mpr (is_root.def.mpr xr) },
  { rw [mem_compl_iff, finset.coe_erase, mem_diff],
    exact (λ ff, ff.right (mem_singleton α)) },
end

lemma interval_1 (α : ℝ) (f : polynomial ℝ) (f0 : f ≠ 0) :
  ∃ l m : ℝ, α ∈ Ioo l m ∧ ∀ x (xI : x ∈ Ioo l m) (xa : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain ⟨U, oU, aU, F⟩ := sep_top α f,
  rcases (mem_nhds_iff_exists_Ioo_subset.mp (mem_nhds_sets oU (by convert aU))) with ⟨l, m, aI, IU⟩,
  refine ⟨l, m, aI, λ x Ix xa xr, _⟩,
  apply (not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp F)) ⟨x, IU Ix, _⟩,
  rw finset.coe_erase,
  refine ⟨_, xa⟩,
  apply multiset.mem_to_finset.mpr,
  exact (mem_roots f0).mpr (is_root.def.mpr xr),
end





#exit
(M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=

/-- The original statement, now a consequence of `non_root_small_interval_of_polynomial_my`. -/
lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain F := non_root_small_interval_of_polynomial_my α f h_f_nonzero,
  rcases (F (min 1 (1 / M)) (lt_min zero_lt_one (one_div_pos.mpr hM))) with ⟨B, B0, BM, F⟩,
  exact ⟨B, B0, le_trans BM (min_le_right _ _), le_trans BM (min_le_left _ _), F⟩,
end

/-- Almost the original statement: I moved the introduction of the second real number `x`
next to the introduction of `α`, I introduced the `hax` hypothesis and used a differentiable
function, instead of a polynomial. -/
lemma exists_deriv_eq_slope_of_fun_zero_lt (α x : ℝ) (f : ℝ → ℝ)
  (fc : continuous_on f (Icc α x)) (df : differentiable_on ℝ f (Ioo α x))
  (h_α_root : f α = 0) (h : f x ≠ 0)
   (hax : α < x) :
  ∃ x₀, α - x = - ((f x) / (deriv f x₀)) ∧ deriv f x₀ ≠ 0 ∧ x₀ ∈ Ioo α x:=
begin
  obtain ⟨c, I, F⟩ := exists_deriv_eq_slope f hax fc df,
  rw [h_α_root, sub_zero] at F,
  refine ⟨c, by rwa [F, div_div_cancel', neg_sub], λ d, _, I⟩,
  { rw [eq_comm, d, div_eq_iff (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
    exact h F },
end

/-- The second half of exists_deriv_eq_slope_of_fun_zero_gt. -/
lemma exists_deriv_eq_slope_of_fun_zero_gt (α x : ℝ) (f : ℝ → ℝ)
  (fc : continuous_on f (Icc x α)) (df : differentiable_on ℝ f (Ioo x α))
  (h_α_root : f α = 0) (h : f x ≠ 0) (hax : x < α) :
  ∃ x₀, α - x = - ((f x) / (deriv f x₀)) ∧ (deriv f x₀ ≠ 0) ∧ (x₀ ∈ Ioo x α) :=
begin
  obtain ⟨c, I, F⟩ := exists_deriv_eq_slope f hax fc df,
  rw [h_α_root, zero_sub] at F,
  refine ⟨c, by { rwa [F, ← neg_div, div_div_cancel'], exact neg_ne_zero.mpr h }, λ d, _, I⟩,
  { rw [eq_comm, d, div_eq_iff_mul_eq (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
    exact h (neg_eq_zero.mp F.symm) },
end

/-- The literal statement appearing in the PR. -/
lemma exists_deriv_eq_slope_of_polynomial_root (α : ℝ) (f : polynomial ℝ) (h_α_root : f.eval α = 0)
  (x : ℝ) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  rcases @trichotomous _ (has_lt.lt) _ α x with ax | rfl | xa,
  { obtain ⟨c, d, e, I⟩:= exists_deriv_eq_slope_of_fun_zero_lt α x (λ y, f.eval y)
      (polynomial.continuous_on f) (polynomial.differentiable_on f) h_α_root h ax,
    refine ⟨c, by rwa [polynomial.deriv] at d, by rwa [polynomial.deriv] at e, _, _⟩,
    exact abs_lt_abs_left I,exact abs_lt_abs_right I },
  { exact false.rec _ (h h_α_root) },
  { obtain ⟨c, d, e, I⟩:= exists_deriv_eq_slope_of_fun_zero_gt α x (λ y, f.eval y)
      (polynomial.continuous_on f) (polynomial.differentiable_on f) h_α_root h xa,
    refine ⟨c, by rwa [polynomial.deriv] at d, by rwa [polynomial.deriv] at e, _, _⟩,
    { rw abs_sub _ x,
      exact abs_lt_abs_right I },
    { rw abs_sub _ x,
      exact abs_lt_abs_left I } },
end



#exit

begin
  obtain ⟨c, hc, F, df⟩ := exists_deriv_eq_slope_of_fun_zero_lt (- α) (- x) (f ∘ has_neg.neg) _ _ _ _ (neg_lt_neg hax),
  { rw [deriv.comp, deriv_neg] at hc,
    { simp [h_α_root] at hc,
      refine ⟨- c, _, _, _⟩,
      { rw [div_neg, neg_neg, ← neg_sub] at hc,
        exact eq_neg_of_eq_neg hc.symm },
      { rw [deriv.comp, deriv_neg, mul_neg_one] at F,
        { exact neg_ne_zero.mp F },
        { sorry },
        { exact differentiable_at.neg differentiable_at_id' } },
      { sorry } },
    { sorry },
    { exact differentiable_at.neg differentiable_at_id' } },
  { intros y hy,
    apply continuous_at.continuous_within_at,
    apply continuous_at.comp,
    have : -y ∈ Icc x α,apply mem_Icc.mpr,
    { rw [le_neg, neg_le],
      exact ⟨hy.2, hy.1⟩ },
    apply continuous_within_at.continuous_at (fc (-y) this),
    apply mem_nhds_iff_exists_Ioo_subset.mpr ⟨x, α, _, _⟩,
    sorry,
    exact continuous_at_neg },
  { sorry },
  repeat { rwa [function.comp_app, neg_neg] },
end

/-- Almost the original statement: I moved the introduction of the second real number `x`
next to the introduction of `α` and I introduced the `hax` hypothesis. -/
lemma exists_deriv_eq_slope_of_polynomial_root_gt (α x : ℝ) (f : polynomial ℝ)
  (h_α_root : f.eval α = 0) (h : f.eval x ≠ 0) (hax : x < α) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin

  { obtain ⟨c, hc, F⟩ := exists_deriv_eq_slope
      (λ y, f.eval y) hax (polynomial.continuous_on f) (polynomial.differentiable_on f),
    simp only [polynomial.deriv, h_α_root, sub_zero] at F,
    cases mem_Ioo.mp hc with hl hr,
    refine ⟨c, by rwa [F, div_div_cancel', neg_sub], λ fd, _, _, _⟩,
    { symmetry' at F,
      rw [fd, div_eq_iff (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
      exact h F },
    { rw [abs_lt, neg_lt, lt_abs, lt_abs],
      exact ⟨or.inr (neg_lt_neg (sub_lt_sub_left hr α)), or.inr (by linarith)⟩ },
    { rw [abs_sub, abs_lt, neg_lt, lt_abs, lt_abs, neg_sub, neg_sub],
      exact ⟨or.inr (sub_lt_sub_left hl x), or.inr (sub_lt_sub hr hax)⟩ } },
end

/-- Almost the original statement: I moved the introduction of the second real number `x`
next to the introduction of `α` and I introduced the `hax` hypothesis. -/
lemma exists_deriv_eq_slope_of_polynomial_root_lt (α x : ℝ) (f : polynomial ℝ)
  (h_α_root : f.eval α = 0) (h : f.eval x ≠ 0) (hax : α < x) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  { obtain ⟨c, hc, F⟩ := exists_deriv_eq_slope
      (λ y, f.eval y) hax (polynomial.continuous_on f) (polynomial.differentiable_on f),
    simp only [polynomial.deriv, h_α_root, sub_zero] at F,
    cases mem_Ioo.mp hc with hl hr,
    refine ⟨c, by rwa [F, div_div_cancel', neg_sub], λ fd, _, _, _⟩,
    { symmetry' at F,
      rw [fd, div_eq_iff (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
      exact h F },
    { rw [abs_lt, neg_lt, lt_abs, lt_abs],
      exact ⟨or.inr (neg_lt_neg (sub_lt_sub_left hr α)), or.inr (by linarith)⟩ },
    { rw [abs_sub, abs_lt, neg_lt, lt_abs, lt_abs, neg_sub, neg_sub],
      exact ⟨or.inr (sub_lt_sub_left hl x), or.inr (sub_lt_sub hr hax)⟩ } },
end

lemma exists_deriv_eq_slope_of_polynomial_root_gt (α x : ℝ) (f : polynomial ℝ)
  (h_α_root : f.eval α = 0) (h : f.eval x ≠ 0) (hax : x < α) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  obtain F := exists_deriv_eq_slope_of_polynomial_root_lt (- α) (- x) _ _ _,
  { obtain ⟨c, hc, F⟩ := exists_deriv_eq_slope
      (λ y, f.eval y) hax (polynomial.continuous_on f) (polynomial.differentiable_on f),
    simp only [polynomial.deriv, h_α_root, sub_zero] at F,
    cases mem_Ioo.mp hc with hl hr,
    refine ⟨c, by rwa [F, div_div_cancel', neg_sub], λ fd, _, _, _⟩,
    { symmetry' at F,
      rw [fd, div_eq_iff (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
      exact h F },
    { rw [abs_lt, neg_lt, lt_abs, lt_abs],
      exact ⟨or.inr (neg_lt_neg (sub_lt_sub_left hr α)), or.inr (by linarith)⟩ },
    { rw [abs_sub, abs_lt, neg_lt, lt_abs, lt_abs, neg_sub, neg_sub],
      exact ⟨or.inr (sub_lt_sub_left hl x), or.inr (sub_lt_sub hr hax)⟩ } },
end



/-- Almost the original statement: I moved the introduction of the second real number `x`
next to the introduction of `α`. -/
lemma exists_deriv_eq_slope_of_polynomial_root (α x : ℝ) (f : polynomial ℝ)
  (h_α_root : f.eval α = 0) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  by_cases hax : α < x,
  { obtain ⟨c, hc, F⟩ := exists_deriv_eq_slope
      (λ y, f.eval y) hax (polynomial.continuous_on f) (polynomial.differentiable_on f),
    simp only [polynomial.deriv, h_α_root, sub_zero] at F,
    cases mem_Ioo.mp hc with hl hr,
    refine ⟨c, by rwa [F, div_div_cancel', neg_sub], λ fd, _, _, _⟩,
    { symmetry' at F,
      rw [fd, div_eq_iff (ne_of_gt (sub_pos.mpr hax)), zero_mul] at F,
      exact h F },
    { rw [abs_lt, neg_lt, lt_abs, lt_abs],
      exact ⟨or.inr (neg_lt_neg (sub_lt_sub_left hr α)), or.inr (by linarith)⟩ },
    { rw [abs_sub, abs_lt, neg_lt, lt_abs, lt_abs, neg_sub, neg_sub],
      exact ⟨or.inr (sub_lt_sub_left hl x), or.inr (sub_lt_sub hr hax)⟩ } },
  sorry,
end

--sorry

#exit

--original lemma
lemma non_root_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0) :
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
