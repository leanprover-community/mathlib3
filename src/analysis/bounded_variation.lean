/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `evariation_on f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `has_bounded_variation_on f s` registers that the variation of `f` on `s` is finite.
* `has_locally_bounded_variation f s` registers that `f` has finite variation on any compact
  subinterval of `s`.

* `evariation_on.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `lipschitz_with.has_locally_bounded_variation_on` shows that a Lipschitz function has locally
  bounded variation.
* `has_locally_bounded_variation_on.ae_differentiable_within_at` shows that a bounded variation
  function into a finite dimensional real vector space is differentiable almost everywhere.
* `lipschitz_on_with.ae_differentiable_within_at` is the same result for Lipschitz functions.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

open_locale big_operators nnreal ennreal
open set measure_theory

variables {α β : Type*} [linear_order α] [linear_order β] (φ : β → α) [monotone φ]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
{V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]

/-- The (extended real valued) variation of a function `f` on a set `s` inside a linear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing
sequences `u` in `s`. -/
noncomputable def evariation_on (f : α → E) (s : set α) : ℝ≥0∞ :=
⨆ (p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s}),
  ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → α) (i+1))) (f ((p.2 : ℕ → α) i))

/-- A function has bounded variation on a set `s` if its total variation there is finite. -/
def has_bounded_variation_on (f : α → E) (s : set α) :=
evariation_on f s ≠ ∞

/-- A function has locally bounded variation on a set `s` if, given any interval `[a, b]` with
endpoints in `s`, then the function has finite variation on `s ∩ [a, b]`. -/
def has_locally_bounded_variation_on (f : α → E) (s : set α) :=
∀ a b, a ∈ s → b ∈ s → has_bounded_variation_on f (s ∩ Icc a b)

/-! ## Basic computations of variation -/

namespace evariation_on

lemma nonempty_monotone_mem {s : set α} (hs : s.nonempty) :
  nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s} :=
begin
  obtain ⟨x, hx⟩ := hs,
  exact ⟨⟨λ i, x, λ i j hij, le_rfl, λ i, hx⟩⟩,
end

lemma sum_le
  (f : α → E) {s : set α} (n : ℕ) {u : ℕ → α} (hu : monotone u) (us : ∀ i, u i ∈ s) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=
begin
  let p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, us⟩),
  change ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → α) (i+1))) (f ((p.2 : ℕ → α) i))
    ≤ evariation_on f s,
  exact le_supr (λ (p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s}),
    ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → α) (i+1))) (f ((p.2 : ℕ → α) i))) _,
end

lemma sum_le_of_monotone_on_Iic
  (f : α → E) {s : set α} {n : ℕ} {u : ℕ → α} (hu : monotone_on u (Iic n))
  (us : ∀ i ≤ n, u i ∈ s) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=
begin
  let v := λ i, if i ≤ n then u i else u n,
  have vs : ∀ i, v i ∈ s,
  { assume i,
    simp only [v],
    split_ifs,
    { exact us i h },
    { exact us n le_rfl } },
  have hv : monotone v,
  { apply monotone_nat_of_le_succ (λ i, _),
    simp only [v],
    rcases lt_trichotomy i n with hi|rfl|hi,
    { have : i + 1 ≤ n, by linarith,
      simp only [hi.le, this, if_true],
      exact hu hi.le this (nat.le_succ i) },
    { simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero,
                 if_false] },
    { have A : ¬(i ≤ n), by linarith,
      have B : ¬(i + 1 ≤ n), by linarith,
      simp [A, B] } },
  convert sum_le f n hv vs using 1,
  apply finset.sum_congr rfl (λ i hi, _),
  simp only [finset.mem_range] at hi,
  have : i + 1 ≤ n, by linarith,
  simp only [v],
  simp [this, hi.le],
end

lemma sum_le_of_monotone_on_Icc
  (f : α → E) {s : set α} {m n : ℕ} {u : ℕ → α} (hu : monotone_on u (Icc m n))
  (us : ∀ i ∈ Icc m n, u i ∈ s) :
  ∑ i in finset.Ico m n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=
begin
  rcases le_or_lt n m with hnm|hmn,
  { simp only [finset.Ico_eq_empty_of_le hnm, finset.sum_empty, zero_le'] },
  let v := λ i, u (m + i),
  have hv : monotone_on v (Iic (n - m)),
  { assume a ha b hb hab,
    simp only [le_tsub_iff_left hmn.le, mem_Iic] at ha hb,
    exact hu ⟨le_add_right le_rfl, ha⟩ ⟨le_add_right le_rfl, hb⟩ (add_le_add le_rfl hab) },
  have vs : ∀ i ∈ Iic (n - m), v i ∈ s,
  { assume i hi,
    simp only [le_tsub_iff_left hmn.le, mem_Iic] at hi,
    exact us _ ⟨le_add_right le_rfl, hi⟩ },
  calc ∑ i in finset.Ico m n, edist (f (u (i + 1))) (f (u i))
      = ∑ i in finset.range (n - m), edist (f (u (m + i + 1))) (f (u (m + i))) :
    begin
      rw [finset.range_eq_Ico],
      convert (finset.sum_Ico_add (λ i, edist (f (u (i + 1))) (f (u i))) 0 (n - m) m).symm,
      { rw [zero_add] },
      { rw tsub_add_cancel_of_le hmn.le }
    end
  ... = ∑ i in finset.range (n - m), edist (f (v (i + 1))) (f (v i)) :
    begin
      apply finset.sum_congr rfl (λ i hi, _),
      simp only [v, add_assoc],
    end
  ... ≤ evariation_on f s : sum_le_of_monotone_on_Iic f hv vs,
end

lemma mono (f : α → E) {s t : set α} (hst : t ⊆ s) :
  evariation_on f t ≤ evariation_on f s :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  exact sum_le f n hu (λ i, hst (ut i)),
end

lemma _root_.has_bounded_variation_on.mono {f : α → E} {s : set α}
  (h : has_bounded_variation_on f s) {t : set α} (ht : t ⊆ s) :
  has_bounded_variation_on f t :=
(lt_of_le_of_lt (evariation_on.mono f ht) (lt_top_iff_ne_top.2 h)).ne

lemma _root_.has_bounded_variation_on.has_locally_bounded_variation_on {f : α → E} {s : set α}
  (h : has_bounded_variation_on f s) : has_locally_bounded_variation_on f s :=
λ x y hx hy, h.mono (inter_subset_left _ _)

@[simp] protected lemma subsingleton (f : α → E) {s : set α} (hs : s.subsingleton) :
  evariation_on f s = 0 :=
begin
  apply le_antisymm _ (zero_le _),
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  have : ∀ i, u i = u 0, from λ i, hs (ut _) (ut _),
  simp [subtype.coe_mk, le_zero_iff, finset.sum_eq_zero_iff, finset.mem_range, this],
end

lemma edist_le (f : α → E) {s : set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ evariation_on f s :=
begin
  wlog hxy : x ≤ y := le_total x y using [x y, y x] tactic.skip, swap,
  { assume hx hy,
    rw edist_comm,
    exact this hy hx },
  let u : ℕ → α := λ n, if n = 0 then x else y,
  have hu : monotone u,
  { assume m n hmn,
    dsimp only [u],
    split_ifs,
    exacts [le_rfl, hxy, by linarith [pos_iff_ne_zero.2 h], le_rfl] },
  have us : ∀ i, u i ∈ s,
  { assume i,
    dsimp only [u],
    split_ifs,
    exacts [hx, hy] },
  convert sum_le f 1 hu us,
  simp [u, edist_comm],
end

lemma _root_.has_bounded_variation_on.dist_le {E : Type*} [pseudo_metric_space E]
  {f : α → E} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  dist (f x) (f y) ≤ (evariation_on f s).to_real :=
begin
  rw [← ennreal.of_real_le_of_real_iff ennreal.to_real_nonneg, ennreal.of_real_to_real h,
      ← edist_dist],
  exact edist_le f hx hy
end

lemma _root_.has_bounded_variation_on.sub_le
  {f : α → ℝ} {s : set α} (h : has_bounded_variation_on f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
  f x - f y ≤ (evariation_on f s).to_real :=
begin
  apply (le_abs_self _).trans,
  rw ← real.dist_eq,
  exact h.dist_le hx hy
end

/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
lemma add_point (f : α → E) {s : set α} {x : α} (hx : x ∈ s)
  (u : ℕ → α) (hu : monotone u) (us : ∀ i, u i ∈ s) (n : ℕ) :
  ∃ (v : ℕ → α) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s) ∧ x ∈ v '' (Iio m) ∧
    ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤
      ∑ j in finset.range m, edist (f (v (j+1))) (f (v j)) :=
begin
  rcases le_or_lt (u n) x with h|h,
  { let v := λ i, if i ≤ n then u i else x,
    have vs : ∀ i, v i ∈ s,
    { assume i,
      simp only [v],
      split_ifs,
      { exact us i },
      { exact hx } },
    have hv : monotone v,
    { apply monotone_nat_of_le_succ (λ i, _),
      simp only [v],
      rcases lt_trichotomy i n with hi|rfl|hi,
      { have : i + 1 ≤ n := nat.succ_le_of_lt hi,
        simp only [hi.le, this, if_true],
        exact hu (nat.le_succ i) },
      { simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero,
                  if_false, h], },
      { have A : ¬(i ≤ n) := hi.not_le,
        have B : ¬(i + 1 ≤ n) := λ h, A (i.le_succ.trans h),
        simp only [A, B, if_false]} },
    refine ⟨v, n+2, hv, vs, (mem_image _ _ _).2 ⟨n+1, _, _⟩, _⟩,
    { rw mem_Iio, exact nat.lt_succ_self (n+1) },
    { have : ¬(n + 1 ≤ n) := nat.not_succ_le_self n,
      simp only [this, ite_eq_right_iff, is_empty.forall_iff] },
    { calc
        ∑ i in finset.range n, edist (f (u (i+1))) (f (u i))
        = ∑ i in finset.range n, edist (f (v (i+1))) (f (v i)) :
        begin
          apply finset.sum_congr rfl (λ i hi, _),
          simp only [finset.mem_range] at hi,
          have : i + 1 ≤ n := nat.succ_le_of_lt hi,
          dsimp only [v],
          simp only [hi.le, this, if_true],
        end
      ... ≤ ∑ j in finset.range (n + 2), edist (f (v (j+1))) (f (v j)) :
        finset.sum_le_sum_of_subset (finset.range_mono (nat.le_add_right n 2)) } },
  have exists_N : ∃ N, N ≤ n ∧ x < u N, from ⟨n, le_rfl, h⟩,
  let N := nat.find exists_N,
  have hN : N ≤ n ∧ x < u N := nat.find_spec exists_N,
  let w : ℕ → α := λ i, if i < N then u i else if i = N then x else u (i - 1),
  have ws : ∀ i, w i ∈ s,
  { dsimp only [w],
    assume i,
    split_ifs,
    exacts [us _, hx, us _] },
  have hw : monotone w,
  { apply monotone_nat_of_le_succ (λ i, _),
    dsimp only [w],
    rcases lt_trichotomy (i + 1) N with hi|hi|hi,
    { have : i < N := nat.lt_of_le_of_lt (nat.le_succ i) hi,
      simp only [hi, this, if_true],
      exact hu (nat.le_succ _) },
    { have A : i < N := hi ▸ (i.lt_succ_self),
      have B : ¬(i + 1 < N) := by { rw ←hi, exact λ h, h.ne rfl, },
      rw [if_pos A, if_neg B, if_pos hi],
      have T := nat.find_min exists_N A,
      push_neg at T,
      exact T (A.le.trans hN.1) },
    { have A : ¬(i < N) := (nat.lt_succ_iff.mp hi).not_lt,
      have B : ¬(i + 1 < N) := hi.not_lt,
      have C : ¬(i + 1 = N) := hi.ne.symm,
      have D : i + 1 - 1 = i := nat.pred_succ i,
      rw [if_neg A, if_neg B, if_neg C, D],
      split_ifs,
      { exact hN.2.le.trans (hu (le_of_not_lt A)) },
      { exact hu (nat.pred_le _) } } },
  refine ⟨w, n+1, hw, ws, (mem_image _ _ _).2 ⟨N, hN.1.trans_lt (nat.lt_succ_self n), _⟩, _⟩,
  { dsimp only [w], rw [if_neg (lt_irrefl N), if_pos rfl] },
  rcases eq_or_lt_of_le (zero_le N) with Npos|Npos,
  { calc ∑ i in finset.range n, edist (f (u (i + 1))) (f (u i))
        = ∑ i in finset.range n, edist (f (w (1 + i + 1))) (f (w (1 + i))) :
      begin
        apply finset.sum_congr rfl (λ i hi, _),
        dsimp only [w],
        simp only [← Npos, nat.not_lt_zero, nat.add_succ_sub_one, add_zero, if_false,
          add_eq_zero_iff, nat.one_ne_zero, false_and, nat.succ_add_sub_one, zero_add],
        rw add_comm 1 i,
      end
    ... = ∑ i in finset.Ico 1 (n + 1), edist (f (w (i + 1))) (f (w i)) :
      begin
        rw finset.range_eq_Ico,
        exact finset.sum_Ico_add (λ i, edist (f (w (i + 1))) (f (w i))) 0 n 1,
      end
    ... ≤ ∑ j in finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) :
      begin
        apply finset.sum_le_sum_of_subset _,
        rw finset.range_eq_Ico,
        exact finset.Ico_subset_Ico zero_le_one le_rfl,
      end },
  { calc ∑ i in finset.range n, edist (f (u (i + 1))) (f (u i))
        = ∑ i in finset.Ico 0 (N-1), edist (f (u (i + 1))) (f (u i)) +
          ∑ i in finset.Ico (N-1) N, edist (f (u (i + 1))) (f (u i)) +
          ∑ i in finset.Ico N n, edist (f (u (i + 1))) (f (u i)) :
      begin
        rw [finset.sum_Ico_consecutive, finset.sum_Ico_consecutive, finset.range_eq_Ico],
        { exact zero_le _ },
        { exact hN.1 },
        { exact zero_le _},
        { exact nat.pred_le _ }
      end
    ... = ∑ i in finset.Ico 0 (N-1), edist (f (w (i + 1))) (f (w i)) +
          edist (f (u N)) (f (u (N - 1))) +
          ∑ i in finset.Ico N n, edist (f (w (1 + i + 1))) (f (w (1 + i))) :
      begin
        congr' 1, congr' 1,
        { apply finset.sum_congr rfl (λ i hi, _),
          simp only [finset.mem_Ico, zero_le', true_and] at hi,
          dsimp only [w],
          have A : i + 1 < N, from nat.lt_pred_iff.1 hi,
          have B : i < N := nat.lt_of_succ_lt A,
          rw [if_pos A, if_pos B] },
        { have A : N - 1 + 1 = N, from nat.succ_pred_eq_of_pos Npos,
          have : finset.Ico (N - 1) N = {N - 1}, by rw [← nat.Ico_succ_singleton, A],
          simp only [this, A, finset.sum_singleton] },
        { apply finset.sum_congr rfl (λ i hi, _),
          simp only [finset.mem_Ico] at hi,
          dsimp only [w],
          have A : ¬(1 + i + 1 < N) := λ h, by
          { rw [add_assoc, add_comm] at h,
            exact (hi.left).not_lt ((i.lt_succ_self).trans ((i.succ.lt_succ_self).trans h)), },
          have B : ¬(1 + i + 1 = N) := λ h, by
          { rw [←h, add_assoc, add_comm] at hi,
            exact nat.not_succ_le_self i (i.succ.le_succ.trans hi.left), },
          have C : ¬(1 + i < N) := λ h, by
          { rw [add_comm] at h, exact (hi.left).not_lt (i.lt_succ_self.trans h), },
          have D : ¬(1 + i = N) := λ h, by
          { rw [←h, add_comm, nat.succ_le_iff] at hi, exact hi.left.ne rfl, },
          rw [if_neg A, if_neg B, if_neg C, if_neg D],
          congr' 3;
          { rw [add_comm, nat.sub_one], apply nat.pred_succ, } }
      end
    ... = ∑ i in finset.Ico 0 (N-1), edist (f (w (i + 1))) (f (w i)) +
          edist (f (w (N + 1))) (f (w (N - 1))) +
          ∑ i in finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w (i))) :
      begin
        congr' 1, congr' 1,
        { dsimp only [w],
          have A : ¬(N + 1 < N) := nat.not_succ_lt_self,
          have B : N - 1 < N := nat.pred_lt Npos.ne',
          simp only [A, not_and, not_lt, nat.succ_ne_self, nat.add_succ_sub_one, add_zero, if_false,
            B, if_true] },
        { exact finset.sum_Ico_add (λ i, edist (f (w (i + 1))) (f (w i))) N n 1 }
      end
    ... ≤ ∑ i in finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i)) +
          ∑ i in finset.Ico (N - 1) (N + 1), edist (f (w (i + 1))) (f (w i)) +
          ∑ i in finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) :
      begin
        refine add_le_add (add_le_add le_rfl _) le_rfl,
        have A : N - 1 + 1 = N := nat.succ_pred_eq_of_pos Npos,
        have B : N - 1 + 1 < N + 1 := A.symm ▸ N.lt_succ_self,
        have C : N - 1 < N + 1 := lt_of_le_of_lt (N.pred_le) (N.lt_succ_self),
        rw [finset.sum_eq_sum_Ico_succ_bot C, finset.sum_eq_sum_Ico_succ_bot B, A, finset.Ico_self,
          finset.sum_empty, add_zero, add_comm (edist _ _)],
        exact edist_triangle _ _ _,
      end
    ... = ∑ j in finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) :
      begin
        rw [finset.sum_Ico_consecutive, finset.sum_Ico_consecutive, finset.range_eq_Ico],
        { exact zero_le _ },
        { linarith },
        { exact zero_le _ },
        { linarith }
      end }
end

/-- The variation of a function on the union of two sets `s` and `t`, with `s` to the left of `t`,
bounds the sum of the variations along `s` and `t`. -/
lemma add_le_union (f : α → E) {s t : set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
  evariation_on f s + evariation_on f t ≤ evariation_on f (s ∪ t) :=
begin
  by_cases hs : s = ∅,
  { simp [hs] },
  haveI : nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s},
    from nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs),
  by_cases ht : t = ∅,
  { simp [ht] },
  haveI : nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ t},
    from nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht),
  refine ennreal.supr_add_supr_le _,
  /- We start from two sequences `u` and `v` along `s` and `t` respectively, and we build a new
  sequence `w` along `s ∪ t` by juxtaposing them. Its variation is larger than the sum of the
  variations. -/
  rintros ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩,
  let w := λ i, if i ≤ n then u i else v (i - (n+1)),
  have wst : ∀ i, w i ∈ s ∪ t,
  { assume i,
    by_cases hi : i ≤ n,
    { simp [w, hi, us] },
    { simp [w, hi, vt] } },
  have hw : monotone w,
  { assume i j hij,
    dsimp only [w],
    split_ifs,
    { exact hu hij },
    { apply h _ (us _) _ (vt _) },
    { linarith },
    { apply hv (tsub_le_tsub hij le_rfl) } },
  calc ∑ i in finset.range n, edist (f (u (i + 1))) (f (u i))
    + ∑ (i : ℕ) in finset.range m, edist (f (v (i + 1))) (f (v i))
  =  ∑ i in finset.range n, edist (f (w (i + 1))) (f (w i))
    + ∑ (i : ℕ) in finset.range m, edist (f (w ((n+1) + i + 1))) (f (w ((n+1) + i))) :
    begin
      dsimp only [w],
      congr' 1,
      { apply finset.sum_congr rfl (λ i hi, _),
        simp only [finset.mem_range] at hi,
        have : i + 1 ≤ n, by linarith,
        simp [hi.le, this] },
      { apply finset.sum_congr rfl (λ i hi, _),
        simp only [finset.mem_range] at hi,
        have A : ¬(n + 1 + i + 1 ≤ n), by linarith,
        have B : ¬(n + 1 + i ≤ n), by linarith,
        have C : n + 1 + i - n = i + 1,
        { rw tsub_eq_iff_eq_add_of_le,
          { abel },
          { linarith } },
        simp only [A, B, C, nat.succ_sub_succ_eq_sub, if_false, add_tsub_cancel_left] }
    end
  ... = ∑ i in finset.range n, edist (f (w (i + 1))) (f (w i))
          + ∑ (i : ℕ) in finset.Ico (n+1) ((n+1)+m), edist (f (w (i + 1))) (f (w i)) :
    begin
      congr' 1,
      rw finset.range_eq_Ico,
      convert finset.sum_Ico_add (λ (i : ℕ), edist (f (w (i + 1))) (f (w i))) 0 m (n+1) using 3;
      abel,
    end
  ... ≤ ∑ i in finset.range ((n+1) + m), edist (f (w (i + 1))) (f (w i)) :
    begin
      rw ← finset.sum_union,
      { apply finset.sum_le_sum_of_subset _,
        rintros i hi,
        simp only [finset.mem_union, finset.mem_range, finset.mem_Ico] at hi ⊢,
        cases hi,
        { linarith },
        { exact hi.2 } },
      { apply finset.disjoint_left.2 (λ i hi h'i, _),
        simp only [finset.mem_Ico, finset.mem_range] at hi h'i,
        linarith [h'i.1] }
    end
  ... ≤ evariation_on f (s ∪ t) : sum_le f _ hw wst
end

/-- If a set `s` is to the left of a set `t`, and both contain the boundary point `x`, then
the variation of `f` along `s ∪ t` is the sum of the variations. -/
lemma union (f : α → E) {s t : set α} {x : α} (hs : is_greatest s x) (ht : is_least t x) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=
begin
  classical,
  apply le_antisymm _ (evariation_on.add_le_union f (λ a ha b hb, le_trans (hs.2 ha) (ht.2 hb))),
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ust⟩⟩,
  obtain ⟨v, m, hv, vst, xv, huv⟩ : ∃ (v : ℕ → α) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s ∪ t) ∧
    x ∈ v '' (Iio m) ∧ ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤
                        ∑ j in finset.range m, edist (f (v (j+1))) (f (v j)),
    from evariation_on.add_point f (mem_union_left t hs.1) u hu ust n,
  obtain ⟨N, hN, Nx⟩ : ∃ N, N < m ∧ v N = x, from xv,
  calc  ∑ j in finset.range n, edist (f (u (j + 1))) (f (u j))
      ≤ ∑ j in finset.range m, edist (f (v (j + 1))) (f (v j)) : huv
  ... = ∑ j in finset.Ico 0 N , edist (f (v (j + 1))) (f (v j))
        + ∑ j in finset.Ico N m , edist (f (v (j + 1))) (f (v j)) :
    by rw [finset.range_eq_Ico, finset.sum_Ico_consecutive _ (zero_le _) hN.le]
  ... ≤ evariation_on f s + evariation_on f t :
  begin
    refine add_le_add _ _,
    { apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) (λ i hi, _),
      rcases vst i with h|h, { exact h },
      have : v i = x,
      { apply le_antisymm,
        { rw ← Nx, exact hv hi.2 },
        { exact ht.2 h } },
      rw this,
      exact hs.1 },
    { apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) (λ i hi, _),
      rcases vst i with h|h, swap, { exact h },
      have : v i = x,
      { apply le_antisymm,
        { exact hs.2 h },
        { rw ← Nx, exact hv hi.1 } },
      rw this,
      exact ht.1 }
  end
end

lemma Icc_add_Icc (f : α → E) {s : set α} {a b c : α}
  (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
  evariation_on f (s ∩ Icc a b) + evariation_on f (s ∩ Icc b c) = evariation_on f (s ∩ Icc a c) :=
begin
  have A : is_greatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, (inter_subset_right _ _).trans (Icc_subset_Iic_self)⟩,
  have B : is_least (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, (inter_subset_right _ _).trans (Icc_subset_Ici_self)⟩,
  rw [← evariation_on.union f A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc],
end

end evariation_on

/-! ## Monotone functions and bounded variation -/

lemma monotone_on.evariation_on_le {f : α → ℝ} {s : set α} (hf : monotone_on f s) {a b : α}
  (as : a ∈ s) (bs : b ∈ s) :
  evariation_on f (s ∩ Icc a b) ≤ ennreal.of_real (f b - f a) :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, us⟩⟩,
  calc
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i))
      = ∑ i in finset.range n, ennreal.of_real (f (u (i + 1)) - f (u i)) :
    begin
      apply finset.sum_congr rfl (λ i hi, _),
      simp only [finset.mem_range] at hi,
      rw [edist_dist, real.dist_eq, abs_of_nonneg],
      exact sub_nonneg_of_le (hf (us i).1 (us (i+1)).1 (hu (nat.le_succ _))),
    end
  ... = ennreal.of_real (∑ i in finset.range n, (f (u (i + 1)) - f (u i))) :
    begin
      rw [ennreal.of_real_sum_of_nonneg],
      assume i hi,
      exact sub_nonneg_of_le (hf (us i).1 (us (i+1)).1 (hu (nat.le_succ _)))
    end
  ... = ennreal.of_real (f (u n) - f (u 0)) : by rw finset.sum_range_sub (λ i, f (u i))
  ... ≤ ennreal.of_real (f b - f a) :
    begin
      apply ennreal.of_real_le_of_real,
      exact sub_le_sub (hf (us n).1 bs (us n).2.2) (hf as (us 0).1 (us 0).2.1),
    end
end

lemma monotone_on.has_locally_bounded_variation_on {f : α → ℝ} {s : set α} (hf : monotone_on f s) :
  has_locally_bounded_variation_on f s :=
λ a b as bs, ((hf.evariation_on_le as bs).trans_lt ennreal.of_real_lt_top).ne

/-- If a real valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
lemma has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on {f : α → ℝ} {s : set α}
  (h : has_locally_bounded_variation_on f s) :
  ∃ (p q : α → ℝ), monotone_on p s ∧ monotone_on q s ∧ f = p - q :=
begin
  rcases eq_empty_or_nonempty s with rfl|hs,
  { exact ⟨f, 0, subsingleton_empty.monotone_on _, subsingleton_empty.monotone_on _,
            by simp only [tsub_zero]⟩ },
  rcases hs with ⟨c, cs⟩,
  let p := λ x, if c ≤ x then (evariation_on f (s ∩ Icc c x)).to_real
    else -(evariation_on f (s ∩ Icc x c)).to_real,
  have hp : monotone_on p s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : evariation_on f (s ∩ Icc c x) + evariation_on f (s ∩ Icc x y)
        = evariation_on f (s ∩ Icc c y), from evariation_on.Icc_add_Icc f hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs) (h x y xs ys)],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { exact (neg_nonpos.2 ennreal.to_real_nonneg).trans ennreal.to_real_nonneg },
    { simp only [neg_le_neg_iff],
      have : evariation_on f (s ∩ Icc x y) + evariation_on f (s ∩ Icc y c)
        = evariation_on f (s ∩ Icc x c), from evariation_on.Icc_add_Icc f hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys) (h y c ys cs), add_comm],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg } },
  have hq : monotone_on (λ x, p x - f x) s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : evariation_on f (s ∩ Icc c x) + evariation_on f (s ∩ Icc x y)
        = evariation_on f (s ∩ Icc c y), from evariation_on.Icc_add_Icc f hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs) (h x y xs ys)],
      suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x y)).to_real, by linarith,
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x c)).to_real
        + (evariation_on f (s ∩ Icc c y)).to_real, by linarith,
      rw [← ennreal.to_real_add (h x c xs cs) (h c y cs ys),
          evariation_on.Icc_add_Icc f (not_le.1 hcx).le hcy cs],
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ },
    { have : evariation_on f (s ∩ Icc x y) + evariation_on f (s ∩ Icc y c)
        = evariation_on f (s ∩ Icc x c), from evariation_on.Icc_add_Icc f hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys) (h y c ys cs)],
      suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x y)).to_real, by linarith,
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ } },
  refine ⟨p, λ x, p x - f x, hp, hq, _⟩,
  ext x,
  dsimp,
  abel,
end


/-! ## Lipschitz functions and bounded variation -/

lemma lipschitz_on_with.comp_evariation_on_le {f : E → F} {C : ℝ≥0} {t : set E}
  (h : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t) :
  evariation_on (f ∘ g) s ≤ C * evariation_on g s :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, us⟩⟩,
  calc
  ∑ i in finset.range n, edist (f (g (u (i+1)))) (f (g (u i)))
      ≤ ∑ i in finset.range n, C * edist (g (u (i+1))) (g (u i)) :
    finset.sum_le_sum (λ i hi, h (hg (us _)) (hg (us _)))
  ... = C * ∑ i in finset.range n, edist (g (u (i+1))) (g (u i)) : by rw finset.mul_sum
  ... ≤ C * evariation_on g s : mul_le_mul_left' (evariation_on.sum_le _ _ hu us) _
end

lemma lipschitz_on_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=
begin
  dsimp [has_bounded_variation_on] at h,
  apply ne_of_lt,
  apply (hf.comp_evariation_on_le hg).trans_lt,
  simp [lt_top_iff_ne_top, h],
end

lemma lipschitz_on_with.comp_has_locally_bounded_variation_on {f : E → F} {C : ℝ≥0} {t : set E}
  (hf : lipschitz_on_with C f t) {g : α → E} {s : set α} (hg : maps_to g s t)
  (h : has_locally_bounded_variation_on g s) :
  has_locally_bounded_variation_on (f ∘ g) s :=
λ x y xs ys, hf.comp_has_bounded_variation_on (hg.mono_left (inter_subset_left _ _)) (h x y xs ys)

lemma lipschitz_with.comp_has_bounded_variation_on {f : E → F} {C : ℝ≥0}
  (hf : lipschitz_with C f) {g : α → E} {s : set α} (h : has_bounded_variation_on g s) :
  has_bounded_variation_on (f ∘ g) s :=
(hf.lipschitz_on_with univ).comp_has_bounded_variation_on (maps_to_univ _ _) h

lemma lipschitz_with.comp_has_locally_bounded_variation_on {f : E → F} {C : ℝ≥0}
  (hf : lipschitz_with C f) {g : α → E} {s : set α} (h : has_locally_bounded_variation_on g s) :
  has_locally_bounded_variation_on (f ∘ g) s :=
(hf.lipschitz_on_with univ).comp_has_locally_bounded_variation_on (maps_to_univ _ _) h

lemma lipschitz_on_with.has_locally_bounded_variation_on {f : ℝ → E} {C : ℝ≥0} {s : set ℝ}
  (hf : lipschitz_on_with C f s) : has_locally_bounded_variation_on f s :=
hf.comp_has_locally_bounded_variation_on (maps_to_id _)
  (@monotone_on_id ℝ _ s).has_locally_bounded_variation_on

lemma lipschitz_with.has_locally_bounded_variation_on {f : ℝ → E} {C : ℝ≥0}
  (hf : lipschitz_with C f) (s : set ℝ) : has_locally_bounded_variation_on f s :=
(hf.lipschitz_on_with s).has_locally_bounded_variation_on


/-! ## Almost everywhere differentiability of functions with locally bounded variation -/

namespace has_locally_bounded_variation_on

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_real
  {f : ℝ → ℝ} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  obtain ⟨p, q, hp, hq, fpq⟩ : ∃ p q, monotone_on p s ∧ monotone_on q s ∧ f = p - q,
    from h.exists_monotone_on_sub_monotone_on,
  filter_upwards [hp.ae_differentiable_within_at_of_mem, hq.ae_differentiable_within_at_of_mem]
    with x hxp hxq xs,
  have fpq : ∀ x, f x = p x - q x, by simp [fpq],
  refine ((hxp xs).sub (hxq xs)).congr (λ y hy, fpq y) (fpq x),
end

/-- A bounded variation function into a finite dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_pi {ι : Type*} [fintype ι]
  {f : ℝ → (ι → ℝ)} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  have A : ∀ (i : ι), lipschitz_with 1 (λ (x : ι → ℝ), x i) := λ i, lipschitz_with.eval i,
  have : ∀ (i : ι), ∀ᵐ x, x ∈ s → differentiable_within_at ℝ (λ (x : ℝ), f x i) s x,
  { assume i,
    apply ae_differentiable_within_at_of_mem_real,
    exact lipschitz_with.comp_has_locally_bounded_variation_on (A i) h },
  filter_upwards [ae_all_iff.2 this] with x hx xs,
  exact differentiable_within_at_pi.2 (λ i, hx i xs),
end

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at_of_mem
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
begin
  let A := (basis.of_vector_space ℝ V).equiv_fun.to_continuous_linear_equiv,
  suffices H : ∀ᵐ x, x ∈ s → differentiable_within_at ℝ (A ∘ f) s x,
  { filter_upwards [H] with x hx xs,
    have : f = (A.symm ∘ A) ∘ f,
      by simp only [continuous_linear_equiv.symm_comp_self, function.comp.left_id],
    rw this,
    exact A.symm.differentiable_at.comp_differentiable_within_at x (hx xs) },
  apply ae_differentiable_within_at_of_mem_pi,
  exact A.lipschitz.comp_has_locally_bounded_variation_on h,
end

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at
  {f : ℝ → V} {s : set ℝ} (h : has_locally_bounded_variation_on f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=
begin
  rw ae_restrict_iff' hs,
  exact h.ae_differentiable_within_at_of_mem
end

/-- A real function into a finite dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiable_at {f : ℝ → V} (h : has_locally_bounded_variation_on f univ) :
  ∀ᵐ x, differentiable_at ℝ f x :=
begin
  filter_upwards [h.ae_differentiable_within_at_of_mem] with x hx,
  rw differentiable_within_at_univ at hx,
  exact hx (mem_univ _),
end

end has_locally_bounded_variation_on

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set . -/
lemma lipschitz_on_with.ae_differentiable_within_at_of_mem
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) :
  ∀ᵐ x, x ∈ s → differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. -/
lemma lipschitz_on_with.ae_differentiable_within_at
  {C : ℝ≥0} {f : ℝ → V} {s : set ℝ} (h : lipschitz_on_with C f s) (hs : measurable_set s) :
  ∀ᵐ x ∂(volume.restrict s), differentiable_within_at ℝ f s x :=
h.has_locally_bounded_variation_on.ae_differentiable_within_at hs

/-- A real Lipschitz function into a finite dimensional real vector space is differentiable
almost everywhere. -/
lemma lipschitz_with.ae_differentiable_at
  {C : ℝ≥0} {f : ℝ → V} (h : lipschitz_with C f) :
  ∀ᵐ x, differentiable_at ℝ f x :=
(h.has_locally_bounded_variation_on univ).ae_differentiable_at


