/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.deriv
import data.set.intervals.monotone
import measure_theory.measure.lebesgue
import analysis.calculus.monotone


/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is differentiable almost everywhere. This implies that Lipschitz functions are differentiable
almost everywhere.
-/


open_locale big_operators nnreal ennreal
open set

variables {α : Type*} [linear_order α]
{E : Type*} [pseudo_emetric_space E] {F : Type*} [pseudo_metric_space F]

/-- The (extended real valued) variation of a function `f` on a set `s` is the supremum of the
sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing sequences `u` in `s`. -/
noncomputable def evariation_on (f : α → E) (s : set α) : ℝ≥0∞ :=
⨆ (p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s}),
  ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → α) (i+1))) (f ((p.2 : ℕ → α) i))

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

lemma dist_le (f : α → F) {s : set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s)
  (h : evariation_on f s ≠ ∞):
  dist (f x) (f y) ≤ (evariation_on f s).to_real :=
begin
  rw [← ennreal.of_real_le_of_real_iff ennreal.to_real_nonneg, ennreal.of_real_to_real h,
      ← edist_dist],
  exact edist_le f hx hy
end

lemma sub_le (f : α → ℝ) {s : set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s)
  (h : evariation_on f s ≠ ∞):
  f x - f y ≤ (evariation_on f s).to_real :=
begin
  apply (le_abs_self _).trans,
  rw ← real.dist_eq,
  exact dist_le f hx hy h
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
      { have : i + 1 ≤ n, by linarith,
        simp only [hi.le, this, if_true],
        exact hu (nat.le_succ i) },
      { simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero,
                  if_false, h], },
      { have A : ¬(i ≤ n), by linarith,
        have B : ¬(i + 1 ≤ n), by linarith,
        simp [A, B] } },
    refine ⟨v, n+2, hv, vs, (mem_image _ _ _).2 ⟨n+1, _, _⟩, _⟩,
    { rw mem_Iio, exact nat.lt_succ_self (n+1) },
    { have : ¬(n + 1 ≤ n), by linarith,
      simp only [this, ite_eq_right_iff, is_empty.forall_iff] },
    { calc
        ∑ i in finset.range n, edist (f (u (i+1))) (f (u i))
        = ∑ i in finset.range n, edist (f (v (i+1))) (f (v i)) :
        begin
          apply finset.sum_congr rfl (λ i hi, _),
          simp only [finset.mem_range] at hi,
          have : i + 1 ≤ n, by linarith,
          dsimp only [v],
          simp only [hi.le, this, if_true],
        end
      ... ≤ ∑ j in finset.range (n + 2), edist (f (v (j+1))) (f (v j)) :
        finset.sum_le_sum_of_subset (finset.range_mono (by linarith)) } },
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
    dsimp [w],
    rcases lt_trichotomy (i + 1) N with hi|hi|hi,
    { have : i < N, by linarith,
      simp [hi, this],
      exact hu (nat.le_succ _) },
    { have A : i < N, by linarith,
      have B : ¬(i + 1 < N), by linarith,
      rw [if_pos A, if_neg B, if_pos hi],
      have T := nat.find_min exists_N A,
      push_neg at T,
      exact T (A.le.trans hN.1) },
    { have A : ¬(i < N), by linarith,
      have B : ¬(i + 1 < N), by linarith,
      have C : ¬(i + 1 = N), by linarith,
      have D : i + 1 - 1 = i := nat.pred_succ i,
      rw [if_neg A, if_neg B, if_neg C, D],
      split_ifs,
      { exact hN.2.le.trans (hu (by linarith)) },
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
          have B : i < N, by linarith,
          rw [if_pos A, if_pos B] },
        { have A : N - 1 + 1 = N, from nat.succ_pred_eq_of_pos Npos,
          have : finset.Ico (N - 1) N = {N - 1}, by rw [← nat.Ico_succ_singleton, A],
          simp only [this, A, finset.sum_singleton] },
        { apply finset.sum_congr rfl (λ i hi, _),
          simp only [finset.mem_Ico] at hi,
          dsimp only [w],
          have A : ¬(1 + i + 1 < N), by linarith,
          have B : ¬(1 + i + 1 = N), by linarith,
          have C : ¬(1 + i < N), by linarith,
          have D : ¬(1 + i = N), by linarith,
          rw [if_neg A, if_neg B, if_neg C, if_neg D],
          congr' 3;
          { rw eq_tsub_iff_add_eq_of_le, { abel }, { linarith } } }
      end
    ... = ∑ i in finset.Ico 0 (N-1), edist (f (w (i + 1))) (f (w i)) +
          edist (f (w (N + 1))) (f (w (N - 1))) +
          ∑ i in finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w (i))) :
      begin
        congr' 1, congr' 1,
        { dsimp only [w],
          have A : ¬(N + 1 < N), by linarith,
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
        have A : N - 1 + 1 = N, from nat.succ_pred_eq_of_pos Npos,
        have B : N - 1 + 1 < N + 1, by linarith,
        have C : N - 1 < N + 1, by linarith,
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

/-- The variation on the union of two sets `s` and `t`, with `s` to the left of `t`, bounds the sum
of the variations along `s` and `t`. -/
lemma add_le_union (f : α → E) {s t : set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
  evariation_on f s + evariation_on f t ≤ evariation_on f (s ∪ t) :=
begin
  by_cases hs : s = ∅,
  { simp [hs] },
  haveI : nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s},
    from nonempty_monotone_mem (ne_empty_iff_nonempty.1 hs),
  by_cases ht : t = ∅,
  { simp [ht] },
  haveI : nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ t},
    from nonempty_monotone_mem (ne_empty_iff_nonempty.1 ht),
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
lemma union (f : α → E) {s t : set α} {x : α}
  (hs : s ⊆ Iic x) (h's : x ∈ s) (ht : t ⊆ Ici x) (h't : x ∈ t) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=
begin
  classical,
  apply le_antisymm _ (evariation_on.add_le_union f (λ a ha b hb, le_trans (hs ha) (ht hb))),
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ust⟩⟩,
  obtain ⟨v, m, hv, vst, xv, huv⟩ : ∃ (v : ℕ → α) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s ∪ t) ∧
    x ∈ v '' (Iio m) ∧ ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤
                        ∑ j in finset.range m, edist (f (v (j+1))) (f (v j)),
    from evariation_on.add_point f (mem_union_left t h's) u hu ust n,
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
        { exact ht h } },
      rw this,
      exact h's },
    { apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) (λ i hi, _),
      rcases vst i with h|h, swap, { exact h },
      have : v i = x,
      { apply le_antisymm,
        { exact hs h },
        { rw ← Nx, exact hv hi.1 },
          },
      rw this,
      exact h't }
  end
end

lemma Icc_add_Icc (f : α → E) {s : set α} {a b c : α}
  (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
  evariation_on f (s ∩ Icc a b) + evariation_on f (s ∩ Icc b c) = evariation_on f (s ∩ Icc a c) :=
begin
  have A : s ∩ Icc a b ⊆ Iic b, from (inter_subset_right _ _).trans (Icc_subset_Iic_self),
  have B : s ∩ Icc b c ⊆ Ici b, from (inter_subset_right _ _).trans (Icc_subset_Ici_self),
  rw [← evariation_on.union f A ⟨hb, hab, le_rfl⟩ B ⟨hb, le_rfl, hbc⟩, ← inter_union_distrib_left,
      Icc_union_Icc_eq_Icc hab hbc]
end

lemma exists_monotone_on_sub_monotone_on {f : α → ℝ} {s : set α}
  (h : ∀ a b, a ∈ s → b ∈ s → a ≤ b → evariation_on f (s ∩ (Icc a b)) ≠ ∞) :
  ∃ (p q : α → ℝ), monotone_on p s ∧ monotone_on q s ∧ ∀ x, f x = p x - q x :=
begin
  rcases eq_empty_or_nonempty s with rfl|hs,
  { exact ⟨f, 0, subsingleton_empty.monotone_on _, subsingleton_empty.monotone_on _,
            λ x, by simp only [pi.zero_apply, tsub_zero]⟩ },
  rcases hs with ⟨c, cs⟩,
  let p := λ x, if c ≤ x then (evariation_on f (s ∩ Icc c x)).to_real
    else -(evariation_on f (s ∩ Icc x c)).to_real,
  have hp : monotone_on p s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : evariation_on f (s ∩ Icc c x) + evariation_on f (s ∩ Icc x y)
        = evariation_on f (s ∩ Icc c y), from Icc_add_Icc f hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs hcx) (h x y xs ys hxy)],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { exact (neg_nonpos.2 ennreal.to_real_nonneg).trans ennreal.to_real_nonneg },
    { simp only [neg_le_neg_iff],
      have : evariation_on f (s ∩ Icc x y) + evariation_on f (s ∩ Icc y c)
        = evariation_on f (s ∩ Icc x c), from Icc_add_Icc f hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys hxy) (h y c ys cs (not_le.1 hcy).le), add_comm],
      exact le_add_of_le_of_nonneg le_rfl ennreal.to_real_nonneg } },
  have hq : monotone_on (λ x, p x - f x) s,
  { assume x xs y ys hxy,
    dsimp only [p],
    split_ifs with hcx hcy hcy,
    { have : evariation_on f (s ∩ Icc c x) + evariation_on f (s ∩ Icc x y)
        = evariation_on f (s ∩ Icc c y), from Icc_add_Icc f hcx hxy xs,
      rw [← this, ennreal.to_real_add (h c x cs xs hcx) (h x y xs ys hxy)],
      suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x y)).to_real, by linarith,
      exact sub_le f ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ (h x y xs ys hxy) },
    { exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim },
    { suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x c)).to_real
        + (evariation_on f (s ∩ Icc c y)).to_real, by linarith,
      rw [← ennreal.to_real_add (h x c xs cs (not_le.1 hcx).le) (h c y cs ys hcy),
          Icc_add_Icc f (not_le.1 hcx).le hcy cs],
      exact sub_le f ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ (h x y xs ys hxy) },
    { have : evariation_on f (s ∩ Icc x y) + evariation_on f (s ∩ Icc y c)
        = evariation_on f (s ∩ Icc x c), from Icc_add_Icc f hxy (not_le.1 hcy).le ys,
      rw [← this, ennreal.to_real_add (h x y xs ys hxy) (h y c ys cs (not_le.1 hcy).le)],
      suffices : f y - f x ≤ (evariation_on f (s ∩ Icc x y)).to_real, by linarith,
      exact sub_le f ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩ (h x y xs ys hxy) } },
  refine ⟨p, λ x, p x - f x, hp, hq, λ x, by abel⟩,
end

lemma exists_monotone_sub_monotone' (f : α → ℝ) {s : set α} {a b : α}
  (h : evariation_on f s ≠ ∞) (as : a ∈ s) (bs : b ∈ s) (hs : s ⊆ Icc a b) :
  ∃ (p q : α → ℝ), monotone p ∧ monotone q ∧ eq_on f (p - q) s :=
begin
  obtain ⟨p', q', hp', hq', H⟩ :
    ∃ (p' q' : α → ℝ), monotone_on p' s ∧ monotone_on q' s ∧ ∀ x, f x = p' x - q' x,
  { apply exists_monotone_on_sub_monotone_on,
    assume c d hc hd hcd,
    apply ne_of_lt (lt_of_le_of_lt _ h.lt_top),
    exact evariation_on.mono _ (inter_subset_left _ _) },
  obtain ⟨p, hp, h'p⟩ : ∃ p, monotone p ∧ eq_on p' p s, from hp'.exists_monotone_extension as bs hs,
  obtain ⟨q, hq, h'q⟩ : ∃ q, monotone q ∧ eq_on q' q s, from hq'.exists_monotone_extension as bs hs,
  exact ⟨p, q, hp, hq, λ x hx, by simp [H x, h'q hx, h'p hx]⟩,
end

lemma exists_monotone_sub_monotone (f : α → ℝ)
  (h : ∀ a b, a ≤ b → evariation_on f (Icc a b) ≠ ∞) :
  ∃ (p q : α → ℝ), monotone p ∧ monotone q ∧ ∀ x, f x = p x - q x :=
by simpa [monotone_on_univ] using
  @exists_monotone_on_sub_monotone_on _ _ f univ (λ a b ha hb hab, by simpa using h a b hab)

end evariation_on

lemma lipschitz_on.evariation_on_le {f : ℝ → E} {s : set ℝ} {C : ℝ≥0}
  (h : lipschitz_on_with C f s) (a b : ℝ) :
  evariation_on f (s ∩ Icc a b) ≤ C * ennreal.of_real (b - a) :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, us⟩⟩,
  calc
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i))
      ≤ ∑ i in finset.range n, C * ennreal.of_real (u (i + 1) - u i) :
    begin
      apply finset.sum_le_sum (λ i hi, _),
      simp only [finset.mem_range] at hi,
      convert h (us (i+1)).1 (us i).1,
      rw [edist_dist, real.dist_eq, abs_of_nonneg (sub_nonneg_of_le (hu (nat.le_succ _)))],
    end
  ... = C * ennreal.of_real (∑ i in finset.range n, (u (i + 1) - u i)) :
    begin
      rw [← finset.mul_sum, ennreal.of_real_sum_of_nonneg],
      assume i hi,
      exact sub_nonneg_of_le (hu (nat.le_succ _))
    end
  ... = C * ennreal.of_real (u n - u 0) : by rw finset.sum_range_sub
  ... ≤ C * ennreal.of_real (b - a) :
    begin
      refine mul_le_mul_left' _ _,
      apply ennreal.of_real_le_of_real,
      exact sub_le_sub (us n).2.2 (us 0).2.1,
    end
end


#exit


/-- If a function is monotone on a set `s`, then it admits a monotone extension to the whole space
provided `s` has a lower point `a` and an upper point `b`. -/
lemma monotone_on.exists_monotone_extension {α β : Type*}
  [linear_order α] [conditionally_complete_linear_order β]
  {f : α → β} {s : set α} (h : monotone_on f s) {a b : α}
  (as : a ∈ s) (bs : b ∈ s) (hab : s ⊆ Icc a b) :
  ∃ g : α → β, monotone g ∧ eq_on f g s :=
begin
  /- The extension is defined by `f a` to the left of `f a`, and `f b` to the right of `b`, and
  the supremum of the values of `f` to the left of `x` between `a` and -/
  have aleb : a ≤ b := (hab as).2,
  have H : ∀ x ∈ s, f x = Sup (f '' (Icc a x ∩ s)),
  { assume x xs,
    have xmem : x ∈ Icc a x ∩ s := ⟨⟨(hab xs).1, le_rfl⟩, xs⟩,
    have H : ∀ z, z ∈ f '' (Icc a x ∩ s) → z ≤ f x,
    { rintros _ ⟨z, ⟨⟨az, zx⟩, zs⟩, rfl⟩,
      exact h zs xs zx },
    apply le_antisymm,
    { exact le_cSup ⟨f x, H⟩ (mem_image_of_mem _ xmem) },
    { exact cSup_le (nonempty_image_iff.2 ⟨x, xmem⟩) H } },
  let g := λ x, if x ≤ a then f a else if b ≤ x then f b else Sup (f '' (Icc a x ∩ s)),
  have hfg : eq_on f g s,
  { assume x xs,
    dsimp only [g],
    by_cases hxa : x ≤ a,
    { have : x = a, from le_antisymm hxa (hab xs).1,
      simp only [if_true, this, le_refl] },
    by_cases hbx : b ≤ x,
    { simp only [if_true, hxa, hbx, if_false],
      have : x = b, from le_antisymm (hab xs).2 hbx,
      simp only [this] },
    rw [if_neg hxa, if_neg hbx],
    exact H x xs,  },
  have M1 : monotone_on g (Iic a),
  { rintros x (hx : x ≤ a) y (hy : y ≤ a) hxy,
    dsimp only [g],
    simp only [hx, hy, if_true] },
  have g_eq : ∀ x ∈ Icc a b, g x = Sup (f '' (Icc a x ∩ s)),
  { rintros x ⟨ax, xb⟩,
    dsimp only [g],
    by_cases hxa : x ≤ a,
    { have : x = a := le_antisymm hxa ax,
      simp_rw [hxa, if_true, H a as, this] },
    by_cases hbx : b ≤ x,
    { have : x = b := le_antisymm xb hbx,
      simp_rw [hxa, if_false, hbx, if_true, H b bs, this] },
    simp only [hxa, hbx, if_false] },
  have M2 : monotone_on g (Icc a b),
  { rintros x ⟨ax, xb⟩ y ⟨ay, yb⟩ hxy,
    rw [g_eq x ⟨ax, xb⟩, g_eq y ⟨ay, yb⟩],
    apply cSup_le_cSup,
    { refine ⟨f b, _⟩,
      rintros _ ⟨z, ⟨⟨az, zy⟩, zs⟩, rfl⟩,
      exact h zs bs (zy.trans yb) },
    { exact ⟨f a, mem_image_of_mem _ ⟨⟨le_rfl, ax⟩, as⟩⟩ },
    { apply image_subset,
      apply inter_subset_inter_left,
      exact Icc_subset_Icc le_rfl hxy } },
  have M3 : monotone_on g (Iic b),
  { have := M1.union' M2 subset.rfl Icc_subset_Ici_self le_rfl ⟨le_rfl, aleb⟩,
    rwa Iic_union_Icc_eq_Iic aleb at this },
  have M4 : monotone_on g (Ici b),
  { rintros x (hx : b ≤ x) y (hy : b ≤ y) hxy,
    dsimp only [g],
    simp only [hx, hy, if_true],
    by_cases hxa : x ≤ a,
    { have : b = a, from le_antisymm (hx.trans hxa) aleb,
      simp only [this, if_t_t] },
    { have : ¬(y ≤ a) := λ hy, hxa (hxy.trans hy),
      simp only [hxa, this] } },
  refine ⟨g, M3.Iic_union_Ici M4, hfg⟩,
end

#exit


/- lemma ae_differentiable_at_Icc (f : ℝ → ℝ) {x y : ℝ} (h : evariation_on f (Icc x y) ≠ ∞) :
  ∀ᵐ x ∂(volume.restrict (Icc x y)), differentiable_at ℝ f x :=
-/




variables {f : ℝ → ℝ} {C : ℝ≥0} (hf : lipschitz_with C f)
include hf

lemma my_bound (n : ℕ) {u : ℕ → ℝ} (hu : monotone u) (h0 : u 0 = 0) :
  ∑ i in finset.range n, |f (u (i+1)) - f (u i)| ≤ C * u n :=
calc
∑ i in finset.range n, |f (u (i+1)) - f (u i)|
≤ ∑ i in finset.range n, C * |u (i+1) - u i| :
begin
  apply finset.sum_le_sum (λ i hi, _),
  simpa [← real.dist_eq] using hf.dist_le_mul _ _,
end
... = ∑ i in finset.range n, C * (u (i+1) - u i) :
begin
  congr' with i,
  rw abs_of_nonneg,
  rw sub_nonneg,
  exact hu (nat.le_succ _),
end
... = C * u n : by rw [← finset.mul_sum, finset.sum_range_sub, h0, sub_zero]





lemma lemma monotone_on_extend_right : monotone_on (extend_right f) (Ici (0 : ℝ)) :=
begin
  rintros x (hx : 0 ≤ x) y hy hxy,
  apply cSup_le,
  { rw range_nonempty_iff_nonempty,
    let u : {u : ℕ → ℝ // monotone u ∧ u 0 = 0 ∧ u 1 = x},
    { refine ⟨λ i, if i = 0 then 0 else x, _, by simp, by simp⟩,
      refine monotone_nat_of_le_succ (λ i, _),
      by_cases hi : i = 0; simp [hi, hx] },
    exact ⟨⟨1, u⟩⟩ },
  rintros _ ⟨⟨n, ⟨u, hu, u0, un⟩⟩, rfl⟩,
  dsimp,
  let v : {u : ℕ → ℝ // monotone u ∧ u 0 = 0 ∧ u (n+1) = y} :=
  begin
    refine ⟨λ i, if i ≤ n then u i else y, _, by simp [u0], by simp⟩,
    apply monotone_nat_of_le_succ (λ i, _),
    rcases lt_trichotomy i n with hi|rfl|hi,
    { have : i + 1 ≤ n, by linarith,
      simp only [this, hi.le, if_true],
      exact hu (nat.le_succ _) },
    { simp only [un, hxy, le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero,
                 if_false] },
    { have A : ¬(i ≤ n), by linarith,
      have B : ¬(i + 1 ≤ n), by linarith,
      simp [A, B] }
  end,
  have I : ∑ i in finset.range n, |f (u (i + 1)) - f (u i)| ≤
    ∑ i in finset.range (n + 1), |f ((v : ℕ → ℝ) (i+1)) - f ((v : ℕ → ℝ) i)|, calc
        ∑ i in finset.range n, |f (u (i + 1)) - f (u i)|
      = ∑ i in finset.range n, |f ((v : ℕ → ℝ) (i+1)) - f ((v : ℕ → ℝ) i)| :
    begin
      apply finset.sum_congr rfl (λ i hi, _),
      simp only [finset.mem_range] at hi,
      have : i + 1 ≤ n, by linarith,
      simp only [this, hi.le, if_true, subtype.coe_mk],
    end
  ... ≤ ∑ i in finset.range (n + 1), |f ((v : ℕ → ℝ) (i+1)) - f ((v : ℕ → ℝ) i)| :
    begin
      refine finset.sum_le_sum_of_subset_of_nonneg _ (λ i hi h'i, abs_nonneg _),
      { exact finset.range_subset.2 (nat.le_succ _) },
    end,
  let R := range (λ (p : Σ (n : ℕ), {u : ℕ → ℝ // monotone u ∧ u 0 = 0 ∧ u n = y}),
    ∑ i in finset.range p.1, |f ((p.2 : ℕ → ℝ) (i+1)) - f ((p.2 : ℕ → ℝ) i)|),
  have B : bdd_above R,
  { refine ⟨C * y, _⟩,
    rintros _ ⟨⟨m, ⟨w, hw, w0, wm⟩⟩, rfl⟩,
    dsimp,
    rw ← wm,
    exact my_bound hf m hw w0 },
  have M : ∑ i in finset.range (n+1), |f ((v : ℕ → ℝ) (i+1)) - f ((v : ℕ → ℝ) i)| ∈ R :=
    mem_range_self (⟨n+1, v⟩ : Σ (n : ℕ), {u : ℕ → ℝ // monotone u ∧ u 0 = 0 ∧ u n = y}),
  exact le_cSup_of_le B M I,
end
