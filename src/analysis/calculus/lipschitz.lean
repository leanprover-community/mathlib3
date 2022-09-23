/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.deriv

open_locale big_operators nnreal ennreal
open set

variables {E : Type*} [pseudo_emetric_space E]

/-- The (extended real valued) variation of a function `f` on a set `s` is the supremum of the
sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing sequences `u` in `s`. -/
noncomputable def evariation_on (f : ℝ → E) (s : set ℝ) : ℝ≥0∞ :=
⨆ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
  ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))

namespace evariation_on

lemma nonempty_monotone_mem {s : set ℝ} (hs : s.nonempty) :
  nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s} :=
begin
  obtain ⟨x, hx⟩ := hs,
  exact ⟨⟨λ i, x, λ i j hij, le_rfl, λ i, hx⟩⟩,
end

lemma sum_le
  (f : ℝ → E) {s : set ℝ} (n : ℕ) {u : ℕ → ℝ} (hu : monotone u) (us : ∀ i, u i ∈ s) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=
begin
  let p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, us⟩),
  change ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))
    ≤ evariation_on f s,
  exact le_supr (λ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
    ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))) _,
end

lemma sum_le_of_monotone_on_Iic
  (f : ℝ → E) {s : set ℝ} {n : ℕ} {u : ℕ → ℝ} (hu : monotone_on u (Iic n))
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
  (f : ℝ → E) {s : set ℝ} (m n : ℕ) (u : ℕ → ℝ) (hu : monotone_on u (Icc m n))
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
      = ∑ i in finset.range (n - m), edist (f (u (m + i + 1))) (f (u (m + i))) : sorry
  ... = ∑ i in finset.range (n - m), edist (f (v (i + 1))) (f (v i)) : sorry
  ... ≤ evariation_on f s : sum_le_of_monotone_on_Iic f hv vs,
end

#exit

lemma mono (f : ℝ → E) {s t : set ℝ} (hst : t ⊆ s) :
  evariation_on f t ≤ evariation_on f s :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  exact sum_le f n u hu (λ i, hst (ut i)),
end

@[simp] protected lemma subsingleton (f : ℝ → E) {s : set ℝ} (hs : s.subsingleton) :
  evariation_on f s = 0 :=
begin
  apply le_antisymm _ (zero_le _),
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  have : ∀ i, u i = u 0, from λ i, hs (ut _) (ut _),
  simp [subtype.coe_mk, le_zero_iff, finset.sum_eq_zero_iff, finset.mem_range, this],
end

/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
lemma add_point (f : ℝ → E) {s : set ℝ} {x : ℝ} (hx : x ∈ s)
  (u : ℕ → ℝ) (hu : monotone u) (us : ∀ i, u i ∈ s) (n : ℕ) :
  ∃ (v : ℕ → ℝ) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s) ∧ x ∈ v '' (Iio m) ∧
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
  let w : ℕ → ℝ := λ i, if i < N then u i else if i = N then x else u (i - 1),
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
        simp only [← Npos, nat.not_lt_zero, nat.add_succ_sub_one, add_zero, if_false, add_eq_zero_iff,
          nat.one_ne_zero, false_and, nat.succ_add_sub_one, zero_add],
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
lemma add_le_union (f : ℝ → E) {s t : set ℝ} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
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
  ... ≤ evariation_on f (s ∪ t) : sum_le f _ _ hw wst
end

lemma evariation_on.union (f : ℝ → E) {s t : set ℝ} {x : ℝ}
  (hs : s ⊆ Iic x) (h's : x ∈ s) (ht : t ⊆ Ici x) (h't : x ∈ t) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=
begin
  classical,
  apply le_antisymm _ (evariation_on.add_le_union f (λ a ha b hb, le_trans (hs ha) (ht hb))),
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ust⟩⟩,
  obtain ⟨v, m, hv, vst, xv, huv⟩ : ∃ (v : ℕ → ℝ) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s ∪ t) ∧
    x ∈ v '' (Iio m) ∧ ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤
                        ∑ j in finset.range m, edist (f (v (j+1))) (f (v j)),
    from evariation_on.add_point f (mem_union_left t h's) u hu ust n,
  apply huv.trans,
end










#exit

def has_bounded_variation_on (f : ℝ → E) (s : set ℝ) :=
  bdd_above (range (λ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
    ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))))

lemma has_bounded_variation_on.mono (f : ℝ → E) {s t : set ℝ} (hst : t ⊆ s)
  (h : has_bounded_variation_on f s) : has_bounded_variation_on f t :=
begin
  rcases h with ⟨C, hC⟩,
  refine ⟨C, _⟩,
  rintros _ ⟨⟨n, ⟨u, hu, ut⟩⟩, rfl⟩,
  apply hC,
  have us : ∀ i, u i ∈ s := λ i, (hst (ut i)),
  exact mem_range_self (⟨n, ⟨u, hu, us⟩⟩ : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s})
end

noncomputable def variation_on (f : ℝ → E) (s : set ℝ) :=
⨆ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
  ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))

lemma has_bounded_variation.le_variation_on
  {f : ℝ → E} {s : set ℝ} (hf : has_bounded_variation_on f s)
  (n : ℕ) (u : ℕ → ℝ) (hu : monotone u) (us : ∀ i, u i ∈ s) :
  ∑ i in finset.range n, dist (f (u (i+1))) (f (u i)) ≤ variation_on f s :=
begin
  let p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, us⟩),
  change ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))
    ≤ variation_on f s,
  exact le_csupr hf _,
end


#exit

@[simp] lemma variation_on_empty (f : ℝ → E) :
  variation_on f ∅ = 0 :=
begin
  rw [variation_on, supr],
  convert real.Sup_empty,
  simp,
end

lemma nonempty_monotone_mem {s : set ℝ} (hs : s.nonempty) :
  nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s} :=
begin
  obtain ⟨x, hx⟩ := hs,
  exact ⟨⟨λ i, x, λ i j hij, le_rfl, λ i, hx⟩⟩,
end

lemma variation_on_nonneg (f : ℝ → E) (s : set ℝ) :
  0 ≤ variation_on f s :=
begin
  by_cases h : bdd_above (range (λ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
    ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i)))),
  swap,
  { apply ge_of_eq, exact real.supr_of_not_bdd_above h },
  by_cases h' : s = ∅,
  { rw [h', variation_on_empty] },
  apply le_cSup h,
  obtain ⟨x, hx⟩ : s.nonempty, from ne_empty_iff_nonempty.1 h',
  let p : ℕ × {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s} := (0, ⟨λ i, x, λ i j hij, le_rfl, λ i, hx⟩),
  have : ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i)) = 0,
    by simp [p],
  rw ← this,
  exact mem_range_self p,
end

lemma variation_on.mono {f : ℝ → E} {s t : set ℝ} (hf : has_bounded_variation_on f s)
  (hst : t ⊆ s) :
  variation_on f t ≤ variation_on f s :=
begin
  rcases eq_empty_or_nonempty t with rfl|ht,
  { simpa using variation_on_nonneg f s },
  haveI := nonempty_monotone_mem ht,
  apply csupr_le,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  let p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, λ i, hst (ut i)⟩),
  change ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))
    ≤ variation_on f s,
  apply le_csupr hf,
end

lemma variation_on.union (f : ℝ → E) (s t : set ℝ) (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
  variation_on f (s ∪ t) ≤ variation_on f s + variation_on f t :=
begin
  by_cases h : s = ∅, { simp [h] },
  have : (s ∪ t).nonempty := sorry,
  haveI := nonempty_monotone_mem this,
  apply csupr_le,
  rintros ⟨n, ⟨u, hu, ust⟩⟩,
  by_cases H : ∀ i, u i ∈ s,
  { let p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, H⟩),
    change ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))
      ≤ variation_on f s + variation_on f t,


  },
end


#exit


noncomputable def extend_right (f : ℝ → ℝ) (x : ℝ) : ℝ :=
⨆ (p : Σ (n : ℕ), {u : ℕ → ℝ // monotone u ∧ u 0 = 0 ∧ u n = x}),
  ∑ i in finset.range p.1, |f ((p.2 : ℕ → ℝ) (i+1)) - f ((p.2 : ℕ → ℝ) i)|

lemma extend_right_non_empty (f : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
  nonempty (Σ (n : ℕ), {u // monotone u ∧ u 0 = 0 ∧ u n = x}) :=
begin
  let u : {u : ℕ → ℝ // monotone u ∧ u 0 = 0 ∧ u 1 = x},
  { refine ⟨λ i, if i = 0 then 0 else x, _, by simp, by simp⟩,
    refine monotone_nat_of_le_succ (λ i, _),
    by_cases hi : i = 0; simp [hi, hx] },
  exact ⟨⟨1, u⟩⟩
end



lemma extend_right_zero (f : ℝ → ℝ) : extend_right f 0 = 0 :=
begin
  apply le_antisymm,
  haveI := extend_right_non_empty f (le_refl (0 : ℝ)),
  apply csupr_le,
  rintros ⟨n, ⟨u, hu, u0, un⟩⟩,


end

#exit


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
