/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.deriv

open_locale big_operators nnreal ennreal
open set

variables {E : Type*} [pseudo_emetric_space E]

lemma nonempty_monotone_mem {s : set ℝ} (hs : s.nonempty) :
  nonempty {u // monotone u ∧ ∀ (i : ℕ), u i ∈ s} :=
begin
  obtain ⟨x, hx⟩ := hs,
  exact ⟨⟨λ i, x, λ i j hij, le_rfl, λ i, hx⟩⟩,
end


noncomputable def evariation_on (f : ℝ → E) (s : set ℝ) : ℝ≥0∞ :=
⨆ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
  ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))

lemma sum_le_evariation_on
  (f : ℝ → E) {s : set ℝ} (n : ℕ) (u : ℕ → ℝ) (hu : monotone u) (us : ∀ i, u i ∈ s) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤ evariation_on f s :=
begin
  let p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, us⟩),
  change ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))
    ≤ evariation_on f s,
  exact le_supr (λ (p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s}),
    ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))) _,
end

lemma sum_le_evariation_on'
  (f : ℝ → E) {s : set ℝ} (n : ℕ) (u : ℕ → ℝ) (hu : monotone_on u (Iic n))
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
  convert sum_le_evariation_on f n v hv vs using 1,
  apply finset.sum_congr rfl (λ i hi, _),
  simp only [finset.mem_range] at hi,
  have : i + 1 ≤ n, by linarith,
  simp only [v],
  simp [this, hi.le],
end

lemma evariation_on.mono (f : ℝ → E) {s t : set ℝ} (hst : t ⊆ s) :
  evariation_on f t ≤ evariation_on f s :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  exact sum_le_evariation_on f n u hu (λ i, hst (ut i)),
end

@[simp] lemma evariation_on.subsingleton (f : ℝ → E) {s : set ℝ} (hs : s.subsingleton) :
  evariation_on f s = 0 :=
begin
  apply le_antisymm _ (zero_le _),
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  have : ∀ i, u i = u 0, from λ i, hs (ut _) (ut _),
  simp [subtype.coe_mk, le_zero_iff, finset.sum_eq_zero_iff, finset.mem_range, this],
end

lemma evariation_on.add_point (f : ℝ → E) {s : set ℝ} {x : ℝ} (hx : x ∈ s)
  (u : ℕ → ℝ) (hu : monotone u) (us : ∀ i, u i ∈ s) (n : ℕ) :
  ∃ (v : ℕ → ℝ) (m : ℕ), monotone v ∧ (∀ i, v i ∈ s) ∧ x ∈ v '' (Iio m) ∧
    ∑ i in finset.range n, edist (f (u (i+1))) (f (u i)) ≤
      ∑ j in finset.range m, edist (f (v (j+1))) (f (v j)) :=
begin
  by_cases h : u n ≤ x,
  {


  }
end

#exit

/-- The variation on the union of two sets `s` and `t`, with `s` to the left of `t`, bounds the sum
of the variations along `s` and `t`. -/
lemma evariation_on.add_le_union (f : ℝ → E) {s t : set ℝ} {x : ℝ}
  (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
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
  ... ≤ evariation_on f (s ∪ t) : sum_le_evariation_on f _ _ hw wst
end

#exit


lemma evariation_on.union (f : ℝ → E) {s t : set ℝ} {x : ℝ}
  (hs : s ⊆ Iic x) (h's : x ∈ s) (ht : t ⊆ Ici x) (h't : x ∈ t) :
  evariation_on f (s ∪ t) = evariation_on f s + evariation_on f t :=
begin
  classical,
  apply le_antisymm,
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ust⟩⟩,
  by_cases H : ∀ i ≤ n, u i ∈ s,
  { apply (sum_le_evariation_on' f n u (hu.monotone_on _) H).trans,
    conv_lhs { rw ← add_zero (evariation_on f s) },
    exact add_le_add le_rfl (zero_le _) },
  push_neg at H,
  let N := nat.find H,
  have hN : N ≤ n ∧ u N ∉ s := nat.find_spec H,
  let w := λ i, if i < N then u i else if i = N then x else u (i-1),
  have ws : ∀ i ≤ N, w i ∈ s,
  { dsimp only [w],
    assume i hi,
    rcases lt_or_eq_of_le hi with h'i|h'i,
    { rw if_pos h'i,
      have T := nat.find_min H h'i,
      push_neg at T,
      exact T (h'i.le.trans hN.1) },
    { have : ¬(i < N), by linarith,
      rw [if_neg this, if_pos h'i],
      exact h's } },
  have wt : ∀ i, N ≤ i → w i ∈ t,
  { dsimp only [w],
    assume i hi,
    have : ¬(i < N), by linarith,
    rw [if_neg this],
    rcases eq_or_lt_of_le hi with h'i|h'i,
    { rw [if_pos h'i.symm], exact h't },
    { rw [if_neg h'i.ne'],
      have : N ≤ i - 1 := nat.le_pred_of_lt h'i,


      }

  },
  have : monotone w,
  { apply monotone_nat_of_le_succ (λ i, _),
    dsimp [w],
    rcases lt_trichotomy (i + 1) N with hi|hi|hi,
    { have : i < N, by linarith,
      simp [hi, this],
      exact hu (nat.le_succ _) },
    { have A : i < N, by linarith,
      have B : ¬(i + 1 < N), by linarith,
      rw [if_pos A, if_neg B, if_pos hi],
      apply hs,
      have T := nat.find_min H A,
      push_neg at T,
      exact T (A.le.trans hN.1) },
    {

    }



  }

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
