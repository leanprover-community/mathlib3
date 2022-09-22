/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.deriv

open_locale big_operators nnreal
open set

variables {E : Type*} [pseudo_metric_space E]

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

@[simp] lemma variation_on_empty (f : ℝ → E) :
  variation_on f ∅ = 0 :=
begin
  rw [variation_on, supr],
  convert real.Sup_empty,
  simp,
end

lemma nonempty_monotone {s : set ℝ} (hs : s.nonempty) :
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
  haveI := nonempty_monotone ht,
  apply csupr_le,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  let p : ℕ × {u : ℕ → ℝ // monotone u ∧ ∀ i, u i ∈ s} := (n, ⟨u, hu, λ i, hst (ut i)⟩),
  change ∑ i in finset.range p.1, dist (f ((p.2 : ℕ → ℝ) (i+1))) (f ((p.2 : ℕ → ℝ) i))
    ≤ variation_on f s,
  apply le_csupr hf,
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
