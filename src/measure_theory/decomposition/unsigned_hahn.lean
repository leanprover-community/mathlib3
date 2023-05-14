/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import measure_theory.measure.measure_space

/-!
# Unsigned Hahn decomposition theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the unsigned version of the Hahn decomposition theorem.

## Main statements

* `hahn_decomposition` : Given two finite measures `μ` and `ν`, there exists a measurable set `s`
    such that any measurable set `t` included in `s` satisfies `ν t ≤ μ t`, and any
    measurable set `u` included in the complement of `s` satisfies `μ u ≤ ν u`.

## Tags

Hahn decomposition
-/

open set filter
open_locale classical topology ennreal

namespace measure_theory

variables {α : Type*} [measurable_space α] {μ ν : measure α}

/-- **Hahn decomposition theorem** -/
lemma hahn_decomposition [is_finite_measure μ] [is_finite_measure ν] :
  ∃s, measurable_set s ∧
    (∀t, measurable_set t → t ⊆ s → ν t ≤ μ t) ∧
    (∀t, measurable_set t → t ⊆ sᶜ → μ t ≤ ν t) :=
begin
  let d : set α → ℝ := λs, ((μ s).to_nnreal : ℝ) - (ν s).to_nnreal,
  let c : set ℝ := d '' {s | measurable_set s },
  let γ : ℝ := Sup c,

  have hμ : ∀ s, μ s ≠ ∞ := measure_ne_top μ,
  have hν : ∀ s, ν s ≠ ∞ := measure_ne_top ν,
  have to_nnreal_μ : ∀s, ((μ s).to_nnreal : ℝ≥0∞) = μ s :=
    (assume s, ennreal.coe_to_nnreal $ hμ _),
  have to_nnreal_ν : ∀s, ((ν s).to_nnreal : ℝ≥0∞) = ν s :=
    (assume s, ennreal.coe_to_nnreal $ hν _),

  have d_empty : d ∅ = 0,
  { change _ - _ = _, rw [measure_empty, measure_empty, sub_self] },

  have d_split : ∀s t, measurable_set s → measurable_set t →
    d s = d (s \ t) + d (s ∩ t),
  { assume s t hs ht,
    simp only [d],
    rw [← measure_inter_add_diff s ht, ← measure_inter_add_diff s ht,
      ennreal.to_nnreal_add (hμ _) (hμ _), ennreal.to_nnreal_add (hν _) (hν _),
      nnreal.coe_add, nnreal.coe_add],
    simp only [sub_eq_add_neg, neg_add],
    abel },

  have d_Union : ∀(s : ℕ → set α), monotone s →
    tendsto (λn, d (s n)) at_top (𝓝 (d (⋃n, s n))),
  { assume s hm,
    refine tendsto.sub _ _;
      refine (nnreal.tendsto_coe.2 $ (ennreal.tendsto_to_nnreal _).comp $
        tendsto_measure_Union hm),
    exact hμ _,
    exact hν _ },

  have d_Inter : ∀(s : ℕ → set α), (∀n, measurable_set (s n)) → (∀n m, n ≤ m → s m ⊆ s n) →
    tendsto (λn, d (s n)) at_top (𝓝 (d (⋂n, s n))),
  { assume s hs hm,
    refine tendsto.sub _ _;
      refine (nnreal.tendsto_coe.2 $ (ennreal.tendsto_to_nnreal $ _).comp $
        tendsto_measure_Inter hs hm _),
    exacts [hμ _, ⟨0, hμ _⟩, hν _, ⟨0, hν _⟩] },

  have bdd_c : bdd_above c,
  { use (μ univ).to_nnreal,
    rintros r ⟨s, hs, rfl⟩,
    refine le_trans (sub_le_self _ $ nnreal.coe_nonneg _) _,
    rw [nnreal.coe_le_coe, ← ennreal.coe_le_coe, to_nnreal_μ, to_nnreal_μ],
    exact measure_mono (subset_univ _) },

  have c_nonempty : c.nonempty := nonempty.image _ ⟨_, measurable_set.empty⟩,

  have d_le_γ : ∀s, measurable_set s → d s ≤ γ := assume s hs, le_cSup bdd_c ⟨s, hs, rfl⟩,

  have : ∀n:ℕ, ∃s : set α, measurable_set s ∧ γ - (1/2)^n < d s,
  { assume n,
    have : γ - (1/2)^n < γ := sub_lt_self γ (pow_pos (half_pos zero_lt_one) n),
    rcases exists_lt_of_lt_cSup c_nonempty this with ⟨r, ⟨s, hs, rfl⟩, hlt⟩,
    exact ⟨s, hs, hlt⟩ },
  rcases classical.axiom_of_choice this with ⟨e, he⟩,
  change ℕ → set α at e,
  have he₁ : ∀n, measurable_set (e n) := assume n, (he n).1,
  have he₂ : ∀n, γ - (1/2)^n < d (e n) := assume n, (he n).2,

  let f : ℕ → ℕ → set α := λn m, (finset.Ico n (m + 1)).inf e,

  have hf : ∀n m, measurable_set (f n m),
  { assume n m,
    simp only [f, finset.inf_eq_infi],
    exact measurable_set.bInter (to_countable _) (assume i _, he₁ _) },

  have f_subset_f : ∀{a b c d}, a ≤ b → c ≤ d → f a d ⊆ f b c,
  { assume a b c d hab hcd,
    dsimp only [f],
    rw [finset.inf_eq_infi, finset.inf_eq_infi],
    exact bInter_subset_bInter_left (finset.Ico_subset_Ico hab $ nat.succ_le_succ hcd) },

  have f_succ : ∀n m, n ≤ m → f n (m + 1) = f n m ∩ e (m + 1),
  { assume n m hnm,
    have : n ≤ m + 1 := le_of_lt (nat.succ_le_succ hnm),
    simp only [f],
    rw [nat.Ico_succ_right_eq_insert_Ico this, finset.inf_insert, set.inter_comm],
    refl },

  have le_d_f : ∀n m, m ≤ n → γ - 2 * ((1 / 2) ^ m) + (1 / 2) ^ n ≤ d (f m n),
  { assume n m h,
    refine nat.le_induction _ _ n h,
    { have := he₂ m,
      simp only [f],
      rw [nat.Ico_succ_singleton, finset.inf_singleton],
      linarith },
    { assume n (hmn : m ≤ n) ih,
      have : γ + (γ - 2 * (1 / 2)^m + (1 / 2) ^ (n + 1)) ≤ γ + d (f m (n + 1)),
      { calc γ + (γ - 2 * (1 / 2)^m + (1 / 2) ^ (n+1)) ≤
            γ + (γ - 2 * (1 / 2)^m + ((1 / 2) ^ n - (1/2)^(n+1))) :
          begin
            refine add_le_add_left (add_le_add_left _ _) γ,
            simp only [pow_add, pow_one, le_sub_iff_add_le],
            linarith
          end
          ... = (γ - (1 / 2)^(n+1)) + (γ - 2 * (1 / 2)^m + (1 / 2)^n) :
            by simp only [sub_eq_add_neg]; abel
          ... ≤ d (e (n + 1)) + d (f m n) : add_le_add (le_of_lt $ he₂ _) ih
          ... ≤ d (e (n + 1)) + d (f m n \ e (n + 1)) + d (f m (n + 1)) :
            by rw [f_succ _ _ hmn, d_split (f m n) (e (n + 1)) (hf _ _) (he₁ _), add_assoc]
          ... = d (e (n + 1) ∪ f m n) + d (f m (n + 1)) :
            begin
              rw [d_split (e (n + 1) ∪ f m n) (e (n + 1)),
                union_diff_left, union_inter_cancel_left],
              abel,
              exact (he₁ _).union (hf _ _),
              exact (he₁ _)
            end
          ... ≤ γ + d (f m (n + 1)) :
            add_le_add_right (d_le_γ _ $ (he₁ _).union (hf _ _)) _ },
      exact (add_le_add_iff_left γ).1 this } },

  let s := ⋃ m, ⋂n, f m n,
  have γ_le_d_s : γ ≤ d s,
  { have hγ : tendsto (λm:ℕ, γ - 2 * (1/2)^m) at_top (𝓝 γ),
    { suffices : tendsto (λm:ℕ, γ - 2 * (1/2)^m) at_top (𝓝 (γ - 2 * 0)),
      { simpa only [mul_zero, tsub_zero] },
      exact (tendsto_const_nhds.sub $ tendsto_const_nhds.mul $
        tendsto_pow_at_top_nhds_0_of_lt_1
          (le_of_lt $ half_pos $ zero_lt_one) (half_lt_self zero_lt_one)) },
    have hd : tendsto (λm, d (⋂n, f m n)) at_top (𝓝 (d (⋃ m, ⋂ n, f m n))),
    { refine d_Union _ _,
      exact assume n m hnm, subset_Inter
        (assume i, subset.trans (Inter_subset (f n) i) $ f_subset_f hnm $ le_rfl) },
    refine le_of_tendsto_of_tendsto' hγ hd (assume m, _),
    have : tendsto (λn, d (f m n)) at_top (𝓝 (d (⋂ n, f m n))),
    { refine d_Inter _ _ _,
      { assume n, exact hf _ _ },
      { assume n m hnm, exact f_subset_f le_rfl hnm } },
    refine ge_of_tendsto this (eventually_at_top.2 ⟨m, assume n hmn, _⟩),
    change γ - 2 * (1 / 2) ^ m ≤ d (f m n),
    refine le_trans _ (le_d_f _ _ hmn),
    exact le_add_of_le_of_nonneg le_rfl (pow_nonneg (le_of_lt $ half_pos $ zero_lt_one) _) },

  have hs : measurable_set s :=
    measurable_set.Union (assume n, measurable_set.Inter (assume m, hf _ _)),
  refine ⟨s, hs, _, _⟩,
  { assume t ht hts,
    have : 0 ≤ d t := ((add_le_add_iff_left γ).1 $
      calc γ + 0 ≤ d s : by rw [add_zero]; exact γ_le_d_s
        ... = d (s \ t) + d t : by rw [d_split _ _ hs ht, inter_eq_self_of_subset_right hts]
        ... ≤ γ + d t : add_le_add (d_le_γ _ (hs.diff ht)) le_rfl),
    rw [← to_nnreal_μ, ← to_nnreal_ν, ennreal.coe_le_coe, ← nnreal.coe_le_coe],
    simpa only [d, le_sub_iff_add_le, zero_add] using this },
  { assume t ht hts,
    have : d t ≤ 0,
    exact ((add_le_add_iff_left γ).1 $
      calc γ + d t ≤ d s + d t : add_le_add γ_le_d_s le_rfl
        ... = d (s ∪ t) :
          by rw [d_split _ _ (hs.union ht) ht, union_diff_right, union_inter_cancel_right,
            (subset_compl_iff_disjoint_left.1 hts).sdiff_eq_left]
        ... ≤ γ + 0 : by rw [add_zero]; exact d_le_γ _ (hs.union ht)),
    rw [← to_nnreal_μ, ← to_nnreal_ν, ennreal.coe_le_coe, ← nnreal.coe_le_coe],
    simpa only [d, sub_le_iff_le_add, zero_add] using this }
end

end measure_theory
