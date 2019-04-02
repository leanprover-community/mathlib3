/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Hahn decomposition theorem

TODO:
* introduce finite measures (into nnreal)
* show general for signed measures (into ℝ)
-/
import measure_theory.measure_space

local attribute [instance, priority 0] classical.prop_decidable

namespace measure_theory
open set lattice filter

variables {α : Type*} [measurable_space α] {μ ν : measure α}

-- suddenly this is necessary?!
private lemma aux {m : ℕ} {γ d : ℝ} (h : γ - (1 / 2) ^ m < d) :
  γ - 2 * (1 / 2) ^ m + (1 / 2) ^ m ≤ d :=
by linarith

lemma hahn_decomposition (hμ : μ univ < ⊤) (hν : ν univ < ⊤) :
  ∃s, is_measurable s ∧
    (∀t, is_measurable t → t ⊆ s → ν t ≤ μ t) ∧
    (∀t, is_measurable t → t ⊆ - s → μ t ≤ ν t) :=
begin
  let d : set α → ℝ := λs, ((μ s).to_nnreal : ℝ) - (ν s).to_nnreal,
  let c : set ℝ := d '' {s | is_measurable s },
  let γ : ℝ := Sup c,

  have hμ : ∀s, μ s < ⊤ := assume s, lt_of_le_of_lt (measure_mono $ subset_univ _) hμ,
  have hν : ∀s, ν s < ⊤ := assume s, lt_of_le_of_lt (measure_mono $ subset_univ _) hν,
  have to_nnreal_μ : ∀s, ((μ s).to_nnreal : ennreal) = μ s :=
    (assume s, ennreal.coe_to_nnreal $ ne_top_of_lt $ hμ _),
  have to_nnreal_ν : ∀s, ((ν s).to_nnreal : ennreal) = ν s :=
    (assume s, ennreal.coe_to_nnreal $ ne_top_of_lt $ hν _),

  have d_empty : d ∅ = 0, { simp [d], rw [measure_empty, measure_empty], simp },

  have d_split : ∀s t, is_measurable s → is_measurable t →
    d s = d (s \ t) + d (s ∩ t),
  { assume s t hs ht,
    simp only [d],
    rw [measure_eq_inter_diff hs ht, measure_eq_inter_diff hs ht,
      ennreal.to_nnreal_add (hμ _) (hμ _), ennreal.to_nnreal_add (hν _) (hν _),
      nnreal.coe_add, nnreal.coe_add],
    simp only [sub_eq_add_neg, neg_add],
    ac_refl },

  have d_Union : ∀(s : ℕ → set α), (∀n, is_measurable (s n)) → monotone s →
    tendsto (λn, d (s n)) at_top (nhds (d (⋃n, s n))),
  { assume s hs hm,
    refine tendsto_sub _ _;
      refine (nnreal.tendsto_coe.2 $
        (tendsto_measure_Union hs hm).comp $ ennreal.tendsto_to_nnreal $ @ne_top_of_lt _ _ _ ⊤ _),
    exact hμ _,
    exact hν _ },

  have d_Inter : ∀(s : ℕ → set α), (∀n, is_measurable (s n)) → (∀n m, n ≤ m → s m ⊆ s n) →
    tendsto (λn, d (s n)) at_top (nhds (d (⋂n, s n))),
  { assume s hs hm,
    refine tendsto_sub _ _;
      refine (nnreal.tendsto_coe.2 $
        (tendsto_measure_Inter hs hm _).comp $ ennreal.tendsto_to_nnreal $ @ne_top_of_lt _ _ _ ⊤ _),
    exact ⟨0, hμ _⟩,
    exact hμ _,
    exact ⟨0, hν _⟩,
    exact hν _ },

  have bdd_c : bdd_above c,
  { use (μ univ).to_nnreal,
    rintros r ⟨s, hs, rfl⟩,
    refine le_trans (sub_le_self _ $ nnreal.coe_nonneg _) _,
    rw [← nnreal.coe_le, ← ennreal.coe_le_coe, to_nnreal_μ, to_nnreal_μ],
    exact measure_mono (subset_univ _) },

  have c_nonempty : c ≠ ∅ := ne_empty_of_mem (mem_image_of_mem _ is_measurable.empty),

  have d_le_γ : ∀s, is_measurable s → d s ≤ γ := assume s hs, le_cSup bdd_c ⟨s, hs, rfl⟩,

  have : ∀n:ℕ, ∃s : set α, is_measurable s ∧ γ - (1/2)^n < d s,
  { assume n,
    have : γ - (1/2)^n < γ := sub_lt_self γ (pow_pos (half_pos zero_lt_one) n),
    rcases exists_lt_of_lt_cSup c_nonempty this with ⟨r, ⟨s, hs, rfl⟩, hlt⟩,
    exact ⟨s, hs, hlt⟩ },
  rcases classical.axiom_of_choice this with ⟨e, he⟩,
  change ℕ → set α at e,
  have he₁ : ∀n, is_measurable (e n) := assume n, (he n).1,
  have he₂ : ∀n, γ - (1/2)^n < d (e n) := assume n, (he n).2,

  let f : ℕ → ℕ → set α := λn m, (finset.Ico n (m + 1)).inf e,

  have hf : ∀n m, is_measurable (f n m),
  { assume n m,
    simp only [f, finset.inf_eq_infi],
    exact is_measurable.bInter (countable_encodable _) (assume i _, he₁ _) },

  have f_subset_f : ∀{a b c d}, a ≤ b → c ≤ d → f a d ⊆ f b c,
  { assume a b c d hab hcd,
    dsimp only [f],
    rw [finset.inf_eq_infi, finset.inf_eq_infi],
    refine bInter_subset_bInter_left _,
    simp,
    rintros j ⟨hbj, hjc⟩,
    exact ⟨le_trans hab hbj, lt_of_lt_of_le hjc $ add_le_add_right hcd 1⟩ },

  have f_succ : ∀n m, n ≤ m → f n (m + 1) = f n m ∩ e (m + 1),
  { assume n m hnm,
    have : n ≤ m + 1 := le_of_lt (nat.succ_le_succ hnm),
    simp only [f],
    rw [finset.Ico.succ_top this, finset.inf_insert, set.inter_comm],
    refl },

  have le_d_f : ∀n m, m ≤ n → γ - 2 * ((1 / 2) ^ m) + (1 / 2) ^ n ≤ d (f m n),
  { assume n m h,
    refine nat.le_induction _ _ n h,
    { have := he₂ m,
      simp only [f],
      rw [finset.Ico.succ_singleton, finset.inf_singleton],
      exact aux this },
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
            by simp only [sub_eq_add_neg]; ac_refl
          ... ≤ d (e (n + 1)) + d (f m n) : add_le_add (le_of_lt $ he₂ _) ih
          ... ≤ d (e (n + 1)) + d (f m n \ e (n + 1)) + d (f m (n + 1)) :
            by rw [f_succ _ _ hmn, d_split (f m n) (e (n + 1)) (hf _ _) (he₁ _), add_assoc]
          ... = d (e (n + 1) ∪ f m n) + d (f m (n + 1)) :
            begin
              rw [d_split (e (n + 1) ∪ f m n) (e (n + 1)),
                union_diff_left, union_inter_cancel_left],
              ac_refl,
              exact (he₁ _).union (hf _ _),
              exact (he₁ _)
            end
          ... ≤ γ + d (f m (n + 1)) :
            add_le_add_right (d_le_γ _ $ (he₁ _).union (hf _ _)) _ },
      exact (add_le_add_iff_left γ).1 this } },

  let s := ⋃ m, ⋂n, f m n,
  have γ_le_d_s : γ ≤ d s,
  { have hγ : tendsto (λm:ℕ, γ - 2 * (1/2)^m) at_top (nhds γ),
    { suffices : tendsto (λm:ℕ, γ - 2 * (1/2)^m) at_top (nhds (γ - 2 * 0)), { simpa },
      exact (tendsto_sub tendsto_const_nhds $ tendsto_mul tendsto_const_nhds $
        tendsto_pow_at_top_nhds_0_of_lt_1
          (le_of_lt $ half_pos $ zero_lt_one) (half_lt_self zero_lt_one)) },
    have hd : tendsto (λm, d (⋂n, f m n)) at_top (nhds (d (⋃ m, ⋂ n, f m n))),
    { refine d_Union _ _ _,
      { assume n, exact is_measurable.Inter (assume m, hf _ _) },
      { exact assume n m hnm, subset_Inter
          (assume i, subset.trans (Inter_subset (f n) i) $ f_subset_f hnm $ le_refl _) } },
    refine le_of_tendsto_of_tendsto (@at_top_ne_bot ℕ _ _) hγ hd (univ_mem_sets' $ assume m, _),
    change γ - 2 * (1 / 2) ^ m ≤ d (⋂ (n : ℕ), f m n),
    have : tendsto (λn, d (f m n)) at_top (nhds (d (⋂ n, f m n))),
    { refine d_Inter _ _ _,
      { assume n, exact hf _ _ },
      { assume n m hnm, exact f_subset_f (le_refl _) hnm } },
    refine ge_of_tendsto (@at_top_ne_bot ℕ _ _) this (mem_at_top_sets.2 ⟨m, assume n hmn, _⟩),
    change γ - 2 * (1 / 2) ^ m ≤ d (f m n),
    refine le_trans _ (le_d_f _ _ hmn),
    exact le_add_of_le_of_nonneg (le_refl _) (pow_nonneg (le_of_lt $ half_pos $ zero_lt_one) _) },

  have hs : is_measurable s :=
    is_measurable.Union (assume n, is_measurable.Inter (assume m, hf _ _)),
  refine ⟨s, hs, _, _⟩,
  { assume t ht hts,
    have : 0 ≤ d t := ((add_le_add_iff_left γ).1 $
      calc γ + 0 ≤ d s : by rw [add_zero]; exact γ_le_d_s
        ... = d (s \ t) + d t : by rw [d_split _ _ hs ht, inter_eq_self_of_subset_right hts]
        ... ≤ γ + d t : add_le_add (d_le_γ _ (hs.diff ht)) (le_refl _)),
    rw [← to_nnreal_μ, ← to_nnreal_ν, ennreal.coe_le_coe, nnreal.coe_le],
    simpa only [d, le_sub_iff_add_le, zero_add] using this },
  { assume t ht hts,
    have : d t ≤ 0,
    exact ((add_le_add_iff_left γ).1 $
      calc γ + d t ≤ d s + d t : add_le_add γ_le_d_s (le_refl _)
        ... = d (s ∪ t) :
        begin
          rw [d_split _ _ (hs.union ht) ht, union_diff_right, union_inter_cancel_right,
            diff_eq_self.2],
          exact assume a ⟨hat, has⟩, hts hat has
        end
        ... ≤ γ + 0 : by rw [add_zero]; exact d_le_γ _ (hs.union ht)),
    rw [← to_nnreal_μ, ← to_nnreal_ν, ennreal.coe_le_coe, nnreal.coe_le],
    simpa only [d, sub_le_iff_le_add, zero_add] using this }
end

end measure_theory
