/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.vector_measure
import order.symm_diff

/-!
# Hahn decomposition

This file defines positive and negative sets with respect to a vector measure and
prove the Hahn decomposition theorem (signed version).

## Main definitions

* `vector_measure.positive` : a set `i` is positive with respect to a vector measure `v` if `v`
  restricted on `i` is non-negative, i.e. `0 ≤ v.restrict i`.
* `vector_measure.negative` : a set `i` is negative with respect to a vector measure `v` if `v`
  restricted on `i` is non-positive, i.e. `v.restrict i ≤ 0`.

## Main results

* `signed_measure.exists_disjoint_positive_negative_union_eq` : the Hahn decomposition theorem.
* `signed_measure.exists_negative_set` : A measurable set of negative measure contains at least
  one negative subset.

## Tags

positive, negative, Hahn decomposition theorem
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

section lemmas

variables {α : Type*}

open_locale topological_space

open set filter topological_space

-- from #8266
lemma strict_mono_of_strict_mono_nat [preorder α] {f : ℕ → α} (hf : ∀n, f n < f (n + 1)) :
  strict_mono f | n m h :=
begin
  induction h,
  { exact hf _ },
  { transitivity, assumption, exact hf _ }
end

variables [conditionally_complete_linear_order α] [topological_space α] [order_topology α]
  [first_countable_topology α]

lemma exists_seq_tendsto_Sup {S : set α} (hS : S.nonempty) (hS' : bdd_above S) :
  ∃ (u : ℕ → α) (hu : ∀ n, u n ∈ S), tendsto u at_top (𝓝 (Sup S)) :=
begin
  by_cases hSup : Sup S ∈ S,
  { exact ⟨λ n, Sup S, λ _, hSup, tendsto_const_nhds⟩ },
  { have hlt : ∀ s ∈ S, s < Sup S,
    { exact λ s hs, lt_of_le_of_ne (le_cSup hS' hs) (λ h, hSup (h ▸ hs)) },
    obtain ⟨s, hs⟩ : ∃ s : ℕ → set α, (𝓝 (Sup S)).has_basis (λ (_x : ℕ), true) s :=
      let ⟨s, hs⟩ := (is_countably_generated_nhds (Sup S)).exists_antimono_basis in
        ⟨s, hs.to_has_basis⟩,
    have : ∀ n k, k ∈ S → ∃ y ∈ S, Ico y (Sup S) ⊆ s n ∧ k < y,
    { intros n k hk,
      obtain ⟨L, hL, h⟩ : ∃ (L : α) (hL : L ∈ Ico k (Sup S)), Ioc L (Sup S) ⊆ s n :=
        exists_Ioc_subset_of_mem_nhds' (hs.mem_of_mem trivial) (hlt _ hk),
      obtain ⟨y, hy⟩ : ∃ y ∈ S, L < y := exists_lt_of_lt_cSup hS hL.2,
      exact ⟨y, (exists_prop.1 hy).1, λ z hz, h ⟨(exists_prop.1 hy).2.trans_le hz.1,
              le_of_lt hz.2⟩, hL.1.trans_lt (exists_prop.1 hy).2⟩ },
    choose! f hf using this,
    obtain ⟨t, ht⟩ := hS,
    let u : ℕ → α := λ n, nat.rec_on n (f 0 t) (λ n h, f n.succ h),
    have I : ∀ n, u n ∈ S,
    { intro n,
      induction n with n IH,
      { exact (hf 0 t ht).1 },
      { exact (hf n.succ _ IH).1 } },
    have hmono : strict_mono u := strict_mono_of_strict_mono_nat (λ n, (hf n.succ _ (I n)).2.2),
    refine ⟨u, I, hs.tendsto_right_iff.2 (λ n _, _)⟩,
    simp only [ge_iff_le, eventually_at_top],
    refine ⟨n, λ p hp, _⟩,
    have up : u p ∈ Icc (u n) (Sup S) := ⟨hmono.monotone hp, le_cSup hS' (I p)⟩,
    have : Ico (u n) (Sup S) ⊆ s n,
      by { cases n, { exact (hf 0 t ht).2.1 }, { exact (hf n.succ (u n) (I n)).2.1 } },
    exact this ⟨up.1, lt_of_le_of_ne up.2 (λ h, hSup (h ▸ I p))⟩ }
end

lemma exists_seq_tendsto_Inf {S : set α} (hS : S.nonempty) (hS' : bdd_below S) :
  ∃ (u : ℕ → α) (hu : ∀ n, u n ∈ S), tendsto u at_top (𝓝 (Inf S)) :=
begin
  haveI : first_countable_topology (order_dual α) := sorry,
  exact @exists_seq_tendsto_Sup (order_dual α) _ _ _ _ _ hS hS',
end

end lemmas

variables {α β : Type*} [measurable_space α]
variables {M : Type*} [add_comm_monoid M] [topological_space M] [ordered_add_comm_monoid M]

namespace measure_theory

namespace vector_measure

/-- A set `i` is positive with respect to a vector measure `v` if `v` restricted
on`i` is non-negative, i.e. `0 ≤ v.restrict i`. -/
def positive (v : vector_measure α M) (i : set α) : Prop :=
0 ≤ v.restrict i

lemma positive_iff {v : vector_measure α M} {i : set α} (hi : measurable_set i) :
  v.positive i ↔ ∀ ⦃j⦄, measurable_set j → j ⊆ i → 0 ≤ v j :=
begin
  convert restrict_le_restrict_iff 0 v hi,
  rw restrict_zero, refl,
end

/-- A set `i` is negative with respect to a vector measure `v` if `v` restricted
on`i` is non-positive, i.e. `v.restrict i ≤ 0`. -/
def negative (v : vector_measure α M) (i : set α) : Prop :=
v.restrict i ≤ 0

lemma negative_iff {v : vector_measure α M} {i : set α} (hi : measurable_set i) :
  v.negative i ↔ ∀ ⦃j⦄, measurable_set j → j ⊆ i → v j ≤ 0 :=
begin
  convert restrict_le_restrict_iff v 0 hi,
  rw restrict_zero, refl,
end

variables {v : signed_measure α} {i j : set α}

lemma empty_positive : v.positive ∅ :=
begin
  intros j hj,
  rw restrict_empty,
end

lemma empty_negative : v.negative ∅ :=
begin
  intros j hj,
  rw restrict_empty,
end

lemma positive_nonneg_measure (hi₂ : v.positive i) :
  0 ≤ v i :=
begin
  by_cases hi₁ : measurable_set i,
  { exact (positive_iff hi₁).1 hi₂ hi₁ set.subset.rfl },
  { rw v.not_measurable hi₁ },
end

lemma negative_nonpos_measure (hi₂ : v.negative i) :
  v i ≤ 0 :=
begin
  by_cases hi₁ : measurable_set i,
  { exact (negative_iff hi₁).1 hi₂ hi₁ set.subset.rfl },
  { rw v.not_measurable hi₁ }
end

lemma positive_of_not_measurable (hi : ¬ measurable_set i) :
  v.positive i :=
begin
  rw [positive, restrict, dif_neg hi],
  exact le_refl _,
end

lemma negative_of_not_measurable (hi : ¬ measurable_set i) :
  v.negative i :=
begin
  rw [negative, restrict, dif_neg hi],
  exact le_refl _,
end

/-- This lemma is similar to the forward direction of `vector_measure.positive_iff` except it
does not have a measurability condition on `j`.

This is useful when we are using the property that a set is positive. -/
lemma subset_nonneg_of_positive {i : set α}
  (hi : measurable_set i) (hi₂ : v.positive i) {j : set α} (hj : j ⊆ i) : 0 ≤ v j :=
begin
  rw ← zero_apply j,
  refine subset_le_of_restrict_le_restrict 0 v hi _ hj,
  rwa restrict_zero
end

/-- This lemma is similar to the backward direction of `vector_measure.positive_iff` except it
does not require `i` to be measurable.

This is useful when we are proving a set is positive. -/
lemma positive_of_subset_nonneg {i : set α}
  (h : ∀ ⦃j⦄, measurable_set j → j ⊆ i → 0 ≤ v j) : v.positive i :=
λ j hj, (@restrict_zero α _ ℝ _ _ i) ▸ restrict_le_restrict_of_subset_le 0 v h _ hj

/-- This lemma is similar to the forward direction of `vector_measure.negative_iff` except it
does not have a measurability condition on `j`.

This is useful when we are using the property that a set is negative. -/
lemma subset_nonpos_of_negative {i : set α}
  (hi : measurable_set i) (hi₂ : v.negative i) {j : set α} (hj : j ⊆ i) : v j ≤ 0 :=
begin
  rw ← zero_apply j,
  refine subset_le_of_restrict_le_restrict v 0 hi _ hj,
  rwa restrict_zero
end

/-- This lemma is similar to the backward direction of `vector_measure.negative_iff` except it
does not require `i` to be measurable.

This is useful when we are proving a set is negative. -/
lemma negative_of_subset_nonpos {i : set α}
  (h : ∀ ⦃j⦄, measurable_set j → j ⊆ i → v j ≤ 0) : v.negative i :=
λ j hj, (@restrict_zero α _ ℝ _ _ i) ▸ restrict_le_restrict_of_subset_le v 0 h _ hj

lemma measurable_of_not_positive (hi : ¬ v.positive i) : measurable_set i :=
not.imp_symm positive_of_not_measurable hi

lemma measurable_of_not_negative (hi : ¬ v.negative i) : measurable_set i :=
not.imp_symm negative_of_not_measurable hi

lemma positive_subset_positive (hi₁ : measurable_set i) (hi₂ : v.positive i) (hij : j ⊆ i) :
  v.positive j :=
positive_of_subset_nonneg (λ k hk₁ hk₂, (positive_iff hi₁).1 hi₂ hk₁ (set.subset.trans hk₂ hij))

lemma negative_subset_negative (hi₁ : measurable_set i) (hi₂ : v.negative i) (hij : j ⊆ i) :
  v.negative j :=
negative_of_subset_nonpos (λ k hk₁ hk₂, (negative_iff hi₁).1 hi₂ hk₁ (set.subset.trans hk₂ hij))

lemma not_positive_subset (hi : ¬ v.positive i) (h : i ⊆ j) (hj : measurable_set j) :
  ¬ v.positive j :=
λ h', hi $ positive_subset_positive hj h' h

lemma not_negative_subset (hi : ¬ v.negative i) (h : i ⊆ j) (hj : measurable_set j) :
  ¬ v.negative j :=
λ h', hi $ negative_subset_negative hj h' h

lemma positive_union_positive
  (hi₁ : measurable_set i) (hi₂ : v.positive i)
  (hj₁ : measurable_set j) (hj₂ : v.positive j) : v.positive (i ∪ j) :=
begin
  refine positive_of_subset_nonneg (λ a ha₁ ha₂, _),
  have h₁ := ha₁.inter hi₁,
  have : a ∩ i ∪ a ∩ j \ (a ∩ i) = a,
    { rwa [set.union_diff_self, ← set.inter_union_distrib_left, set.inter_eq_left_iff_subset] },
  rw [← this, of_union disjoint_sdiff_self_right h₁ ((ha₁.inter hj₁).diff h₁)],
  refine add_nonneg ((positive_iff hi₁).1 hi₂ h₁ (a.inter_subset_right i)) _,
  exact (positive_iff hj₁).1 hj₂ ((ha₁.inter hj₁).diff h₁)
    (set.subset.trans ((a ∩ j).diff_subset (a ∩ i)) (a.inter_subset_right j)),
  apply_instance
end

lemma positive_Union_positive {f : ℕ → set α}
  (hf₁ : ∀ n, measurable_set (f n)) (hf₂ : ∀ n, v.positive (f n)) :
  v.positive ⋃ n, f n :=
begin
  convert restrict_le_restrict_Union 0 v hf₁ _,
  { rw restrict_zero, refl },
  { intro n,
    rw restrict_zero,
    exact hf₂ n }
end

lemma negative_union_negative
  (hi₁ : measurable_set i) (hi₂ : v.negative i)
  (hj₁ : measurable_set j) (hj₂ : v.negative j) : v.negative (i ∪ j) :=
begin
  refine negative_of_subset_nonpos (λ a ha₁ ha₂, _),
  have h₁ := ha₁.inter hi₁,
  have : a ∩ i ∪ a ∩ j \ (a ∩ i) = a,
    { rwa [set.union_diff_self, ← set.inter_union_distrib_left, set.inter_eq_left_iff_subset] },
  rw [← this, of_union disjoint_sdiff_self_right h₁ ((ha₁.inter hj₁).diff h₁)],
  refine add_nonpos ((negative_iff hi₁).1 hi₂ h₁ (a.inter_subset_right i)) _,
  exact (negative_iff hj₁).1 hj₂ ((ha₁.inter hj₁).diff h₁)
    (set.subset.trans ((a ∩ j).diff_subset (a ∩ i)) (a.inter_subset_right j)),
  apply_instance
end

lemma negative_Union_negative {f : ℕ → set α}
  (hf₁ : ∀ n, measurable_set (f n)) (hf₂ : ∀ n, v.negative (f n)) :
  v.negative ⋃ n, f n :=
begin
  convert restrict_le_restrict_Union v 0 hf₁ _,
  { rw restrict_zero, refl },
  { intro n,
    rw restrict_zero,
    exact hf₂ n }
end

lemma exists_pos_measure_of_not_negative (hi : ¬ v.negative i) :
  ∃ (j : set α) (hj₁ : measurable_set j) (hj₂ : j ⊆ i) , 0 < v j :=
begin
  have hi₁ : measurable_set i := measurable_of_not_negative hi,
  rw [negative_iff hi₁] at hi,
  push_neg at hi,
  obtain ⟨j, hj₁, hj₂, hj⟩ := hi,
  exact ⟨j, hj₁, hj₂, hj⟩,
end

end vector_measure

namespace signed_measure

open filter vector_measure

variables {s : signed_measure α} {i j : set α}

section exists_negative_set

private def p (s : signed_measure α) (i j : set α) (n : ℕ) : Prop :=
∃ (k : set α) (hj₁ : k ⊆ i \ j) (hj₂ : measurable_set k), (1 / (n + 1) : ℝ) < s k

private lemma exists_nat_one_div_lt_measure_of_not_negative (hi : ¬ s.negative (i \ j)) :
  ∃ (n : ℕ), p s i j n :=
let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_negative hi in
let ⟨n, hn⟩ := exists_nat_one_div_lt hj in ⟨n, k, hj₂, hj₁, hn⟩

private def aux₀ (s : signed_measure α) (i j : set α) : ℕ :=
if hi : ¬ s.negative (i \ j) then nat.find (exists_nat_one_div_lt_measure_of_not_negative hi) else 0

private lemma aux₀_spec (hi : ¬ s.negative (i \ j)) : p s i j (aux₀ s i j) :=
begin
  rw [aux₀, dif_pos hi],
  convert nat.find_spec _,
end

private lemma aux₀_min (hi : ¬ s.negative (i \ j)) {m : ℕ} (hm : m < aux₀ s i j) :
  ¬ p s i j m :=
begin
  rw [aux₀, dif_pos hi] at hm,
  exact nat.find_min _ hm
end

private def aux₁ (s : signed_measure α) (i j : set α) : set α :=
if hi : ¬ s.negative (i \ j) then classical.some (aux₀_spec hi) else ∅

private lemma aux₁_spec (hi : ¬ s.negative (i \ j)) :
  ∃ (hj₁ : (aux₁ s i j) ⊆ i \ j) (hj₂ : measurable_set (aux₁ s i j)),
  (1 / (aux₀ s i j + 1) : ℝ) < s (aux₁ s i j) :=
begin
  rw [aux₁, dif_pos hi],
  exact classical.some_spec (aux₀_spec hi),
end

private lemma aux₁_subset : aux₁ s i j ⊆ i \ j :=
begin
  by_cases hi : ¬ s.negative (i \ j),
  { exact let ⟨h, _⟩ := aux₁_spec hi in h },
  { rw [aux₁, dif_neg hi],
    exact set.empty_subset _ },
end

private lemma aux₁_subset' : aux₁ s i j ⊆ i :=
set.subset.trans aux₁_subset (set.diff_subset _ _)

private lemma aux₁_measurable_set : measurable_set (aux₁ s i j) :=
begin
  by_cases hi : ¬ s.negative (i \ j),
  { exact let ⟨_, h, _⟩ := aux₁_spec hi in h },
  { rw [aux₁, dif_neg hi],
    exact measurable_set.empty }
end

private lemma aux₁_lt (hi : ¬ s.negative (i \ j)) :
  (1 / (aux₀ s i j + 1) : ℝ) < s (aux₁ s i j) :=
let ⟨_, _, h⟩ := aux₁_spec hi in h

private def aux (s : signed_measure α) (i : set α) : ℕ → set α
| 0 := aux₁ s i ∅
| (n + 1) := aux₁ s i ⋃ k ≤ n,
  have k < n + 1 := nat.lt_succ_iff.mpr H,
  aux k

private lemma aux_succ (n : ℕ) : aux s i n.succ = aux₁ s i ⋃ k ≤ n, aux s i k :=
by rw aux

private lemma aux_subset (n : ℕ) :
  aux s i n ⊆ i :=
begin
  cases n;
  { rw aux, exact aux₁_subset' }
end

private lemma aux_lt (n : ℕ) (hn :¬ s.negative (i \ ⋃ l ≤ n, aux s i l)) :
  (1 / (aux₀ s i (⋃ k ≤ n, aux s i k) + 1) : ℝ) < s (aux s i n.succ) :=
begin
  rw aux_succ,
  apply aux₁_lt hn,
end

private lemma measure_of_aux (hi₂ : ¬ s.negative i)
  (n : ℕ) (hn : ¬ s.negative (i \ ⋃ k < n, aux s i k)) :
  0 < s (aux s i n) :=
begin
  cases n,
  { rw aux, rw ← @set.diff_empty _ i at hi₂,
    rcases aux₁_spec hi₂ with ⟨_, _, h⟩,
    exact (lt_trans nat.one_div_pos_of_nat h) },
  { rw aux_succ,
    have h₁ : ¬ s.negative (i \ ⋃ (k : ℕ) (H : k ≤ n), aux s i k),
    { apply not_negative_subset hn,
      { apply set.diff_subset_diff_right,
        intros x,
        simp_rw [set.mem_Union],
        rintro ⟨n, hn₁, hn₂⟩,
        exact ⟨n, nat.lt_succ_iff.mpr hn₁, hn₂⟩ },
      { convert measurable_of_not_negative hn,
        exact funext (λ x, by rw nat.lt_succ_iff) } },
    rcases aux₁_spec h₁ with ⟨_, _, h⟩,
    exact (lt_trans nat.one_div_pos_of_nat h) }
end

private lemma aux_measurable_set (n : ℕ) : measurable_set (aux s i n) :=
begin
  cases n,
  { rw aux,
    exact aux₁_measurable_set },
  { rw aux,
    exact aux₁_measurable_set }
end

private lemma aux_disjoint' {n m : ℕ} (h : n < m) : aux s i n ∩ aux s i m = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  rintro x ⟨hx₁, hx₂⟩,
  cases m, linarith,
  { rw aux at hx₂,
    exact (aux₁_subset hx₂).2
      (set.mem_Union.2 ⟨n, set.mem_Union.2 ⟨nat.lt_succ_iff.mp h, hx₁⟩⟩) }
end

private lemma aux_disjoint : pairwise (disjoint on (aux s i)) :=
begin
  intros n m h,
  rcases lt_or_gt_of_ne h with (h | h),
  { intro x,
    rw [set.inf_eq_inter, aux_disjoint' h],
    exact id },
  { intro x,
    rw [set.inf_eq_inter, set.inter_comm, aux_disjoint' h],
    exact id }
end

private lemma exists_negative_set' (hi₁ : measurable_set i) (hi₂ : s i < 0)
  (hn : ¬ ∀ n : ℕ, ¬ s.negative (i \ ⋃ l < n, aux s i l)) :
  ∃ (j : set α) (hj₁ : measurable_set j) (hj₂ : j ⊆ i), s.negative j ∧ s j < 0 :=
begin
  by_cases s.negative i,
  { exact ⟨i, hi₁, set.subset.refl _, h, hi₂⟩ },
  { push_neg at hn,
    set k := nat.find hn with hk₁,
    have hk₂ : s.negative (i \ ⋃ l < k, aux s i l) := nat.find_spec hn,
    have hmeas : measurable_set (⋃ (l : ℕ) (H : l < k), aux s i l) :=
      (measurable_set.Union $ λ _, measurable_set.Union_Prop (λ _, aux_measurable_set _)),
    refine ⟨i \ ⋃ l < k, aux s i l, hi₁.diff hmeas, set.diff_subset _ _, hk₂, _⟩,
    rw [of_diff hmeas hi₁, s.of_disjoint_Union_nat],
    { have h₁ : ∀ l < k, 0 ≤ s (aux s i l),
      { intros l hl,
        refine le_of_lt (measure_of_aux h _ _),
        refine (not_negative_subset (nat.find_min hn hl) (set.subset.refl _)) (hi₁.diff _),
        exact (measurable_set.Union $ λ _, measurable_set.Union_Prop (λ _, aux_measurable_set _)) },
      suffices : 0 ≤ ∑' (l : ℕ), s (⋃ (H : l < k), aux s i l),
        linarith,
      refine tsum_nonneg _,
      intro l, by_cases l < k,
      { convert h₁ _ h,
        ext x,
        rw [set.mem_Union, exists_prop, and_iff_right_iff_imp],
        exact λ _, h },
      { convert le_of_eq s.empty.symm,
        ext, simp only [exists_prop, set.mem_empty_eq, set.mem_Union, not_and, iff_false],
        exact λ h', false.elim (h h') } },
    { intro, exact measurable_set.Union_Prop (λ _, aux_measurable_set _) },
    { intros a b hab x hx,
      simp only [exists_prop, set.mem_Union, set.mem_inter_eq, set.inf_eq_inter] at hx,
      exact let ⟨⟨_, hx₁⟩, _, hx₂⟩ := hx in aux_disjoint a b hab ⟨hx₁, hx₂⟩ },
    { apply set.Union_subset,
      intros a x,
      simp only [and_imp, exists_prop, set.mem_Union],
      intros _ hx,
      exact aux_subset _ hx },
    { apply_instance } }
end .

/-- A measurable set of negative measure has a negative subset of negative measure. -/
theorem exists_negative_set (hi₁ : measurable_set i) (hi₂ : s i < 0) :
  ∃ (j : set α) (hj₁ : measurable_set j) (hj₂ : j ⊆ i), s.negative j ∧ s j < 0 :=
begin
  by_cases s.negative i,
  { exact ⟨i, hi₁, set.subset.refl _, h, hi₂⟩ },
  { by_cases hn : ∀ n : ℕ, ¬ s.negative (i \ ⋃ l < n, aux s i l),
    { set A := i \ ⋃ l, aux s i l with hA,
      set bdd : ℕ → ℕ := λ n, aux₀ s i (⋃ k ≤ n, aux s i k) with hbdd,

      have hn' : ∀ n : ℕ, ¬ s.negative (i \ ⋃ l ≤ n, aux s i l),
      { intro n,
        convert hn (n + 1), ext l,
        simp only [exists_prop, set.mem_Union, and.congr_left_iff],
        exact λ _, nat.lt_succ_iff.symm },
      have h₁ : s i = s A + ∑' l, s (aux s i l),
      { rw [hA, ← s.of_disjoint_Union_nat, add_comm, of_add_of_diff],
        exact measurable_set.Union (λ _, aux_measurable_set _),
        exacts [hi₁, set.Union_subset (λ _, aux_subset _), λ _,
                aux_measurable_set _, aux_disjoint] },
      have h₂ : s A ≤ s i,
      { rw h₁,
        apply le_add_of_nonneg_right,
        exact tsum_nonneg (λ n, le_of_lt (measure_of_aux h _ (hn n))) },
      have h₃' : summable (λ n, (1 / (bdd n + 1) : ℝ)),
      { have : summable (λ l, s (aux s i l)),
        { exact has_sum.summable (s.m_Union (λ _, aux_measurable_set _) aux_disjoint) },
        refine summable_of_nonneg_of_le _ _ (summable.comp_injective this nat.succ_injective),
        { intro _, exact le_of_lt nat.one_div_pos_of_nat },
        { intro n, exact le_of_lt (aux_lt n (hn' n)) } },
      have h₃ : tendsto (λ n, (bdd n : ℝ) + 1) at_top at_top,
      { simp only [one_div] at h₃',
        exact summable.tendsto_top_of_pos h₃' (λ n, nat.cast_add_one_pos (bdd n)) },
      have h₄ : tendsto (λ n, (bdd n : ℝ)) at_top at_top,
      { convert at_top.tendsto_at_top_add_const_right (-1) h₃, simp },

      refine ⟨A, _, set.diff_subset _ _, _, _⟩,
      { exact hi₁.diff (measurable_set.Union (λ _, aux_measurable_set _)) },
      { by_contra hnn,
        have hA₁ : measurable_set A := measurable_of_not_negative hnn,
        rw negative_iff hA₁ at hnn, push_neg at hnn,
        obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn,
        have : ∃ k, 1 ≤ bdd k ∧ 1 / (bdd k : ℝ) < s E,
        { rw tendsto_at_top_at_top at h₄,
          obtain ⟨k, hk⟩ := h₄ (max (1 / s E + 1) 1),
          refine ⟨k, _, _⟩,
          { have hle := le_of_max_le_right (hk k le_rfl),
            norm_cast at hle,
            exact hle },
          { have : 1 / s E < bdd k, linarith [le_of_max_le_left (hk k le_rfl)],
            rw one_div at this ⊢,
            rwa inv_lt (lt_trans (inv_pos.2 hE₃) this) hE₃ } },
        obtain ⟨k, hk₁, hk₂⟩ := this,
        have hA' : A ⊆ i \ ⋃ l ≤ k, aux s i l,
        { rw hA,
          apply set.diff_subset_diff_right,
          intro x, simp only [set.mem_Union],
          rintro ⟨n, _, hn₂⟩,
          exact ⟨n, hn₂⟩ },
        refine aux₀_min (hn' k) (buffer.lt_aux_2 hk₁) ⟨E, set.subset.trans hE₂ hA', hE₁, _⟩,
        convert hk₂, norm_cast,
        exact nat.sub_add_cancel hk₁ },
      { exact lt_of_le_of_lt h₂ hi₂ } },
    { exact exists_negative_set' hi₁ hi₂ hn } }
end .

end exists_negative_set

/-- The set of measures of the set of measurable negative sets. -/
def measure_of_negatives (s : signed_measure α) : set ℝ :=
  s '' { B | ∃ (hB₁ : measurable_set B), s.negative B }

lemma zero_mem_measure_of_negatives : (0 : ℝ) ∈ s.measure_of_negatives :=
⟨∅, ⟨measurable_set.empty, empty_negative⟩, s.empty⟩

lemma measure_of_negatives_bdd_below :
  ∃ x, ∀ y ∈ s.measure_of_negatives, x ≤ y :=
begin
  by_contra, push_neg at h,
  have h' : ∀ n : ℕ, ∃ y : ℝ, y ∈ s.measure_of_negatives ∧ y < -n := λ n, h (-n),
  choose f hf using h',
  have hf' : ∀ n : ℕ, ∃ B ∈ { B | ∃ (hB₁ : measurable_set B), s.negative B }, s B < -n,
  { intro n,
    rcases hf n with ⟨⟨B, hB₁, hB₂⟩, hlt⟩,
    exact ⟨B, hB₁, hB₂.symm ▸ hlt⟩ },
  choose B hB using hf',
  have hmeas : ∀ n, measurable_set (B n) := λ n, let ⟨h, _⟩ := (hB n).1 in h,
  set A := ⋃ n, B n with hA,
  have hfalse : ∀ n : ℕ, s A ≤ -n,
  { intro n,
    refine le_trans _ (le_of_lt (hB n).2),
    rw [hA, ← set.diff_union_of_subset (set.subset_Union _ n),
        of_union (disjoint.comm.1 set.disjoint_diff) _ (hmeas n)],
    { refine add_le_of_nonpos_left _,
      have : s.negative A := negative_Union_negative hmeas (λ m, let ⟨_, h⟩ := (hB m).1 in h),
      refine negative_nonpos_measure (negative_subset_negative _ this (set.diff_subset _ _)),
      exact measurable_set.Union hmeas },
    { apply_instance },
    { exact (measurable_set.Union hmeas).diff (hmeas n) } },
  suffices : ¬ ∀ n : ℕ, s A ≤ -n,
  { exact this hfalse },
  push_neg,
  rcases exists_nat_gt (-(s A)) with ⟨n, hn⟩,
  exact ⟨n, neg_lt.1 hn⟩,
end

/-- **The Hahn decomposition thoerem**: Given a signed measure `s`, there exist
disjoint measurable sets `i`, `j` such that `i` is positive, `j` is negative
and `i ∪ j = set.univ`.  -/
theorem exists_disjoint_positive_negative_union_eq (s : signed_measure α) :
  ∃ (i j : set α) (hi₁ : measurable_set i) (hi₂ : s.positive i)
                  (hj₁ : measurable_set j) (hj₂ : s.negative j),
  disjoint i j ∧ i ∪ j = set.univ :=
begin
  obtain ⟨f, hf₁, hf₂⟩ := exists_seq_tendsto_Inf
    ⟨0, @zero_mem_measure_of_negatives _ _ s⟩ measure_of_negatives_bdd_below,

  choose B hB using hf₁,
  have hB₁ : ∀ n, measurable_set (B n) := λ n, let ⟨h, _⟩ := (hB n).1 in h,
  have hB₂ : ∀ n, s.negative (B n) := λ n, let ⟨_, h⟩ := (hB n).1 in h,

  set A := ⋃ n, B n with hA,
  have hA₁ : measurable_set A := measurable_set.Union hB₁,
  have hA₂ : s.negative A := negative_Union_negative hB₁ hB₂,
  have hA₃ : s A = Inf s.measure_of_negatives,
  { apply has_le.le.antisymm,
    { refine le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (eventually_of_forall _),
      intro n,
      rw [← (hB n).2, hA, ← set.diff_union_of_subset (set.subset_Union _ n),
      of_union (disjoint.comm.1 set.disjoint_diff) _ (hB₁ n)],
      { refine add_le_of_nonpos_left _,
        have : s.negative A := negative_Union_negative hB₁ (λ m, let ⟨_, h⟩ := (hB m).1 in h),
        refine negative_nonpos_measure (negative_subset_negative _ this (set.diff_subset _ _)),
        exact measurable_set.Union hB₁ },
      { apply_instance },
      { exact (measurable_set.Union hB₁).diff (hB₁ n) } },
    { exact real.Inf_le _ measure_of_negatives_bdd_below ⟨A, ⟨hA₁, hA₂⟩, rfl⟩ } },

  refine ⟨Aᶜ, A, hA₁.compl, _, hA₁, hA₂,
          disjoint_compl_left, (set.union_comm A Aᶜ) ▸ set.union_compl_self A⟩,
  rw positive_iff hA₁.compl,
  intros C hC hC₁,
  by_contra hC₂, push_neg at hC₂,
  rcases exists_negative_set hC hC₂ with ⟨D, hD₁, hD, hD₂, hD₃⟩,

  have : s (A ∪ D) < Inf s.measure_of_negatives,
  { rw [← hA₃, of_union (set.disjoint_of_subset_right (set.subset.trans hD hC₁)
        disjoint_compl_right) hA₁ hD₁],
    linarith, apply_instance },
  refine not_le.2 this _,
  refine real.Inf_le _ measure_of_negatives_bdd_below ⟨A ∪ D, ⟨_, _⟩, rfl⟩,
  { exact hA₁.union hD₁ },
  { exact negative_union_negative hA₁ hA₂ hD₁ hD₂ }
end

/-- Alternative formulation of `exists_disjoint_positive_negative_union_eq` using complements. -/
lemma exists_compl_positive_negative (s : signed_measure α) :
  ∃ (i : set α) (hi₁ : measurable_set i), s.positive i ∧ s.negative iᶜ :=
begin
  obtain ⟨i, j, hi₁, hi₂, _, hj₂, hdisj, huniv⟩ :=
    s.exists_disjoint_positive_negative_union_eq,
  refine ⟨i, hi₁, hi₂, _⟩,
  rw [set.compl_eq_univ_diff, ← huniv,
      set.union_diff_cancel_left (set.disjoint_iff.mp hdisj)],
  exact hj₂,
end

/-- The symmetric difference of two Hahn decompositions have measure zero. -/
lemma of_symm_diff_compl_positive_negative {s : signed_measure α}
  {i j : set α} (hi : measurable_set i) (hj : measurable_set j)
  (hi' : s.positive i ∧ s.negative iᶜ) (hj' : s.positive j ∧ s.negative jᶜ) :
  s (i Δ j) = 0 ∧ s (iᶜ Δ jᶜ) = 0 :=
begin
  rw [positive_iff, negative_iff] at hi' hj',
  split,
  { rw [symm_diff_def, set.diff_eq_compl_inter, set.diff_eq_compl_inter,
        set.sup_eq_union, of_union,
        le_antisymm (hi'.2 (hi.compl.inter hj) (set.inter_subset_left _ _))
          (hj'.1 (hi.compl.inter hj) (set.inter_subset_right _ _)),
        le_antisymm (hj'.2 (hj.compl.inter hi) (set.inter_subset_left _ _))
          (hi'.1 (hj.compl.inter hi) (set.inter_subset_right _ _)), add_zero],
    { exact set.disjoint_of_subset_left (set.inter_subset_left _ _)
        (set.disjoint_of_subset_right (set.inter_subset_right _ _)
        (disjoint.comm.1 (is_compl.disjoint is_compl_compl))) },
    { exact hj.compl.inter hi },
    { exact hi.compl.inter hj } },
  { rw [symm_diff_def, set.diff_eq_compl_inter, set.diff_eq_compl_inter,
        compl_compl, compl_compl, set.sup_eq_union, of_union,
        le_antisymm (hi'.2 (hj.inter hi.compl) (set.inter_subset_right _ _))
          (hj'.1 (hj.inter hi.compl) (set.inter_subset_left _ _)),
        le_antisymm (hj'.2 (hi.inter hj.compl) (set.inter_subset_right _ _))
          (hi'.1 (hi.inter hj.compl) (set.inter_subset_left _ _)), add_zero],
    { exact set.disjoint_of_subset_left (set.inter_subset_left _ _)
        (set.disjoint_of_subset_right (set.inter_subset_right _ _)
        (is_compl.disjoint is_compl_compl)) },
    { exact hj.inter hi.compl },
    { exact hi.inter hj.compl } },
  all_goals { measurability },
end

end signed_measure

end measure_theory
