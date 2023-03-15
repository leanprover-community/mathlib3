/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/

import probability.process.adapted

/-!
# Stopping times, stopped processes and stopped values

Definition and properties of stopping times.

## Main definitions

* `measure_theory.is_stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.is_stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Main results

* `prog_measurable.stopped_process`: the stopped process of a progressively measurable process is
  progressively measurable.
* `mem_ℒp_stopped_process`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Tags

stopping time, stochastic process

-/

open filter order topological_space
open_locale classical measure_theory nnreal ennreal topology big_operators

namespace measure_theory

variables {Ω β ι : Type*} {m : measurable_space Ω}


/-! ### Stopping times -/

/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def is_stopping_time [preorder ι] (f : filtration ι m) (τ : Ω → ι) :=
∀ i : ι, measurable_set[f i] $ {ω | τ ω ≤ i}

lemma is_stopping_time_const [preorder ι] (f : filtration ι m) (i : ι) :
  is_stopping_time f (λ ω, i) :=
λ j, by simp only [measurable_set.const]

section measurable_set

section preorder
variables [preorder ι] {f : filtration ι m} {τ : Ω → ι}

protected lemma is_stopping_time.measurable_set_le (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | τ ω ≤ i} :=
hτ i

lemma is_stopping_time.measurable_set_lt_of_pred [pred_order ι]
  (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | τ ω < i} :=
begin
  by_cases hi_min : is_min i,
  { suffices : {ω : Ω | τ ω < i} = ∅, by { rw this, exact @measurable_set.empty _ (f i), },
    ext1 ω,
    simp only [set.mem_set_of_eq, set.mem_empty_iff_false, iff_false],
    rw is_min_iff_forall_not_lt at hi_min,
    exact hi_min (τ ω), },
  have : {ω : Ω | τ ω < i} = τ ⁻¹' (set.Iio i) := rfl,
  rw [this, ←Iic_pred_of_not_is_min hi_min],
  exact f.mono (pred_le i) _ (hτ.measurable_set_le $ pred i),
end

end preorder

section countable_stopping_time

namespace is_stopping_time

variables [partial_order ι] {τ : Ω → ι} {f : filtration ι m}

protected lemma measurable_set_eq_of_countable_range
  (hτ : is_stopping_time f τ) (h_countable : (set.range τ).countable) (i : ι) :
  measurable_set[f i] {ω | τ ω = i} :=
begin
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} \ (⋃ (j ∈ set.range τ) (hj : j < i), {ω | τ ω ≤ j}),
  { ext1 a,
    simp only [set.mem_set_of_eq, set.mem_range, set.Union_exists, set.Union_Union_eq',
      set.mem_diff, set.mem_Union, exists_prop, not_exists, not_and, not_le],
    split; intro h,
    { simp only [h, lt_iff_le_not_le, le_refl, and_imp, imp_self, implies_true_iff, and_self], },
    { have h_lt_or_eq : τ a < i ∨ τ a = i := lt_or_eq_of_le h.1,
      rcases h_lt_or_eq with h_lt | rfl,
      { exfalso,
        exact h.2 a h_lt (le_refl (τ a)), },
      { refl, }, }, },
  rw this,
  refine (hτ.measurable_set_le i).diff _,
  refine measurable_set.bUnion h_countable (λ j hj, _),
  by_cases hji : j < i,
  { simp only [hji, set.Union_true],
    exact f.mono hji.le _ (hτ.measurable_set_le j), },
  { simp only [hji, set.Union_false],
    exact @measurable_set.empty _ (f i), },
end

protected lemma measurable_set_eq_of_countable [countable ι] (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | τ ω = i} :=
hτ.measurable_set_eq_of_countable_range (set.to_countable _) i

protected lemma measurable_set_lt_of_countable_range
  (hτ : is_stopping_time f τ) (h_countable : (set.range τ).countable) (i : ι) :
  measurable_set[f i] {ω | τ ω < i} :=
begin
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i},
  { ext1 ω, simp [lt_iff_le_and_ne], },
  rw this,
  exact (hτ.measurable_set_le i).diff (hτ.measurable_set_eq_of_countable_range h_countable i),
end

protected lemma measurable_set_lt_of_countable [countable ι] (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | τ ω < i} :=
hτ.measurable_set_lt_of_countable_range (set.to_countable _) i

protected lemma measurable_set_ge_of_countable_range {ι} [linear_order ι] {τ : Ω → ι}
  {f : filtration ι m}
  (hτ : is_stopping_time f τ) (h_countable : (set.range τ).countable) (i : ι) :
  measurable_set[f i] {ω | i ≤ τ ω} :=
begin
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ,
  { ext1 ω, simp only [set.mem_set_of_eq, set.mem_compl_iff, not_lt], },
  rw this,
  exact (hτ.measurable_set_lt_of_countable_range h_countable i).compl,
end

protected lemma measurable_set_ge_of_countable {ι} [linear_order ι] {τ : Ω → ι} {f : filtration ι m}
  [countable ι] (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | i ≤ τ ω} :=
hτ.measurable_set_ge_of_countable_range (set.to_countable _) i

end is_stopping_time

end countable_stopping_time

section linear_order
variables [linear_order ι] {f : filtration ι m} {τ : Ω → ι}

lemma is_stopping_time.measurable_set_gt (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | i < τ ω} :=
begin
  have : {ω | i < τ ω} = {ω | τ ω ≤ i}ᶜ,
  { ext1 ω, simp only [set.mem_set_of_eq, set.mem_compl_iff, not_le], },
  rw this,
  exact (hτ.measurable_set_le i).compl,
end

section topological_space

variables [topological_space ι] [order_topology ι] [first_countable_topology ι]

/-- Auxiliary lemma for `is_stopping_time.measurable_set_lt`. -/
lemma is_stopping_time.measurable_set_lt_of_is_lub
  (hτ : is_stopping_time f τ) (i : ι) (h_lub : is_lub (set.Iio i) i) :
  measurable_set[f i] {ω | τ ω < i} :=
begin
  by_cases hi_min : is_min i,
  { suffices : {ω | τ ω < i} = ∅, by { rw this, exact @measurable_set.empty _ (f i), },
    ext1 ω,
    simp only [set.mem_set_of_eq, set.mem_empty_iff_false, iff_false],
    exact is_min_iff_forall_not_lt.mp hi_min (τ ω), },
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ : ∃ seq : ℕ → ι,
      monotone seq ∧ (∀ j, seq j ≤ i) ∧ tendsto seq at_top (𝓝 i) ∧ (∀ j, seq j < i),
    from h_lub.exists_seq_monotone_tendsto (not_is_min_iff.mp hi_min),
  have h_Ioi_eq_Union : set.Iio i = ⋃ j, {k | k ≤ seq j},
  { ext1 k,
    simp only [set.mem_Iio, set.mem_Union, set.mem_set_of_eq],
    refine ⟨λ hk_lt_i, _, λ h_exists_k_le_seq, _⟩,
    { rw tendsto_at_top' at h_tendsto,
      have h_nhds : set.Ici k ∈ 𝓝 i,
        from mem_nhds_iff.mpr ⟨set.Ioi k, set.Ioi_subset_Ici le_rfl, is_open_Ioi, hk_lt_i⟩,
      obtain ⟨a, ha⟩ : ∃ (a : ℕ), ∀ (b : ℕ), b ≥ a → k ≤ seq b := h_tendsto (set.Ici k) h_nhds,
      exact ⟨a, ha a le_rfl⟩, },
    { obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq,
      exact hk_seq_j.trans_lt (h_bound j), }, },
  have h_lt_eq_preimage : {ω | τ ω < i} = τ ⁻¹' (set.Iio i),
  { ext1 ω, simp only [set.mem_set_of_eq, set.mem_preimage, set.mem_Iio], },
  rw [h_lt_eq_preimage, h_Ioi_eq_Union],
  simp only [set.preimage_Union, set.preimage_set_of_eq],
  exact measurable_set.Union
    (λ n, f.mono (h_bound n).le _ (hτ.measurable_set_le (seq n))),
end

lemma is_stopping_time.measurable_set_lt (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | τ ω < i} :=
begin
  obtain ⟨i', hi'_lub⟩ : ∃ i', is_lub (set.Iio i) i', from exists_lub_Iio i,
  cases lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i h_Iio_eq_Iic,
  { rw ← hi'_eq_i at hi'_lub ⊢,
    exact hτ.measurable_set_lt_of_is_lub i' hi'_lub, },
  { have h_lt_eq_preimage : {ω : Ω | τ ω < i} = τ ⁻¹' (set.Iio i) := rfl,
    rw [h_lt_eq_preimage, h_Iio_eq_Iic],
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurable_set_le i'), },
end

lemma is_stopping_time.measurable_set_ge (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | i ≤ τ ω} :=
begin
  have : {ω | i ≤ τ ω} = {ω | τ ω < i}ᶜ,
  { ext1 ω, simp only [set.mem_set_of_eq, set.mem_compl_iff, not_lt], },
  rw this,
  exact (hτ.measurable_set_lt i).compl,
end

lemma is_stopping_time.measurable_set_eq (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[f i] {ω | τ ω = i} :=
begin
  have : {ω | τ ω = i} = {ω | τ ω ≤ i} ∩ {ω | τ ω ≥ i},
  { ext1 ω, simp only [set.mem_set_of_eq, ge_iff_le, set.mem_inter_iff, le_antisymm_iff], },
  rw this,
  exact (hτ.measurable_set_le i).inter (hτ.measurable_set_ge i),
end

lemma is_stopping_time.measurable_set_eq_le (hτ : is_stopping_time f τ) {i j : ι} (hle : i ≤ j) :
  measurable_set[f j] {ω | τ ω = i} :=
f.mono hle _ $ hτ.measurable_set_eq i

lemma is_stopping_time.measurable_set_lt_le (hτ : is_stopping_time f τ) {i j : ι} (hle : i ≤ j) :
  measurable_set[f j] {ω | τ ω < i} :=
f.mono hle _ $ hτ.measurable_set_lt i

end topological_space

end linear_order

section countable

lemma is_stopping_time_of_measurable_set_eq [preorder ι] [countable ι]
  {f : filtration ι m} {τ : Ω → ι} (hτ : ∀ i, measurable_set[f i] {ω | τ ω = i}) :
  is_stopping_time f τ :=
begin
  intro i,
  rw show {ω | τ ω ≤ i} = ⋃ k ≤ i, {ω | τ ω = k}, by { ext, simp },
  refine measurable_set.bUnion (set.to_countable _) (λ k hk, _),
  exact f.mono hk _ (hτ k),
end

end countable

end measurable_set

namespace is_stopping_time

protected lemma max [linear_order ι] {f : filtration ι m} {τ π : Ω → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ ω, max (τ ω) (π ω)) :=
begin
  intro i,
  simp_rw [max_le_iff, set.set_of_and],
  exact (hτ i).inter (hπ i),
end

protected lemma max_const [linear_order ι] {f : filtration ι m} {τ : Ω → ι}
  (hτ : is_stopping_time f τ) (i : ι) :
  is_stopping_time f (λ ω, max (τ ω) i) :=
hτ.max (is_stopping_time_const f i)

protected lemma min [linear_order ι] {f : filtration ι m} {τ π : Ω → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ ω, min (τ ω) (π ω)) :=
begin
  intro i,
  simp_rw [min_le_iff, set.set_of_or],
  exact (hτ i).union (hπ i),
end

protected lemma min_const [linear_order ι] {f : filtration ι m} {τ : Ω → ι}
  (hτ : is_stopping_time f τ) (i : ι) :
  is_stopping_time f (λ ω, min (τ ω) i) :=
hτ.min (is_stopping_time_const f i)

lemma add_const [add_group ι] [preorder ι] [covariant_class ι ι (function.swap (+)) (≤)]
  [covariant_class ι ι (+) (≤)]
  {f : filtration ι m} {τ : Ω → ι} (hτ : is_stopping_time f τ) {i : ι} (hi : 0 ≤ i) :
  is_stopping_time f (λ ω, τ ω + i) :=
begin
  intro j,
  simp_rw [← le_sub_iff_add_le],
  exact f.mono (sub_le_self j hi) _ (hτ (j - i)),
end

lemma add_const_nat
  {f : filtration ℕ m} {τ : Ω → ℕ} (hτ : is_stopping_time f τ) {i : ℕ} :
  is_stopping_time f (λ ω, τ ω + i) :=
begin
  refine is_stopping_time_of_measurable_set_eq (λ j, _),
  by_cases hij : i ≤ j,
  { simp_rw [eq_comm, ← nat.sub_eq_iff_eq_add hij, eq_comm],
    exact f.mono (j.sub_le i) _ (hτ.measurable_set_eq (j - i)) },
  { rw not_le at hij,
    convert measurable_set.empty,
    ext ω,
    simp only [set.mem_empty_iff_false, iff_false],
    rintro (hx : τ ω + i = j),
    linarith },
end

-- generalize to certain countable type?
lemma add
  {f : filtration ℕ m} {τ π : Ω → ℕ} (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (τ + π) :=
begin
  intro i,
  rw (_ : {ω | (τ + π) ω ≤ i} = ⋃ k ≤ i, {ω | π ω = k} ∩ {ω | τ ω + k ≤ i}),
  { exact measurable_set.Union (λ k, measurable_set.Union
      (λ hk, (hπ.measurable_set_eq_le hk).inter (hτ.add_const_nat i))) },
  ext ω,
  simp only [pi.add_apply, set.mem_set_of_eq, set.mem_Union, set.mem_inter_iff, exists_prop],
  refine ⟨λ h, ⟨π ω, by linarith, rfl, h⟩, _⟩,
  rintro ⟨j, hj, rfl, h⟩,
  assumption
end

section preorder

variables [preorder ι] {f : filtration ι m} {τ π : Ω → ι}

/-- The associated σ-algebra with a stopping time. -/
protected def measurable_space (hτ : is_stopping_time f τ) : measurable_space Ω :=
{ measurable_set' := λ s, ∀ i : ι, measurable_set[f i] (s ∩ {ω | τ ω ≤ i}),
  measurable_set_empty :=
    λ i, (set.empty_inter {ω | τ ω ≤ i}).symm ▸ @measurable_set.empty _ (f i),
  measurable_set_compl := λ s hs i,
    begin
      rw (_ : sᶜ ∩ {ω | τ ω ≤ i} = (sᶜ ∪ {ω | τ ω ≤ i}ᶜ) ∩ {ω | τ ω ≤ i}),
      { refine measurable_set.inter _ _,
        { rw ← set.compl_inter,
          exact (hs i).compl },
        { exact hτ i} },
      { rw set.union_inter_distrib_right,
        simp only [set.compl_inter_self, set.union_empty] }
    end,
  measurable_set_Union := λ s hs i,
    begin
      rw forall_swap at hs,
      rw set.Union_inter,
      exact measurable_set.Union (hs i),
    end }

protected lemma measurable_set (hτ : is_stopping_time f τ) (s : set Ω) :
  measurable_set[hτ.measurable_space] s ↔
  ∀ i : ι, measurable_set[f i] (s ∩ {ω | τ ω ≤ i}) :=
iff.rfl

lemma measurable_space_mono
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) (hle : τ ≤ π) :
  hτ.measurable_space ≤ hπ.measurable_space :=
begin
  intros s hs i,
  rw (_ : s ∩ {ω | π ω ≤ i} = s ∩ {ω | τ ω ≤ i} ∩ {ω | π ω ≤ i}),
  { exact (hs i).inter (hπ i) },
  { ext,
    simp only [set.mem_inter_iff, iff_self_and, and.congr_left_iff, set.mem_set_of_eq],
    intros hle' _,
    exact le_trans (hle _) hle' },
end

lemma measurable_space_le_of_countable [countable ι] (hτ : is_stopping_time f τ) :
  hτ.measurable_space ≤ m :=
begin
  intros s hs,
  change ∀ i, measurable_set[f i] (s ∩ {ω | τ ω ≤ i}) at hs,
  rw (_ : s = ⋃ i, s ∩ {ω | τ ω ≤ i}),
  { exact measurable_set.Union (λ i, f.le i _ (hs i)) },
  { ext ω, split; rw set.mem_Union,
    { exact λ hx, ⟨τ ω, hx, le_rfl⟩ },
    { rintro ⟨_, hx, _⟩,
      exact hx } }
end

lemma measurable_space_le' [is_countably_generated (at_top : filter ι)] [(at_top : filter ι).ne_bot]
  (hτ : is_stopping_time f τ) :
  hτ.measurable_space ≤ m :=
begin
  intros s hs,
  change ∀ i, measurable_set[f i] (s ∩ {ω | τ ω ≤ i}) at hs,
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := at_top.exists_seq_tendsto,
  rw (_ : s = ⋃ n, s ∩ {ω | τ ω ≤ seq n}),
  { exact measurable_set.Union (λ i, f.le (seq i) _ (hs (seq i))), },
  { ext ω, split; rw set.mem_Union,
    { intros hx,
      suffices : ∃ i, τ ω ≤ seq i, from ⟨this.some, hx, this.some_spec⟩,
      rw tendsto_at_top at h_seq_tendsto,
      exact (h_seq_tendsto (τ ω)).exists, },
    { rintro ⟨_, hx, _⟩,
      exact hx }, },
  all_goals { apply_instance, },
end

lemma measurable_space_le {ι} [semilattice_sup ι] {f : filtration ι m} {τ : Ω → ι}
  [is_countably_generated (at_top : filter ι)] (hτ : is_stopping_time f τ) :
  hτ.measurable_space ≤ m :=
begin
  casesI is_empty_or_nonempty ι,
  { haveI : is_empty Ω := ⟨λ ω, is_empty.false (τ ω)⟩,
    intros s hsτ,
    suffices hs : s = ∅, by { rw hs, exact measurable_set.empty, },
    haveI : unique (set Ω) := set.unique_empty,
    rw [unique.eq_default s, unique.eq_default ∅], },
  exact measurable_space_le' hτ,
end

example {f : filtration ℕ m} {τ : Ω → ℕ} (hτ : is_stopping_time f τ) : hτ.measurable_space ≤ m :=
hτ.measurable_space_le

example {f : filtration ℝ m} {τ : Ω → ℝ} (hτ : is_stopping_time f τ) : hτ.measurable_space ≤ m :=
hτ.measurable_space_le

@[simp] lemma measurable_space_const (f : filtration ι m) (i : ι) :
  (is_stopping_time_const f i).measurable_space = f i :=
begin
  ext1 s,
  change measurable_set[(is_stopping_time_const f i).measurable_space] s ↔ measurable_set[f i] s,
  rw is_stopping_time.measurable_set,
  split; intro h,
  { specialize h i,
    simpa only [le_refl, set.set_of_true, set.inter_univ] using h, },
  { intro j,
    by_cases hij : i ≤ j,
    { simp only [hij, set.set_of_true, set.inter_univ],
      exact f.mono hij _ h, },
    { simp only [hij, set.set_of_false, set.inter_empty, measurable_set.empty], }, },
end

lemma measurable_set_inter_eq_iff (hτ : is_stopping_time f τ) (s : set Ω) (i : ι) :
  measurable_set[hτ.measurable_space] (s ∩ {ω | τ ω = i})
    ↔ measurable_set[f i] (s ∩ {ω | τ ω = i}) :=
begin
  have : ∀ j, ({ω : Ω | τ ω = i} ∩ {ω : Ω | τ ω ≤ j}) = {ω : Ω | τ ω = i} ∩ {ω | i ≤ j},
  { intro j,
    ext1 ω,
    simp only [set.mem_inter_iff, set.mem_set_of_eq, and.congr_right_iff],
    intro hxi,
    rw hxi, },
  split; intro h,
  { specialize h i,
    simpa only [set.inter_assoc, this, le_refl, set.set_of_true, set.inter_univ] using h, },
  { intro j,
    rw [set.inter_assoc, this],
    by_cases hij : i ≤ j,
    { simp only [hij, set.set_of_true, set.inter_univ],
      exact f.mono hij _ h, },
    { simp [hij], }, },
end

lemma measurable_space_le_of_le_const (hτ : is_stopping_time f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) :
  hτ.measurable_space ≤ f i :=
(measurable_space_mono hτ _ hτ_le).trans (measurable_space_const _ _).le

lemma measurable_space_le_of_le (hτ : is_stopping_time f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
  hτ.measurable_space ≤ m :=
(hτ.measurable_space_le_of_le_const hτ_le).trans (f.le n)

lemma le_measurable_space_of_const_le (hτ : is_stopping_time f τ) {i : ι} (hτ_le : ∀ ω, i ≤ τ ω) :
  f i ≤ hτ.measurable_space :=
(measurable_space_const _ _).symm.le.trans (measurable_space_mono _ hτ hτ_le)

end preorder

instance sigma_finite_stopping_time {ι} [semilattice_sup ι] [order_bot ι]
  [(filter.at_top : filter ι).is_countably_generated]
  {μ : measure Ω} {f : filtration ι m} {τ : Ω → ι}
  [sigma_finite_filtration μ f] (hτ : is_stopping_time f τ) :
  sigma_finite (μ.trim hτ.measurable_space_le) :=
begin
  refine sigma_finite_trim_mono hτ.measurable_space_le _,
  { exact f ⊥, },
  { exact hτ.le_measurable_space_of_const_le (λ _, bot_le), },
  { apply_instance, },
end

instance sigma_finite_stopping_time_of_le {ι} [semilattice_sup ι] [order_bot ι]
  {μ : measure Ω} {f : filtration ι m} {τ : Ω → ι}
  [sigma_finite_filtration μ f] (hτ : is_stopping_time f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
  sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le)) :=
begin
  refine sigma_finite_trim_mono (hτ.measurable_space_le_of_le hτ_le) _,
  { exact f ⊥, },
  { exact hτ.le_measurable_space_of_const_le (λ _, bot_le), },
  { apply_instance, },
end

section linear_order

variables [linear_order ι] {f : filtration ι m} {τ π : Ω → ι}

protected lemma measurable_set_le' (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω ≤ i} :=
begin
  intro j,
  have : {ω : Ω | τ ω ≤ i} ∩ {ω : Ω | τ ω ≤ j} = {ω : Ω | τ ω ≤ min i j},
  { ext1 ω, simp only [set.mem_inter_iff, set.mem_set_of_eq, le_min_iff], },
  rw this,
  exact f.mono (min_le_right i j) _ (hτ _),
end

protected lemma measurable_set_gt' (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | i < τ ω} :=
begin
  have : {ω : Ω | i < τ ω} = {ω : Ω | τ ω ≤ i}ᶜ, by { ext1 ω, simp, },
  rw this,
  exact (hτ.measurable_set_le' i).compl,
end

protected lemma measurable_set_eq' [topological_space ι] [order_topology ι]
  [first_countable_topology ι]
  (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω = i} :=
begin
  rw [← set.univ_inter {ω | τ ω = i}, measurable_set_inter_eq_iff, set.univ_inter],
  exact hτ.measurable_set_eq i,
end

protected lemma measurable_set_ge' [topological_space ι] [order_topology ι]
  [first_countable_topology ι]
  (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | i ≤ τ ω} :=
begin
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω},
  { ext1 ω,
    simp only [le_iff_lt_or_eq, set.mem_set_of_eq, set.mem_union],
    rw [@eq_comm _ i, or_comm], },
  rw this,
  exact (hτ.measurable_set_eq' i).union (hτ.measurable_set_gt' i),
end

protected lemma measurable_set_lt' [topological_space ι] [order_topology ι]
  [first_countable_topology ι]
  (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω < i} :=
begin
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i},
  { ext1 ω,
    simp only [lt_iff_le_and_ne, set.mem_set_of_eq, set.mem_diff], },
  rw this,
  exact (hτ.measurable_set_le' i).diff (hτ.measurable_set_eq' i),
end

section countable

protected lemma measurable_set_eq_of_countable_range'
  (hτ : is_stopping_time f τ) (h_countable : (set.range τ).countable) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω = i} :=
begin
  rw [← set.univ_inter {ω | τ ω = i}, measurable_set_inter_eq_iff, set.univ_inter],
  exact hτ.measurable_set_eq_of_countable_range h_countable i,
end

protected lemma measurable_set_eq_of_countable' [countable ι] (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω = i} :=
hτ.measurable_set_eq_of_countable_range' (set.to_countable _) i

protected lemma measurable_set_ge_of_countable_range'
  (hτ : is_stopping_time f τ) (h_countable : (set.range τ).countable) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | i ≤ τ ω} :=
begin
  have : {ω | i ≤ τ ω} = {ω | τ ω = i} ∪ {ω | i < τ ω},
  { ext1 ω,
    simp only [le_iff_lt_or_eq, set.mem_set_of_eq, set.mem_union],
    rw [@eq_comm _ i, or_comm], },
  rw this,
  exact (hτ.measurable_set_eq_of_countable_range' h_countable i).union (hτ.measurable_set_gt' i),
end

protected lemma measurable_set_ge_of_countable' [countable ι] (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | i ≤ τ ω} :=
hτ.measurable_set_ge_of_countable_range' (set.to_countable _) i

protected lemma measurable_set_lt_of_countable_range'
  (hτ : is_stopping_time f τ) (h_countable : (set.range τ).countable) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω < i} :=
begin
  have : {ω | τ ω < i} = {ω | τ ω ≤ i} \ {ω | τ ω = i},
  { ext1 ω,
    simp only [lt_iff_le_and_ne, set.mem_set_of_eq, set.mem_diff], },
  rw this,
  exact (hτ.measurable_set_le' i).diff (hτ.measurable_set_eq_of_countable_range' h_countable i),
end

protected lemma measurable_set_lt_of_countable' [countable ι] (hτ : is_stopping_time f τ) (i : ι) :
  measurable_set[hτ.measurable_space] {ω | τ ω < i} :=
hτ.measurable_set_lt_of_countable_range' (set.to_countable _) i

protected lemma measurable_space_le_of_countable_range (hτ : is_stopping_time f τ)
  (h_countable : (set.range τ).countable) :
  hτ.measurable_space ≤ m :=
begin
  intros s hs,
  change ∀ i, measurable_set[f i] (s ∩ {ω | τ ω ≤ i}) at hs,
  rw (_ : s = ⋃ (i ∈ set.range τ), s ∩ {ω | τ ω ≤ i}),
  { exact measurable_set.bUnion h_countable (λ i _, f.le i _ (hs i)), },
  { ext ω,
    split; rw set.mem_Union,
    { exact λ hx, ⟨τ ω, by simpa using hx⟩,},
    { rintro ⟨i, hx⟩,
      simp only [set.mem_range, set.Union_exists, set.mem_Union, set.mem_inter_iff,
        set.mem_set_of_eq, exists_prop, exists_and_distrib_right] at hx,
      exact hx.1.2, } }
end

end countable

protected lemma measurable [topological_space ι] [measurable_space ι]
  [borel_space ι] [order_topology ι] [second_countable_topology ι]
  (hτ : is_stopping_time f τ) :
  measurable[hτ.measurable_space] τ :=
@measurable_of_Iic ι Ω _ _ _ hτ.measurable_space _ _ _ _ (λ i, hτ.measurable_set_le' i)

protected lemma measurable_of_le [topological_space ι] [measurable_space ι]
  [borel_space ι] [order_topology ι] [second_countable_topology ι]
  (hτ : is_stopping_time f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) :
  measurable[f i] τ :=
hτ.measurable.mono (measurable_space_le_of_le_const _ hτ_le) le_rfl

lemma measurable_space_min (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  (hτ.min hπ).measurable_space = hτ.measurable_space ⊓ hπ.measurable_space :=
begin
  refine le_antisymm _ _,
  { exact le_inf (measurable_space_mono _ hτ (λ _, min_le_left _ _))
      (measurable_space_mono _ hπ (λ _, min_le_right _ _)), },
  { intro s,
    change measurable_set[hτ.measurable_space] s ∧ measurable_set[hπ.measurable_space] s
      → measurable_set[(hτ.min hπ).measurable_space] s,
    simp_rw is_stopping_time.measurable_set,
    have : ∀ i, {ω | min (τ ω) (π ω) ≤ i} = {ω | τ ω ≤ i} ∪ {ω | π ω ≤ i},
    { intro i, ext1 ω, simp, },
    simp_rw [this, set.inter_union_distrib_left],
    exact λ h i, (h.left i).union (h.right i), },
end

lemma measurable_set_min_iff (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) (s : set Ω) :
  measurable_set[(hτ.min hπ).measurable_space] s
    ↔ measurable_set[hτ.measurable_space] s ∧ measurable_set[hπ.measurable_space] s :=
by { rw measurable_space_min, refl, }

lemma measurable_space_min_const (hτ : is_stopping_time f τ) {i : ι} :
  (hτ.min_const i).measurable_space = hτ.measurable_space ⊓ f i :=
by rw [hτ.measurable_space_min (is_stopping_time_const _ i), measurable_space_const]

lemma measurable_set_min_const_iff (hτ : is_stopping_time f τ) (s : set Ω)
  {i : ι} :
  measurable_set[(hτ.min_const i).measurable_space] s
    ↔ measurable_set[hτ.measurable_space] s ∧ measurable_set[f i] s :=
by rw [measurable_space_min_const, measurable_space.measurable_set_inf]

lemma measurable_set_inter_le [topological_space ι] [second_countable_topology ι] [order_topology ι]
  [measurable_space ι] [borel_space ι]
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) (s : set Ω)
  (hs : measurable_set[hτ.measurable_space] s) :
  measurable_set[(hτ.min hπ).measurable_space] (s ∩ {ω | τ ω ≤ π ω}) :=
begin
  simp_rw is_stopping_time.measurable_set at ⊢ hs,
  intro i,
  have : (s ∩ {ω | τ ω ≤ π ω} ∩ {ω | min (τ ω) (π ω) ≤ i})
    = (s ∩ {ω | τ ω ≤ i}) ∩ {ω | min (τ ω) (π ω) ≤ i} ∩ {ω | min (τ ω) i ≤ min (min (τ ω) (π ω)) i},
  { ext1 ω,
    simp only [min_le_iff, set.mem_inter_iff, set.mem_set_of_eq, le_min_iff, le_refl, true_and,
      and_true, true_or, or_true],
    by_cases hτi : τ ω ≤ i,
    { simp only [hτi, true_or, and_true, and.congr_right_iff],
      intro hx,
      split; intro h,
      { exact or.inl h, },
      { cases h,
        { exact h, },
        { exact hτi.trans h, }, }, },
    simp only [hτi, false_or, and_false, false_and, iff_false, not_and, not_le, and_imp],
    refine λ hx hτ_le_π, lt_of_lt_of_le _ hτ_le_π,
    rw ← not_le,
    exact hτi, },
  rw this,
  refine ((hs i).inter ((hτ.min hπ) i)).inter _,
  apply measurable_set_le,
  { exact (hτ.min_const i).measurable_of_le (λ _, min_le_right _ _), },
  { exact ((hτ.min hπ).min_const i).measurable_of_le (λ _, min_le_right _ _),  },
end

lemma measurable_set_inter_le_iff [topological_space ι]
  [second_countable_topology ι] [order_topology ι] [measurable_space ι] [borel_space ι]
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π)
  (s : set Ω) :
  measurable_set[hτ.measurable_space] (s ∩ {ω | τ ω ≤ π ω})
    ↔ measurable_set[(hτ.min hπ).measurable_space] (s ∩ {ω | τ ω ≤ π ω}) :=
begin
  split; intro h,
  { have : s ∩ {ω | τ ω ≤ π ω} = s ∩ {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ π ω},
      by rw [set.inter_assoc, set.inter_self],
    rw this,
    exact measurable_set_inter_le _ _ _ h, },
  { rw measurable_set_min_iff at h,
    exact h.1, },
end

lemma measurable_set_inter_le_const_iff (hτ : is_stopping_time f τ) (s : set Ω) (i : ι) :
  measurable_set[hτ.measurable_space] (s ∩ {ω | τ ω ≤ i})
    ↔ measurable_set[(hτ.min_const i).measurable_space] (s ∩ {ω | τ ω ≤ i}) :=
begin
  rw [is_stopping_time.measurable_set_min_iff hτ (is_stopping_time_const _ i),
    is_stopping_time.measurable_space_const, is_stopping_time.measurable_set],
  refine ⟨λ h, ⟨h, _⟩, λ h j, h.1 j⟩,
  specialize h i,
  rwa [set.inter_assoc, set.inter_self] at h,
end

lemma measurable_set_le_stopping_time [topological_space ι]
  [second_countable_topology ι] [order_topology ι] [measurable_space ι] [borel_space ι]
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  measurable_set[hτ.measurable_space] {ω | τ ω ≤ π ω} :=
begin
  rw hτ.measurable_set,
  intro j,
  have : {ω | τ ω ≤ π ω} ∩ {ω | τ ω ≤ j} = {ω | min (τ ω) j ≤ min (π ω) j} ∩ {ω | τ ω ≤ j},
  { ext1 ω,
    simp only [set.mem_inter_iff, set.mem_set_of_eq, min_le_iff, le_min_iff, le_refl, and_true,
      and.congr_left_iff],
    intro h,
    simp only [h, or_self, and_true],
    by_cases hj : j ≤ π ω,
    { simp only [hj, h.trans hj, or_self], },
    { simp only [hj, or_false], }, },
  rw this,
  refine measurable_set.inter _ (hτ.measurable_set_le j),
  apply measurable_set_le,
  { exact (hτ.min_const j).measurable_of_le (λ _, min_le_right _ _), },
  { exact (hπ.min_const j).measurable_of_le (λ _, min_le_right _ _), },
end

lemma measurable_set_stopping_time_le [topological_space ι]
  [second_countable_topology ι] [order_topology ι] [measurable_space ι] [borel_space ι]
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  measurable_set[hπ.measurable_space] {ω | τ ω ≤ π ω} :=
begin
  suffices : measurable_set[(hτ.min hπ).measurable_space] {ω : Ω | τ ω ≤ π ω},
    by { rw measurable_set_min_iff hτ hπ at this, exact this.2, },
  rw [← set.univ_inter {ω : Ω | τ ω ≤ π ω}, ← hτ.measurable_set_inter_le_iff hπ, set.univ_inter],
  exact measurable_set_le_stopping_time hτ hπ,
end

lemma measurable_set_eq_stopping_time [add_group ι]
  [topological_space ι] [measurable_space ι] [borel_space ι] [order_topology ι]
  [measurable_singleton_class ι] [second_countable_topology ι] [has_measurable_sub₂ ι]
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  measurable_set[hτ.measurable_space] {ω | τ ω = π ω} :=
begin
  rw hτ.measurable_set,
  intro j,
  have : {ω | τ ω = π ω} ∩ {ω | τ ω ≤ j}
    = {ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤ j},
  { ext1 ω,
    simp only [set.mem_inter_iff, set.mem_set_of_eq],
    refine ⟨λ h, ⟨⟨_, h.2⟩, _⟩, λ h, ⟨_, h.1.2⟩⟩,
    { rw h.1, },
    { rw ← h.1, exact h.2, },
    { cases h with h' hσ_le,
      cases h' with h_eq hτ_le,
      rwa [min_eq_left hτ_le, min_eq_left hσ_le] at h_eq, }, },
  rw this,
  refine measurable_set.inter (measurable_set.inter _ (hτ.measurable_set_le j))
    (hπ.measurable_set_le j),
  apply measurable_set_eq_fun,
  { exact (hτ.min_const j).measurable_of_le (λ _, min_le_right _ _), },
  { exact (hπ.min_const j).measurable_of_le (λ _, min_le_right _ _), },
end

lemma measurable_set_eq_stopping_time_of_countable [countable ι]
  [topological_space ι] [measurable_space ι] [borel_space ι] [order_topology ι]
  [measurable_singleton_class ι] [second_countable_topology ι]
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  measurable_set[hτ.measurable_space] {ω | τ ω = π ω} :=
begin
  rw hτ.measurable_set,
  intro j,
  have : {ω | τ ω = π ω} ∩ {ω | τ ω ≤ j}
    = {ω | min (τ ω) j = min (π ω) j} ∩ {ω | τ ω ≤ j} ∩ {ω | π ω ≤ j},
  { ext1 ω,
    simp only [set.mem_inter_iff, set.mem_set_of_eq],
    refine ⟨λ h, ⟨⟨_, h.2⟩, _⟩, λ h, ⟨_, h.1.2⟩⟩,
    { rw h.1, },
    { rw ← h.1, exact h.2, },
    { cases h with h' hπ_le,
      cases h' with h_eq hτ_le,
      rwa [min_eq_left hτ_le, min_eq_left hπ_le] at h_eq, }, },
  rw this,
  refine measurable_set.inter (measurable_set.inter _ (hτ.measurable_set_le j))
    (hπ.measurable_set_le j),
  apply measurable_set_eq_fun_of_countable,
  { exact (hτ.min_const j).measurable_of_le (λ _, min_le_right _ _), },
  { exact (hπ.min_const j).measurable_of_le (λ _, min_le_right _ _), },
end

end linear_order

end is_stopping_time

section linear_order

/-! ## Stopped value and stopped process -/

/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
def stopped_value (u : ι → Ω → β) (τ : Ω → ι) : Ω → β :=
λ ω, u (τ ω) ω

lemma stopped_value_const (u : ι → Ω → β) (i : ι) : stopped_value u (λ ω, i) = u i :=
rfl

variable [linear_order ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occured. -/
def stopped_process (u : ι → Ω → β) (τ : Ω → ι) : ι → Ω → β :=
λ i ω, u (min i (τ ω)) ω

lemma stopped_process_eq_stopped_value {u : ι → Ω → β} {τ : Ω → ι} :
  stopped_process u τ = λ i, stopped_value u (λ ω, min i (τ ω)) := rfl

lemma stopped_value_stopped_process {u : ι → Ω → β} {τ σ : Ω → ι} :
  stopped_value (stopped_process u τ) σ = stopped_value u (λ ω, min (σ ω) (τ ω)) := rfl

lemma stopped_process_eq_of_le {u : ι → Ω → β} {τ : Ω → ι}
  {i : ι} {ω : Ω} (h : i ≤ τ ω) : stopped_process u τ i ω = u i ω :=
by simp [stopped_process, min_eq_left h]

lemma stopped_process_eq_of_ge {u : ι → Ω → β} {τ : Ω → ι}
  {i : ι} {ω : Ω} (h : τ ω ≤ i) : stopped_process u τ i ω = u (τ ω) ω :=
by simp [stopped_process, min_eq_right h]

section prog_measurable

variables [measurable_space ι] [topological_space ι] [order_topology ι]
  [second_countable_topology ι] [borel_space ι]
  [topological_space β]
  {u : ι → Ω → β} {τ : Ω → ι} {f : filtration ι m}

lemma prog_measurable_min_stopping_time [metrizable_space ι] (hτ : is_stopping_time f τ) :
  prog_measurable f (λ i ω, min i (τ ω)) :=
begin
  intro i,
  let m_prod : measurable_space (set.Iic i × Ω) := measurable_space.prod _ (f i),
  let m_set : ∀ t : set (set.Iic i × Ω), measurable_space t :=
    λ _, @subtype.measurable_space (set.Iic i × Ω) _ m_prod,
  let s := {p : set.Iic i × Ω | τ p.2 ≤ i},
  have hs : measurable_set[m_prod] s, from @measurable_snd (set.Iic i) Ω _ (f i) _ (hτ i),
  have h_meas_fst : ∀ t : set (set.Iic i × Ω),
      measurable[m_set t] (λ x : t, ((x : set.Iic i × Ω).fst : ι)),
    from λ t, (@measurable_subtype_coe (set.Iic i × Ω) m_prod _).fst.subtype_coe,
  apply measurable.strongly_measurable,
  refine measurable_of_restrict_of_restrict_compl hs _ _,
  { refine @measurable.min _ _ _ _ _ (m_set s) _ _ _ _ _ (h_meas_fst s) _,
    refine @measurable_of_Iic ι s _ _ _ (m_set s) _ _ _ _ (λ j, _),
    have h_set_eq : (λ x : s, τ (x : set.Iic i × Ω).snd) ⁻¹' set.Iic j
      = (λ x : s, (x : set.Iic i × Ω).snd) ⁻¹' {ω | τ ω ≤ min i j},
    { ext1 ω,
      simp only [set.mem_preimage, set.mem_Iic, iff_and_self, le_min_iff, set.mem_set_of_eq],
      exact λ _, ω.prop, },
    rw h_set_eq,
    suffices h_meas : @measurable _ _ (m_set s) (f i) (λ x : s, (x : set.Iic i × Ω).snd),
      from h_meas (f.mono (min_le_left _ _) _ (hτ.measurable_set_le (min i j))),
    exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _), },
  { suffices h_min_eq_left : (λ x : sᶜ, min ↑((x : set.Iic i × Ω).fst) (τ (x : set.Iic i × Ω).snd))
      = λ x : sᶜ, ↑((x : set.Iic i × Ω).fst),
    { rw [set.restrict, h_min_eq_left],
      exact h_meas_fst _, },
    ext1 ω,
    rw min_eq_left,
    have hx_fst_le : ↑(ω : set.Iic i × Ω).fst ≤ i, from (ω : set.Iic i × Ω).fst.prop,
    refine hx_fst_le.trans (le_of_lt _),
    convert ω.prop,
    simp only [not_le, set.mem_compl_iff, set.mem_set_of_eq], },
end

lemma prog_measurable.stopped_process [metrizable_space ι]
  (h : prog_measurable f u) (hτ : is_stopping_time f τ) :
  prog_measurable f (stopped_process u τ) :=
h.comp (prog_measurable_min_stopping_time hτ) (λ i x, min_le_left _ _)

lemma prog_measurable.adapted_stopped_process [metrizable_space ι]
  (h : prog_measurable f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
(h.stopped_process hτ).adapted

lemma prog_measurable.strongly_measurable_stopped_process [metrizable_space ι]
  (hu : prog_measurable f u) (hτ : is_stopping_time f τ) (i : ι) :
  strongly_measurable (stopped_process u τ i) :=
(hu.adapted_stopped_process hτ i).mono (f.le _)

lemma strongly_measurable_stopped_value_of_le
  (h : prog_measurable f u) (hτ : is_stopping_time f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
  strongly_measurable[f n] (stopped_value u τ) :=
begin
  have : stopped_value u τ = (λ (p : set.Iic n × Ω), u ↑(p.fst) p.snd) ∘ (λ ω, (⟨τ ω, hτ_le ω⟩, ω)),
  { ext1 ω, simp only [stopped_value, function.comp_app, subtype.coe_mk], },
  rw this,
  refine strongly_measurable.comp_measurable (h n) _,
  exact (hτ.measurable_of_le hτ_le).subtype_mk.prod_mk measurable_id,
end

lemma measurable_stopped_value [metrizable_space β] [measurable_space β] [borel_space β]
  (hf_prog : prog_measurable f u) (hτ : is_stopping_time f τ) :
  measurable[hτ.measurable_space] (stopped_value u τ) :=
begin
  have h_str_meas : ∀ i, strongly_measurable[f i] (stopped_value u (λ ω, min (τ ω) i)),
    from λ i, strongly_measurable_stopped_value_of_le hf_prog (hτ.min_const i)
      (λ _, min_le_right _ _),
  intros t ht i,
  suffices : stopped_value u τ ⁻¹' t ∩ {ω : Ω | τ ω ≤ i}
      = stopped_value u (λ ω, min (τ ω) i) ⁻¹' t ∩ {ω : Ω | τ ω ≤ i},
    by { rw this, exact ((h_str_meas i).measurable ht).inter (hτ.measurable_set_le i), },
  ext1 ω,
  simp only [stopped_value, set.mem_inter_iff, set.mem_preimage, set.mem_set_of_eq,
    and.congr_left_iff],
  intro h,
  rw min_eq_left h,
end

end prog_measurable

end linear_order

section stopped_value_of_mem_finset

variables {μ : measure Ω} {τ σ : Ω → ι} {E : Type*} {p : ℝ≥0∞} {u : ι → Ω → E}

lemma stopped_value_eq_of_mem_finset [add_comm_monoid E] {s : finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
  stopped_value u τ = ∑ i in s, set.indicator {ω | τ ω = i} (u i) :=
begin
  ext y,
  rw [stopped_value, finset.sum_apply, finset.sum_indicator_eq_sum_filter],
  suffices : finset.filter (λ i, y ∈ {ω : Ω | τ ω = i}) s = ({τ y} : finset ι),
    by rw [this, finset.sum_singleton],
  ext1 ω,
  simp only [set.mem_set_of_eq, finset.mem_filter, finset.mem_singleton],
  split; intro h,
  { exact h.2.symm, },
  { refine ⟨_, h.symm⟩, rw h, exact hbdd y, },
end

lemma stopped_value_eq' [preorder ι] [locally_finite_order_bot ι] [add_comm_monoid E]
  {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
  stopped_value u τ = ∑ i in finset.Iic N, set.indicator {ω | τ ω = i} (u i) :=
stopped_value_eq_of_mem_finset (λ ω, finset.mem_Iic.mpr (hbdd ω))

lemma stopped_process_eq_of_mem_finset [linear_order ι] [add_comm_monoid E]
  {s : finset ι} (n : ι) (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) :
  stopped_process u τ n =
  set.indicator {a | n ≤ τ a} (u n) + ∑ i in s.filter (< n), set.indicator {ω | τ ω = i} (u i) :=
begin
  ext ω,
  rw [pi.add_apply, finset.sum_apply],
  cases le_or_lt n (τ ω),
  { rw [stopped_process_eq_of_le h, set.indicator_of_mem, finset.sum_eq_zero, add_zero],
    { intros m hm,
      refine set.indicator_of_not_mem _ _,
      rw [finset.mem_filter] at hm,
      exact (hm.2.trans_le h).ne', },
    { exact h, } },
  { rw [stopped_process_eq_of_ge (le_of_lt h), finset.sum_eq_single_of_mem (τ ω)],
    { rw [set.indicator_of_not_mem, zero_add, set.indicator_of_mem],
      { exact rfl }, -- refl does not work
      { exact not_le.2 h } },
    { rw [finset.mem_filter],
      exact ⟨hbdd ω h, h⟩, },
    { intros b hb hneq,
      rw set.indicator_of_not_mem,
      exact hneq.symm } },
end

lemma stopped_process_eq'' [linear_order ι] [locally_finite_order_bot ι] [add_comm_monoid E]
  (n : ι) :
  stopped_process u τ n =
    set.indicator {a | n ≤ τ a} (u n) + ∑ i in finset.Iio n, set.indicator {ω | τ ω = i} (u i) :=
begin
  have h_mem : ∀ ω, τ ω < n → τ ω ∈ finset.Iio n := λ ω h, finset.mem_Iio.mpr h,
  rw stopped_process_eq_of_mem_finset n h_mem,
  swap, { apply_instance, },
  congr' with i,
  simp only [finset.Iio_filter_lt, min_eq_right],
end

section stopped_value
variables [partial_order ι] {ℱ : filtration ι m} [normed_add_comm_group E]

lemma mem_ℒp_stopped_value_of_mem_finset (hτ : is_stopping_time ℱ τ) (hu : ∀ n, mem_ℒp (u n) p μ)
  {s : finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
  mem_ℒp (stopped_value u τ) p μ :=
begin
  rw stopped_value_eq_of_mem_finset hbdd,
  swap, apply_instance,
  refine mem_ℒp_finset_sum' _ (λ i hi, mem_ℒp.indicator _ (hu i)),
  refine ℱ.le i {a : Ω | τ a = i} (hτ.measurable_set_eq_of_countable_range _ i),
  refine ((finset.finite_to_set s).subset (λ ω hω, _)).countable,
  obtain ⟨y, rfl⟩ := hω,
  exact hbdd y,
end

lemma mem_ℒp_stopped_value [locally_finite_order_bot ι]
  (hτ : is_stopping_time ℱ τ) (hu : ∀ n, mem_ℒp (u n) p μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
  mem_ℒp (stopped_value u τ) p μ :=
mem_ℒp_stopped_value_of_mem_finset hτ hu (λ ω, finset.mem_Iic.mpr (hbdd ω))

lemma integrable_stopped_value_of_mem_finset (hτ : is_stopping_time ℱ τ)
  (hu : ∀ n, integrable (u n) μ) {s : finset ι} (hbdd : ∀ ω, τ ω ∈ s) :
  integrable (stopped_value u τ) μ :=
begin
  simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢,
  exact mem_ℒp_stopped_value_of_mem_finset hτ hu hbdd,
end

variables (ι)

lemma integrable_stopped_value [locally_finite_order_bot ι]
  (hτ : is_stopping_time ℱ τ) (hu : ∀ n, integrable (u n) μ) {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
  integrable (stopped_value u τ) μ :=
integrable_stopped_value_of_mem_finset hτ hu (λ ω, finset.mem_Iic.mpr (hbdd ω))

end stopped_value

section stopped_process
variables [linear_order ι] [topological_space ι] [order_topology ι] [first_countable_topology ι]
  {ℱ : filtration ι m} [normed_add_comm_group E]

lemma mem_ℒp_stopped_process_of_mem_finset (hτ : is_stopping_time ℱ τ)
  (hu : ∀ n, mem_ℒp (u n) p μ) (n : ι) {s : finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) :
  mem_ℒp (stopped_process u τ n) p μ :=
begin
  rw stopped_process_eq_of_mem_finset n hbdd,
  swap, { apply_instance, },
  refine mem_ℒp.add _ _,
  { exact mem_ℒp.indicator (ℱ.le n {a : Ω | n ≤ τ a} (hτ.measurable_set_ge n)) (hu n) },
  { suffices : mem_ℒp (λ ω, ∑ i in s.filter (< n), {a : Ω | τ a = i}.indicator (u i) ω) p μ,
    { convert this, ext1 ω, simp only [finset.sum_apply] },
    refine mem_ℒp_finset_sum _ (λ i hi, mem_ℒp.indicator _ (hu i)),
    exact ℱ.le i {a : Ω | τ a = i} (hτ.measurable_set_eq i) },
end

lemma mem_ℒp_stopped_process [locally_finite_order_bot ι] (hτ : is_stopping_time ℱ τ)
  (hu : ∀ n, mem_ℒp (u n) p μ) (n : ι) :
  mem_ℒp (stopped_process u τ n) p μ :=
mem_ℒp_stopped_process_of_mem_finset hτ hu n (λ ω h, finset.mem_Iio.mpr h)

lemma integrable_stopped_process_of_mem_finset (hτ : is_stopping_time ℱ τ)
  (hu : ∀ n, integrable (u n) μ) (n : ι) {s : finset ι} (hbdd : ∀ ω, τ ω < n → τ ω ∈ s) :
  integrable (stopped_process u τ n) μ :=
begin
  simp_rw ← mem_ℒp_one_iff_integrable at hu ⊢,
  exact mem_ℒp_stopped_process_of_mem_finset hτ hu n hbdd,
end

lemma integrable_stopped_process [locally_finite_order_bot ι] (hτ : is_stopping_time ℱ τ)
  (hu : ∀ n, integrable (u n) μ) (n : ι) :
  integrable (stopped_process u τ n) μ :=
integrable_stopped_process_of_mem_finset hτ hu n (λ ω h, finset.mem_Iio.mpr h)

end stopped_process

end stopped_value_of_mem_finset

section adapted_stopped_process

variables [topological_space β] [pseudo_metrizable_space β]
  [linear_order ι]
  [topological_space ι] [second_countable_topology ι] [order_topology ι]
  [measurable_space ι] [borel_space ι]
  {f : filtration ι m} {u : ι → Ω → β} {τ : Ω → ι}

/-- The stopped process of an adapted process with continuous paths is adapted. -/
lemma adapted.stopped_process [metrizable_space ι]
  (hu : adapted f u) (hu_cont : ∀ ω, continuous (λ i, u i ω)) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
((hu.prog_measurable_of_continuous hu_cont).stopped_process hτ).adapted

/-- If the indexing order has the discrete topology, then the stopped process of an adapted process
is adapted. -/
lemma adapted.stopped_process_of_discrete [discrete_topology ι]
  (hu : adapted f u) (hτ : is_stopping_time f τ) :
  adapted f (stopped_process u τ) :=
(hu.prog_measurable_of_discrete.stopped_process hτ).adapted

lemma adapted.strongly_measurable_stopped_process [metrizable_space ι]
  (hu : adapted f u) (hu_cont : ∀ ω, continuous (λ i, u i ω)) (hτ : is_stopping_time f τ)
  (n : ι) :
  strongly_measurable (stopped_process u τ n) :=
(hu.prog_measurable_of_continuous hu_cont).strongly_measurable_stopped_process hτ n

lemma adapted.strongly_measurable_stopped_process_of_discrete [discrete_topology ι]
  (hu : adapted f u) (hτ : is_stopping_time f τ) (n : ι) :
  strongly_measurable (stopped_process u τ n) :=
hu.prog_measurable_of_discrete.strongly_measurable_stopped_process hτ n

end adapted_stopped_process

section nat
/-! ### Filtrations indexed by `ℕ` -/

open filtration

variables {f : filtration ℕ m} {u : ℕ → Ω → β} {τ π : Ω → ℕ}

lemma stopped_value_sub_eq_sum [add_comm_group β] (hle : τ ≤ π) :
  stopped_value u π - stopped_value u τ =
  λ ω, (∑ i in finset.Ico (τ ω) (π ω), (u (i + 1) - u i)) ω :=
begin
  ext ω,
  rw [finset.sum_Ico_eq_sub _ (hle ω), finset.sum_range_sub, finset.sum_range_sub],
  simp [stopped_value],
end

lemma stopped_value_sub_eq_sum' [add_comm_group β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
  stopped_value u π - stopped_value u τ =
  λ ω, (∑ i in finset.range (N + 1),
    set.indicator {ω | τ ω ≤ i ∧ i < π ω} (u (i + 1) - u i)) ω :=
begin
  rw stopped_value_sub_eq_sum hle,
  ext ω,
  simp only [finset.sum_apply, finset.sum_indicator_eq_sum_filter],
  refine finset.sum_congr _ (λ _ _, rfl),
  ext i,
  simp only [finset.mem_filter, set.mem_set_of_eq, finset.mem_range, finset.mem_Ico],
  exact ⟨λ h, ⟨lt_trans h.2 (nat.lt_succ_iff.2 $ hbdd _), h⟩, λ h, h.2⟩
end

section add_comm_monoid
variables [add_comm_monoid β]

lemma stopped_value_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
  stopped_value u τ =
  λ x, (∑ i in finset.range (N + 1), set.indicator {ω | τ ω = i} (u i)) x :=
stopped_value_eq_of_mem_finset (λ ω, finset.mem_range_succ_iff.mpr (hbdd ω))

lemma stopped_process_eq (n : ℕ) :
  stopped_process u τ n =
  set.indicator {a | n ≤ τ a} (u n) + ∑ i in finset.range n, set.indicator {ω | τ ω = i} (u i) :=
begin
  rw stopped_process_eq'' n,
  swap, { apply_instance, },
  congr' with i,
  rw [finset.mem_Iio, finset.mem_range],
end

lemma stopped_process_eq' (n : ℕ) :
  stopped_process u τ n =
  set.indicator {a | n + 1 ≤ τ a} (u n) +
    ∑ i in finset.range (n + 1), set.indicator {a | τ a = i} (u i) :=
begin
  have : {a | n ≤ τ a}.indicator (u n) =
    {a | n + 1 ≤ τ a}.indicator (u n) + {a | τ a = n}.indicator (u n),
  { ext x,
    rw [add_comm, pi.add_apply, ← set.indicator_union_of_not_mem_inter],
    { simp_rw [@eq_comm _ _ n, @le_iff_eq_or_lt _ _ n, nat.succ_le_iff],
      refl },
    { rintro ⟨h₁, h₂⟩,
      exact (nat.succ_le_iff.1 h₂).ne h₁.symm } },
  rw [stopped_process_eq, this, finset.sum_range_succ_comm, ← add_assoc],
end

end add_comm_monoid

end nat

section piecewise_const

variables [preorder ι] {𝒢 : filtration ι m} {τ η : Ω → ι} {i j : ι} {s : set Ω}
  [decidable_pred (∈ s)]

/-- Given stopping times `τ` and `η` which are bounded below, `set.piecewise s τ η` is also
a stopping time with respect to the same filtration. -/
lemma is_stopping_time.piecewise_of_le (hτ_st : is_stopping_time 𝒢 τ)
  (hη_st : is_stopping_time 𝒢 η) (hτ : ∀ ω, i ≤ τ ω) (hη : ∀ ω, i ≤ η ω)
  (hs : measurable_set[𝒢 i] s) :
  is_stopping_time 𝒢 (s.piecewise τ η) :=
begin
  intro n,
  have : {ω | s.piecewise τ η ω ≤ n} = (s ∩ {ω | τ ω ≤ n}) ∪ (sᶜ ∩ {ω | η ω ≤ n}),
  { ext1 ω,
    simp only [set.piecewise, set.mem_inter_iff, set.mem_set_of_eq, and.congr_right_iff],
    by_cases hx : ω ∈ s; simp [hx], },
  rw this,
  by_cases hin : i ≤ n,
  { have hs_n : measurable_set[𝒢 n] s, from 𝒢.mono hin _ hs,
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n)), },
  { have hτn : ∀ ω, ¬ τ ω ≤ n := λ ω hτn, hin ((hτ ω).trans hτn),
    have hηn : ∀ ω, ¬ η ω ≤ n := λ ω hηn, hin ((hη ω).trans hηn),
    simp [hτn, hηn], },
end

lemma is_stopping_time_piecewise_const (hij : i ≤ j) (hs : measurable_set[𝒢 i] s) :
  is_stopping_time 𝒢 (s.piecewise (λ _, i) (λ _, j)) :=
(is_stopping_time_const 𝒢 i).piecewise_of_le (is_stopping_time_const 𝒢 j)
  (λ x, le_rfl) (λ _, hij) hs

lemma stopped_value_piecewise_const {ι' : Type*} {i j : ι'} {f : ι' → Ω → ℝ} :
  stopped_value f (s.piecewise (λ _, i) (λ _, j)) = s.piecewise (f i) (f j) :=
by { ext ω, rw stopped_value, by_cases hx : ω ∈ s; simp [hx] }

lemma stopped_value_piecewise_const' {ι' : Type*} {i j : ι'} {f : ι' → Ω → ℝ} :
  stopped_value f (s.piecewise (λ _, i) (λ _, j)) = s.indicator (f i) + sᶜ.indicator (f j) :=
by { ext ω, rw stopped_value, by_cases hx : ω ∈ s; simp [hx] }

end piecewise_const

end measure_theory
