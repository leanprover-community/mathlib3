/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Counting measure on a set.
-/

import measure_theory.measure_space

universes u

variables (α : Type u)

namespace measure_theory

section count

local attribute [instance, priority 0] classical.dec

noncomputable def count (x : set α) : ennreal :=
if h : x.finite then h.to_finset.card else ⊤

variables {α}

theorem count_of_finite {x : set α} (h : x.finite) : count α x = h.to_finset.card :=
dif_pos h

theorem count_of_infinite {x : set α} (h : ¬ x.finite) : count α x = ⊤ :=
dif_neg h

theorem count_empty : count α ∅ = 0 :=
by rw [count, dif_pos set.finite_empty, ← ennreal.coe_nat, ennreal.coe_eq_zero,
    nat.cast_eq_zero, finset.card_eq_zero, finset.ext]; intro;
rw [set.finite.mem_to_finset]; refl

theorem count_mono {s t : set α} (H : s ⊆ t) : count α s ≤ count α t :=
begin
  conv_rhs { rw count }; split_ifs,
  { rw [count, dif_pos (set.finite_subset h H), ← ennreal.coe_nat, ← ennreal.coe_nat,
      ennreal.coe_le_coe, nat.cast_le],
    apply finset.card_le_of_subset, intros x,
    rw [set.finite.mem_to_finset, set.finite.mem_to_finset], exact @H x },
  exact lattice.le_top
end

theorem count_insert {a : α} {s : set α} (has : a ∉ s) : count α (insert a s) = count α s + 1 :=
begin
  by_cases hfs : s.finite,
  { have : a ∉ set.finite.to_finset hfs, { rwa set.finite.mem_to_finset },
    rw [count_of_finite (set.finite_insert a hfs), set.to_finset_insert, finset.card_insert_of_not_mem this,
        nat.cast_add, nat.cast_one, ← count_of_finite hfs] },
  have hf : ¬(insert a s).finite := mt (λ h, set.finite_subset h $ set.subset_insert a s) hfs,
  rw [count_of_infinite hfs, ennreal.top_add, count_of_infinite hf]
end

theorem set.nat_of_not_finite {s : set α} (hfs : ¬s.finite) :
  ∃ f : ℕ → α, function.injective f ∧ ∀ n, f n ∈ s :=
begin
  have : ∀ t : finset α, ∃ x ∈ s, x ∉ t,
  { intros t, by_contradiction h, simp only [not_exists, not_not] at h,
    exact hfs (set.finite_subset (finset.finite_to_set t) h) },
  choose f hf1 hf2,
  refine ⟨nat.strong_rec' (λ n ih, f $ (finset.range n).attach.image $ λ x, _), _, _⟩,
  { exact ih x.1 (finset.mem_range.1 x.2) },
  { intros m n h, apply linarith.eq_of_not_lt_of_not_gt,
    { intros hmn, conv_rhs at h { rw nat.strong_rec' },
      apply hf2, rw [← h, finset.mem_image], use [⟨m, finset.mem_range.2 hmn⟩, finset.mem_attach _ _] },
    { intros hnm, conv_lhs at h { rw nat.strong_rec' },
      apply hf2, rw [h, finset.mem_image], use [⟨n, finset.mem_range.2 hnm⟩, finset.mem_attach _ _] } },
  { intros n, rw nat.strong_rec', exact hf1 _ }
end

theorem set.finset_of_not_finite {s : set α} (hfs : ¬s.finite) (n : ℕ) :
  ∃ t : finset α, ↑t ⊆ s ∧ t.card = n :=
let ⟨f, hf1, hf2⟩ := set.nat_of_not_finite hfs in
⟨(finset.range n).image f,
λ x (hx : _ ∈ finset.image _ _), let ⟨m, hm, hfmx⟩ := finset.mem_image.1 hx in hfmx ▸ hf2 m,
(finset.card_image_of_injective _ hf1).trans $ finset.card_range n⟩

theorem count_eq_tsum {s : set α} : count α s = ∑ x : α, if x ∈ s then 1 else 0 :=
begin
  have hf : ∀ s : finset α, (s.card : ennreal) = ∑ x : α, if x ∈ s then 1 else 0,
  { intros s,
    calc  (s.card : ennreal)
        = add_monoid.smul s.card 1 : by rw add_monoid.smul_one
    ... = s.sum (λ x, 1) : by rw finset.sum_const
    ... = s.sum (λ x, if x ∈ s then 1 else 0) : finset.sum_congr rfl (λ x hxs, by rw if_pos hxs)
    ... = ∑ x : α, if x ∈ s then 1 else 0 : by rw tsum_eq_sum; intros x hxs; rw if_neg hxs },
  by_cases hfs : s.finite,
  { calc  count α s
        = hfs.to_finset.card : count_of_finite hfs
    ... = ∑ x : α, if x ∈ hfs.to_finset then 1 else 0 : hf hfs.to_finset
    ... = ∑ x : α, if x ∈ s then 1 else 0 : begin
      congr' 1, ext, split_ifs with h1 h2 h2; rw set.finite.mem_to_finset at h1,
      exacts [absurd h1 h2, absurd h2 h1]
    end },
  rw count_of_infinite hfs, symmetry,
  by_contradiction ht,
  cases ennreal.exists_nat_gt ht with n hn,
  rcases set.finset_of_not_finite hfs n with ⟨t, hts, htn⟩,
  refine lt_irrefl (∑ x : α, if x ∈ s then 1 else 0 : ennreal) _,
  have : ∀ x : α, (if x ∈ t then 1 else 0 : ennreal) ≤ if x ∈ s then 1 else 0,
  { intros x, by_cases hxt : x ∈ t,
    { rw [if_pos hxt, if_pos (hts hxt)], exact le_refl _ },
    { rw if_neg hxt, exact zero_le _ } },
  calc  (∑ x : α, if x ∈ s then 1 else 0 : ennreal)
      < n : hn
  ... = t.card : by rw htn
  ... = ∑ x : α, if x ∈ t then 1 else 0 : hf t
  ... ≤ ∑ x : α, if x ∈ s then 1 else 0 : ennreal.tsum_le_tsum this
end

theorem count_Union_nat (f : ℕ → set α) : count α (⋃ i, f i) ≤ ∑ i, count α (f i) :=
have ∀ x : α, (if (x ∈ ⋃ i, f i) then 1 else 0 : ennreal) ≤ ∑ i, if x ∈ f i then 1 else 0,
begin
  intros x, by_cases hx : x ∈ ⋃ i, f i,
  { rw if_pos hx, cases set.mem_Union.1 hx with i hxi,
    have : (ite (x ∈ f i) 1 0 : ennreal) = 1 := if_pos hxi,
    conv_lhs { rw ← this }, exact ennreal.le_tsum i },
  rw if_neg hx, exact zero_le _
end,
calc  count α (⋃ i, f i)
    = ∑ x : α, if x ∈ ⋃ i, f i then 1 else 0 : count_eq_tsum
... ≤ ∑ x : α, ∑ i, if x ∈ f i then 1 else 0 : ennreal.tsum_le_tsum this
... = ∑ i, ∑ x : α, if x ∈ f i then 1 else 0 : ennreal.tsum_comm
... = ∑ i, count α (f i) : by simp only [count_eq_tsum]

theorem count_Union_of_disjoint (f : ℕ → set α) (hf : pairwise (disjoint on f)) :
  count α (⋃ i, f i) = ∑ i, count α (f i) :=
have ∀ x : α, (if (x ∈ ⋃ i, f i) then 1 else 0 : ennreal) = ∑ i, if x ∈ f i then 1 else 0,
begin
  intros x, by_cases hx : x ∈ ⋃ i, f i,
  { rw if_pos hx, cases set.mem_Union.1 hx with i hxi,
    have : (ite (x ∈ f i) 1 0 : ennreal) = 1 := if_pos hxi,
    conv_lhs { rw ← this }, rw tsum_eq_single,
    intros j hji, rw if_neg, intro hxj,
    exact set.disjoint_iff.1 (hf j i hji) ⟨hxj, hxi⟩ },
  have : ∀ n, x ∉ f n := λ n hn, hx (set.mem_Union.2 ⟨n, hn⟩),
  rw [if_neg hx, tsum_eq_sum, finset.sum_empty], intros, rw if_neg (this _)
end,
calc  count α (⋃ i, f i)
    = ∑ x : α, if x ∈ ⋃ i, f i then 1 else 0 : count_eq_tsum
... = ∑ x : α, ∑ i, if x ∈ f i then 1 else 0 : congr_arg tsum (funext this)
... = ∑ i, ∑ x : α, if x ∈ f i then 1 else 0 : ennreal.tsum_comm
... = ∑ i, count α (f i) : by simp only [count_eq_tsum]

end count

noncomputable def counting_measure : measure_space α :=
{ μ := { measure_of := count α,
    empty := count_empty,
    mono := λ _ _, count_mono,
    Union_nat := count_Union_nat,
    m_Union := λ f _ hf, count_Union_of_disjoint f hf,
    trimmed := outer_measure.ext $ λ s, @@outer_measure.trim_eq ⊤ _ measurable_space.is_measurable_top },
  .. (⊤ : measurable_space α) }

end measure_theory
