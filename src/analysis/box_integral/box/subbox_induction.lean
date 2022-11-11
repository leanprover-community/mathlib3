/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.box.basic
import analysis.specific_limits.basic

/-!
# Induction on subboxes

In this file we prove the following induction principle for `box_integral.box`, see
`box_integral.box.subbox_induction_on`. Let `p` be a predicate on `box_integral.box ι`, let `I` be a
box. Suppose that the following two properties hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it is true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true.

## Tags

rectangular box, induction
-/

open set finset function filter metric
open_locale classical topological_space filter ennreal
noncomputable theory

namespace box_integral

namespace box

variables {ι : Type*} {I J : box ι}

/-- For a box `I`, the hyperplanes passing through its center split `I` into `2 ^ card ι` boxes.
`box_integral.box.split_center_box I s` is one of these boxes. See also
`box_integral.partition.split_center` for the corresponding `box_integral.partition`. -/
def split_center_box (I : box ι) (s : set ι) : box ι :=
{ lower := s.piecewise (λ i, (I.lower i + I.upper i) / 2) I.lower,
  upper := s.piecewise I.upper (λ i, (I.lower i + I.upper i) / 2),
  lower_lt_upper := λ i, by { dunfold set.piecewise, split_ifs;
    simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper] } }

lemma mem_split_center_box {s : set ι} {y : ι → ℝ} :
  y ∈ I.split_center_box s ↔ y ∈ I ∧ ∀ i, (I.lower i + I.upper i) / 2 < y i ↔ i ∈ s :=
begin
  simp only [split_center_box, mem_def, ← forall_and_distrib],
  refine forall_congr (λ i, _),
  dunfold set.piecewise,
  split_ifs with hs; simp only [hs, iff_true, iff_false, not_lt],
  exacts [⟨λ H, ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩,
    λ H, ⟨H.2, H.1.2⟩⟩,
    ⟨λ H, ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩,
      λ H, ⟨H.1.1, H.2⟩⟩]
end

lemma split_center_box_le (I : box ι) (s : set ι) : I.split_center_box s ≤ I :=
λ x hx, (mem_split_center_box.1 hx).1

lemma disjoint_split_center_box (I : box ι) {s t : set ι} (h : s ≠ t) :
  disjoint (I.split_center_box s : set (ι → ℝ)) (I.split_center_box t) :=
begin
  rintro y ⟨hs, ht⟩, apply h,
  ext i,
  rw [mem_coe, mem_split_center_box] at hs ht,
  rw [← hs.2, ← ht.2]
end

lemma injective_split_center_box (I : box ι) : injective I.split_center_box :=
λ s t H, by_contra $ λ Hne, (I.disjoint_split_center_box Hne).ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp] lemma exists_mem_split_center_box {I : box ι} {x : ι → ℝ} :
  (∃ s, x ∈ I.split_center_box s) ↔ x ∈ I :=
⟨λ ⟨s, hs⟩, I.split_center_box_le s hs,
  λ hx, ⟨{i | (I.lower i + I.upper i) / 2 < x i}, mem_split_center_box.2 ⟨hx, λ i, iff.rfl⟩⟩⟩

/-- `box_integral.box.split_center_box` bundled as a `function.embedding`. -/
@[simps] def split_center_box_emb (I : box ι) : set ι ↪ box ι :=
⟨split_center_box I, injective_split_center_box I⟩

@[simp] lemma Union_coe_split_center_box (I : box ι) :
  (⋃ s, (I.split_center_box s : set (ι → ℝ))) = I :=
by { ext x, simp }

@[simp] lemma upper_sub_lower_split_center_box (I : box ι) (s : set ι) (i : ι) :
  (I.split_center_box s).upper i - (I.split_center_box s).lower i = (I.upper i - I.lower i) / 2 :=
by by_cases hs : i ∈ s; field_simp [split_center_box, hs, mul_two, two_mul]

/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* `H_ind` : Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split
  it into `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.

* `H_nhds` : For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within
  `I.Icc` such that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I`
  with a coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `box_integral.box.subbox_induction_on` for a version using
`box_integral.prepartition.split_center` instead of `box_integral.box.split_center_box`.

The proof still works if we assume `H_ind` only for subboxes `J ≤ I` that are homothetic to `I` with
a coefficient of the form `2⁻ᵐ` but we do not need this generalization yet. -/
@[elab_as_eliminator]
lemma subbox_induction_on' {p : box ι → Prop} (I : box ι)
  (H_ind : ∀ J ≤ I, (∀ s, p (split_center_box J s)) → p J)
  (H_nhds : ∀ z ∈ I.Icc, ∃ (U ∈ 𝓝[I.Icc] z), ∀ (J ≤ I) (m : ℕ), z ∈ J.Icc → J.Icc ⊆ U →
    (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
  p I :=
begin
  by_contra hpI,
  -- First we use `H_ind` to construct a decreasing sequence of boxes such that `∀ m, ¬p (J m)`.
  replace H_ind := λ J hJ, not_imp_not.2 (H_ind J hJ),
  simp only [exists_imp_distrib, not_forall] at H_ind,
  choose! s hs using H_ind,
  set J : ℕ → box ι := λ m, (λ J, split_center_box J (s J))^[m] I,
  have J_succ : ∀ m, J (m + 1) = split_center_box (J m) (s $ J m) := λ m, iterate_succ_apply' _ _ _,
  -- Now we prove some properties of `J`
  have hJmono : antitone J,
    from antitone_nat_of_succ_le (λ n, by simpa [J_succ] using split_center_box_le _ _),
  have hJle : ∀ m, J m ≤ I, from λ m, hJmono (zero_le m),
  have hJp : ∀ m, ¬p (J m),
    from λ m, nat.rec_on m hpI (λ m, by simpa only [J_succ] using hs (J m) (hJle m)),
  have hJsub : ∀ m i, (J m).upper i - (J m).lower i = (I.upper i - I.lower i) / 2 ^ m,
  { intros m i, induction m with m ihm, { simp [J] },
    simp only [pow_succ', J_succ, upper_sub_lower_split_center_box, ihm, div_div] },
  have h0 : J 0 = I, from rfl,
  -- Now we clear unneeded assumptions
  clear_value J, clear hpI hs J_succ s,
  -- Let `z` be the unique common point of all `(J m).Icc`. Then `H_nhds` proves `p (J m)` for
  -- sufficiently large `m`. This contradicts `hJp`.
  set z : ι → ℝ := ⨆ m, (J m).lower,
  have hzJ : ∀ m, z ∈ (J m).Icc,
    from mem_Inter.1 (csupr_mem_Inter_Icc_of_antitone_Icc
      ((@box.Icc ι).monotone.comp_antitone hJmono) (λ m, (J m).lower_le_upper)),
  have hJl_mem : ∀ m, (J m).lower ∈ I.Icc, from λ m, le_iff_Icc.1 (hJle m) (J m).lower_mem_Icc,
  have hJu_mem : ∀ m, (J m).upper ∈ I.Icc, from λ m, le_iff_Icc.1 (hJle m) (J m).upper_mem_Icc,
  have hJlz : tendsto (λ m, (J m).lower) at_top (𝓝 z),
    from tendsto_at_top_csupr (antitone_lower.comp hJmono)
      ⟨I.upper, λ x ⟨m, hm⟩, hm ▸ (hJl_mem m).2⟩,
  have hJuz : tendsto (λ m, (J m).upper) at_top (𝓝 z),
  { suffices : tendsto (λ m, (J m).upper - (J m).lower) at_top (𝓝 0), by simpa using hJlz.add this,
    refine tendsto_pi_nhds.2 (λ i, _),
    simpa [hJsub] using tendsto_const_nhds.div_at_top
      (tendsto_pow_at_top_at_top_of_one_lt (@one_lt_two ℝ _ _)) },
  replace hJlz : tendsto (λ m, (J m).lower) at_top (𝓝[Icc I.lower I.upper] z),
    from tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJlz
      (eventually_of_forall hJl_mem),
  replace hJuz : tendsto (λ m, (J m).upper) at_top (𝓝[Icc I.lower I.upper] z),
    from tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJuz
      (eventually_of_forall hJu_mem),
  rcases H_nhds z (h0 ▸ hzJ 0) with ⟨U, hUz, hU⟩,
  rcases (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists with ⟨m, hUm⟩,
  exact hJp m (hU (J m) (hJle m) m (hzJ m) hUm (hJsub m))
end

end box

end box_integral
