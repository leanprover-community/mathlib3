/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.signed_hahn

/-!
# Jordan decomposition

This file proves the existence and uniqueness of the Jordan decomposition for signed measures.
The Jordan decomposition theorem states that, given a signed measure `s`, there exists a
unique pair of mutually singular measures `μ` and `ν`, such that `s = μ - ν`.

The Jordan decomposition theorem for measures is a corollary of the Hahn decomposition theorem and
is useful for the Lebesgue decomposition theorem.

## Main definitions

* `measure_theory.jordan_decomposition`: a Jordan decomposition of a measurable space is a
  pair of mutually singular finite measures. We say `j` is a Jordan decomposition of a signed
  meausre `s` if `s = j.pos_part - j.neg_part`.
* `measure_theory.signed_measure.to_jordan_decomposition`: the Jordan decomposition of a
  signed measure.
* `measure_theory.signed_measure.to_jordan_decomposition_equiv`: is the `equiv` between
  `measure_theory.signed_measure` and `measure_theory.jordan_decomposition` formed by
  `measure_theory.signed_measure.to_jordan_decomposition`.

## Main results

* `measure_theory.signed_measure.to_signed_measure_to_jordan_decomposition` : the Jordan
  decomposition theorem.
* `measure_theory.jordan_decomposition.to_signed_measure_injective` : the Jordan decomposition of a
  signed measure is unique.

## Tags

Jordan decomposition theorem
-/

noncomputable theory
open_locale classical measure_theory ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

/-- A Jordan decomposition of a measurable space is a pair of mutually singular,
finite measures. -/
@[ext] structure jordan_decomposition (α : Type*) [measurable_space α] :=
(pos_part neg_part : measure α)
[pos_part_finite : is_finite_measure pos_part]
[neg_part_finite : is_finite_measure neg_part]
(mutually_singular : pos_part ⊥ₘ neg_part)

attribute [instance] jordan_decomposition.pos_part_finite
attribute [instance] jordan_decomposition.neg_part_finite

namespace jordan_decomposition

open measure vector_measure

variable (j : jordan_decomposition α)

instance : has_zero (jordan_decomposition α) :=
{ zero := ⟨0, 0, mutually_singular.zero⟩ }

instance : inhabited (jordan_decomposition α) :=
{ default := 0 }

instance : has_neg (jordan_decomposition α) :=
{ neg := λ j, ⟨j.neg_part, j.pos_part, j.mutually_singular.symm⟩ }

@[simp] lemma zero_pos_part : (0 : jordan_decomposition α).pos_part = 0 := rfl
@[simp] lemma zero_neg_part : (0 : jordan_decomposition α).neg_part = 0 := rfl

@[simp] lemma neg_pos_part : (-j).pos_part = j.neg_part := rfl
@[simp] lemma neg_neg_part : (-j).neg_part = j.pos_part := rfl

/-- The signed measure associated with a Jordan decomposition. -/
def to_signed_measure : signed_measure α :=
j.pos_part.to_signed_measure - j.neg_part.to_signed_measure

lemma to_signed_measure_zero : (0 : jordan_decomposition α).to_signed_measure = 0 :=
begin
  ext1 i hi,
  erw [to_signed_measure, to_signed_measure_sub_apply hi, sub_self, zero_apply],
end

lemma to_signed_measure_neg : (-j).to_signed_measure = -j.to_signed_measure :=
begin
  ext1 i hi,
  rw [neg_apply, to_signed_measure, to_signed_measure,
      to_signed_measure_sub_apply hi, to_signed_measure_sub_apply hi, neg_sub],
  refl,
end

/-- A Jordan decomposition provides a Hahn decomposition. -/
lemma exists_compl_positive_negative :
  ∃ S : set α, measurable_set S ∧
    j.to_signed_measure ≤[S] 0 ∧ 0 ≤[Sᶜ] j.to_signed_measure ∧
    j.pos_part S = 0 ∧ j.neg_part Sᶜ = 0 :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutually_singular,
  refine ⟨S, hS₁, _, _, hS₂, hS₃⟩,
  { refine restrict_le_restrict_of_subset_le _ _ (λ A hA hA₁, _),
    rw [to_signed_measure, to_signed_measure_sub_apply hA,
        show j.pos_part A = 0, by exact nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁),
        ennreal.zero_to_real, zero_sub, neg_le, zero_apply, neg_zero],
    exact ennreal.to_real_nonneg },
  { refine restrict_le_restrict_of_subset_le _ _ (λ A hA hA₁, _),
    rw [to_signed_measure, to_signed_measure_sub_apply hA,
        show j.neg_part A = 0, by exact nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁),
        ennreal.zero_to_real, sub_zero],
    exact ennreal.to_real_nonneg },
end

end jordan_decomposition

namespace signed_measure

open measure vector_measure jordan_decomposition classical

variables {s : signed_measure α} {μ ν : measure α} [is_finite_measure μ] [is_finite_measure ν]

/-- Given a signed measure `s`, `s.to_jordan_decomposition` is the Jordan decomposition `j`,
such that `s = j.to_signed_measure`. This property is known as the Jordan decomposition
theorem, and is shown by
`measure_theory.signed_measure.to_signed_measure_to_jordan_decomposition`. -/
def to_jordan_decomposition (s : signed_measure α) : jordan_decomposition α :=
let i := some s.exists_compl_positive_negative in
let hi := some_spec s.exists_compl_positive_negative in
{ pos_part := s.to_measure_of_zero_le i hi.1 hi.2.1,
  neg_part := s.to_measure_of_le_zero iᶜ hi.1.compl hi.2.2,
  pos_part_finite := infer_instance,
  neg_part_finite := infer_instance,
  mutually_singular :=
  begin
    refine ⟨iᶜ, hi.1.compl, _, _⟩,
    { rw [to_measure_of_zero_le_apply _ _ hi.1 hi.1.compl], simpa },
    { rw [to_measure_of_le_zero_apply _ _ hi.1.compl hi.1.compl.compl], simpa }
  end }

lemma to_jordan_decomposition_spec (s : signed_measure α) :
  ∃ (i : set α) (hi₁ : measurable_set i) (hi₂ : 0 ≤[i] s) (hi₃ : s ≤[iᶜ] 0),
    s.to_jordan_decomposition.pos_part = s.to_measure_of_zero_le i hi₁ hi₂ ∧
    s.to_jordan_decomposition.neg_part = s.to_measure_of_le_zero iᶜ hi₁.compl hi₃ :=
begin
  set i := some s.exists_compl_positive_negative,
  obtain ⟨hi₁, hi₂, hi₃⟩ := some_spec s.exists_compl_positive_negative,
  exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩,
end

/-- **The Jordan decomposition theorem**: Given a signed measure `s`, there exists a pair of
mutually singular measures `μ` and `ν` such that `s = μ - ν`. In this case, the measures `μ`
and `ν` are given by `s.to_jordan_decomposition.pos_part` and
`s.to_jordan_decomposition.neg_part` respectively.

Note that we use `measure_theory.jordan_decomposition.to_signed_measure` to represent the
signed measure corresponding to
`s.to_jordan_decomposition.pos_part - s.to_jordan_decomposition.neg_part`. -/
@[simp] lemma to_signed_measure_to_jordan_decomposition (s : signed_measure α) :
  s.to_jordan_decomposition.to_signed_measure = s :=
begin
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.to_jordan_decomposition_spec,
  simp only [jordan_decomposition.to_signed_measure, hμ, hν],
  ext k hk,
  rw [to_signed_measure_sub_apply hk, to_measure_of_zero_le_apply _ hi₂ hi₁ hk,
      to_measure_of_le_zero_apply _ hi₃ hi₁.compl hk],
  simp only [ennreal.coe_to_real, subtype.coe_mk, ennreal.some_eq_coe, sub_neg_eq_add],
  rw [← of_union _ (measurable_set.inter hi₁ hk) (measurable_set.inter hi₁.compl hk),
      set.inter_comm i, set.inter_comm iᶜ, set.inter_union_compl _ _],
  { apply_instance },
  { rintro x ⟨⟨hx₁, _⟩, hx₂, _⟩,
    exact false.elim (hx₂ hx₁) }
end

section

variables {u v w : set α}

/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a positive set `u`. -/
lemma subset_positive_null_set
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : 0 ≤[u] s) (hw₁ : s w = 0) (hw₂ : w ⊆ u) (hwt : v ⊆ w) : s v = 0 :=
begin
  have : s v + s (w \ v) = 0,
  { rw [← hw₁, ← of_union set.disjoint_diff hv (hw.diff hv),
        set.union_diff_self, set.union_eq_self_of_subset_left hwt],
    apply_instance },
  have h₁ := nonneg_of_zero_le_restrict _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂)),
  have h₂ := nonneg_of_zero_le_restrict _
    (restrict_le_restrict_subset _ _ hu hsu ((w.diff_subset v).trans hw₂)),
  linarith,
end

/-- A subset `v` of a null-set `w` has zero measure if `w` is a subset of a negative set `u`. -/
lemma subset_negative_null_set
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : s ≤[u] 0) (hw₁ : s w = 0) (hw₂ : w ⊆ u) (hwt : v ⊆ w) : s v = 0 :=
begin
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu,
  have := subset_positive_null_set hu hv hw hsu,
  simp only [pi.neg_apply, neg_eq_zero, coe_neg] at this,
  exact this hw₁ hw₂ hwt,
end

/-- If the symmetric difference of two positive sets is a null-set, then so are the differences
between the two sets. -/
lemma of_diff_eq_zero_of_symm_diff_eq_zero_positive
  (hu : measurable_set u) (hv : measurable_set v)
  (hsu : 0 ≤[u] s) (hsv : 0 ≤[v] s) (hs : s (u Δ v) = 0) :
  s (u \ v) = 0 ∧ s (v \ u) = 0 :=
begin
  rw restrict_le_restrict_iff at hsu hsv,
  have a := hsu (hu.diff hv) (u.diff_subset v),
  have b := hsv (hv.diff hu) (v.diff_subset u),
  erw [of_union (set.disjoint_of_subset_left (u.diff_subset v) set.disjoint_diff)
        (hu.diff hv) (hv.diff hu)] at hs,
  rw zero_apply at a b,
  split,
  all_goals { linarith <|> apply_instance <|> assumption },
end

/-- If the symmetric difference of two negative sets is a null-set, then so are the differences
between the two sets. -/
lemma of_diff_eq_zero_of_symm_diff_eq_zero_negative
  (hu : measurable_set u) (hv : measurable_set v)
  (hsu : s ≤[u] 0) (hsv : s ≤[v] 0) (hs : s (u Δ v) = 0) :
  s (u \ v) = 0 ∧ s (v \ u) = 0 :=
begin
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu,
  rw [← s.neg_le_neg_iff _ hv, neg_zero] at hsv,
  have := of_diff_eq_zero_of_symm_diff_eq_zero_positive hu hv hsu hsv,
  simp only [pi.neg_apply, neg_eq_zero, coe_neg] at this,
  exact this hs,
end

lemma of_inter_eq_of_symm_diff_eq_zero_positive
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : 0 ≤[u] s) (hsv : 0 ≤[v] s) (hs : s (u Δ v) = 0) :
  s (w ∩ u) = s (w ∩ v) :=
begin
  have hwuv : s ((w ∩ u) Δ (w ∩ v)) = 0,
  { refine subset_positive_null_set (hu.union hv) ((hw.inter hu).symm_diff (hw.inter hv))
      (hu.symm_diff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs _ _,
    { exact symm_diff_le_sup u v },
    { rintro x (⟨⟨hxw, hxu⟩, hx⟩ | ⟨⟨hxw, hxv⟩, hx⟩);
      rw [set.mem_inter_eq, not_and] at hx,
      { exact or.inl ⟨hxu, hx hxw⟩ },
      { exact or.inr ⟨hxv, hx hxw⟩ } } },
  obtain ⟨huv, hvu⟩ := of_diff_eq_zero_of_symm_diff_eq_zero_positive
    (hw.inter hu) (hw.inter hv)
    (restrict_le_restrict_subset _ _ hu hsu (w.inter_subset_right u))
    (restrict_le_restrict_subset _ _ hv hsv (w.inter_subset_right v)) hwuv,
  rw [← of_diff_of_diff_eq_zero (hw.inter hu) (hw.inter hv) hvu, huv, zero_add]
end

lemma of_inter_eq_of_symm_diff_eq_zero_negative
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : s ≤[u] 0) (hsv : s ≤[v] 0) (hs : s (u Δ v) = 0) :
  s (w ∩ u) = s (w ∩ v) :=
begin
  rw [← s.neg_le_neg_iff _ hu, neg_zero] at hsu,
  rw [← s.neg_le_neg_iff _ hv, neg_zero] at hsv,
  have := of_inter_eq_of_symm_diff_eq_zero_positive hu hv hw hsu hsv,
  simp only [pi.neg_apply, neg_inj, neg_eq_zero, coe_neg] at this,
  exact this hs,
end

end

end signed_measure

namespace jordan_decomposition

open measure vector_measure signed_measure function

private lemma eq_of_pos_part_eq_pos_part {j₁ j₂ : jordan_decomposition α}
  (hj : j₁.pos_part = j₂.pos_part) (hj' : j₁.to_signed_measure = j₂.to_signed_measure) :
  j₁ = j₂ :=
begin
  ext1,
  { exact hj },
  { rw ← to_signed_measure_eq_to_signed_measure_iff,
    suffices : j₁.pos_part.to_signed_measure - j₁.neg_part.to_signed_measure =
      j₁.pos_part.to_signed_measure - j₂.neg_part.to_signed_measure,
    { exact sub_right_inj.mp this },
    convert hj' }
end

/-- The Jordan decomposition of a signed measure is unique. -/
theorem to_signed_measure_injective :
  injective $ @jordan_decomposition.to_signed_measure α _ :=
begin
  /- The main idea is that two Jordan decompositions of a signed measure provide two
  Hahn decompositions for that measure. Then, from `of_symm_diff_compl_positive_negative`,
  the symmetric difference of the two Hahn decompositions has measure zero, thus, allowing us to
  show the equality of the underlying measures of the Jordan decompositions. -/
  intros j₁ j₂ hj,
  -- obtain the two Hahn decompositions from the Jordan decompositions
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ := j₁.exists_compl_positive_negative,
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ := j₂.exists_compl_positive_negative,
  rw ← hj at hT₂ hT₃,
  -- the symmetric differences of the two Hahn decompositions have measure zero
  obtain ⟨hST₁, -⟩ := of_symm_diff_compl_positive_negative hS₁.compl hT₁.compl
    ⟨hS₃, (compl_compl S).symm ▸ hS₂⟩ ⟨hT₃, (compl_compl T).symm ▸ hT₂⟩,
  -- it suffices to show the Jordan decompositions have the same positive parts
  refine eq_of_pos_part_eq_pos_part _ hj,
  ext1 i hi,
  -- we see that the positive parts of the two Jordan decompositions are equal to their
  -- associated signed measures restricted on their associated Hahn decompositions
  have hμ₁ : (j₁.pos_part i).to_real = j₁.to_signed_measure (i ∩ Sᶜ),
  { rw [to_signed_measure, to_signed_measure_sub_apply (hi.inter hS₁.compl),
        show j₁.neg_part (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1
          (hS₅ ▸ measure_mono (set.inter_subset_right _ _)),
        ennreal.zero_to_real, sub_zero],
    conv_lhs { rw ← set.inter_union_compl i S },
    rw [measure_union, show j₁.pos_part (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1
          (hS₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add],
    { refine set.disjoint_of_subset_left (set.inter_subset_right _ _)
        (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
    { exact hi.inter hS₁ },
    { exact hi.inter hS₁.compl } },
  have hμ₂ : (j₂.pos_part i).to_real = j₂.to_signed_measure (i ∩ Tᶜ),
  { rw [to_signed_measure, to_signed_measure_sub_apply (hi.inter hT₁.compl),
        show j₂.neg_part (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1
          (hT₅ ▸ measure_mono (set.inter_subset_right _ _)),
        ennreal.zero_to_real, sub_zero],
    conv_lhs { rw ← set.inter_union_compl i T },
    rw [measure_union, show j₂.pos_part (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1
          (hT₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add],
    { exact set.disjoint_of_subset_left (set.inter_subset_right _ _)
        (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
    { exact hi.inter hT₁ },
    { exact hi.inter hT₁.compl } },
  -- since the two signed measures associated with the Jordan decompositions are the same,
  -- and the symmetric difference of the Hahn decompositions have measure zero, the result follows
  rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _),
      hμ₁, hμ₂, ← hj],
  exact of_inter_eq_of_symm_diff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁,
  all_goals { apply_instance },
end

@[simp]
lemma to_jordan_decomposition_to_signed_measure (j : jordan_decomposition α) :
  (j.to_signed_measure).to_jordan_decomposition = j :=
(@to_signed_measure_injective _ _ j (j.to_signed_measure).to_jordan_decomposition (by simp)).symm

end jordan_decomposition

namespace signed_measure

open jordan_decomposition

/-- `measure_theory.signed_measure.to_jordan_decomposition` and
`measure_theory.jordan_decomposition.to_signed_measure` form a `equiv`. -/
@[simps apply symm_apply]
def to_jordan_decomposition_equiv (α : Type*) [measurable_space α] :
  signed_measure α ≃ jordan_decomposition α :=
{ to_fun := to_jordan_decomposition,
  inv_fun := to_signed_measure,
  left_inv := to_signed_measure_to_jordan_decomposition,
  right_inv := to_jordan_decomposition_to_signed_measure }

lemma to_jordan_decomposition_zero : (0 : signed_measure α).to_jordan_decomposition = 0 :=
begin
  apply to_signed_measure_injective,
  simp [to_signed_measure_zero],
end

lemma to_jordan_decomposition_neg (s : signed_measure α) :
  (-s).to_jordan_decomposition = -s.to_jordan_decomposition :=
begin
  apply to_signed_measure_injective,
  simp [to_signed_measure_neg],
end

/-- The total variation of a signed measure. -/
def total_variation (s : signed_measure α) : measure α :=
s.to_jordan_decomposition.pos_part + s.to_jordan_decomposition.neg_part

lemma total_variation_zero : (0 : signed_measure α).total_variation = 0 :=
by simp [total_variation, to_jordan_decomposition_zero]

lemma total_variation_neg (s : signed_measure α) : (-s).total_variation = s.total_variation :=
by simp [total_variation, to_jordan_decomposition_neg, add_comm]

lemma absolutely_continuous_iff (s : signed_measure α) (μ : vector_measure α ℝ≥0∞) :
  s ≪ μ ↔ s.total_variation ≪ μ.ennreal_to_measure :=
begin
  split; intro h,
  { refine measure.absolutely_continuous.mk (λ S hS₁ hS₂, _),
    obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.to_jordan_decomposition_spec,
    rw [total_variation, measure.add_apply, hpos, hneg,
        to_measure_of_zero_le_apply _ _ _ hS₁, to_measure_of_le_zero_apply _ _ _ hS₁],
    rw ← vector_measure.absolutely_continuous.ennreal_to_measure at h,
    simp [h (measure_mono_null (i.inter_subset_right S) hS₂),
          h (measure_mono_null (iᶜ.inter_subset_right S) hS₂)],
    refl },
  { refine vector_measure.absolutely_continuous.mk (λ S hS₁ hS₂, _),
    rw ← vector_measure.ennreal_to_measure_apply hS₁ at hS₂,
    have := h hS₂,
    rw [total_variation, measure.add_apply, add_eq_zero_iff] at this,
    rw [← s.to_signed_measure_to_jordan_decomposition, to_signed_measure,
        measure.to_signed_measure_sub_apply hS₁, this.1, this.2, ennreal.zero_to_real, sub_zero] }
end

lemma total_variation_absolutely_continuous_iff (s : signed_measure α) (μ : measure α) :
  s.total_variation ≪ μ ↔
  s.to_jordan_decomposition.pos_part ≪ μ ∧ s.to_jordan_decomposition.neg_part ≪ μ :=
begin
  split; intro h,
  { split, all_goals
    { refine measure.absolutely_continuous.mk (λ S hS₁ hS₂, _),
      have := h hS₂,
      rw [total_variation, measure.add_apply, add_eq_zero_iff] at this },
    exacts [this.1, this.2] },
  { refine measure.absolutely_continuous.mk (λ S hS₁ hS₂, _),
    rw [total_variation, measure.add_apply, h.1 hS₂, h.2 hS₂, add_zero] }
end

end signed_measure

end measure_theory
