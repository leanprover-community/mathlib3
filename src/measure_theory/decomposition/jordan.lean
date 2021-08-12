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

## Main results
* `signed_measure.exists_mutually_sigular_eq_sub` : the Jordan decomposition theorem.
* `signed_measure.mutually_sigular_eq_sub_unique` : the Jordan decomposition of a signed measure
  is unique.

## Tags

Jordan decomposition theorem
-/

noncomputable theory
open_locale classical measure_theory

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace signed_measure

open measure vector_measure

variables {s : signed_measure α} {μ ν : measure α} [hμ : finite_measure μ] [hν : finite_measure ν]

/-- **The Jordan decomposition theorem**: Given a signed measure `s`, there exists
a pair of mutually singular measures `μ` and `ν` such that `s = μ - ν`.

Note that we use `measure.sub_to_signed_measure μ ν` to represent the signed measure corresponding
to `μ - ν`. -/
theorem exists_mutually_sigular_eq_sub (s : signed_measure α) :
  ∃ (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν],
    μ ⊥ₘ ν ∧ s = @sub_to_signed_measure _ _ μ ν hμ hν :=
begin
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative,
  have hi₄ := measurable_set.compl hi₁,
  refine ⟨s.to_measure_of_zero_le i hi₁ hi₂, s.to_measure_of_le_zero iᶜ hi₄ hi₃, _⟩,
  refine ⟨infer_instance, infer_instance, _, _⟩,
  { refine ⟨iᶜ, hi₄, _, _⟩,
    { rw [to_measure_of_zero_le_apply _ _ hi₁ hi₄], simpa },
    { rw [to_measure_of_le_zero_apply _ _ hi₄ (measurable_set.compl hi₄)], simpa } },
  { ext k hk,
    rw [sub_to_signed_measure_apply hk, to_measure_of_zero_le_apply _ hi₂ hi₁ hk,
        to_measure_of_le_zero_apply _ hi₃ hi₄ hk],
    simp only [ennreal.coe_to_real, subtype.coe_mk, ennreal.some_eq_coe, sub_neg_eq_add],
    rw [← of_union _ (measurable_set.inter hi₁ hk) (measurable_set.inter hi₄ hk),
        set.inter_comm i, set.inter_comm iᶜ, set.inter_union_compl _ _],
    { apply_instance },
    { rintro x ⟨⟨hx₁, _⟩, hx₂, _⟩,
      exact false.elim (hx₂ hx₁) } }
end

/-- A Jordan decomposition provides a Hahn decomposition. -/
lemma exists_compl_positive_negative_of_exists_mutually_sigular_sub
  (h : μ ⊥ₘ ν ∧ s = @sub_to_signed_measure _ _ μ ν hμ hν) :
  ∃ S : set α, measurable_set S ∧ s ≤[S] 0 ∧ 0 ≤[Sᶜ] s ∧ μ S = 0 ∧ ν Sᶜ = 0 :=
begin
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, h₁⟩ := h,
  refine ⟨S, hS₁, _, _, hS₂, hS₃⟩,
  { refine restrict_le_restrict_of_subset_le _ _ (λ A hA hA₁, _),
    rw [h₁, sub_to_signed_measure_apply hA,
        show μ A = 0, by exact nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁),
        ennreal.zero_to_real, zero_sub, neg_le, zero_apply, neg_zero],
    exact ennreal.to_real_nonneg },
  { refine restrict_le_restrict_of_subset_le _ _ (λ A hA hA₁, _),
    rw [h₁, sub_to_signed_measure_apply hA,
        show ν A = 0, by exact nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁),
        ennreal.zero_to_real, sub_zero],
    exact ennreal.to_real_nonneg },
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
  have : s v + s (w \ v) = 0,
  { rw [← hw₁, ← of_union set.disjoint_diff hv (hw.diff hv),
        set.union_diff_self, set.union_eq_self_of_subset_left hwt],
    apply_instance },
  have h₁ := nonpos_of_restrict_le_zero _ (restrict_le_restrict_subset _ _ hu hsu (hwt.trans hw₂)),
  have h₂ := nonpos_of_restrict_le_zero _
    (restrict_le_restrict_subset _ _ hu hsu ((w.diff_subset v).trans hw₂)),
  linarith,
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
  rw restrict_le_restrict_iff at hsu hsv,
  have a := hsu (hu.diff hv) (u.diff_subset v),
  have b := hsv (hv.diff hu) (v.diff_subset u),
  erw [of_union (set.disjoint_of_subset_left (u.diff_subset v) set.disjoint_diff)
        (hu.diff hv) (hv.diff hu)] at hs,
  rw zero_apply at a b,
  split,
  all_goals { linarith <|> apply_instance <|> assumption },
end

lemma of_diff_of_diff_eq_zero
  (hu : measurable_set u) (hv : measurable_set v) (h' : s (v \ u) = 0) :
  s (u \ v) + s v = s u :=
begin
  symmetry,
  calc s u = s (u \ v ∪ u ∩ v) : by simp only [set.diff_union_inter]
       ... = s (u \ v) + s (u ∩ v) :
  by { rw of_union,
       { rw disjoint.comm,
         exact set.disjoint_of_subset_left (u.inter_subset_right v) set.disjoint_diff },
       { exact hu.diff hv },
       { exact hu.inter hv } }
       ... = s (u \ v) + s (u ∩ v ∪ v \ u) :
  by { rw [of_union, h', add_zero],
       { exact set.disjoint_of_subset_left (u.inter_subset_left v) set.disjoint_diff },
       { exact hu.inter hv },
       { exact hv.diff hu } }
       ... = s (u \ v) + s v :
  by { rw [set.union_comm, set.inter_comm, set.diff_union_inter] }
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
  have hwuv : s ((w ∩ u) Δ (w ∩ v)) = 0,
  { refine subset_negative_null_set (hu.union hv) ((hw.inter hu).symm_diff (hw.inter hv))
      (hu.symm_diff hv) (restrict_le_restrict_union _ _ hu hsu hv hsv) hs _ _,
    { exact symm_diff_le_sup u v },
    { rintro x (⟨⟨hxw, hxu⟩, hx⟩ | ⟨⟨hxw, hxv⟩, hx⟩);
      rw [set.mem_inter_eq, not_and] at hx,
      { exact or.inl ⟨hxu, hx hxw⟩ },
      { exact or.inr ⟨hxv, hx hxw⟩ } } },
  obtain ⟨huv, hvu⟩ := of_diff_eq_zero_of_symm_diff_eq_zero_negative
    (hw.inter hu) (hw.inter hv)
    (restrict_le_restrict_subset _ _ hu hsu (w.inter_subset_right u))
    (restrict_le_restrict_subset _ _ hv hsv (w.inter_subset_right v)) hwuv,
  rw [← of_diff_of_diff_eq_zero (hw.inter hu) (hw.inter hv) hvu, huv, zero_add]
end

end

/-- The Jordan decomposition of a signed measure is unique. -/
theorem mutually_sigular_eq_sub_unique {s : signed_measure α} {μ₁ ν₁ μ₂ ν₂ : measure α}
  [hμ₁ : finite_measure μ₁] [hν₁ : finite_measure ν₁]
  [hμ₂ : finite_measure μ₂] [hν₂ : finite_measure ν₂]
  (h₁ : μ₁ ⊥ₘ ν₁ ∧ s = @sub_to_signed_measure _ _ μ₁ ν₁ hμ₁ hν₁)
  (h₂ : μ₂ ⊥ₘ ν₂ ∧ s = @sub_to_signed_measure _ _ μ₂ ν₂ hμ₂ hν₂) :
  μ₁ = μ₂ ∧ ν₁ = ν₂ :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ :=
    exists_compl_positive_negative_of_exists_mutually_sigular_sub h₁,
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ :=
    exists_compl_positive_negative_of_exists_mutually_sigular_sub h₂,
  obtain ⟨hST₁, hST₂⟩ := of_symm_diff_compl_positive_negative hS₁.compl hT₁.compl
    ⟨hS₃, (compl_compl S).symm ▸ hS₂⟩ ⟨hT₃, (compl_compl T).symm ▸ hT₂⟩,
  rw [compl_compl, compl_compl] at hST₂,
  split,
  { refine measure_theory.measure.ext (λ i hi, _),
    have hμ₁ : (μ₁ i).to_real = s (i ∩ Sᶜ),
    { rw [h₁.2, sub_to_signed_measure_apply (hi.inter hS₁.compl),
          show ν₁ (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hS₅ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, sub_zero],
      conv_lhs { rw ← set.inter_union_compl i S },
      rw [measure_union, show μ₁ (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1
            (hS₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add],
      { refine set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
      { exact hi.inter hS₁ },
      { exact hi.inter hS₁.compl } },
    have hμ₂ : (μ₂ i).to_real = s (i ∩ Tᶜ),
    { rw [h₂.2, sub_to_signed_measure_apply (hi.inter hT₁.compl),
          show ν₂ (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hT₅ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, sub_zero],
      conv_lhs { rw ← set.inter_union_compl i T },
      rw [measure_union, show μ₂ (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1
            (hT₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add],
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
      { exact hi.inter hT₁ },
      { exact hi.inter hT₁.compl } },
    rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _),
        hμ₁, hμ₂],
    exact of_inter_eq_of_symm_diff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁,
    all_goals { apply_instance } },
  { refine measure_theory.measure.ext (λ i hi, _),
    have hν₁ : (ν₁ i).to_real = - s (i ∩ S),
    { rw [h₁.2, sub_to_signed_measure_apply (hi.inter hS₁),
          show μ₁ (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1
            (hS₄ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, zero_sub],
      conv_lhs { rw ← set.inter_union_compl i S },
      rw [measure_union, show ν₁ (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hS₅ ▸ measure_mono (set.inter_subset_right _ _)), add_zero, neg_neg],
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
      { exact hi.inter hS₁ },
      { exact hi.inter hS₁.compl } },
    have hν₂ : (ν₂ i).to_real = - s (i ∩ T),
    { rw [h₂.2, sub_to_signed_measure_apply (hi.inter hT₁),
          show μ₂ (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1
            (hT₄ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, zero_sub],
      conv_lhs { rw ← set.inter_union_compl i T },
      rw [measure_union, show ν₂ (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hT₅ ▸ measure_mono (set.inter_subset_right _ _)), add_zero, neg_neg],
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
      { exact hi.inter hT₁ },
      { exact hi.inter hT₁.compl } },
    rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _),
        hν₁, hν₂, neg_eq_iff_neg_eq, neg_neg],
    exact eq.symm (of_inter_eq_of_symm_diff_eq_zero_negative hS₁ hT₁ hi hS₂ hT₂ hST₂),
    all_goals { apply_instance } }
end

end signed_measure

end measure_theory
