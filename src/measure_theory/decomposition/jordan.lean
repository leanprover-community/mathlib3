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
* `signed_measure.exists_mutually_singular_eq_sub` : the Jordan decomposition theorem.
* `signed_measure.mutually_singular_eq_sub_unique` : the Jordan decomposition of a signed measure
  is unique.

## Tags

Jordan decomposition theorem
-/

noncomputable theory
open_locale classical measure_theory

variables {α β : Type*} [measurable_space α]

namespace measure_theory

/-- A Jordan decomposition of a measurable space is a pair of mutually singular,
finite measures. -/
@[ext] structure jordan_decomposition (α : Type*) [measurable_space α] :=
(μ ν : measure α)
[μ_finite : finite_measure μ]
[ν_finite : finite_measure ν]
(mutually_singular : μ ⊥ₘ ν)

namespace jordan_decomposition

open measure vector_measure

variable (j : jordan_decomposition α)

instance jordan_decomposition_inhabited : inhabited (jordan_decomposition α) :=
{ default := ⟨0, 0, mutually_singular.zero⟩ }

attribute [instance] μ_finite ν_finite

/-- A Jordan decomposition provides a Hahn decomposition. -/
lemma exists_compl_positive_negative
  (s : signed_measure α) (hs : j.μ.sub_to_signed_measure j.ν = s):
  ∃ S : set α, measurable_set S ∧ s ≤[S] 0 ∧ 0 ≤[Sᶜ] s ∧ j.μ S = 0 ∧ j.ν Sᶜ = 0 :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := j.mutually_singular,
  refine ⟨S, hS₁, _, _, hS₂, hS₃⟩,
  { refine restrict_le_restrict_of_subset_le _ _ (λ A hA hA₁, _),
    rw [← hs, sub_to_signed_measure_apply hA,
        show j.μ A = 0, by exact nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA₁),
        ennreal.zero_to_real, zero_sub, neg_le, zero_apply, neg_zero],
    exact ennreal.to_real_nonneg },
  { refine restrict_le_restrict_of_subset_le _ _ (λ A hA hA₁, _),
    rw [← hs, sub_to_signed_measure_apply hA,
        show j.ν A = 0, by exact nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA₁),
        ennreal.zero_to_real, sub_zero],
    exact ennreal.to_real_nonneg },
end

end jordan_decomposition

namespace signed_measure

open measure vector_measure jordan_decomposition classical

variables {s : signed_measure α} {μ ν : measure α} [finite_measure μ] [finite_measure ν]

/-- Given a signed measure `s`, `s.to_jordan_decomposition` is the Jordan decomposition `j`,
such that `s = j.μ.sub_to_signed_measure j.ν`. This property is known as the Jordan decomposition
theorem, and is shown by `signed_measure.to_jordan_decomposition_sub`. -/
def to_jordan_decomposition (s : signed_measure α) : jordan_decomposition α :=
let i := some s.exists_compl_positive_negative in
{ μ := s.to_measure_of_zero_le i
    (some_spec s.exists_compl_positive_negative).1
    (some_spec s.exists_compl_positive_negative).2.1,
  ν := s.to_measure_of_le_zero iᶜ
    (some_spec s.exists_compl_positive_negative).1.compl
    (some_spec s.exists_compl_positive_negative).2.2,
  μ_finite := infer_instance,
  ν_finite := infer_instance,
  mutually_singular :=
  begin
    have hi : measurable_set i := (some_spec s.exists_compl_positive_negative).1,
    refine ⟨iᶜ, hi.compl, _, _⟩,
    { rw [to_measure_of_zero_le_apply _ _ hi hi.compl], simpa },
    { rw [to_measure_of_le_zero_apply _ _ hi.compl hi.compl.compl], simpa }
  end }

lemma to_jordan_decomposition_spec (s : signed_measure α) :
  ∃ (i : set α) (hi₁ : measurable_set i) (hi₂ : 0 ≤[i] s) (hi₃ : s ≤[iᶜ] 0),
    s.to_jordan_decomposition.μ = s.to_measure_of_zero_le i hi₁ hi₂ ∧
    s.to_jordan_decomposition.ν = s.to_measure_of_le_zero iᶜ hi₁.compl hi₃ :=
begin
  set i := some s.exists_compl_positive_negative,
  obtain ⟨hi₁, hi₂, hi₃⟩ := some_spec s.exists_compl_positive_negative,
  exact ⟨i, hi₁, hi₂, hi₃, rfl, rfl⟩,
end

/-- **The Jordan decomposition theorem**: Given a signed measure `s`, there exists a pair of
mutually singular measures `μ` and `ν` such that `s = μ - ν`. In this case, the measures `μ`
and `ν` are given by `s.to_jordan_decomposition.μ` and `s.to_jordan_decomposition.ν` respectively.

Note that we use `measure.sub_to_signed_measure μ ν` to represent the signed measure corresponding
to `μ - ν`. -/
@[simp] lemma to_jordan_decomposition_sub (s : signed_measure α) :
  s.to_jordan_decomposition.μ.sub_to_signed_measure s.to_jordan_decomposition.ν = s :=
begin
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.to_jordan_decomposition_spec,
  simp only [hμ, hν],
  ext k hk,
  rw [sub_to_signed_measure_apply hk, to_measure_of_zero_le_apply _ hi₂ hi₁ hk,
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
theorem jordan_decomposition_eq_sub_unique
  (s : signed_measure α) (j₁ j₂ : jordan_decomposition α)
  (hj₁ : j₁.μ.sub_to_signed_measure j₁.ν = s)
  (hj₂ : j₂.μ.sub_to_signed_measure j₂.ν = s) : j₁ = j₂ :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ := j₁.exists_compl_positive_negative s hj₁,
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ := j₂.exists_compl_positive_negative s hj₂,
  obtain ⟨hST₁, hST₂⟩ := of_symm_diff_compl_positive_negative hS₁.compl hT₁.compl
    ⟨hS₃, (compl_compl S).symm ▸ hS₂⟩ ⟨hT₃, (compl_compl T).symm ▸ hT₂⟩,
  rw [compl_compl, compl_compl] at hST₂,
  refine jordan_decomposition.ext _ _ _ _,
  { refine measure_theory.measure.ext (λ i hi, _),
    have hμ₁ : (j₁.μ i).to_real = s (i ∩ Sᶜ),
    { rw [← hj₁, sub_to_signed_measure_apply (hi.inter hS₁.compl),
          show j₁.ν (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hS₅ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, sub_zero],
      conv_lhs { rw ← set.inter_union_compl i S },
      rw [measure_union, show j₁.μ (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1
            (hS₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add],
      { refine set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
      { exact hi.inter hS₁ },
      { exact hi.inter hS₁.compl } },
    have hμ₂ : (j₂.μ i).to_real = s (i ∩ Tᶜ),
    { rw [← hj₂, sub_to_signed_measure_apply (hi.inter hT₁.compl),
          show j₂.ν (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hT₅ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, sub_zero],
      conv_lhs { rw ← set.inter_union_compl i T },
      rw [measure_union, show j₂.μ (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1
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
    have hν₁ : (j₁.ν i).to_real = - s (i ∩ S),
    { rw [← hj₁, sub_to_signed_measure_apply (hi.inter hS₁),
          show j₁.μ (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1
            (hS₄ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, zero_sub],
      conv_lhs { rw ← set.inter_union_compl i S },
      rw [measure_union, show j₁.ν (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1
            (hS₅ ▸ measure_mono (set.inter_subset_right _ _)), add_zero, neg_neg],
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) disjoint_compl_right) },
      { exact hi.inter hS₁ },
      { exact hi.inter hS₁.compl } },
    have hν₂ : (j₂.ν i).to_real = - s (i ∩ T),
    { rw [← hj₂, sub_to_signed_measure_apply (hi.inter hT₁),
          show j₂.μ (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1
            (hT₄ ▸ measure_mono (set.inter_subset_right _ _)),
          ennreal.zero_to_real, zero_sub],
      conv_lhs { rw ← set.inter_union_compl i T },
      rw [measure_union, show j₂.ν (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1
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

lemma sub_to_signed_measure_to_jordan_decomposition (j : jordan_decomposition α) :
  (j.μ.sub_to_signed_measure j.ν).to_jordan_decomposition = j :=
(jordan_decomposition_eq_sub_unique (j.μ.sub_to_signed_measure j.ν)
  j (j.μ.sub_to_signed_measure j.ν).to_jordan_decomposition rfl (by simp)).symm

lemma to_jordan_decomposition_bijective :
  function.bijective $ @to_jordan_decomposition α _ :=
begin
  split,
  { intros s t hst,
    rw [← to_jordan_decomposition_sub s, hst, to_jordan_decomposition_sub t] },
  { intro j,
    exact ⟨j.μ.sub_to_signed_measure j.ν, sub_to_signed_measure_to_jordan_decomposition _⟩ }
end

/-- `signed_measure.to_jordan_decomposition` forms a `equiv` between
`signed_measure α` and `jordan_decomposition α` -/
def to_jordan_decomposition_equiv (α : Type*) [measurable_space α] :
  signed_measure α ≃ jordan_decomposition α :=
equiv.of_bijective to_jordan_decomposition to_jordan_decomposition_bijective

end signed_measure

end measure_theory
