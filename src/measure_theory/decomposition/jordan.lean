import measure_theory.decomposition.signed_hahn

noncomputable theory
open_locale classical big_operators nnreal ennreal measure_theory

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace signed_measure

open measure vector_measure

variables {μ ν : measure α}

/-- The underlying function for `signed_measure.positive_to_measure`. -/
def positive_to_measure_of_measure (s : signed_measure α)
  (i : set α) (hi₁ : measurable_set i) (hi₂ : 0 ≤[i] s)
  (j : set α) (hj₁ : measurable_set j) : ℝ≥0∞ :=
some ⟨s (i ∩ j),
begin
  rw [set.inter_comm, ← s.restrict_apply hi₁ hj₁],
  exact le_trans (by simp) (hi₂ j hj₁),
end⟩

/-- Given a signed measure `s` and a positive measurable set `i`, `positive_to_measure`
provides the measure mapping measurable sets `j` to `s (i ∩ j)`. -/
def positive_to_measure (s : signed_measure α)
  (i : set α) (hi₁ : measurable_set i) (hi₂ : 0 ≤[i] s) : measure α :=
measure.of_measurable (s.positive_to_measure_of_measure i hi₁ hi₂)
  (by { simp_rw [positive_to_measure_of_measure, set.inter_empty i, s.measure_of_empty], refl })
  begin
    intros f hf₁ hf₂,
    simp_rw [positive_to_measure_of_measure, set.inter_Union],
    have h₁ : ∀ n, measurable_set (i ∩ f n) := λ n, hi₁.inter (hf₁ n),
    have h₂ : pairwise (disjoint on λ (n : ℕ), i ∩ f n),
    { rintro n m hnm x ⟨⟨_, hx₁⟩, _, hx₂⟩,
      exact hf₂ n m hnm ⟨hx₁, hx₂⟩ },
    simp_rw [s.measure_of_disjoint_Union h₁ h₂, ennreal.some_eq_coe,
      ← ennreal.coe_tsum (nnreal.summable_coe_of_summable _ (summable_measure_of h₁ h₂))],
    rw ← nnreal.tsum_coe_eq_of_nonneg,
  end

lemma positive_to_measure_apply (hi₁ : measurable_set i) (hi₂ : s.positive i)
  {j : set α} (hj₁ : measurable_set j) :
  s.positive_to_measure i hi₁ hi₂ j =
  some ⟨s (i ∩ j), positive_nonneg_measure (measurable_set.inter hi₁ hj₁)
  (positive_subset_positive hi₂ $ set.inter_subset_left _ _)⟩ :=
by { rw [positive_to_measure, measure.of_measurable_apply _ hj₁], refl }

/-- `signed_measure.positive_to_measure` is a finite measure (this is a def since it
takes arguments). -/
def positive_to_measure_finite (hi₁ : measurable_set i) (hi₂ : s.positive i) :
  finite_measure (s.positive_to_measure i hi₁ hi₂) :=
{ measure_univ_lt_top :=
  begin
    rw [positive_to_measure_apply hi₁ hi₂ measurable_set.univ, ennreal.some_eq_coe],
    exact ennreal.coe_lt_top,
  end }

/-- The Jordan decomposition theorem: Given a signed measure `s`, there exists
a pair of mutually singular measures `μ` and `ν` such that `s = μ - ν`. -/
theorem exists_sigular_sub (s : signed_measure α) :
  ∃ (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν],
    μ ⊥ ν ∧ s = @sub_to_signed_measure _ _ μ ν hμ hν :=
begin
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative,
  have hi₄ := measurable_set.compl hi₁,
  refine ⟨s.positive_to_measure i hi₁ hi₂, s.negative_to_measure iᶜ hi₄ hi₃, _⟩,
  refine ⟨positive_to_measure_finite hi₁ hi₂, negative_to_measure_finite hi₄ hi₃, _, _⟩,
  { refine ⟨iᶜ, hi₄, _, _⟩,
    { simp_rw [positive_to_measure_apply _ _ hi₄,
               set.inter_compl_self, s.measure_of_empty], refl },
    { simp_rw [negative_to_measure_apply _ _ (measurable_set.compl hi₄),
               set.inter_compl_self, s.measure_of_empty, neg_zero], refl } },
  { ext k hk,
    rw [sub_to_signed_measure_apply hk, positive_to_measure_apply hi₁ hi₂ hk,
        negative_to_measure_apply hi₄ hi₃ hk],
    simp only [ennreal.coe_to_real, subtype.coe_mk, ennreal.some_eq_coe, sub_neg_eq_add],
    rw [← measure_of_union _ (measurable_set.inter hi₁ hk) (measurable_set.inter hi₄ hk),
        set.inter_comm i, set.inter_comm iᶜ, set.inter_union_compl _ _],
    rintro x ⟨⟨hx₁, _⟩, hx₂, _⟩,
    exact false.elim (hx₂ hx₁) }
end

/-- A Jordan decomposition provides a Hahn decomposition. -/
lemma exists_compl_positive_negative_of_exists_sigular_sub
  {s : signed_measure α} {μ ν : measure α}
  [hμ : finite_measure μ] [hν : finite_measure ν]
  (h : μ ⊥ ν ∧ s = @sub_to_signed_measure _ _ μ ν hμ hν) :
  ∃ S (hS₁ : measurable_set S) (hS₄: s.negative S) (hS₅: s.positive Sᶜ),
  μ S = 0 ∧ ν Sᶜ = 0 :=
begin
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, h₁⟩ := h,
  refine ⟨S, hS₁, _, _, hS₂, hS₃⟩,
  { intros A hA hA₁,
    rw [h₁, sub_to_signed_measure_apply hA₁,
        show μ A = 0, by exact nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA),
        ennreal.zero_to_real, zero_sub, neg_le, neg_zero],
    exact ennreal.to_real_nonneg },
  { intros A hA hA₁,
    rw [h₁, sub_to_signed_measure_apply hA₁,
        show ν A = 0, by exact nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA),
        ennreal.zero_to_real, sub_zero],
    exact ennreal.to_real_nonneg },
end

lemma subset_positive_null_set {s : signed_measure α} {u w t : set α}
  (hw : measurable_set w) (ht : measurable_set t)
  (hsu : s.positive u) (ht₁ : s t = 0) (ht₂ : t ⊆ u) (hwt : w ⊆ t) : s w = 0 :=
begin
  have : s w + s (t \ w) = 0,
  { rw [← ht₁, ← measure_of_union set.disjoint_diff hw (ht.diff hw),
        set.union_diff_self, set.union_eq_self_of_subset_left hwt] },
  rw add_eq_zero_iff' at this,
  exacts [this.1, hsu _ (hwt.trans ht₂) hw, hsu _ ((t.diff_subset w).trans ht₂) (ht.diff hw)],
end

lemma subset_negative_null_set {s : signed_measure α} {u w t : set α}
  (hw : measurable_set w) (ht : measurable_set t)
  (hsu : s.negative u) (ht₁ : s t = 0) (ht₂ : t ⊆ u) (hwt : w ⊆ t) : s w = 0 :=
begin
  have : s w + s (t \ w) = 0,
  { rw [← ht₁, ← measure_of_union set.disjoint_diff hw (ht.diff hw),
        set.union_diff_self, set.union_eq_self_of_subset_left hwt] },
  linarith [hsu _ (hwt.trans ht₂) hw, hsu _ ((t.diff_subset w).trans ht₂) (ht.diff hw)]
end

lemma set.diff_disjoint_diff (u v : set α) : disjoint (u \ v) (v \ u) :=
set.disjoint_of_subset_left (u.diff_subset v) set.disjoint_diff

lemma of_diff_eq_zero_of_symm_diff_eq_zero_positive {s : signed_measure α} {u v : set α}
  (hu : measurable_set u) (hv : measurable_set v)
  (hsu : s.positive u) (hsv : s.positive v) (hs : s (u Δ v) = 0) :
  s (u \ v) = 0 ∧ s (v \ u) = 0 :=
begin
  rwa [← add_eq_zero_iff' (hsu _ (u.diff_subset v) (hu.diff hv))
           (hsv _ (v.diff_subset u) (hv.diff hu)),
       ← measure_of_union (set.diff_disjoint_diff u v) (hu.diff hv) (hv.diff hu)]
end

lemma of_diff_eq_zero_of_symm_diff_eq_zero_negative {s : signed_measure α} {u v : set α}
  (hu : measurable_set u) (hv : measurable_set v)
  (hsu : s.negative u) (hsv : s.negative v) (hs : s (u Δ v) = 0) :
  s (u \ v) = 0 ∧ s (v \ u) = 0 :=
begin
  have a := hsu _ (u.diff_subset v) (hu.diff hv),
  have b := hsv _ (v.diff_subset u) (hv.diff hu),
  erw [measure_of_union (set.diff_disjoint_diff u v) (hu.diff hv) (hv.diff hu)] at hs,
  split; linarith,
end

-- probably dont need this
lemma of_diff_of_symm_diff_eq_zero {s : signed_measure α} {u v : set α}
  (hu : measurable_set u) (hv : measurable_set v)
  (h : s (u Δ v) = 0) (h' : s (v \ u) = 0) : s (u \ v) + s v = s u :=
begin
  symmetry,
  calc s u = s (u \ v ∪ u ∩ v) : by simp only [set.diff_union_inter]
       ... = s (u \ v) + s (u ∩ v) :
  by { rw measure_of_union,
       { rw disjoint.comm,
         exact set.disjoint_of_subset_left (u.inter_subset_right v) set.disjoint_diff },
       { exact hu.diff hv },
       { exact hu.inter hv } }
       ... = s (u \ v) + s (u ∩ v ∪ v \ u) :
  by { rw [measure_of_union, h', add_zero],
       { exact set.disjoint_of_subset_left (u.inter_subset_left v) set.disjoint_diff },
       { exact hu.inter hv },
       { exact hv.diff hu } }
       ... = s (u \ v) + s v :
  by { rw [set.union_comm, set.inter_comm, set.diff_union_inter] }
end

-- probably have this already
lemma of_inter_eq_of_symm_diff_eq_zero_positive {s : signed_measure α} {u v w : set α}
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : s.positive u) (hsv : s.positive v) (hs : s (u Δ v) = 0) :
  s (w ∩ u) = s (w ∩ v) :=
begin
  have hwuv : s ((w ∩ u) Δ (w ∩ v)) = 0,
  { refine subset_positive_null_set _ _ (positive_union_positive hu hsu hv hsv) hs _ _,
    { exact (hw.inter hu).symm_diff (hw.inter hv) },
    { exact hu.symm_diff hv },
    { exact symm_diff_le_sup u v },
    { rintro x (⟨⟨hxw, hxu⟩, hx⟩ | ⟨⟨hxw, hxv⟩, hx⟩);
      rw [set.mem_inter_eq, not_and] at hx,
      { exact or.inl ⟨hxu, hx hxw⟩ },
      { exact or.inr ⟨hxv, hx hxw⟩ } } },
  obtain ⟨huv, hvu⟩ := of_diff_eq_zero_of_symm_diff_eq_zero_positive
    (hw.inter hu) (hw.inter hv)
    (positive_subset_positive hsu (w.inter_subset_right u))
    (positive_subset_positive hsv (w.inter_subset_right v)) hwuv,
  rw [← of_diff_of_symm_diff_eq_zero (hw.inter hu) (hw.inter hv) hwuv hvu, huv, zero_add]
end

lemma of_inter_eq_of_symm_diff_eq_zero_negative {s : signed_measure α} {u v w : set α}
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : s.negative u) (hsv : s.negative v) (hs : s (u Δ v) = 0) :
  s (w ∩ u) = s (w ∩ v) :=
begin
  have hwuv : s ((w ∩ u) Δ (w ∩ v)) = 0,
  { refine subset_negative_null_set _ _ (negative_union_negative hu hsu hv hsv) hs _ _,
    { exact (hw.inter hu).symm_diff (hw.inter hv) },
    { exact hu.symm_diff hv },
    { exact symm_diff_le_sup u v },
    { rintro x (⟨⟨hxw, hxu⟩, hx⟩ | ⟨⟨hxw, hxv⟩, hx⟩);
      rw [set.mem_inter_eq, not_and] at hx,
      { exact or.inl ⟨hxu, hx hxw⟩ },
      { exact or.inr ⟨hxv, hx hxw⟩ } } },
  obtain ⟨huv, hvu⟩ := of_diff_eq_zero_of_symm_diff_eq_zero_negative
    (hw.inter hu) (hw.inter hv)
    (negative_subset_negative hsu (w.inter_subset_right u))
    (negative_subset_negative hsv (w.inter_subset_right v)) hwuv,
  rw [← of_diff_of_symm_diff_eq_zero (hw.inter hu) (hw.inter hv) hwuv hvu, huv, zero_add]
end

/-- The Jordan decomposition of a signed measure is unique. -/
theorem singular_sub_unique {s : signed_measure α} {μ₁ ν₁ μ₂ ν₂ : measure α}
  [hμ₁ : finite_measure μ₁] [hν₁ : finite_measure ν₁]
  [hμ₂ : finite_measure μ₂] [hν₂ : finite_measure ν₂]
  (h₁ : μ₁ ⊥ ν₁ ∧ s = @sub_to_signed_measure _ _ μ₁ ν₁ hμ₁ hν₁)
  (h₂ : μ₂ ⊥ ν₂ ∧ s = @sub_to_signed_measure _ _ μ₂ ν₂ hμ₂ hν₂) :
  μ₁ = μ₂ ∧ ν₁ = ν₂ :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ :=
    exists_compl_positive_negative_of_exists_sigular_sub h₁,
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ :=
    exists_compl_positive_negative_of_exists_sigular_sub h₂,
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
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _)
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) S.disjoint_compl) },
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
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) T.disjoint_compl) },
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
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) S.disjoint_compl) },
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
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) T.disjoint_compl) },
      { exact hi.inter hT₁ },
      { exact hi.inter hT₁.compl } },
    rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _),
        hν₁, hν₂, neg_eq_iff_neg_eq, neg_neg],
    exact eq.symm (of_inter_eq_of_symm_diff_eq_zero_negative hS₁ hT₁ hi hS₂ hT₂ hST₂),
    all_goals { apply_instance } }
end

end signed_measure

end measure_theory
