/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Lebesgue measure on the real line
-/
import analysis.measure_theory.measure_space analysis.measure_theory.borel_space
noncomputable theory
open classical set lattice filter
open ennreal (of_real)

namespace measure_theory

/- "Lebesgue" lebesgue_length of an interval

Important: if `s` is not a interval [a, b) its value is `∞`. This is important to extend this to the
Lebesgue measure. -/
def lebesgue_length (s : set ℝ) : ennreal := ⨅a b (h₁ : a ≤ b) (h₂ : s = Ico a b), of_real (b - a)

lemma lebesgue_length_Ico' {a b : ℝ} (h : a ≤ b) :
  lebesgue_length (Ico a b) = of_real (b - a) :=
le_antisymm
  (infi_le_of_le a $ infi_le_of_le b $ infi_le_of_le h $ infi_le_of_le rfl $ le_refl _)
  (le_infi $ assume a', le_infi $ assume b', le_infi $ assume h', le_infi $ assume eq,
    match Ico_eq_Ico_iff.mp eq with
    | or.inl ⟨h₁, h₂⟩ :=
      have a = b, from le_antisymm h h₁,
      have a' = b', from le_antisymm h' h₂,
      by simp *
    | or.inr ⟨h₁, h⟩ := by simp *
    end)

@[simp] lemma lebesgue_length_empty : lebesgue_length ∅ = 0 :=
by rw [← (Ico_self : Ico 0 (0:ℝ) = ∅), lebesgue_length_Ico'];
   simp [le_refl]

@[simp] lemma lebesgue_length_Ico {a b : ℝ} :
  lebesgue_length (Ico a b) = of_real (b - a) :=
(le_total a b).elim lebesgue_length_Ico' $ λ h,
  by rw [ennreal.of_real_of_nonpos (sub_nonpos.2 h), Ico_eq_empty h]; simp

lemma le_lebesgue_length {r : ennreal} {s : set ℝ} (h : ∀a b, a ≤ b → s ≠ Ico a b) :
  r ≤ lebesgue_length s :=
le_infi $ assume a, le_infi $ assume b, le_infi $ assume hab, le_infi $ assume heq, (h a b hab heq).elim

lemma lebesgue_length_subadditive {a b : ℝ} {c d : ℕ → ℝ}
  (hcd : ∀i, c i ≤ d i) (habcd : Ico a b ⊆ (⋃i, Ico (c i) (d i))) :
  lebesgue_length (Ico a b) ≤ (∑i, lebesgue_length (Ico (c i) (d i))) :=
(le_total b a).elim (λ h, by rw [Ico_eq_empty h]; simp) $ λ hab,
let
  s := λx, ∑i, lebesgue_length (Ico (c i) (min (d i) x)),
  M := {x : ℝ | a ≤ x ∧ x ≤ b ∧ of_real (x - a) ≤ s x }
in
have a ∈ M, by simp [M, le_refl, hab],
have b ∈ upper_bounds M, by simp [upper_bounds, M] {contextual:=tt},
let ⟨x, hx⟩ := exists_supremum_real ‹a ∈ M› ‹b ∈ upper_bounds M› in
have h' : is_lub ((λx, of_real (x - a)) '' M) (of_real (x - a)),
  from is_lub_of_is_lub_of_tendsto
    (assume x ⟨hx, _, _⟩ y ⟨hy, _, _⟩ h,
      have hx : 0 ≤ x - a, by rw [le_sub_iff_add_le]; simp [hx],
      have hy : 0 ≤ y - a, by rw [le_sub_iff_add_le]; simp [hy],
      by rw [ennreal.of_real_le_of_real_iff hx hy]; from sub_le_sub h (le_refl a))
    hx
    (ne_empty_iff_exists_mem.mpr ⟨a, ‹_›⟩)
    (tendsto.comp (tendsto_sub (tendsto_id' inf_le_left) tendsto_const_nhds) ennreal.tendsto_of_real),
have hax : a ≤ x, from hx.left a ‹a ∈ M›,
have hxb : x ≤ b, from hx.right b ‹b ∈ upper_bounds M›,
have hx_sx : of_real (x - a) ≤ s x,
  from h'.right _ $ assume r ⟨y, hy, eq⟩,
    have ∀i, lebesgue_length (Ico (c i) (min (d i) y)) ≤ lebesgue_length (Ico (c i) (min (d i) x)),
      from assume i, by simp; exact
      ennreal.of_real_le_of_real (add_le_add_right (inf_le_inf (le_refl _) (hx.left _ hy)) _),
    eq ▸ le_trans hy.2.2 $ ennreal.tsum_le_tsum this,
have hxM : x ∈ M,
  from ⟨hax, hxb, hx_sx⟩,
have x = b,
  from le_antisymm hxb $ not_lt.mp $ assume hxb : x < b,
  have ∃k, x ∈ Ico (c k) (d k), by simpa using habcd ⟨hxM.left, hxb⟩,
  let ⟨k, hxc, hxd⟩ := this, y := min (d k) b in
  have hxy' : x < y, from lt_min hxd hxb,
  have hxy : x ≤ y, from le_of_lt hxy',
  have of_real (y - a) ≤ s y,
    from calc of_real (y - a) = of_real (x - a) + of_real (y - x) :
      begin
        rw [ennreal.of_real_add],
        simp,
        repeat { simp [hax, hxy, -sub_eq_add_neg] }
      end
      ... ≤ s x + (∑i, ⨆ h : i = k, of_real (y - x)) :
        add_le_add' hx_sx (le_trans (by simp) (@ennreal.le_tsum _ _ k))
      ... ≤ (∑i, lebesgue_length (Ico (c i) (min (d i) x)) + ⨆ h : i = k, of_real (y - x)) :
        by rw [tsum_add]; simp [ennreal.has_sum]
      ... ≤ s y : ennreal.tsum_le_tsum $ assume i, by_cases
          (assume : i = k,
            have eq₁ : min (d k) y = y, from min_eq_right $ min_le_left _ _,
            have eq₂ : min (d k) x = x, from min_eq_right $ le_of_lt hxd,
            have h : c k ≤ y, from le_min (hcd _) (le_trans hxc $ le_of_lt hxb),
            have eq: y - x + (x - c k) = y - c k, by rw [add_sub, sub_add_cancel],
            by simp [h, hxy, hxc, eq, eq₁, eq₂, this, -sub_eq_add_neg, add_sub_cancel'_right, le_refl])
          (assume h : i ≠ k, by simp [h];
            from ennreal.of_real_le_of_real (add_le_add_right (inf_le_inf (le_refl _) hxy) _)),
  have ¬ x < y, from not_lt.mpr $ hx.left y ⟨le_trans hax hxy, min_le_right _ _, this⟩,
  this hxy',
have hbM : b ∈ M, from this ▸ hxM,
calc lebesgue_length (Ico a b) ≤ s b : by simp [hab]; exact hbM.right.right
  ... ≤ ∑i, lebesgue_length (Ico (c i) (d i)) : ennreal.tsum_le_tsum $ assume a,
    by simp; exact ennreal.of_real_le_of_real (add_le_add_right (min_le_left _ _) _)

/-- The Lebesgue outer measure, as an outer measure of ℝ. -/
def lebesgue_outer : outer_measure ℝ :=
outer_measure.of_function lebesgue_length lebesgue_length_empty

lemma lebesgue_outer_Ico {a b : ℝ} :
  lebesgue_outer.measure_of (Ico a b) = of_real (b - a) :=
le_antisymm
  (by rw ← lebesgue_length_Ico; apply outer_measure.of_function_le)
  (le_infi $ assume f, le_infi $ assume hf, by_cases
    (assume : ∀i, ∃p:ℝ×ℝ, p.1 ≤ p.2 ∧ f i = Ico p.1 p.2,
      let ⟨cd, hcd⟩ := axiom_of_choice this in
      have hcd₁ : ∀i, (cd i).1 ≤ (cd i).2, from assume i, (hcd i).1,
      have hcd₂ : ∀i, f i = Ico (cd i).1 (cd i).2, from assume i, (hcd i).2,
      calc of_real (b - a) = lebesgue_length (Ico a b) :
          by simp
        ... ≤ (∑i, lebesgue_length (Ico (cd i).1 (cd i).2)) :
          lebesgue_length_subadditive hcd₁ (by simpa [hcd₂] using hf)
        ... = _ :
          by simp [hcd₂])
    (assume h,
      have ∃i, ∀(c d : ℝ), c ≤ d → f i ≠ Ico c d,
        by simpa [classical.not_forall] using h,
      let ⟨i, hi⟩ := this in
      calc of_real (b - a) ≤ lebesgue_length (f i) : le_lebesgue_length hi
        ... ≤ (∑i, lebesgue_length (f i)) : ennreal.le_tsum))

lemma lebesgue_outer_is_measurable_Iio {c : ℝ} :
  lebesgue_outer.caratheodory.is_measurable (Iio c) :=
outer_measure.caratheodory_is_measurable $ assume t, by_cases
  (assume : ∃a b, a ≤ b ∧ t = Ico a b,
    let ⟨a, b, hab, ht⟩ := this in
    begin
      cases le_total a c with hac hca; cases le_total b c with hbc hcb;
      simp [*, max_eq_right, max_eq_left, min_eq_left, min_eq_right, le_refl,
        -sub_eq_add_neg, sub_add_sub_cancel'],
      show of_real (b - a + (b - a)) ≤ of_real (b - a),
      rw [ennreal.of_real_of_nonpos],
      { apply zero_le },
      { have : b - a ≤ 0, from sub_nonpos.2 (le_trans hbc hca),
        simpa using add_le_add this this }
    end)
  (assume h, by simp at h; from le_lebesgue_length h)

/-- Lebesgue measure on the Borel sets

The outer Lebesgue measure is the completion of this measure. (TODO: proof this)
-/
def lebesgue : measure_space ℝ :=
lebesgue_outer.to_measure $
  calc measure_theory.borel ℝ = measurable_space.generate_from (⋃a:ℚ, {Iio a}) :
      borel_eq_generate_from_Iio_rat
    ... ≤ lebesgue_outer.caratheodory :
      measurable_space.generate_from_le $ by simp [lebesgue_outer_is_measurable_Iio] {contextual := tt}

lemma tendsto_of_nat_at_top_at_top : tendsto (coe : ℕ → ℝ) at_top at_top :=
tendsto_infi.2 $ assume r, tendsto_principal.2 $
let ⟨n, hn⟩ := exists_nat_gt r in
mem_at_top_sets.2 ⟨n, λ m h, le_trans (le_of_lt hn) (nat.cast_le.2 h)⟩

@[simp] lemma lebesgue_Ico {a b : ℝ} : lebesgue (Ico a b) = of_real (b - a) :=
by rw [lebesgue.measure_eq is_measurable_Ico]; exact lebesgue_outer_Ico

@[simp] lemma lebesgue_Ioo {a b : ℝ} : lebesgue (Ioo a b) = of_real (b - a) :=
begin
  cases le_total b a with ba ab,
  { rw ennreal.of_real_of_nonpos (sub_nonpos.2 ba), simp [ba] },
  refine (eq_of_le_of_forall_ge_of_dense _ (λ r h, _)).symm,
  { rw ← lebesgue_Ico,
    exact measure_mono Ioo_subset_Ico_self },
  rcases ennreal.lt_iff_exists_of_real.1 h with ⟨c, c0, rfl, _⟩,
  replace h := (ennreal.of_real_lt_of_real_iff c0 (sub_nonneg.2 ab)).1 h,
  rw ← show lebesgue (Ico (b - c) b) = of_real c,
    by simp [-sub_eq_add_neg, sub_sub_cancel],
  exact measure_mono (Ico_subset_Ioo_left $ lt_sub.1 h)
end

lemma lebesgue_singleton {a : ℝ} : lebesgue {a} = 0 :=
by rw [← Ico_sdiff_Ioo_eq_singleton (lt_add_one a),
       @measure_sdiff ℝ _ _ _ _ Ioo_subset_Ico_self is_measurable_Ico is_measurable_Ioo];
   simp; exact ennreal.of_real_lt_infty

end measure_theory
