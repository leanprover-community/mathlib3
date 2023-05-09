/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.constructions.borel_space
import measure_theory.measure.stieltjes
import probability.kernel.composition
import measure_theory.decomposition.radon_nikodym

/-!
# Conditional cumulative distribution function

Given `ρ : measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `cond_cdf ρ : α → ℝ → ℝ` such that for all `a : α`,
`cond_cdf ρ a` is monotone and right-continuous with limit 0 at -∞ and limit 1 at +∞, and such that
for all `x : ℝ`, `a ↦ cond_cdf ρ a x` is measurable. For all `x : ℝ` and measurable set `s`, that
function verifies `∫⁻ a in s, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

## Main definitions

* `probability_theory.cond_cdf ρ : α → stieltjes_function`: the conditional cdf of
  `ρ : measure (α × ℝ)`. A `stieltjes_function` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `probability_theory.set_lintegral_cond_cdf`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

## References

The construction of the conditional cdf in this file follows the proof of Theorem 3.4 in
[O. Kallenberg, Foundations of modern probability][kallenberg2021].

## TODO

* The conditional cdf can be used to define the cdf of a real measure by using the
  conditional cdf of `(measure.dirac unit.star).prod μ : measure (unit × ℝ)`.

-/

open measure_theory set filter topological_space

open_locale nnreal ennreal measure_theory topology probability_theory

section aux_lemmas_to_be_moved

variables {α β ι : Type*}

namespace directed
-- todo after the port: move this to logic.encodable.basic near sequence_mono
variables [encodable α] [inhabited α] [preorder β] {f : α → β} (hf : directed (≥) f)

lemma sequence_anti : antitone (f ∘ (hf.sequence f)) :=
antitone_nat_of_succ_le $ hf.sequence_mono_nat

lemma sequence_le (a : α) : f (hf.sequence f (encodable.encode a + 1)) ≤ f a :=
hf.rel_sequence a

end directed

-- todo: move to data/set/lattice next to prod_Union or prod_sInter
lemma prod_Inter {s : set α} {t : ι → set β} [hι : nonempty ι] :
  s ×ˢ (⋂ i, t i) = ⋂ i, s ×ˢ (t i) :=
begin
  ext x,
  simp only [mem_prod, mem_Inter],
  exact ⟨λ h i, ⟨h.1, h.2 i⟩, λ h, ⟨(h hι.some).1, λ i, (h i).2⟩⟩,
end

lemma real.Union_Iic_rat : (⋃ r : ℚ, Iic (r : ℝ)) = univ :=
begin
  ext1,
  simp only [mem_Union, mem_Iic, mem_univ, iff_true],
  obtain ⟨r, hr⟩ := exists_rat_gt x,
  exact ⟨r, hr.le⟩,
end

lemma real.Inter_Iic_rat : (⋂ r : ℚ, Iic (r : ℝ)) = ∅ :=
begin
  ext1,
  simp only [mem_Inter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le],
  exact exists_rat_lt x,
end

lemma infi_Ioi_eq_infi_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : bdd_below (f '' Ioi x))
  (hf_mono : monotone f) :
  (⨅ r : Ioi x, f r) = ⨅ q : {q' : ℚ // x < q'}, f q :=
begin
  refine le_antisymm _ _,
  { haveI : nonempty {r' : ℚ // x < ↑r'},
    { obtain ⟨r, hrx⟩ := exists_rat_gt x,
      exact ⟨⟨r, hrx⟩⟩, },
    refine le_cinfi (λ r, _),
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop,
    refine cinfi_set_le hf (hxy.trans _),
    exact_mod_cast hyr, },
  { refine le_cinfi (λ q, _),
    have hq := q.prop,
    rw mem_Ioi at hq,
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq,
    refine (cinfi_le _ _).trans _,
    { exact ⟨y, hxy⟩, },
    { refine ⟨hf.some, λ z, _⟩,
      rintros ⟨u, rfl⟩,
      suffices hfu : f u ∈ f '' Ioi x, from hf.some_spec hfu,
      exact ⟨u, u.prop, rfl⟩, },
    { refine hf_mono (le_trans _ hyq.le),
      norm_cast, }, },
end

lemma ennreal.tendsto_at_top_at_bot [nonempty ι] [semilattice_sup ι]
  {f : ι → ℝ≥0∞} (h : tendsto f at_top at_bot) :
  tendsto f at_top (𝓝 0) :=
begin
  rw tendsto_at_bot at h,
  obtain ⟨i, hi⟩ := eventually_at_top.mp (h 0),
  rw ennreal.tendsto_at_top_zero,
  exact λ ε hε, ⟨i, λ n hn, (hi n hn).trans (zero_le _)⟩,
end

-- todo: move to topology/algebra/order/monotone_convergence
lemma tendsto_of_antitone {ι α : Type*} [preorder ι] [topological_space α]
  [conditionally_complete_linear_order α] [order_topology α] {f : ι → α} (h_mono : antitone f) :
  tendsto f at_top at_bot ∨ (∃ l, tendsto f at_top (𝓝 l)) :=
@tendsto_of_monotone ι αᵒᵈ _ _ _ _ _ h_mono

-- todo: move to data/real/ennreal
lemma ennreal.of_real_cinfi (f : α → ℝ) [nonempty α] :
  ennreal.of_real (⨅ i, f i) = ⨅ i, ennreal.of_real (f i) :=
begin
  by_cases hf : bdd_below (range f),
  { exact monotone.map_cinfi_of_continuous_at ennreal.continuous_of_real.continuous_at
      (λ i j hij, ennreal.of_real_le_of_real hij) hf, },
  { symmetry,
    rw [real.infi_of_not_bdd_below hf, ennreal.of_real_zero, ← ennreal.bot_eq_zero, infi_eq_bot],
    intros x hx,
    obtain ⟨i, hfi⟩ : ∃ i, f i ≤ 0,
    { by_contra h,
      refine hf ⟨0, _⟩,
      rintros i ⟨y, rfl⟩,
      push_neg at h,
      exact (h y).le, },
    refine ⟨i, _⟩,
    rw ennreal.of_real_of_nonpos hfi,
    exact hx, },
end

-- todo: move to measure_theory/measurable_space
/-- Monotone convergence for an infimum over a directed family and indexed by a countable type -/
theorem lintegral_infi_directed_of_measurable {mα : measurable_space α} [countable β]
  {f : β → α → ℝ≥0∞} {μ : measure α} (hμ : μ ≠ 0)
  (hf : ∀ b, measurable (f b)) (hf_int : ∀ b, ∫⁻ a, f b a ∂μ ≠ ∞) (h_directed : directed (≥) f) :
  ∫⁻ a, ⨅ b, f b a ∂μ = ⨅ b, ∫⁻ a, f b a ∂μ :=
begin
  casesI nonempty_encodable β,
  casesI is_empty_or_nonempty β,
  { simp only [with_top.cinfi_empty, lintegral_const],
    rw [ennreal.top_mul, if_neg],
    simp only [measure.measure_univ_eq_zero, hμ, not_false_iff], },
  inhabit β,
  have : ∀ a, (⨅ b, f b a) = (⨅ n, f (h_directed.sequence f n) a),
  { refine λ a, le_antisymm (le_infi (λ n, infi_le _ _))
      (le_infi (λ b, infi_le_of_le (encodable.encode b + 1) _)),
    exact (h_directed.sequence_le b a), },
  calc ∫⁻ a, ⨅ b, f b a ∂μ
        = ∫⁻ a, ⨅ n, f (h_directed.sequence f n) a ∂μ : by simp only [this]
    ... = ⨅ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :
      by { rw lintegral_infi (λ n, _) h_directed.sequence_anti,
        { exact hf_int _, },
        { exact hf _, }, }
    ... = ⨅ b, ∫⁻ a, f b a ∂μ :
    begin
      refine le_antisymm (le_infi (λ b, _)) (le_infi (λ n, _)),
      { exact infi_le_of_le (encodable.encode b + 1) (lintegral_mono $ h_directed.sequence_le b) },
      { exact infi_le (λb, ∫⁻ a, f b a ∂μ) _ },
    end
end

-- todo: move to measure_theory/pi_system
lemma real.is_pi_system_Ioc_rat :
  @is_pi_system ℝ {S | ∃ (l u : ℚ) (h : l < u), Ioc (l : ℝ) u = S} :=
begin
  rintros s ⟨ls, us, hlus, rfl⟩ t ⟨lt, ut, hlut, rfl⟩ hst,
  rw [Ioc_inter_Ioc, sup_eq_max, inf_eq_min] at hst ⊢,
  refine ⟨max ls lt, min us ut, _, _⟩,
  { rw [nonempty_Ioc] at hst,
    exact_mod_cast hst, },
  { norm_cast, },
end

-- todo: move to measure_theory/pi_system
lemma real.is_pi_system_Iic_rat : @is_pi_system ℝ {S | ∃ (u : ℚ), Iic (u : ℝ) = S} :=
begin
  rintros s ⟨us, rfl⟩ t ⟨ut, rfl⟩ _,
  rw [Iic_inter_Iic, inf_eq_min],
  refine ⟨min us ut, _⟩,
  norm_cast,
end

-- todo: move to measure_theory/pi_system
lemma is_pi_system_Iic [semilattice_inf α] : @is_pi_system α (range Iic) :=
by { rintros s ⟨us, rfl⟩ t ⟨ut, rfl⟩ _, rw [Iic_inter_Iic], exact ⟨us ⊓ ut, rfl⟩, }

-- todo: move to measure_theory/pi_system
lemma is_pi_system_Ici [semilattice_sup α] : @is_pi_system α (range Ici) :=
by { rintros s ⟨us, rfl⟩ t ⟨ut, rfl⟩ _, rw [Ici_inter_Ici], exact ⟨us ⊔ ut, rfl⟩, }


end aux_lemmas_to_be_moved

namespace measure_theory.measure

variables {α β : Type*} {mα : measurable_space α}

include mα

/-- Measure on `α` such that for a measurable set `s`, `ρ.Iic_snd r s = ρ (s ×ˢ Iic r)`. -/
noncomputable
def Iic_snd (ρ : measure (α × ℝ)) (r : ℚ) : measure α :=
measure.of_measurable (λ s hs, ρ (s ×ˢ Iic r))
  (by simp only [empty_prod, measure_empty])
  (λ f hf_meas hf_disj,
    begin
      rw [set.Union_prod_const, measure_Union],
      { intros i j hij,
        rw [function.on_fun, disjoint_prod],
        exact or.inl (hf_disj hij), },
      { exact λ i, measurable_set.prod (hf_meas i) measurable_set_Iic, }
    end)

lemma Iic_snd_apply (ρ : measure (α × ℝ)) (r : ℚ) {s : set α} (hs : measurable_set s) :
  ρ.Iic_snd r s = ρ (s ×ˢ Iic r) :=
measure.of_measurable_apply s hs

lemma Iic_snd_univ (ρ : measure (α × ℝ)) (r : ℚ) : ρ.Iic_snd r univ = ρ (univ ×ˢ Iic r) :=
Iic_snd_apply ρ r measurable_set.univ

lemma Iic_snd_mono (ρ : measure (α × ℝ)) {r r' : ℚ} (h_le : r ≤ r') :
  ρ.Iic_snd r ≤ ρ.Iic_snd r' :=
begin
  intros s hs,
  simp_rw Iic_snd_apply ρ _ hs,
  refine measure_mono (prod_subset_prod_iff.mpr (or.inl ⟨subset_rfl, Iic_subset_Iic.mpr _⟩)),
  exact_mod_cast h_le,
end

lemma Iic_snd_le_fst (ρ : measure (α × ℝ)) (r : ℚ) : ρ.Iic_snd r ≤ ρ.fst :=
begin
  intros s hs,
  simp_rw [fst_apply hs, Iic_snd_apply ρ r hs],
  exact measure_mono (prod_subset_preimage_fst _ _),
end

lemma Iic_snd_ac_fst (ρ : measure (α × ℝ)) (r : ℚ) : ρ.Iic_snd r ≪ ρ.fst :=
measure.absolutely_continuous_of_le (Iic_snd_le_fst ρ r)

instance {ρ : measure (α × ℝ)} [is_finite_measure ρ] (r : ℚ) : is_finite_measure (ρ.Iic_snd r) :=
is_finite_measure_of_le _ (Iic_snd_le_fst ρ _)

lemma infi_Iic_snd_gt (ρ : measure (α × ℝ)) (t : ℚ) {s : set α} (hs : measurable_set s)
  [is_finite_measure ρ] :
  (⨅ r : {r' : ℚ // t < r'}, ρ.Iic_snd r s) = ρ.Iic_snd t s :=
begin
  simp_rw [ρ.Iic_snd_apply _ hs],
  rw ← measure_Inter_eq_infi,
  { rw ← prod_Inter,
    congr' with x : 1,
    simp only [mem_Inter, mem_Iic, subtype.forall, subtype.coe_mk],
    refine ⟨λ h, _, λ h a hta, h.trans _⟩,
    { refine le_of_forall_lt_rat_imp_le (λ q htq, h q _),
      exact_mod_cast htq, },
    { exact_mod_cast hta.le, }, },
  { exact λ _, hs.prod measurable_set_Iic, },
  { refine monotone.directed_ge (λ r r' hrr', prod_subset_prod_iff.mpr (or.inl ⟨subset_rfl, _⟩)),
    refine Iic_subset_Iic.mpr _,
    exact_mod_cast hrr', },
  { exact ⟨⟨t+1, lt_add_one _⟩, measure_ne_top ρ _⟩, },
end

lemma tendsto_Iic_snd_at_top (ρ : measure (α × ℝ)) {s : set α} (hs : measurable_set s) :
  tendsto (λ r, ρ.Iic_snd r s) at_top (𝓝 (ρ.fst s)) :=
begin
  simp_rw [ρ.Iic_snd_apply _ hs, fst_apply hs, ← prod_univ],
  rw [← real.Union_Iic_rat, prod_Union],
  refine tendsto_measure_Union (λ r q hr_le_q x, _),
  simp only [mem_prod, mem_Iic, and_imp],
  refine λ hxs hxr, ⟨hxs, hxr.trans _⟩,
  exact_mod_cast hr_le_q,
end

lemma tendsto_Iic_snd_at_bot (ρ : measure (α × ℝ)) [is_finite_measure ρ]
  {s : set α} (hs : measurable_set s) :
  tendsto (λ r, ρ.Iic_snd r s) at_bot (𝓝 0) :=
begin
  simp_rw [ρ.Iic_snd_apply _ hs],
  have h_empty : ρ (s ×ˢ ∅) = 0, by simp only [prod_empty, measure_empty],
  rw [← h_empty, ← real.Inter_Iic_rat, prod_Inter],
  suffices h_neg : tendsto (λ r : ℚ, ρ (s ×ˢ Iic (↑-r))) at_top (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic (↑-r)))),
  { have h_inter_eq : (⋂ r : ℚ, s ×ˢ Iic (↑-r)) = (⋂ r : ℚ, s ×ˢ Iic (r : ℝ)),
    { ext1 x,
      simp only [rat.cast_eq_id, id.def, mem_Inter, mem_prod, mem_Iic],
      refine ⟨λ h i, ⟨(h i).1, _⟩, λ h i, ⟨(h i).1, _⟩⟩; have h' := h (-i),
      { rw neg_neg at h', exact h'.2, },
      { exact h'.2, }, },
    rw h_inter_eq at h_neg,
    have h_fun_eq : (λ (r : ℚ), ρ (s ×ˢ Iic (r : ℝ))) = (λ r, ρ (s ×ˢ Iic ↑(- -r))),
    { simp_rw neg_neg, },
    rw h_fun_eq,
    exact h_neg.comp tendsto_neg_at_bot_at_top, },
  refine tendsto_measure_Inter (λ q, hs.prod measurable_set_Iic) _ ⟨0, measure_ne_top ρ _⟩,
  refine λ q r hqr, prod_subset_prod_iff.mpr (or.inl ⟨subset_rfl, λ x hx, _⟩),
  simp only [rat.cast_neg, mem_Iic] at hx ⊢,
  refine hx.trans (neg_le_neg _),
  exact_mod_cast hqr,
end

end measure_theory.measure

open measure_theory

namespace probability_theory

variables {α β ι : Type*} {mα : measurable_space α}

include mα

/-! ### Auxiliary definitions

We build towards the definition of `probability_theory.cond_cdf`. We first define
`probability_theory.pre_cdf`, a function defined on `α × ℚ` with the properties of a cdf almost
everywhere. We then introduce `probability_theory.cond_cdf_rat`, a function on `α × ℚ` which has
the properties of a cdf for all `a : α`. We finally extend to `ℝ`. -/

/-- `pre_cdf` is the Radon-Nikodym derivative of `ρ.Iic_snd` with respect to `ρ.fst` at each
`r : ℚ`. This function `ℚ → α → ℝ≥0∞` is such that for almost all `a : α`, the function `ℚ → ℝ≥0∞`
satisfies the properties of a cdf (monotone with limit 0 at -∞ and 1 at +∞, right-continuous).

We define this function on `ℚ` and not `ℝ` because `ℚ` is countable, which allows us to prove
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (pre_cdf q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (pre_cdf q a)`. -/
noncomputable
def pre_cdf (ρ : measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ := measure.rn_deriv (ρ.Iic_snd r) ρ.fst

lemma measurable_pre_cdf {ρ : measure (α × ℝ)} {r : ℚ} : measurable (pre_cdf ρ r) :=
measure.measurable_rn_deriv _ _

lemma with_density_pre_cdf (ρ : measure (α × ℝ)) (r : ℚ) [is_finite_measure ρ] :
  ρ.fst.with_density (pre_cdf ρ r) = ρ.Iic_snd r :=
measure.absolutely_continuous_iff_with_density_rn_deriv_eq.mp (measure.Iic_snd_ac_fst ρ r)

lemma set_lintegral_pre_cdf_fst (ρ : measure (α × ℝ)) (r : ℚ) {s : set α}
  (hs : measurable_set s) [is_finite_measure ρ] :
  ∫⁻ x in s, pre_cdf ρ r x ∂ρ.fst = ρ.Iic_snd r s :=
begin
  have : ∀ r, ∫⁻ x in s, pre_cdf ρ r x ∂ρ.fst = ∫⁻ x in s, (pre_cdf ρ r * 1) x ∂ρ.fst,
  { simp only [mul_one, eq_self_iff_true, forall_const], },
  rw [this, ← set_lintegral_with_density_eq_set_lintegral_mul _ measurable_pre_cdf _ hs],
  { simp only [with_density_pre_cdf ρ r, pi.one_apply, lintegral_one, measure.restrict_apply,
      measurable_set.univ, univ_inter], },
  { rw (_ : (1 : α → ℝ≥0∞) = (λ _, 1)),
    exacts [measurable_const, rfl], },
end

lemma monotone_pre_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, monotone (λ r, pre_cdf ρ r a) :=
begin
  simp_rw [monotone, ae_all_iff],
  refine λ r r' hrr', ae_le_of_forall_set_lintegral_le_of_sigma_finite
    measurable_pre_cdf measurable_pre_cdf (λ s hs hs_fin, _),
  rw [set_lintegral_pre_cdf_fst ρ r hs, set_lintegral_pre_cdf_fst ρ r' hs],
  refine measure.Iic_snd_mono ρ _ s hs,
  exact_mod_cast hrr',
end

lemma set_lintegral_infi_gt_pre_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] (t : ℚ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ x in s, ⨅ r : Ioi t, pre_cdf ρ r x ∂ρ.fst = ρ.Iic_snd t s :=
begin
  refine le_antisymm _ _,
  { have h : ∀ q : Ioi t, ∫⁻ x in s, ⨅ r : Ioi t, pre_cdf ρ r x ∂ρ.fst ≤ ρ.Iic_snd q s,
    { intros q,
      rw ← set_lintegral_pre_cdf_fst ρ _ hs,
      refine set_lintegral_mono_ae _ measurable_pre_cdf _,
      { exact measurable_infi (λ _, measurable_pre_cdf), },
      { filter_upwards [monotone_pre_cdf] with a ha_mono,
        exact λ _, infi_le _ q, }, },
    calc ∫⁻ x in s, (⨅ (r : Ioi t), pre_cdf ρ r x) ∂ρ.fst
        ≤ ⨅ q : Ioi t, ρ.Iic_snd q s : le_infi h
    ... = ρ.Iic_snd t s : measure.infi_Iic_snd_gt ρ t hs, },
  { rw (set_lintegral_pre_cdf_fst ρ t hs).symm,
    refine set_lintegral_mono_ae measurable_pre_cdf _ _,
    { exact measurable_infi (λ _, measurable_pre_cdf), },
    { filter_upwards [monotone_pre_cdf] with a ha_mono,
      exact λ _, le_infi (λ r, ha_mono (le_of_lt r.prop)), }, },
end

lemma pre_cdf_le_one (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, ∀ r, pre_cdf ρ r a ≤ 1 :=
begin
  rw ae_all_iff,
  refine λ r, ae_le_of_forall_set_lintegral_le_of_sigma_finite measurable_pre_cdf
    measurable_const (λ s hs hs_fin, _),
  rw set_lintegral_pre_cdf_fst ρ r hs,
  simp only [pi.one_apply, lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
  exact measure.Iic_snd_le_fst ρ r s hs,
end

lemma tendsto_lintegral_pre_cdf_at_top (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top (𝓝 (ρ univ)) :=
begin
  convert ρ.tendsto_Iic_snd_at_top measurable_set.univ,
  { ext1 r,
    rw [← set_lintegral_univ, set_lintegral_pre_cdf_fst ρ _ measurable_set.univ], },
  { exact measure.fst_univ.symm, },
end

lemma tendsto_lintegral_pre_cdf_at_bot (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  tendsto (λ r, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_bot (𝓝 0) :=
begin
  convert ρ.tendsto_Iic_snd_at_bot measurable_set.univ,
  ext1 r,
  rw [← set_lintegral_univ, set_lintegral_pre_cdf_fst ρ _ measurable_set.univ],
end

lemma tendsto_pre_cdf_at_top_one (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 1) :=
begin
  have h_mono := monotone_pre_cdf ρ,
  have h_le_one := pre_cdf_le_one ρ,
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 l),
  { filter_upwards [h_mono, h_le_one] with a ha_mono ha_le_one,
    have h_tendsto : tendsto (λ r, pre_cdf ρ r a) at_top at_top
      ∨ ∃ l, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 l) := tendsto_of_monotone ha_mono,
    cases h_tendsto with h_absurd h_tendsto,
    { rw monotone.tendsto_at_top_at_top_iff ha_mono at h_absurd,
      obtain ⟨r, hr⟩ := h_absurd 2,
      exact absurd (hr.trans (ha_le_one r)) ennreal.one_lt_two.not_le, },
    { exact h_tendsto, }, },
  classical,
  let F : α → ℝ≥0∞ := λ a,
    if h : ∃ l, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 l) then h.some else 0,
  have h_tendsto_ℚ : ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 (F a)),
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec },
  have h_tendsto_ℕ : ∀ᵐ a ∂ρ.fst, tendsto (λ n : ℕ, pre_cdf ρ n a) at_top (𝓝 (F a)),
  { filter_upwards [h_tendsto_ℚ] with a ha using ha.comp tendsto_coe_nat_at_top_at_top, },
  have hF_ae_meas : ae_measurable F ρ.fst,
  { refine ae_measurable_of_tendsto_metrizable_ae _ (λ n, _) h_tendsto_ℚ,
    exact measurable_pre_cdf.ae_measurable, },
  have hF_le_one : ∀ᵐ a ∂ρ.fst, F a ≤ 1,
  { filter_upwards [h_tendsto_ℚ, h_le_one] with a ha ha_le using le_of_tendsto' ha ha_le, },
  suffices : ∀ᵐ a ∂ρ.fst, F a = 1,
  { filter_upwards [h_tendsto_ℚ, this] with a ha_tendsto ha_eq,
    rwa ha_eq at ha_tendsto, },
  have h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = ∫⁻ a, 1 ∂ρ.fst,
  { have h_lintegral : tendsto (λ r : ℕ, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top
      (𝓝 (∫⁻ a, F a ∂ρ.fst)),
    { refine lintegral_tendsto_of_tendsto_of_monotone  -- does this exist only for ℕ?
        (λ _, measurable_pre_cdf.ae_measurable) _ h_tendsto_ℕ,
      filter_upwards [h_mono] with a ha,
      refine λ n m hnm, ha _,
      exact_mod_cast hnm, },
    have h_lintegral' : tendsto (λ r : ℕ, ∫⁻ a, pre_cdf ρ r a ∂ρ.fst) at_top
      (𝓝 (∫⁻ a, 1 ∂ρ.fst)),
    { rw [lintegral_one, measure.fst_univ],
      exact (tendsto_lintegral_pre_cdf_at_top ρ).comp tendsto_coe_nat_at_top_at_top, },
    exact tendsto_nhds_unique h_lintegral h_lintegral', },
  have : ∫⁻ a, (1 - F a) ∂ρ.fst = 0,
  { rw [lintegral_sub' hF_ae_meas _ hF_le_one, h_lintegral_eq, tsub_self],
    calc ∫⁻ a, F a ∂ρ.fst = ∫⁻ a, 1 ∂ρ.fst : h_lintegral_eq
    ... = ρ.fst univ : lintegral_one
    ... = ρ univ : measure.fst_univ
    ... ≠ ∞ : measure_ne_top ρ _, },
  rw lintegral_eq_zero_iff' (ae_measurable_const.sub hF_ae_meas) at this,
  filter_upwards [this, hF_le_one] with ha h_one_sub_eq_zero h_le_one,
  rw [pi.zero_apply, tsub_eq_zero_iff_le] at h_one_sub_eq_zero,
  exact le_antisymm h_le_one h_one_sub_eq_zero,
end

lemma tendsto_pre_cdf_at_bot_zero (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ r a) at_bot (𝓝 0) :=
begin
  suffices : ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 0),
  { filter_upwards [this] with a ha,
    have h_eq_neg : (λ (r : ℚ), pre_cdf ρ r a) = (λ (r : ℚ), pre_cdf ρ (- -r) a),
    { simp_rw neg_neg, },
    rw h_eq_neg,
    exact ha.comp tendsto_neg_at_bot_at_top, },
  have h_exists : ∀ᵐ a ∂ρ.fst, ∃ l, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 l),
  { filter_upwards [monotone_pre_cdf ρ] with a ha,
    have h_anti : antitone (λ r, pre_cdf ρ (-r) a) := λ p q hpq, ha (neg_le_neg hpq),
    have h_tendsto : tendsto (λ r, pre_cdf ρ (-r) a) at_top at_bot
      ∨ ∃ l, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 l) := tendsto_of_antitone h_anti,
    cases h_tendsto with h_bot h_tendsto,
    { exact ⟨0, ennreal.tendsto_at_top_at_bot h_bot⟩, },
    { exact h_tendsto, }, },
  classical,
  let F : α → ℝ≥0∞ := λ a,
    if h : ∃ l, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 l) then h.some else 0,
  have h_tendsto : ∀ᵐ a ∂ρ.fst, tendsto (λ r, pre_cdf ρ (-r) a) at_top (𝓝 (F a)),
  { filter_upwards [h_exists] with a ha,
    simp_rw [F, dif_pos ha],
    exact ha.some_spec, },
  suffices h_lintegral_eq : ∫⁻ a, F a ∂ρ.fst = 0,
  { have hF_ae_meas : ae_measurable F ρ.fst,
    { refine ae_measurable_of_tendsto_metrizable_ae _ (λ n, _) h_tendsto,
      exact measurable_pre_cdf.ae_measurable, },
    rw [lintegral_eq_zero_iff' hF_ae_meas] at h_lintegral_eq,
    filter_upwards [h_tendsto, h_lintegral_eq] with a ha_tendsto ha_eq,
    rwa ha_eq at ha_tendsto, },
  have h_lintegral : tendsto (λ r, ∫⁻ a, pre_cdf ρ (-r) a ∂ρ.fst) at_top (𝓝 (∫⁻ a, F a ∂ρ.fst)),
  { refine tendsto_lintegral_filter_of_dominated_convergence (λ _, 1)
      (eventually_of_forall (λ _, measurable_pre_cdf)) (eventually_of_forall (λ _, _))
      _ h_tendsto,
    { filter_upwards [pre_cdf_le_one ρ] with a ha using ha _, },
    { rw lintegral_one,
      exact measure_ne_top _ _, }, },
  have h_lintegral' : tendsto (λ r, ∫⁻ a, pre_cdf ρ (-r) a ∂ρ.fst) at_top (𝓝 0),
  { have h_lintegral_eq : (λ r, ∫⁻ a, pre_cdf ρ (-r) a ∂ρ.fst) = λ r, ρ (univ ×ˢ Iic (-r)),
    { ext1 n,
      rw [← set_lintegral_univ, set_lintegral_pre_cdf_fst ρ _ measurable_set.univ,
        measure.Iic_snd_univ],
      norm_cast, },
    rw h_lintegral_eq,
    have h_zero_eq_measure_Inter : (0 : ℝ≥0∞) = ρ (⋂ r : ℚ, univ ×ˢ Iic (-r)),
    { suffices : (⋂ r : ℚ, Iic (-(r : ℝ))) = ∅,
      { rwa [← prod_Inter, this, prod_empty, measure_empty], },
      ext1 x,
      simp only [mem_Inter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le],
      simp_rw neg_lt,
      exact exists_rat_gt _, },
    rw h_zero_eq_measure_Inter,
    refine tendsto_measure_Inter (λ n, measurable_set.univ.prod measurable_set_Iic)
      (λ i j hij x, _) ⟨0, measure_ne_top ρ _⟩,
    simp only [mem_prod, mem_univ, mem_Iic, true_and],
    refine λ hxj, hxj.trans (neg_le_neg _),
    exact_mod_cast hij, },
  exact tendsto_nhds_unique h_lintegral h_lintegral',
end

lemma inf_gt_pre_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, ∀ t : ℚ, (⨅ r : Ioi t, pre_cdf ρ r a) = pre_cdf ρ t a :=
begin
  rw ae_all_iff,
  refine λ t, ae_eq_of_forall_set_lintegral_eq_of_sigma_finite _ measurable_pre_cdf _,
  { exact measurable_infi (λ i, measurable_pre_cdf), },
  intros s hs hs_fin,
  rw [set_lintegral_infi_gt_pre_cdf ρ t hs, set_lintegral_pre_cdf_fst ρ t hs],
end


section has_cond_cdf

/-- A product measure on `α × ℝ` is said to have a conditional cdf at `a : α` if `pre_cdf` is
monotone with limit 0 at -∞ and 1 at +∞, and is right continuous.
This property holds almost everywhere (see `has_cond_cdf_ae`). -/
def has_cond_cdf (ρ : measure (α × ℝ)) (a : α) : Prop :=
monotone (λ r, pre_cdf ρ r a) ∧ (∀ r, pre_cdf ρ r a ≤ 1)
  ∧ (tendsto (λ r, pre_cdf ρ r a) at_top (𝓝 1)) ∧ (tendsto (λ r, pre_cdf ρ r a) at_bot (𝓝 0))
  ∧ (∀ t : ℚ, (⨅ r : Ioi t, pre_cdf ρ r a) = pre_cdf ρ t a)

lemma has_cond_cdf_ae (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, has_cond_cdf ρ a :=
begin
  simp_rw [has_cond_cdf, eventually_and],
  exact ⟨monotone_pre_cdf ρ, pre_cdf_le_one ρ, tendsto_pre_cdf_at_top_one ρ,
    tendsto_pre_cdf_at_bot_zero ρ, inf_gt_pre_cdf ρ⟩,
end

/-- A measurable set of elements of `α` such that `ρ` has a conditional cdf at all
`a ∈ cond_cdf_set`. -/
def cond_cdf_set (ρ : measure (α × ℝ)) : set α := (to_measurable ρ.fst {b | ¬ has_cond_cdf ρ b})ᶜ

lemma measurable_set_cond_cdf_set (ρ : measure (α × ℝ)) : measurable_set (cond_cdf_set ρ) :=
(measurable_set_to_measurable _ _).compl

lemma has_cond_cdf_of_mem_cond_cdf_set {ρ : measure (α × ℝ)} {a : α} (h : a ∈ cond_cdf_set ρ) :
  has_cond_cdf ρ a :=
begin
  rw [cond_cdf_set, mem_compl_iff] at h,
  have h_ss := subset_to_measurable ρ.fst {b | ¬ has_cond_cdf ρ b},
  by_contra ha,
  exact h (h_ss ha),
end

lemma mem_cond_cdf_set_ae (ρ : measure (α × ℝ)) [is_finite_measure ρ] :
  ∀ᵐ a ∂ρ.fst, a ∈ cond_cdf_set ρ :=
begin
  simp_rw [ae_iff, cond_cdf_set, not_mem_compl_iff, set_of_mem_eq, measure_to_measurable],
  exact has_cond_cdf_ae ρ,
end

end has_cond_cdf


open_locale classical

/-- Conditional cdf of the measure given the value on `α`, restricted to the rationals.
It is defined to be `pre_cdf` if `a ∈ cond_cdf_set`, and a default cdf-like function
otherwise. This is an auxiliary definition used to define `cond_cdf`. -/
noncomputable
def cond_cdf_rat (ρ : measure (α × ℝ)) : α → ℚ → ℝ :=
λ a, if a ∈ cond_cdf_set ρ then (λ r, (pre_cdf ρ r a).to_real) else (λ r, if r < 0 then 0 else 1)

lemma cond_cdf_rat_of_not_mem (ρ : measure (α × ℝ)) (a : α) (h : a ∉ cond_cdf_set ρ) {r : ℚ} :
  cond_cdf_rat ρ a r = if r < 0 then 0 else 1 :=
by simp only [cond_cdf_rat, h, if_false]

lemma cond_cdf_rat_of_mem (ρ : measure (α × ℝ)) (a : α) (h : a ∈ cond_cdf_set ρ) (r : ℚ) :
  cond_cdf_rat ρ a r = (pre_cdf ρ r a).to_real :=
by simp only [cond_cdf_rat, h, if_true]

lemma monotone_cond_cdf_rat (ρ : measure (α × ℝ)) (a : α) :
  monotone (cond_cdf_rat ρ a) :=
begin
  by_cases h : a ∈ cond_cdf_set ρ,
  { simp only [cond_cdf_rat, h, if_true, forall_const, and_self],
    intros r r' hrr',
    have h' := has_cond_cdf_of_mem_cond_cdf_set h,
    have h_ne_top : ∀ r, pre_cdf ρ r a ≠ ∞ := λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne,
    rw ennreal.to_real_le_to_real (h_ne_top _) (h_ne_top _),
    exact h'.1 hrr', },
  { simp only [cond_cdf_rat, h, if_false],
    intros x y hxy,
    dsimp only,
    split_ifs,
    exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl], },
end

lemma measurable_cond_cdf_rat (ρ : measure (α × ℝ)) (q : ℚ) :
  measurable (λ a, cond_cdf_rat ρ a q) :=
begin
  simp_rw [cond_cdf_rat, ite_apply],
  exact measurable.ite (measurable_set_cond_cdf_set ρ) measurable_pre_cdf.ennreal_to_real
    measurable_const,
end

lemma cond_cdf_rat_nonneg (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  0 ≤ cond_cdf_rat ρ a r :=
by { unfold cond_cdf_rat, split_ifs, exacts [ennreal.to_real_nonneg, le_rfl, zero_le_one], }

lemma cond_cdf_rat_le_one (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  cond_cdf_rat ρ a r ≤ 1 :=
begin
  unfold cond_cdf_rat,
  split_ifs with h,
  { refine ennreal.to_real_le_of_le_of_real zero_le_one _,
    rw ennreal.of_real_one,
    exact (has_cond_cdf_of_mem_cond_cdf_set h).2.1 r, },
  exacts [zero_le_one, le_rfl],
end

lemma tendsto_cond_cdf_rat_at_bot (ρ : measure (α × ℝ)) (a : α) :
  tendsto (cond_cdf_rat ρ a) at_bot (𝓝 0) :=
begin
  unfold cond_cdf_rat,
  split_ifs with h,
  { rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff],
    { exact (has_cond_cdf_of_mem_cond_cdf_set h).2.2.2.1, },
    { have h' := has_cond_cdf_of_mem_cond_cdf_set h,
      exact λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne, },
    { exact ennreal.zero_ne_top, }, },
  { refine (tendsto_congr' _).mp tendsto_const_nhds,
    rw [eventually_eq, eventually_at_bot],
    refine ⟨-1, λ q hq, (if_pos (hq.trans_lt _)).symm⟩,
    linarith, },
end

lemma tendsto_cond_cdf_rat_at_top (ρ : measure (α × ℝ)) (a : α) :
  tendsto (cond_cdf_rat ρ a) at_top (𝓝 1) :=
begin
  unfold cond_cdf_rat,
  split_ifs with h,
  { have h' := has_cond_cdf_of_mem_cond_cdf_set h,
    rw [← ennreal.one_to_real, ennreal.tendsto_to_real_iff],
    { exact h'.2.2.1, },
    { exact λ r, ((h'.2.1 r).trans_lt ennreal.one_lt_top).ne, },
    { exact ennreal.one_ne_top, }, },
  { refine (tendsto_congr' _).mp tendsto_const_nhds,
    rw [eventually_eq, eventually_at_top],
    exact ⟨0, λ q hq, (if_neg (not_lt.mpr hq)).symm⟩, },
end

lemma cond_cdf_rat_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, cond_cdf_rat ρ a r) =ᵐ[ρ.fst] λ a, (pre_cdf ρ r a).to_real :=
by filter_upwards [mem_cond_cdf_set_ae ρ] with a ha using cond_cdf_rat_of_mem ρ a ha r

lemma of_real_cond_cdf_rat_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, ennreal.of_real (cond_cdf_rat ρ a r)) =ᵐ[ρ.fst] pre_cdf ρ r :=
begin
  filter_upwards [cond_cdf_rat_ae_eq ρ r, pre_cdf_le_one ρ] with a ha ha_le_one,
  rw [ha, ennreal.of_real_to_real],
  exact ((ha_le_one r).trans_lt ennreal.one_lt_top).ne,
end

lemma inf_gt_cond_cdf_rat (ρ : measure (α × ℝ)) (a : α) (t : ℚ) :
  (⨅ r : Ioi t, cond_cdf_rat ρ a r) = cond_cdf_rat ρ a t :=
begin
  by_cases ha : a ∈ cond_cdf_set ρ,
  { simp_rw cond_cdf_rat_of_mem ρ a ha,
    have ha' := has_cond_cdf_of_mem_cond_cdf_set ha,
    rw ← ennreal.to_real_infi,
    { suffices : (⨅ (i : ↥(Ioi t)), pre_cdf ρ ↑i a) = pre_cdf ρ t a, by rw this,
      rw ← ha'.2.2.2.2, },
    { exact λ r, ((ha'.2.1 r).trans_lt ennreal.one_lt_top).ne, }, },
  { simp_rw cond_cdf_rat_of_not_mem ρ a ha,
    have h_bdd : bdd_below (range (λ (r : ↥(Ioi t)), ite ((r : ℚ) < 0) (0 : ℝ) 1)),
    { refine ⟨0, λ x hx, _⟩,
      obtain ⟨y, rfl⟩ := mem_range.mpr hx,
      dsimp only,
      split_ifs,
      exacts [le_rfl, zero_le_one], },
    split_ifs with h h,
    { refine le_antisymm _ (le_cinfi (λ x, _)),
      { obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0,
        { refine ⟨t/2, _, _⟩,
          { linarith, },
          { linarith, }, },
        refine (cinfi_le h_bdd ⟨q, htq⟩).trans _,
        rw if_pos,
        rwa subtype.coe_mk, },
      { split_ifs,
        exacts [le_rfl, zero_le_one], }, },
    { refine le_antisymm _ _,
      { refine (cinfi_le h_bdd ⟨t+1, lt_add_one t⟩).trans _,
        split_ifs,
        exacts [zero_le_one, le_rfl], },
      { refine le_cinfi (λ x, _),
        rw if_neg,
        rw not_lt at h ⊢,
        exact h.trans (mem_Ioi.mp x.prop).le, }, }, },
end

/-- Conditional cdf of the measure given the value on `α`, as a plain function. This is an auxiliary
definition used to define `cond_cdf`. -/
noncomputable
def cond_cdf' (ρ : measure (α × ℝ)) : α → ℝ → ℝ :=
λ a t, ⨅ r : {r' : ℚ // t < r'}, cond_cdf_rat ρ a r

lemma cond_cdf'_eq_cond_cdf_rat (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  cond_cdf' ρ a r = cond_cdf_rat ρ a r :=
begin
  rw [← inf_gt_cond_cdf_rat ρ a r, cond_cdf'],
  refine equiv.infi_congr _ _,
  { exact
    { to_fun := λ t, ⟨t.1, by exact_mod_cast t.2⟩,
      inv_fun := λ t, ⟨t.1, by exact_mod_cast t.2⟩,
      left_inv := λ t, by simp only [subtype.val_eq_coe, subtype.coe_eta],
      right_inv := λ t, by simp only [subtype.val_eq_coe, subtype.coe_eta], }, },
  { intro t,
    simp only [subtype.val_eq_coe, equiv.coe_fn_mk, subtype.coe_mk], },
end

lemma cond_cdf'_nonneg (ρ : measure (α × ℝ)) (a : α) (r : ℝ) :
  0 ≤ cond_cdf' ρ a r :=
begin
  haveI : nonempty {r' : ℚ // r < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt r,
    exact ⟨⟨r, hrx⟩⟩, },
  exact le_cinfi (λ r', cond_cdf_rat_nonneg ρ a _),
end

lemma bdd_below_range_cond_cdf_rat_gt (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  bdd_below (range (λ (r : {r' : ℚ // x < ↑r'}), cond_cdf_rat ρ a r)) :=
by { refine ⟨0, λ z, _⟩, rintros ⟨u, rfl⟩, exact cond_cdf_rat_nonneg ρ a _, }

lemma monotone_cond_cdf' (ρ : measure (α × ℝ)) (a : α) : monotone (cond_cdf' ρ a) :=
begin
  intros x y hxy,
  haveI : nonempty {r' : ℚ // y < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt y,
    exact ⟨⟨r, hrx⟩⟩, },
  refine le_cinfi (λ r, (cinfi_le _ _).trans_eq _),
  { exact ⟨r.1, hxy.trans_lt r.prop⟩, },
  { exact bdd_below_range_cond_cdf_rat_gt ρ a x, },
  { refl, },
end

lemma continuous_within_at_cond_cdf'_Ici (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  continuous_within_at (cond_cdf' ρ a) (Ici x) x :=
begin
  rw ← continuous_within_at_Ioi_iff_Ici,
  convert monotone.tendsto_nhds_within_Ioi (monotone_cond_cdf' ρ a) x,
  rw Inf_image',
  have h' : (⨅ r : Ioi x, cond_cdf' ρ a r) = ⨅ r : {r' : ℚ // x < r'}, cond_cdf' ρ a r,
  { refine infi_Ioi_eq_infi_rat_gt x _ (monotone_cond_cdf' ρ a),
    refine ⟨0, λ z, _⟩,
    rintros ⟨u, hux, rfl⟩,
    exact cond_cdf'_nonneg ρ a u, },
  have h'' : (⨅ r : {r' : ℚ // x < r'}, cond_cdf' ρ a r)
    = ⨅ r : {r' : ℚ // x < r'}, cond_cdf_rat ρ a r,
  { congr' with r,
    exact cond_cdf'_eq_cond_cdf_rat ρ a r, },
  rw [h', h''],
  refl,
end

/-! ### Conditional cdf -/

/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
noncomputable
def cond_cdf (ρ : measure (α × ℝ)) (a : α) : stieltjes_function :=
{ to_fun := cond_cdf' ρ a,
  mono' := monotone_cond_cdf' ρ a,
  right_continuous' := λ x, continuous_within_at_cond_cdf'_Ici ρ a x, }

lemma cond_cdf_eq_cond_cdf_rat (ρ : measure (α × ℝ)) (a : α) (r : ℚ) :
  cond_cdf ρ a r = cond_cdf_rat ρ a r :=
cond_cdf'_eq_cond_cdf_rat ρ a r

lemma cond_cdf_eq_infi_cond_cdf (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  cond_cdf ρ a x = ⨅ r : {r' : ℚ // x < r'}, cond_cdf ρ a r :=
begin
  have : (⨅ r : {r' : ℚ // x < ↑r'}, cond_cdf ρ a ↑r)
    = ⨅ r : {r' : ℚ // x < r'}, cond_cdf ρ a (r : ℚ),
  { congr, },
  rw this,
  simp_rw cond_cdf_eq_cond_cdf_rat ρ a,
  refl,
end

/-- The conditional cdf is non-negative for all `a : α`. -/
lemma cond_cdf_nonneg (ρ : measure (α × ℝ)) (a : α) (r : ℝ) :
  0 ≤ cond_cdf ρ a r :=
cond_cdf'_nonneg ρ a r

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
lemma cond_cdf_le_one (ρ : measure (α × ℝ)) (a : α) (x : ℝ) :
  cond_cdf ρ a x ≤ 1 :=
begin
  obtain ⟨r, hrx⟩ := exists_rat_gt x,
  refine cinfi_le_of_le (bdd_below_range_cond_cdf_rat_gt ρ a x) _ (cond_cdf_rat_le_one _ _ _),
  exact ⟨r, hrx⟩,
end

/-- The conditional cdf is monotone for all `a : α`. -/
lemma monotone_cond_cdf (ρ : measure (α × ℝ)) (a : α) : monotone (cond_cdf ρ a) :=
(cond_cdf ρ a).mono

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
lemma tendsto_cond_cdf_at_bot (ρ : measure (α × ℝ)) (a : α) :
  tendsto (cond_cdf ρ a) at_bot (𝓝 0) :=
begin
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := λ x, exists_rat_btwn (lt_add_one x),
  let qs : ℝ → ℚ := λ x, (h_exists x).some,
  have hqs_tendsto : tendsto qs at_bot at_bot,
  { rw tendsto_at_bot_at_bot,
    refine λ q, ⟨q - 1, λ y hy, _⟩,
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      ((h_exists y).some_spec.2.le).trans (add_le_add hy le_rfl),
    rw sub_add_cancel at h_le,
    exact_mod_cast h_le, },
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((tendsto_cond_cdf_rat_at_bot ρ a).comp hqs_tendsto) (cond_cdf_nonneg ρ a) (λ x, _),
  rw [function.comp_apply, ← cond_cdf_eq_cond_cdf_rat],
  exact monotone_cond_cdf ρ a (h_exists x).some_spec.1.le,
end

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
lemma tendsto_cond_cdf_at_top (ρ : measure (α × ℝ)) (a : α) :
  tendsto (cond_cdf ρ a) at_top (𝓝 1) :=
begin
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x-1 < q ∧ ↑q < x := λ x, exists_rat_btwn (sub_one_lt x),
  let qs : ℝ → ℚ := λ x, (h_exists x).some,
  have hqs_tendsto : tendsto qs at_top at_top,
  { rw tendsto_at_top_at_top,
    refine λ q, ⟨q + 1, λ y hy, _⟩,
    have h_le : y - 1 ≤ qs y := (h_exists y).some_spec.1.le,
    rw sub_le_iff_le_add at h_le,
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le),},
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((tendsto_cond_cdf_rat_at_top ρ a).comp hqs_tendsto) tendsto_const_nhds _ (cond_cdf_le_one ρ a),
  intro x,
  rw [function.comp_apply, ← cond_cdf_eq_cond_cdf_rat],
  exact monotone_cond_cdf ρ a (le_of_lt (h_exists x).some_spec.2),
end

lemma cond_cdf_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, cond_cdf ρ a r) =ᵐ[ρ.fst] λ a, (pre_cdf ρ r a).to_real :=
by filter_upwards [mem_cond_cdf_set_ae ρ] with a ha
  using (cond_cdf_eq_cond_cdf_rat ρ a r).trans (cond_cdf_rat_of_mem ρ a ha r)

lemma of_real_cond_cdf_ae_eq (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ) :
  (λ a, ennreal.of_real (cond_cdf ρ a r)) =ᵐ[ρ.fst] pre_cdf ρ r :=
begin
  filter_upwards [cond_cdf_ae_eq ρ r, pre_cdf_le_one ρ] with a ha ha_le_one,
  rw [ha, ennreal.of_real_to_real],
  exact ((ha_le_one r).trans_lt ennreal.one_lt_top).ne,
end

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
lemma measurable_cond_cdf (ρ : measure (α × ℝ)) (x : ℝ) :
  measurable (λ a, cond_cdf ρ a x) :=
measurable_cinfi (λ q, measurable_cond_cdf_rat ρ q) (λ a, bdd_below_range_cond_cdf_rat_gt ρ a _)

/-- Auxiliary lemma for `set_lintegral_cond_cdf`. -/
lemma set_lintegral_cond_cdf_rat (ρ : measure (α × ℝ)) [is_finite_measure ρ] (r : ℚ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, ennreal.of_real (cond_cdf ρ a r) ∂ρ.fst = ρ (s ×ˢ Iic r) :=
begin
  have : ∀ᵐ a ∂ρ.fst, a ∈ s → ennreal.of_real (cond_cdf ρ a r) = pre_cdf ρ r a,
  { filter_upwards [of_real_cond_cdf_ae_eq ρ r] with a ha using λ _, ha, },
  rw [set_lintegral_congr_fun hs this, set_lintegral_pre_cdf_fst ρ r hs],
  exact ρ.Iic_snd_apply r hs,
end

lemma set_lintegral_cond_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] (x : ℝ)
  {s : set α} (hs : measurable_set s) :
  ∫⁻ a in s, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
begin
  by_cases hρ_zero : ρ.fst.restrict s = 0,
  { rw [hρ_zero, lintegral_zero_measure],
    refine le_antisymm (zero_le _) _,
    calc ρ (s ×ˢ Iic x)
        ≤ ρ (prod.fst ⁻¹' s) : measure_mono (prod_subset_preimage_fst s (Iic x))
    ... = ρ.fst s : by rw [measure.fst_apply hs]
    ... = ρ.fst.restrict s univ : by rw measure.restrict_apply_univ
    ... = 0 : by simp only [hρ_zero, measure.coe_zero, pi.zero_apply], },
  have h : ∫⁻ a in s, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst
    = ∫⁻ a in s, ennreal.of_real (⨅ r : {r' : ℚ // x < r'}, cond_cdf ρ a r) ∂ρ.fst,
  { congr' with a : 1,
    rw cond_cdf_eq_infi_cond_cdf ρ a x, },
  haveI h_nonempty : nonempty {r' : ℚ // x < ↑r'},
  { obtain ⟨r, hrx⟩ := exists_rat_gt x,
    exact ⟨⟨r, hrx⟩⟩, },
  rw h,
  simp_rw ennreal.of_real_cinfi,
  have h_coe : ∀ b : {r' : ℚ // x < ↑r'}, (b : ℝ) = ((b : ℚ) : ℝ) := λ _, by congr,
  rw lintegral_infi_directed_of_measurable hρ_zero
    (λ q : {r' : ℚ // x < ↑r'}, (measurable_cond_cdf ρ q).ennreal_of_real),
  rotate,
  { intro b,
    simp_rw h_coe,
    rw [set_lintegral_cond_cdf_rat ρ _ hs],
    exact measure_ne_top ρ _, },
  { refine monotone.directed_ge (λ i j hij a, ennreal.of_real_le_of_real (monotone_cond_cdf ρ a _)),
    rw [h_coe, h_coe],
    exact_mod_cast hij, },
  simp_rw [h_coe, set_lintegral_cond_cdf_rat ρ _ hs],
  rw ← measure_Inter_eq_infi,
  { rw ← prod_Inter,
    congr' with y,
    simp only [mem_Inter, mem_Iic, subtype.forall, subtype.coe_mk],
    exact ⟨le_of_forall_lt_rat_imp_le, λ hyx q hq, hyx.trans hq.le⟩, },
  { exact λ i, hs.prod measurable_set_Iic, },
  { refine monotone.directed_ge (λ i j hij, _),
    refine prod_subset_prod_iff.mpr (or.inl ⟨subset_rfl, Iic_subset_Iic.mpr _⟩),
    exact_mod_cast hij, },
  { exact ⟨h_nonempty.some, measure_ne_top _ _⟩, },
end

lemma lintegral_cond_cdf (ρ : measure (α × ℝ)) [is_finite_measure ρ] (x : ℝ) :
  ∫⁻ a, ennreal.of_real (cond_cdf ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
by rw [← set_lintegral_univ, set_lintegral_cond_cdf ρ _ measurable_set.univ]

end probability_theory
