/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import dynamics.ergodic.measure_preserving
import measure_theory.function.simple_func
import measure_theory.measure.mutually_singular

/-!
# Lower Lebesgue integral for `ℝ≥0∞`-valued functions

We define the lower Lebesgue integral of an `ℝ≥0∞`-valued function.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.

-/

noncomputable theory
open set (hiding restrict restrict_apply) filter ennreal function (support)
open_locale classical topology big_operators nnreal ennreal measure_theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

variables {α β γ δ : Type*}

section lintegral

open simple_func

variables {m : measurable_space α} {μ ν : measure α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
@[irreducible] def lintegral {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
⨆ (g : α →ₛ ℝ≥0∞) (hf : ⇑g ≤ f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/
notation `∫⁻` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := lintegral μ r
notation `∫⁻` binders `, ` r:(scoped:60 f, lintegral volume f) := r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 :=
  lintegral (measure.restrict μ s) r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, lintegral (measure.restrict volume s) f) := r

theorem simple_func.lintegral_eq_lintegral {m : measurable_space α} (f : α →ₛ ℝ≥0∞)
  (μ : measure α) :
  ∫⁻ a, f a ∂ μ = f.lintegral μ :=
begin
  rw lintegral,
  exact le_antisymm
    (supr₂_le $ λ g hg, lintegral_mono hg $ le_rfl)
    (le_supr₂_of_le f le_rfl le_rfl)
end

@[mono] lemma lintegral_mono' {m : measurable_space α} ⦃μ ν : measure α⦄ (hμν : μ ≤ ν)
  ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν :=
begin
  rw [lintegral, lintegral],
  exact supr_mono (λ φ, supr_mono' $ λ hφ, ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩)
end

lemma lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
lintegral_mono' (le_refl μ) hfg

lemma lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
lintegral_mono $ λ a, ennreal.coe_le_coe.2 (h a)

lemma supr_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
  (⨆ (g : α → ℝ≥0∞) (g_meas : measurable g) (hg : g ≤ f), ∫⁻ a, g a ∂μ) = ∫⁻ a, f a ∂μ :=
begin
  apply le_antisymm,
  { exact supr_le (λ i, supr_le (λ hi, supr_le (λ h'i, lintegral_mono h'i))) },
  { rw lintegral,
    refine supr₂_le (λ i hi, le_supr₂_of_le i i.measurable $ le_supr_of_le hi _),
    exact le_of_eq (i.lintegral_eq_lintegral _).symm },
end

lemma lintegral_mono_set {m : measurable_space α} ⦃μ : measure α⦄
  {s t : set α} {f : α → ℝ≥0∞} (hst : s ⊆ t) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
lintegral_mono' (measure.restrict_mono hst (le_refl μ)) (le_refl f)

lemma lintegral_mono_set' {m : measurable_space α} ⦃μ : measure α⦄
  {s t : set α} {f : α → ℝ≥0∞} (hst : s ≤ᵐ[μ] t) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
lintegral_mono' (measure.restrict_mono' hst (le_refl μ)) (le_refl f)

lemma monotone_lintegral {m : measurable_space α} (μ : measure α) : monotone (lintegral μ) :=
lintegral_mono

@[simp] lemma lintegral_const (c : ℝ≥0∞) : ∫⁻ a, c ∂μ = c * μ univ :=
by rw [← simple_func.const_lintegral, ← simple_func.lintegral_eq_lintegral, simple_func.coe_const]

lemma lintegral_zero : ∫⁻ a:α, 0 ∂μ = 0 := by simp

lemma lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 := lintegral_zero

@[simp] lemma lintegral_one : ∫⁻ a, (1 : ℝ≥0∞) ∂μ = μ univ :=
by rw [lintegral_const, one_mul]

lemma set_lintegral_const (s : set α) (c : ℝ≥0∞) : ∫⁻ a in s, c ∂μ = c * μ s :=
by rw [lintegral_const, measure.restrict_apply_univ]

lemma set_lintegral_one (s) : ∫⁻ a in s, 1 ∂μ = μ s :=
by rw [set_lintegral_const, one_mul]

lemma set_lintegral_const_lt_top [is_finite_measure μ] (s : set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
  ∫⁻ a in s, c ∂μ < ∞ :=
begin
  rw lintegral_const,
  exact ennreal.mul_lt_top hc (measure_ne_top (μ.restrict s) univ),
end

lemma lintegral_const_lt_top [is_finite_measure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
  ∫⁻ a, c ∂μ < ∞ :=
by simpa only [measure.restrict_univ] using set_lintegral_const_lt_top univ hc

section

variable (μ)

/-- For any function `f : α → ℝ≥0∞`, there exists a measurable function `g ≤ f` with the same
integral. -/
lemma exists_measurable_le_lintegral_eq (f : α → ℝ≥0∞) :
  ∃ g : α → ℝ≥0∞, measurable g ∧ g ≤ f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ :=
begin
  cases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ h₀,
  { exact ⟨0, measurable_zero, zero_le f, h₀.trans lintegral_zero.symm⟩ },
  rcases exists_seq_strict_mono_tendsto' h₀.bot_lt with ⟨L, hL_mono, hLf, hL_tendsto⟩,
  have : ∀ n, ∃ g : α → ℝ≥0∞, measurable g ∧ g ≤ f ∧ L n < ∫⁻ a, g a ∂μ,
  { intro n,
    simpa only [← supr_lintegral_measurable_le_eq_lintegral f, lt_supr_iff, exists_prop]
      using (hLf n).2 },
  choose g hgm hgf hLg,
  refine ⟨λ x, ⨆ n, g n x, measurable_supr hgm, λ x, supr_le (λ n, hgf n x), le_antisymm _ _⟩,
  { refine le_of_tendsto' hL_tendsto (λ n, (hLg n).le.trans $ lintegral_mono $ λ x, _),
    exact le_supr (λ n, g n x) n },
  { exact lintegral_mono (λ x, supr_le $ λ n, hgf n x) }
end

end

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
lemma lintegral_eq_nnreal {m : measurable_space α} (f : α → ℝ≥0∞) (μ : measure α) :
  (∫⁻ a, f a ∂μ) = (⨆ (φ : α →ₛ ℝ≥0) (hf : ∀ x, ↑(φ x) ≤ f x),
      (φ.map (coe : ℝ≥0 → ℝ≥0∞)).lintegral μ) :=
begin
  rw lintegral,
  refine le_antisymm
    (supr₂_le $ assume φ hφ, _)
    (supr_mono' $ λ φ, ⟨φ.map (coe : ℝ≥0 → ℝ≥0∞), le_rfl⟩),
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞,
  { let ψ := φ.map ennreal.to_nnreal,
    replace h : ψ.map (coe : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ :=
      h.mono (λ a, ennreal.coe_to_nnreal),
    have : ∀ x, ↑(ψ x) ≤ f x := λ x, le_trans ennreal.coe_to_nnreal_le_self (hφ x),
    exact le_supr_of_le (φ.map ennreal.to_nnreal)
      (le_supr_of_le this (ge_of_eq $ lintegral_congr h)) },
  { have h_meas : μ (φ ⁻¹' {∞}) ≠ 0, from mt measure_zero_iff_ae_nmem.1 h,
    refine le_trans le_top (ge_of_eq $ (supr_eq_top _).2 $ λ b hb, _),
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞}), from exists_nat_mul_gt h_meas (ne_of_lt hb),
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞}),
    simp only [lt_supr_iff, exists_prop, coe_restrict, φ.measurable_set_preimage, coe_const,
      ennreal.coe_indicator, map_coe_ennreal_restrict, simple_func.map_const, ennreal.coe_nat,
      restrict_const_lintegral],
    refine ⟨indicator_le (λ x hx, le_trans _ (hφ _)), hn⟩,
    simp only [mem_preimage, mem_singleton_iff] at hx,
    simp only [hx, le_top] }
end

lemma exists_simple_func_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
  {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ φ : α →ₛ ℝ≥0, (∀ x, ↑(φ x) ≤ f x) ∧ ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) →
    (map coe (ψ - φ)).lintegral μ < ε :=
begin
  rw lintegral_eq_nnreal at h,
  have := ennreal.lt_add_right h hε,
  erw ennreal.bsupr_add at this; [skip, exact ⟨0, λ x, zero_le _⟩],
  simp_rw [lt_supr_iff, supr_lt_iff, supr_le_iff] at this,
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩,
  refine ⟨φ, hle, λ ψ hψ, _⟩,
  have : (map coe φ).lintegral μ ≠ ∞, from ne_top_of_le_ne_top h (le_supr₂ φ hle),
  rw [← ennreal.add_lt_add_iff_left this, ← add_lintegral, ← map_add @ennreal.coe_add],
  refine (hb _ (λ x, le_trans _ (max_le (hle x) (hψ x)))).trans_lt hbφ,
  norm_cast,
  simp only [add_apply, sub_apply, add_tsub_eq_max]
end

theorem supr_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
  (⨆i, ∫⁻ a, f i a ∂μ) ≤ (∫⁻ a, ⨆i, f i a ∂μ) :=
begin
  simp only [← supr_apply],
  exact (monotone_lintegral μ).le_map_supr
end

lemma supr₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ℝ≥0∞) :
  (⨆ i j, ∫⁻ a, f i j a ∂μ) ≤ (∫⁻ a, ⨆ i j, f i j a ∂μ) :=
by { convert (monotone_lintegral μ).le_map_supr₂ f, ext1 a, simp only [supr_apply] }

theorem le_infi_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
  (∫⁻ a, ⨅i, f i a ∂μ) ≤ (⨅i, ∫⁻ a, f i a ∂μ) :=
by { simp only [← infi_apply], exact (monotone_lintegral μ).map_infi_le }

lemma le_infi₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ℝ≥0∞) :
  (∫⁻ a, ⨅ i (h : ι' i), f i h a ∂μ) ≤ (⨅ i (h : ι' i), ∫⁻ a, f i h a ∂μ) :=
by { convert (monotone_lintegral μ).map_infi₂_le f, ext1 a, simp only [infi_apply] }

lemma lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
  (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, g a ∂μ) :=
begin
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩,
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0,
  rw [lintegral, lintegral],
  refine (supr_le $ assume s, supr_le $ assume hfs,
    le_supr_of_le (s.restrict tᶜ) $ le_supr_of_le _ _),
  { assume a,
    by_cases a ∈ t;
      simp [h, restrict_apply, ht.compl],
    exact le_trans (hfs a) (by_contradiction $ assume hnfg, h (hts hnfg)) },
  { refine le_of_eq (simple_func.lintegral_congr $ this.mono $ λ a hnt, _),
    by_cases hat : a ∈ t; simp [hat, ht.compl],
    exact (hnt hat).elim }
end

lemma set_lintegral_mono_ae {s : set α} {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
lintegral_mono_ae $ (ae_restrict_iff $ measurable_set_le hf hg).2 hfg

lemma set_lintegral_mono {s : set α} {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfg : ∀ x ∈ s, f x ≤ g x) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
set_lintegral_mono_ae hf hg (ae_of_all _ hfg)

lemma lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
  (∫⁻ a, f a ∂μ) = (∫⁻ a, g a ∂μ) :=
le_antisymm (lintegral_mono_ae $ h.le) (lintegral_mono_ae $ h.symm.le)

lemma lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) :
  (∫⁻ a, f a ∂μ) = (∫⁻ a, g a ∂μ) :=
by simp only [h]

lemma set_lintegral_congr {f : α → ℝ≥0∞} {s t : set α} (h : s =ᵐ[μ] t) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
by rw [measure.restrict_congr_set h]

lemma set_lintegral_congr_fun {f g : α → ℝ≥0∞} {s : set α} (hs : measurable_set s)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
by { rw lintegral_congr_ae, rw eventually_eq, rwa ae_restrict_iff' hs, }

lemma lintegral_of_real_le_lintegral_nnnorm (f : α → ℝ) :
  ∫⁻ x, ennreal.of_real (f x) ∂μ ≤ ∫⁻ x, ‖f x‖₊ ∂μ :=
begin
  simp_rw ← of_real_norm_eq_coe_nnnorm,
  refine lintegral_mono (λ x, ennreal.of_real_le_of_real _),
  rw real.norm_eq_abs,
  exact le_abs_self (f x),
end

lemma lintegral_nnnorm_eq_of_ae_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ᵐ[μ] f) :
  ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ennreal.of_real (f x) ∂μ :=
begin
  apply lintegral_congr_ae,
  filter_upwards [h_nonneg] with x hx,
  rw [real.nnnorm_of_nonneg hx, ennreal.of_real_eq_coe_nnreal hx],
end

lemma lintegral_nnnorm_eq_of_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ f) :
  ∫⁻ x, ‖f x‖₊ ∂μ = ∫⁻ x, ennreal.of_real (f x) ∂μ :=
lintegral_nnnorm_eq_of_ae_nonneg (filter.eventually_of_forall h_nonneg)

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr
  {f : ℕ → α → ℝ≥0∞} (hf : ∀n, measurable (f n)) (h_mono : monotone f) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
begin
  set c : ℝ≥0 → ℝ≥0∞ := coe,
  set F := λ a:α, ⨆n, f n a,
  have hF : measurable F := measurable_supr hf,
  refine le_antisymm _ (supr_lintegral_le _),
  rw [lintegral_eq_nnreal],
  refine supr_le (assume s, supr_le (assume hsf, _)),
  refine ennreal.le_of_forall_lt_one_mul_le (assume a ha, _),
  rcases ennreal.lt_iff_exists_coe.1 ha with ⟨r, rfl, ha⟩,
  have ha : r < 1 := ennreal.coe_lt_coe.1 ha,
  let rs := s.map (λa, r * a),
  have eq_rs : (const α r : α →ₛ ℝ≥0∞) * map c s = rs.map c,
  { ext1 a, exact ennreal.coe_mul.symm },
  have eq : ∀p, (rs.map c) ⁻¹' {p} = (⋃n, (rs.map c) ⁻¹' {p} ∩ {a | p ≤ f n a}),
  { assume p,
    rw [← inter_Union, ← inter_univ ((map c rs) ⁻¹' {p})] {occs := occurrences.pos [1]},
    refine set.ext (assume x, and_congr_right $ assume hx, (true_iff _).2 _),
    by_cases p_eq : p = 0, { simp [p_eq] },
    simp at hx, subst hx,
    have : r * s x ≠ 0, { rwa [(≠), ← ennreal.coe_eq_zero] },
    have : s x ≠ 0, { refine mt _ this, assume h, rw [h, mul_zero] },
    have : (rs.map c) x < ⨆ (n : ℕ), f n x,
    { refine lt_of_lt_of_le (ennreal.coe_lt_coe.2 (_)) (hsf x),
      suffices : r * s x < 1 * s x, simpa [rs],
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this) },
    rcases lt_supr_iff.1 this with ⟨i, hi⟩,
    exact mem_Union.2 ⟨i, le_of_lt hi⟩ },
  have mono : ∀r:ℝ≥0∞, monotone (λn, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}),
  { assume r i j h,
    refine inter_subset_inter (subset.refl _) _,
    assume x hx, exact le_trans hx (h_mono h x) },
  have h_meas : ∀n, measurable_set {a : α | ⇑(map c rs) a ≤ f n a} :=
    assume n, measurable_set_le (simple_func.measurable _) (hf n),
  calc (r:ℝ≥0∞) * (s.map c).lintegral μ = ∑ r in (rs.map c).range, r * μ ((rs.map c) ⁻¹' {r}) :
      by rw [← const_mul_lintegral, eq_rs, simple_func.lintegral]
    ... = ∑ r in (rs.map c).range, r * μ (⋃n, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      by simp only [(eq _).symm]
    ... = ∑ r in (rs.map c).range, (⨆n, r * μ ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a})) :
      finset.sum_congr rfl $ assume x hx,
        begin
          rw [measure_Union_eq_supr (directed_of_sup $ mono x), ennreal.mul_supr],
        end
    ... = ⨆n, ∑ r in (rs.map c).range, r * μ ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      begin
        rw [ennreal.finset_sum_supr_nat],
        assume p i j h,
        exact mul_le_mul_left' (measure_mono $ mono p h) _
      end
    ... ≤ (⨆n:ℕ, ((rs.map c).restrict {a | (rs.map c) a ≤ f n a}).lintegral μ) :
    begin
      refine supr_mono (λ n, _),
      rw [restrict_lintegral _ (h_meas n)],
      { refine le_of_eq (finset.sum_congr rfl $ assume r hr, _),
        congr' 2 with a,
        refine and_congr_right _,
        simp {contextual := tt} }
    end
    ... ≤ (⨆n, ∫⁻ a, f n a ∂μ) :
    begin
      refine supr_mono (λ n, _),
      rw [← simple_func.lintegral_eq_lintegral],
      refine lintegral_mono (assume a, _),
      simp only [map_apply] at h_meas,
      simp only [coe_map, restrict_apply _ (h_meas _), (∘)],
      exact indicator_apply_le id,
    end
end

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_supr' {f : ℕ → α → ℝ≥0∞} (hf : ∀n, ae_measurable (f n) μ)
  (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x)) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
begin
  simp_rw ←supr_apply,
  let p : α → (ℕ → ℝ≥0∞) → Prop := λ x f', monotone f',
  have hp : ∀ᵐ x ∂μ, p x (λ i, f i x), from h_mono,
  have h_ae_seq_mono : monotone (ae_seq hf p),
  { intros n m hnm x,
    by_cases hx : x ∈ ae_seq_set hf p,
    { exact ae_seq.prop_of_mem_ae_seq_set hf hx hnm, },
    { simp only [ae_seq, hx, if_false],
      exact le_rfl, }, },
  rw lintegral_congr_ae (ae_seq.supr hf hp).symm,
  simp_rw supr_apply,
  rw @lintegral_supr _ _ μ _ (ae_seq.measurable hf p) h_ae_seq_mono,
  congr,
  exact funext (λ n, lintegral_congr_ae (ae_seq.ae_seq_n_eq_fun_n_ae hf hp n)),
end

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
  (hf : ∀n, ae_measurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x))
  (h_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 $ F x)) :
  tendsto (λ n, ∫⁻ x, f n x ∂μ) at_top (𝓝 $ ∫⁻ x, F x ∂μ) :=
begin
  have : monotone (λ n, ∫⁻ x, f n x ∂μ) :=
    λ i j hij, lintegral_mono_ae (h_mono.mono $ λ x hx, hx hij),
  suffices key : ∫⁻ x, F x ∂μ = ⨆n, ∫⁻ x, f n x ∂μ,
  { rw key,
    exact tendsto_at_top_supr this },
  rw ← lintegral_supr' hf h_mono,
  refine lintegral_congr_ae _,
  filter_upwards [h_mono, h_tendsto]
    with _ hx_mono hx_tendsto using tendsto_nhds_unique hx_tendsto (tendsto_at_top_supr hx_mono),
end

lemma lintegral_eq_supr_eapprox_lintegral {f : α → ℝ≥0∞} (hf : measurable f) :
  (∫⁻ a, f a ∂μ) = (⨆n, (eapprox f n).lintegral μ) :=
calc (∫⁻ a, f a ∂μ) = (∫⁻ a, ⨆n, (eapprox f n : α → ℝ≥0∞) a ∂μ) :
  by congr; ext a; rw [supr_eapprox_apply f hf]
... = (⨆n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ) :
begin
  rw [lintegral_supr],
  { measurability, },
  { assume i j h, exact (monotone_eapprox f h) }
end
... = (⨆n, (eapprox f n).lintegral μ) : by congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
lemma exists_pos_set_lintegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
  {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε :=
begin
  rcases exists_between hε.bot_lt with ⟨ε₂, hε₂0 : 0 < ε₂, hε₂ε⟩,
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩,
  rcases exists_simple_func_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, hle, hφ⟩,
  rcases φ.exists_forall_le with ⟨C, hC⟩,
  use [(ε₂ - ε₁) / C, ennreal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ennreal.coe_ne_top⟩],
  refine λ s hs, lt_of_le_of_lt _ hε₂ε,
  simp only [lintegral_eq_nnreal, supr_le_iff],
  intros ψ hψ,
  calc (map coe ψ).lintegral (μ.restrict s)
      ≤ (map coe φ).lintegral (μ.restrict s) + (map coe (ψ - φ)).lintegral (μ.restrict s) :
    begin
      rw [← simple_func.add_lintegral, ← simple_func.map_add @ennreal.coe_add],
      refine simple_func.lintegral_mono (λ x, _) le_rfl,
      simp only [add_tsub_eq_max, le_max_right, coe_map, function.comp_app, simple_func.coe_add,
        simple_func.coe_sub, pi.add_apply, pi.sub_apply, with_top.coe_max]
    end
  ... ≤ (map coe φ).lintegral (μ.restrict s) + ε₁ :
    begin
      refine add_le_add le_rfl (le_trans _ (hφ _ hψ).le),
      exact simple_func.lintegral_mono le_rfl measure.restrict_le_self
    end
  ... ≤ (simple_func.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ :
    add_le_add (simple_func.lintegral_mono (λ x, coe_le_coe.2 (hC x)) le_rfl) le_rfl
  ... = C * μ s + ε₁ : by simp only [←simple_func.lintegral_eq_lintegral, coe_const,
    lintegral_const, measure.restrict_apply, measurable_set.univ, univ_inter]
  ... ≤ C * ((ε₂ - ε₁) / C) + ε₁ :
    add_le_add_right (mul_le_mul_left' hs.le _) _
  ... ≤ (ε₂ - ε₁) + ε₁ : add_le_add mul_div_le le_rfl
  ... = ε₂ : tsub_add_cancel_of_le hε₁₂.le,
end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma tendsto_set_lintegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
  {l : filter ι} {s : ι → set α} (hl : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫⁻ x in s i, f x ∂μ) l (𝓝 0) :=
begin
  simp only [ennreal.nhds_zero, tendsto_infi, tendsto_principal, mem_Iio, ← pos_iff_ne_zero]
    at hl ⊢,
  intros ε ε0,
  rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩,
  exact (hl δ δ0).mono (λ i, hδ _)
end

/-- The sum of the lower Lebesgue integrals of two functions is less than or equal to the integral
of their sum. The other inequality needs one of these functions to be (a.e.-)measurable. -/
lemma le_lintegral_add (f g : α → ℝ≥0∞) : ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ :=
begin
  dunfold lintegral,
  refine ennreal.bsupr_add_bsupr_le' ⟨0, zero_le f⟩  ⟨0, zero_le g⟩ (λ f' hf' g' hg', _),
  exact le_supr₂_of_le (f' + g') (add_le_add hf' hg') (add_lintegral _ _).ge
end

-- Use stronger lemmas `lintegral_add_left`/`lintegral_add_right` instead
lemma lintegral_add_aux {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
calc (∫⁻ a, f a + g a ∂μ) =
    (∫⁻ a, (⨆n, (eapprox f n : α → ℝ≥0∞) a) + (⨆n, (eapprox g n : α → ℝ≥0∞) a) ∂μ) :
    by simp only [supr_eapprox_apply, hf, hg]
  ... = (∫⁻ a, (⨆n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a) ∂μ) :
  begin
    congr, funext a,
    rw [ennreal.supr_add_supr_of_monotone], { refl },
    { assume i j h, exact monotone_eapprox _ h a },
    { assume i j h, exact monotone_eapprox _ h a },
  end
  ... = (⨆n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ) :
  begin
    rw [lintegral_supr],
    { congr,
      funext n, rw [← simple_func.add_lintegral, ← simple_func.lintegral_eq_lintegral],
      refl },
    { measurability, },
    { assume i j h a, exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _) }
  end
  ... = (⨆n, (eapprox f n).lintegral μ) + (⨆n, (eapprox g n).lintegral μ) :
  by refine (ennreal.supr_add_supr_of_monotone _ _).symm;
     { assume i j h, exact simple_func.lintegral_mono (monotone_eapprox _ h) (le_refl μ) }
  ... = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :
    by rw [lintegral_eq_supr_eapprox_lintegral hf, lintegral_eq_supr_eapprox_lintegral hg]

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `f` is integrable, see also
`measure_theory.lintegral_add_right` and primed versions of these lemmas. -/
@[simp] lemma lintegral_add_left {f : α → ℝ≥0∞} (hf : measurable f) (g : α → ℝ≥0∞) :
  ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
begin
  refine le_antisymm _ (le_lintegral_add _ _),
  rcases exists_measurable_le_lintegral_eq μ (λ a, f a + g a) with ⟨φ, hφm, hφ_le, hφ_eq⟩,
  calc ∫⁻ a, f a + g a ∂μ = ∫⁻ a, φ a ∂μ : hφ_eq
  ... ≤ ∫⁻ a, f a + (φ a - f a) ∂μ        : lintegral_mono (λ a, le_add_tsub)
  ... = ∫⁻ a, f a ∂μ + ∫⁻ a, φ a - f a ∂μ : lintegral_add_aux hf (hφm.sub hf)
  ... ≤ ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ       :
    add_le_add_left (lintegral_mono $ λ a, tsub_le_iff_left.2 $ hφ_le a) _
end

lemma lintegral_add_left' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (g : α → ℝ≥0∞) :
  ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
by rw [lintegral_congr_ae hf.ae_eq_mk, ← lintegral_add_left hf.measurable_mk,
  lintegral_congr_ae (hf.ae_eq_mk.add (ae_eq_refl g))]

lemma lintegral_add_right' (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : ae_measurable g μ) :
  ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
by simpa only [add_comm] using lintegral_add_left' hg f

/-- If `f g : α → ℝ≥0∞` are two functions and one of them is (a.e.) measurable, then the Lebesgue
integral of `f + g` equals the sum of integrals. This lemma assumes that `g` is integrable, see also
`measure_theory.lintegral_add_left` and primed versions of these lemmas. -/
@[simp] lemma lintegral_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
lintegral_add_right' f hg.ae_measurable

@[simp] lemma lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂ (c • μ) = c * ∫⁻ a, f a ∂μ :=
by simp only [lintegral, supr_subtype', simple_func.lintegral_smul, ennreal.mul_supr, smul_eq_mul]

@[simp] lemma lintegral_sum_measure {m : measurable_space α} {ι} (f : α → ℝ≥0∞)
  (μ : ι → measure α) :
  ∫⁻ a, f a ∂(measure.sum μ) = ∑' i, ∫⁻ a, f a ∂(μ i) :=
begin
  simp only [lintegral, supr_subtype', simple_func.lintegral_sum, ennreal.tsum_eq_supr_sum],
  rw [supr_comm],
  congr, funext s,
  induction s using finset.induction_on with i s hi hs, { apply bot_unique, simp },
  simp only [finset.sum_insert hi, ← hs],
  refine (ennreal.supr_add_supr _).symm,
  intros φ ψ,
  exact ⟨⟨φ ⊔ ψ, λ x, sup_le (φ.2 x) (ψ.2 x)⟩,
    add_le_add (simple_func.lintegral_mono le_sup_left le_rfl)
      (finset.sum_le_sum $ λ j hj, simple_func.lintegral_mono le_sup_right le_rfl)⟩
end

theorem has_sum_lintegral_measure {ι} {m : measurable_space α} (f : α → ℝ≥0∞) (μ : ι → measure α) :
  has_sum (λ i, ∫⁻ a, f a ∂(μ i)) (∫⁻ a, f a ∂(measure.sum μ)) :=
(lintegral_sum_measure f μ).symm ▸ ennreal.summable.has_sum

@[simp] lemma lintegral_add_measure {m : measurable_space α} (f : α → ℝ≥0∞) (μ ν : measure α) :
  ∫⁻ a, f a ∂ (μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν :=
by simpa [tsum_fintype] using lintegral_sum_measure f (λ b, cond b μ ν)

@[simp] lemma lintegral_finset_sum_measure {ι} {m : measurable_space α} (s : finset ι)
  (f : α → ℝ≥0∞) (μ : ι → measure α) :
  ∫⁻ a, f a ∂(∑ i in s, μ i) = ∑ i in s, ∫⁻ a, f a ∂μ i :=
by { rw [← measure.sum_coe_finset, lintegral_sum_measure, ← finset.tsum_subtype'], refl }

@[simp] lemma lintegral_zero_measure {m : measurable_space α} (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂(0 : measure α) = 0 :=
bot_unique $ by simp [lintegral]

lemma set_lintegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 :=
by rw [measure.restrict_empty, lintegral_zero_measure]

lemma set_lintegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw measure.restrict_univ

lemma set_lintegral_measure_zero (s : set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
  ∫⁻ x in s, f x ∂μ = 0 :=
begin
  convert lintegral_zero_measure _,
  exact measure.restrict_eq_zero.2 hs',
end

lemma lintegral_finset_sum' (s : finset β) {f : β → α → ℝ≥0∞}
  (hf : ∀ b ∈ s, ae_measurable (f b) μ) :
  (∫⁻ a, ∑ b in s, f b a ∂μ) = ∑ b in s, ∫⁻ a, f b a ∂μ :=
begin
  induction s using finset.induction_on with a s has ih,
  { simp },
  { simp only [finset.sum_insert has],
    rw [finset.forall_mem_insert] at hf,
    rw [lintegral_add_left' hf.1, ih hf.2] }
end

lemma lintegral_finset_sum (s : finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, measurable (f b)) :
  (∫⁻ a, ∑ b in s, f b a ∂μ) = ∑ b in s, ∫⁻ a, f b a ∂μ :=
lintegral_finset_sum' s (λ b hb, (hf b hb).ae_measurable)

@[simp] lemma lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
calc (∫⁻ a, r * f a ∂μ) = (∫⁻ a, (⨆n, (const α r * eapprox f n) a) ∂μ) :
    by { congr, funext a, rw [← supr_eapprox_apply f hf, ennreal.mul_supr], refl }
  ... = (⨆n, r * (eapprox f n).lintegral μ) :
  begin
    rw [lintegral_supr],
    { congr, funext n,
      rw [← simple_func.const_mul_lintegral, ← simple_func.lintegral_eq_lintegral] },
    { assume n, exact simple_func.measurable _ },
    { assume i j h a, exact mul_le_mul_left' (monotone_eapprox _ h _) _ }
  end
  ... = r * (∫⁻ a, f a ∂μ) : by rw [← ennreal.mul_supr, lintegral_eq_supr_eapprox_lintegral hf]

lemma lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
begin
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk,
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (eventually_eq.fun_comp hf.ae_eq_mk _),
  rw [A, B, lintegral_const_mul _ hf.measurable_mk],
end

lemma lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
  r * (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, r * f a ∂μ) :=
begin
  rw [lintegral, ennreal.mul_supr],
  refine supr_le (λs, _),
  rw [ennreal.mul_supr],
  simp only [supr_le_iff],
  assume hs,
  rw [← simple_func.const_mul_lintegral, lintegral],
  refine le_supr_of_le (const α r * s) (le_supr_of_le (λx, _) le_rfl),
  exact mul_le_mul_left' (hs x) _
end

lemma lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
begin
  by_cases h : r = 0,
  { simp [h] },
  apply le_antisymm _ (lintegral_const_mul_le r f),
  have rinv : r * r⁻¹  = 1 := ennreal.mul_inv_cancel h hr,
  have rinv' : r ⁻¹ * r = 1, by { rw mul_comm, exact rinv },
  have := lintegral_const_mul_le (r⁻¹) (λx, r * f x),
  simp [(mul_assoc _ _ _).symm, rinv'] at this,
  simpa [(mul_assoc _ _ _).symm, rinv]
    using mul_le_mul_left' this r
end

lemma lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul r hf]

lemma lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul'' r hf]

lemma lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂μ * r ≤ ∫⁻ a, f a * r ∂μ :=
by simp_rw [mul_comm, lintegral_const_mul_le r f]

lemma lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞):
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul' r f hr]

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
lemma lintegral_lintegral_mul {β} [measurable_space β] {ν : measure β}
  {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : ae_measurable f μ) (hg : ae_measurable g ν) :
  ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = ∫⁻ x, f x ∂μ * ∫⁻ y, g y ∂ν :=
by simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
  (∫⁻ a, g (f a) ∂μ) = (∫⁻ a, g (f' a) ∂μ) :=
lintegral_congr_ae $ h.mono $ λ a h, by rw h

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁')
  (h₂ : f₂ =ᵐ[μ] f₂') (g : β → γ → ℝ≥0∞) :
  (∫⁻ a, g (f₁ a) (f₂ a) ∂μ) = (∫⁻ a, g (f₁' a) (f₂' a) ∂μ) :=
lintegral_congr_ae $ h₁.mp $ h₂.mono $ λ _ h₂ h₁, by rw [h₁, h₂]

@[simp] lemma lintegral_indicator (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ :=
begin
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, supr_subtype'],
  apply le_antisymm; refine supr_mono' (subtype.forall.2 $ λ φ hφ, _),
  { refine ⟨⟨φ, le_trans hφ (indicator_le_self _ _)⟩, _⟩,
    refine simple_func.lintegral_mono (λ x, _) le_rfl,
    by_cases hx : x ∈ s,
    { simp [hx, hs, le_refl] },
    { apply le_trans (hφ x),
      simp [hx, hs, le_refl] } },
  { refine ⟨⟨φ.restrict s, λ x, _⟩, le_rfl⟩,
    simp [hφ x, hs, indicator_le_indicator] }
end

lemma lintegral_indicator₀ (f : α → ℝ≥0∞) {s : set α} (hs : null_measurable_set s μ) :
  ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ :=
by rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.to_measurable_ae_eq),
  lintegral_indicator _ (measurable_set_to_measurable _ _),
  measure.restrict_congr_set hs.to_measurable_ae_eq]

lemma lintegral_indicator_const {s : set α} (hs : measurable_set s) (c : ℝ≥0∞) :
  ∫⁻ a, s.indicator (λ _, c) a ∂μ = c * μ s :=
by rw [lintegral_indicator _ hs, set_lintegral_const]

lemma set_lintegral_eq_const {f : α → ℝ≥0∞} (hf : measurable f) (r : ℝ≥0∞) :
  ∫⁻ x in {x | f x = r}, f x ∂μ = r * μ {x | f x = r} :=
begin
  have : ∀ᵐ x ∂μ, x ∈ {x | f x = r} → f x = r := ae_of_all μ (λ _ hx, hx),
  rw [set_lintegral_congr_fun _ this],
  dsimp,
  rw [lintegral_const, measure.restrict_apply measurable_set.univ, set.univ_inter],
  exact hf (measurable_set_singleton r)
end

/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
lemma lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
  (hg : ae_measurable g μ) (ε : ℝ≥0∞) :
  ∫⁻ a, f a ∂μ + ε * μ {x | f x + ε ≤ g x} ≤ ∫⁻ a, g a ∂μ :=
begin
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩,
  calc ∫⁻ x, f x ∂μ + ε * μ {x | f x + ε ≤ g x} = ∫⁻ x, φ x ∂μ + ε * μ {x | f x + ε ≤ g x} :
    by rw [hφ_eq]
  ... ≤ ∫⁻ x, φ x ∂μ + ε * μ {x | φ x + ε ≤ g x} :
    add_le_add_left (mul_le_mul_left'
      (measure_mono $ λ x, (add_le_add_right (hφ_le _) _).trans) _) _
  ... = ∫⁻ x, φ x + indicator {x | φ x + ε ≤ g x} (λ _, ε) x ∂μ :
    begin
      rw [lintegral_add_left hφm, lintegral_indicator₀, set_lintegral_const],
      exact measurable_set_le (hφm.null_measurable.measurable'.add_const _) hg.null_measurable
    end
  ... ≤ ∫⁻ x, g x ∂μ : lintegral_mono_ae (hle.mono $ λ x hx₁, _),
  simp only [indicator_apply], split_ifs with hx₂,
  exacts [hx₂, (add_zero _).trans_le $ (hφ_le x).trans hx₁]
end

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
lemma mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ :=
by simpa only [lintegral_zero, zero_add]
  using lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ $ λ x, zero_le (f x)) hf ε

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
`ae_measurable`, see `mul_meas_ge_le_lintegral₀`. -/
lemma mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : measurable f) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ :=
mul_meas_ge_le_lintegral₀ hf.ae_measurable ε

lemma lintegral_eq_top_of_measure_eq_top_pos {f : α → ℝ≥0∞} (hf : ae_measurable f μ)
  (hμf : 0 < μ {x | f x = ∞}) : ∫⁻ x, f x ∂μ = ∞ :=
eq_top_iff.mpr $
calc ∞ = ∞ * μ {x | ∞ ≤ f x} : by simp [mul_eq_top, hμf.ne.symm]
   ... ≤ ∫⁻ x, f x ∂μ : mul_meas_ge_le_lintegral₀ hf ∞

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
lemma meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : ae_measurable f μ) {ε : ℝ≥0∞}
  (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
  μ {x | ε ≤ f x} ≤ (∫⁻ a, f a ∂μ) / ε :=
(ennreal.le_div_iff_mul_le (or.inl hε) (or.inl hε')).2 $
by { rw [mul_comm], exact mul_meas_ge_le_lintegral₀ hf ε }

lemma ae_eq_of_ae_le_of_lintegral_le {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g)
  (hf : ∫⁻ x, f x ∂μ ≠ ∞) (hg : ae_measurable g μ) (hgf : ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ) :
  f =ᵐ[μ] g :=
begin
  have : ∀ n : ℕ, ∀ᵐ x ∂μ, g x < f x + n⁻¹,
  { intro n,
    simp only [ae_iff, not_lt],
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ {x : α | f x + n⁻¹ ≤ g x} ≤ ∫⁻ x, f x ∂μ,
      from (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf,
    rw [(ennreal.cancel_of_ne hf).add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero] at this,
    exact this.resolve_left (ennreal.inv_ne_zero.2 (ennreal.nat_ne_top _)) },
  refine hfg.mp ((ae_all_iff.2 this).mono (λ x hlt hle, hle.antisymm _)),
  suffices : tendsto (λ n : ℕ, f x + n⁻¹) at_top (𝓝 (f x)),
    from ge_of_tendsto' this (λ i, (hlt i).le),
  simpa only [inv_top, add_zero]
    using tendsto_const_nhds.add (ennreal.tendsto_inv_iff.2 ennreal.tendsto_nat_nhds_top)
end

@[simp] lemma lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
have ∫⁻ a : α, 0 ∂μ ≠ ∞, by simpa only [lintegral_zero] using zero_ne_top,
⟨λ h, (ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ $ zero_le f) this hf
  (h.trans lintegral_zero.symm).le).symm, λ h, (lintegral_congr_ae h).trans lintegral_zero⟩

@[simp] lemma lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
lintegral_eq_zero_iff' hf.ae_measurable

lemma lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : measurable f) :
  0 < ∫⁻ a, f a ∂μ ↔ 0 < μ (function.support f) :=
by simp [pos_iff_ne_zero, hf, filter.eventually_eq, ae_iff, function.support]

/-- Weaker version of the monotone convergence theorem-/
lemma lintegral_supr_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀n, measurable (f n))
  (h_mono : ∀n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
let ⟨s, hs⟩ := exists_measurable_superset_of_null
                       (ae_iff.1 (ae_all_iff.2 h_mono)) in
let g := λ n a, if a ∈ s then 0 else f n a in
have g_eq_f : ∀ᵐ a ∂μ, ∀n, g n a = f n a,
  from (measure_zero_iff_ae_nmem.1 hs.2.2).mono (assume a ha n, if_neg ha),
calc
  ∫⁻ a, ⨆n, f n a ∂μ = ∫⁻ a, ⨆n, g n a ∂μ :
  lintegral_congr_ae $ g_eq_f.mono $ λ a ha, by simp only [ha]
  ... = ⨆n, (∫⁻ a, g n a ∂μ) :
  lintegral_supr
    (assume n, measurable_const.piecewise hs.2.1 (hf n))
    (monotone_nat_of_le_succ $ assume n a, classical.by_cases
      (assume h : a ∈ s, by simp [g, if_pos h])
      (assume h : a ∉ s,
      begin
        simp only [g, if_neg h], have := hs.1, rw subset_def at this, have := mt (this a) h,
        simp only [not_not, mem_set_of_eq] at this, exact this n
      end))
  ... = ⨆n, (∫⁻ a, f n a ∂μ) :
    by simp only [lintegral_congr_ae (g_eq_f.mono $ λ a ha, ha _)]

lemma lintegral_sub' {f g : α → ℝ≥0∞} (hg : ae_measurable g μ)
  (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞) (h_le : g ≤ᵐ[μ] f) :
  ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
begin
  refine ennreal.eq_sub_of_add_eq hg_fin _,
  rw [← lintegral_add_right' _ hg],
  exact lintegral_congr_ae (h_le.mono $ λ x hx, tsub_add_cancel_of_le hx)
end

lemma lintegral_sub {f g : α → ℝ≥0∞} (hg : measurable g)
  (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞) (h_le : g ≤ᵐ[μ] f) :
  ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
lintegral_sub' hg.ae_measurable hg_fin h_le

lemma lintegral_sub_le' (f g : α → ℝ≥0∞) (hf : ae_measurable f μ) :
  ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x - f x ∂μ :=
begin
  rw tsub_le_iff_right,
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞,
  { rw [hfi, add_top],
    exact le_top },
  { rw [← lintegral_add_right' _ hf],
    exact lintegral_mono (λ x, le_tsub_add) }
end

lemma lintegral_sub_le (f g : α → ℝ≥0∞) (hf : measurable f) :
  ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x - f x ∂μ :=
lintegral_sub_le' f g hf.ae_measurable

lemma lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : ae_measurable g μ)
  (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
  ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
begin
  contrapose! h,
  simp only [not_frequently, ne.def, not_not],
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h
end

lemma lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞}
  (hg : ae_measurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g)
  {s : set α} (hμs : μ s ≠ 0) (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) :
  ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le $
  ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono $ λ x hx, (hx.2 hx.1).ne

lemma lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0)
  (hg : ae_measurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) :
  ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
begin
  rw [ne.def, ← measure.measure_univ_eq_zero] at hμ,
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ _,
  simpa using h,
end

lemma set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : set α}
  (hsm : measurable_set s) (hs : μ s ≠ 0) (hg : measurable g)
  (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) :
  ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
lintegral_strict_mono (by simp [hs]) hg.ae_measurable hfi ((ae_restrict_iff' hsm).mpr h)

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi_ae
  {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n))
  (h_mono : ∀n:ℕ, f n.succ ≤ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
  ∫⁻ a, ⨅n, f n a ∂μ = ⨅n, ∫⁻ a, f n a ∂μ :=
have fn_le_f0 : ∫⁻ a, ⨅n, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ, from
  lintegral_mono (assume a, infi_le_of_le 0 le_rfl),
have fn_le_f0' : (⨅n, ∫⁻ a, f n a ∂μ) ≤ ∫⁻ a, f 0 a ∂μ, from infi_le_of_le 0 le_rfl,
(ennreal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 $
show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - (⨅n, ∫⁻ a, f n a ∂μ), from
calc
  ∫⁻ a, f 0 a ∂μ - (∫⁻ a, ⨅n, f n a ∂μ) = ∫⁻ a, f 0 a - ⨅n, f n a ∂μ:
    (lintegral_sub (measurable_infi h_meas)
    (ne_top_of_le_ne_top h_fin $ lintegral_mono (assume a, infi_le _ _))
    (ae_of_all _ $ assume a, infi_le _ _)).symm
  ... = ∫⁻ a, ⨆n, f 0 a - f n a ∂μ : congr rfl (funext (assume a, ennreal.sub_infi))
  ... = ⨆n, ∫⁻ a, f 0 a - f n a ∂μ :
    lintegral_supr_ae
      (assume n, (h_meas 0).sub (h_meas n))
      (assume n, (h_mono n).mono $ assume a ha, tsub_le_tsub le_rfl ha)
  ... = ⨆n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :
    have h_mono : ∀ᵐ a ∂μ, ∀n:ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono,
    have h_mono : ∀n, ∀ᵐ a ∂μ, f n a ≤ f 0 a := assume n, h_mono.mono $ assume a h,
    begin
      induction n with n ih,
      {exact le_rfl}, {exact le_trans (h n) ih}
    end,
    congr_arg supr $ funext $ assume n, lintegral_sub (h_meas _)
      (ne_top_of_le_ne_top h_fin $ lintegral_mono_ae $ h_mono n) (h_mono n)
  ... = ∫⁻ a, f 0 a ∂μ - ⨅n, ∫⁻ a, f n a ∂μ : ennreal.sub_infi.symm

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi
  {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n))
  (h_anti : antitone f) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
  ∫⁻ a, ⨅n, f n a ∂μ = ⨅n, ∫⁻ a, f n a ∂μ :=
lintegral_infi_ae h_meas (λ n, ae_of_all _ $ h_anti n.le_succ) h_fin

/-- Known as Fatou's lemma, version with `ae_measurable` functions -/
lemma lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, ae_measurable (f n) μ) :
  ∫⁻ a, liminf (λ n, f n a) at_top ∂μ ≤ liminf (λ n, ∫⁻ a, f n a ∂μ) at_top :=
calc
  ∫⁻ a, liminf (λ n, f n a) at_top ∂μ = ∫⁻ a, ⨆n:ℕ, ⨅i≥n, f i a ∂μ :
     by simp only [liminf_eq_supr_infi_of_nat]
  ... = ⨆n:ℕ, ∫⁻ a, ⨅i≥n, f i a ∂μ :
    lintegral_supr'
      (assume n, ae_measurable_binfi _ (to_countable _) h_meas)
      (ae_of_all μ (assume a n m hnm, infi_le_infi_of_subset $ λ i hi, le_trans hnm hi))
  ... ≤ ⨆n:ℕ, ⨅i≥n, ∫⁻ a, f i a ∂μ :
    supr_mono $ λ n, le_infi₂_lintegral _
  ... = at_top.liminf (λ n, ∫⁻ a, f n a ∂μ) : filter.liminf_eq_supr_infi_of_nat.symm

/-- Known as Fatou's lemma -/
lemma lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n)) :
  ∫⁻ a, liminf (λ n, f n a) at_top ∂μ ≤ liminf (λ n, ∫⁻ a, f n a ∂μ) at_top :=
lintegral_liminf_le' (λ n, (h_meas n).ae_measurable)

lemma limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
  (hf_meas : ∀ n, measurable (f n)) (h_bound : ∀n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
  limsup (λn, ∫⁻ a, f n a ∂μ) at_top ≤ ∫⁻ a, limsup (λn, f n a) at_top ∂μ :=
calc
  limsup (λn, ∫⁻ a, f n a ∂μ) at_top = ⨅n:ℕ, ⨆i≥n, ∫⁻ a, f i a ∂μ :
    limsup_eq_infi_supr_of_nat
  ... ≤ ⨅n:ℕ, ∫⁻ a, ⨆i≥n, f i a ∂μ :
    infi_mono $ assume n, supr₂_lintegral_le _
  ... = ∫⁻ a, ⨅n:ℕ, ⨆i≥n, f i a ∂μ :
    begin
      refine (lintegral_infi _ _ _).symm,
      { assume n, exact measurable_bsupr _ (to_countable _) hf_meas },
      { assume n m hnm a, exact (supr_le_supr_of_subset $ λ i hi, le_trans hnm hi) },
      { refine ne_top_of_le_ne_top h_fin (lintegral_mono_ae _),
        refine (ae_all_iff.2 h_bound).mono (λ n hn, _),
        exact supr_le (λ i, supr_le $ λ hi, hn i) }
    end
  ... = ∫⁻ a, limsup (λn, f n a) at_top ∂μ :
    by simp only [limsup_eq_infi_supr_of_nat]

/-- Dominated convergence theorem for nonnegative functions -/
lemma tendsto_lintegral_of_dominated_convergence
  {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀n, measurable (F n)) (h_bound : ∀n, F n ≤ᵐ[μ] bound)
  (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) at_top (𝓝 (∫⁻ a, f a ∂μ)) :=
tendsto_of_le_liminf_of_limsup_le
(calc ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (λ (n : ℕ), F n a) at_top ∂μ :
      lintegral_congr_ae $ h_lim.mono $ assume a h, h.liminf_eq.symm
 ... ≤ liminf (λ n, ∫⁻ a, F n a ∂μ) at_top : lintegral_liminf_le hF_meas)
(calc limsup (λ (n : ℕ), ∫⁻ a, F n a ∂μ) at_top ≤ ∫⁻ a, limsup (λn, F n a) at_top ∂μ :
      limsup_lintegral_le hF_meas h_bound h_fin
 ... = ∫⁻ a, f a ∂μ : lintegral_congr_ae $ h_lim.mono $ λ a h, h.limsup_eq)

/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
lemma tendsto_lintegral_of_dominated_convergence'
  {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀n, ae_measurable (F n) μ) (h_bound : ∀n, F n ≤ᵐ[μ] bound)
  (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) at_top (𝓝 (∫⁻ a, f a ∂μ)) :=
begin
  have : ∀ n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ :=
    λ n, lintegral_congr_ae (hF_meas n).ae_eq_mk,
  simp_rw this,
  apply tendsto_lintegral_of_dominated_convergence bound (λ n, (hF_meas n).measurable_mk) _ h_fin,
  { have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a :=
      λ n, (hF_meas n).ae_eq_mk.symm,
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this,
    filter_upwards [this, h_lim] with a H H',
    simp_rw H,
    exact H', },
  { assume n,
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H',
    rwa H' at H, },
end

/-- Dominated convergence theorem for filters with a countable basis -/
lemma tendsto_lintegral_filter_of_dominated_convergence {ι} {l : filter ι}
  [l.is_countably_generated]
  {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀ᶠ n in l, measurable (F n))
  (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
  (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) l (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) l (𝓝 $ ∫⁻ a, f a ∂μ) :=
begin
  rw tendsto_iff_seq_tendsto,
  intros x xl,
  have hxl, { rw tendsto_at_top' at xl, exact xl },
  have h := inter_mem hF_meas h_bound,
  replace h := hxl _ h,
  rcases h with ⟨k, h⟩,
  rw ← tendsto_add_at_top_iff_nat k,
  refine tendsto_lintegral_of_dominated_convergence _ _ _ _ _,
  { exact bound },
  { intro, refine (h _ _).1, exact nat.le_add_left _ _ },
  { intro, refine (h _ _).2, exact nat.le_add_left _ _ },
  { assumption },
  { refine h_lim.mono (λ a h_lim, _),
    apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
    { assumption },
    rw tendsto_add_at_top_iff_nat,
    assumption }
end

section
open encodable

/-- Monotone convergence for a supremum over a directed family and indexed by a countable type -/
theorem lintegral_supr_directed_of_measurable [countable β] {f : β → α → ℝ≥0∞}
  (hf : ∀ b, measurable (f b)) (h_directed : directed (≤) f) :
  ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ :=
begin
  casesI nonempty_encodable β,
  casesI is_empty_or_nonempty β, { simp [supr_of_empty] },
  inhabit β,
  have : ∀a, (⨆ b, f b a) = (⨆ n, f (h_directed.sequence f n) a),
  { assume a,
    refine le_antisymm (supr_le $ assume b, _) (supr_le $ assume n, le_supr (λn, f n a) _),
    exact le_supr_of_le (encode b + 1) (h_directed.le_sequence b a) },
  calc ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ :
      by simp only [this]
    ... = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :
      lintegral_supr (assume n, hf _) h_directed.sequence_mono
    ... = ⨆ b, ∫⁻ a, f b a ∂μ :
    begin
      refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume b, _),
      { exact le_supr (λb, ∫⁻ a, f b a ∂μ) _ },
      { exact le_supr_of_le (encode b + 1)
          (lintegral_mono $ h_directed.le_sequence b) }
    end
end

/-- Monotone convergence for a supremum over a directed family and indexed by a countable type. -/
theorem lintegral_supr_directed [countable β] {f : β → α → ℝ≥0∞}
  (hf : ∀ b, ae_measurable (f b) μ) (h_directed : directed (≤) f) :
  ∫⁻ a, ⨆ b, f b a ∂μ = ⨆ b, ∫⁻ a, f b a ∂μ :=
begin
  simp_rw ←supr_apply,
  let p : α → (β → ennreal) → Prop := λ x f', directed has_le.le f',
  have hp : ∀ᵐ x ∂μ, p x (λ i, f i x),
  { filter_upwards with x i j,
    obtain ⟨z, hz₁, hz₂⟩ := h_directed i j,
    exact ⟨z, hz₁ x, hz₂ x⟩, },
  have h_ae_seq_directed : directed has_le.le (ae_seq hf p),
  { intros b₁ b₂,
    obtain ⟨z, hz₁, hz₂⟩ := h_directed b₁ b₂,
    refine ⟨z, _, _⟩;
    { intros x,
      by_cases hx : x ∈ ae_seq_set hf p,
      { repeat { rw ae_seq.ae_seq_eq_fun_of_mem_ae_seq_set hf hx },
        apply_rules [hz₁, hz₂], },
      { simp only [ae_seq, hx, if_false],
        exact le_rfl, }, }, },
  convert (lintegral_supr_directed_of_measurable (ae_seq.measurable hf p)
    h_ae_seq_directed) using 1,
  { simp_rw ←supr_apply,
    rw lintegral_congr_ae (ae_seq.supr hf hp).symm, },
  { congr' 1,
    ext1 b,
    rw lintegral_congr_ae,
    symmetry,
    refine ae_seq.ae_seq_n_eq_fun_n_ae hf hp _, },
end

end

lemma lintegral_tsum [countable β] {f : β → α → ℝ≥0∞} (hf : ∀i, ae_measurable (f i) μ) :
  ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ :=
begin
  simp only [ennreal.tsum_eq_supr_sum],
  rw [lintegral_supr_directed],
  { simp [lintegral_finset_sum' _ (λ i _, hf i)] },
  { assume b, exact finset.ae_measurable_sum _ (λ i _, hf i) },
  { assume s t,
    use [s ∪ t],
    split,
    { exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_left _ _), },
    { exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_right _ _) } }
end

open measure

lemma lintegral_Union₀ [countable β] {s : β → set α} (hm : ∀ i, null_measurable_set (s i) μ)
  (hd : pairwise (ae_disjoint μ on s)) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
by simp only [measure.restrict_Union_ae hd hm, lintegral_sum_measure]

lemma lintegral_Union [countable β] {s : β → set α} (hm : ∀ i, measurable_set (s i))
  (hd : pairwise (disjoint on s)) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
lintegral_Union₀ (λ i, (hm i).null_measurable_set) hd.ae_disjoint f

lemma lintegral_bUnion₀ {t : set β} {s : β → set α} (ht : t.countable)
  (hm : ∀ i ∈ t, null_measurable_set (s i) μ)
  (hd : t.pairwise (ae_disjoint μ on s)) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
begin
  haveI := ht.to_encodable,
  rw [bUnion_eq_Union, lintegral_Union₀ (set_coe.forall'.1 hm) (hd.subtype _ _)]
end

lemma lintegral_bUnion {t : set β} {s : β → set α} (ht : t.countable)
  (hm : ∀ i ∈ t, measurable_set (s i)) (hd : t.pairwise_disjoint s) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i ∈ t, s i, f a ∂μ = ∑' i : t, ∫⁻ a in s i, f a ∂μ :=
lintegral_bUnion₀ ht (λ i hi, (hm i hi).null_measurable_set) hd.ae_disjoint f

lemma lintegral_bUnion_finset₀ {s : finset β} {t : β → set α}
  (hd : set.pairwise ↑s (ae_disjoint μ on t)) (hm : ∀ b ∈ s, null_measurable_set (t b) μ)
  (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ :=
by simp only [← finset.mem_coe, lintegral_bUnion₀ s.countable_to_set hm hd, ← s.tsum_subtype']

lemma lintegral_bUnion_finset {s : finset β} {t : β → set α}
  (hd : set.pairwise_disjoint ↑s t) (hm : ∀ b ∈ s, measurable_set (t b)) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ = ∑ b in s, ∫⁻ a in t b, f a ∂μ :=
lintegral_bUnion_finset₀ hd.ae_disjoint (λ b hb, (hm b hb).null_measurable_set) f

lemma lintegral_Union_le [countable β] (s : β → set α) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ :=
begin
  rw [← lintegral_sum_measure],
  exact lintegral_mono' restrict_Union_le le_rfl
end

lemma lintegral_union {f : α → ℝ≥0∞} {A B : set α} (hB : measurable_set B) (hAB : disjoint A B) :
  ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ :=
by rw [restrict_union hAB hB, lintegral_add_measure]

lemma lintegral_inter_add_diff {B : set α} (f : α → ℝ≥0∞) (A : set α) (hB : measurable_set B) :
  ∫⁻ x in A ∩ B, f x ∂μ + ∫⁻ x in A \ B, f x ∂μ = ∫⁻ x in A, f x ∂μ :=
by rw [← lintegral_add_measure, restrict_inter_add_diff _ hB]

lemma lintegral_add_compl (f : α → ℝ≥0∞) {A : set α} (hA : measurable_set A) :
  ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw [← lintegral_add_measure, measure.restrict_add_restrict_compl hA]

lemma lintegral_max {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  ∫⁻ x, max (f x) (g x) ∂μ = ∫⁻ x in {x | f x ≤ g x}, g x ∂μ + ∫⁻ x in {x | g x < f x}, f x ∂μ :=
begin
  have hm : measurable_set {x | f x ≤ g x}, from measurable_set_le hf hg,
  rw [← lintegral_add_compl (λ x, max (f x) (g x)) hm],
  simp only [← compl_set_of, ← not_le],
  refine congr_arg2 (+) (set_lintegral_congr_fun hm _) (set_lintegral_congr_fun hm.compl _),
  exacts [ae_of_all _ (λ x, max_eq_right), ae_of_all _ (λ x hx, max_eq_left (not_le.1 hx).le)]
end

lemma set_lintegral_max {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) (s : set α) :
  ∫⁻ x in s, max (f x) (g x) ∂μ =
    ∫⁻ x in s ∩ {x | f x ≤ g x}, g x ∂μ + ∫⁻ x in s ∩ {x | g x < f x}, f x ∂μ :=
begin
  rw [lintegral_max hf hg, restrict_restrict, restrict_restrict, inter_comm s, inter_comm s],
  exacts [measurable_set_lt hg hf, measurable_set_le hf hg]
end

lemma lintegral_map {mβ : measurable_space β} {f : β → ℝ≥0∞} {g : α → β}
  (hf : measurable f) (hg : measurable g) : ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
begin
  simp only [lintegral_eq_supr_eapprox_lintegral, hf, hf.comp hg],
  congr' with n : 1,
  convert simple_func.lintegral_map _ hg,
  ext1 x, simp only [eapprox_comp hf hg, coe_comp]
end

lemma lintegral_map' {mβ : measurable_space β} {f : β → ℝ≥0∞} {g : α → β}
  (hf : ae_measurable f (measure.map g μ)) (hg : ae_measurable g μ) :
  ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, f (g a) ∂μ :=
calc ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, hf.mk f a ∂(measure.map g μ) :
  lintegral_congr_ae hf.ae_eq_mk
... = ∫⁻ a, hf.mk f a ∂(measure.map (hg.mk g) μ) :
  by { congr' 1, exact measure.map_congr hg.ae_eq_mk }
... = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ : lintegral_map hf.measurable_mk hg.measurable_mk
... = ∫⁻ a, hf.mk f (g a) ∂μ : lintegral_congr_ae $ hg.ae_eq_mk.symm.fun_comp _
... = ∫⁻ a, f (g a) ∂μ : lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

lemma lintegral_map_le {mβ : measurable_space β} (f : β → ℝ≥0∞) {g : α → β} (hg : measurable g) :
  ∫⁻ a, f a ∂(measure.map g μ) ≤ ∫⁻ a, f (g a) ∂μ :=
begin
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral],
  refine supr₂_le (λ i hi, supr_le $ λ h'i, _),
  refine le_supr₂_of_le (i ∘ g) (hi.comp hg) _,
  exact le_supr_of_le (λ x, h'i (g x)) (le_of_eq (lintegral_map hi hg))
end

lemma lintegral_comp [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  (hf : measurable f) (hg : measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂(map g μ) :=
(lintegral_map hf hg).symm

lemma set_lintegral_map [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  {s : set β} (hs : measurable_set s) (hf : measurable f) (hg : measurable g) :
  ∫⁻ y in s, f y ∂(map g μ) = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ :=
by rw [restrict_map hg hs, lintegral_map hf hg]

lemma lintegral_indicator_const_comp {mβ : measurable_space β}
  {f : α → β} {s : set β} (hf : measurable f) (hs : measurable_set s) (c : ℝ≥0∞) :
  ∫⁻ a, s.indicator (λ _, c) (f a) ∂μ = c * μ (f ⁻¹' s) :=
by rw [lintegral_comp (measurable_const.indicator hs) hf, lintegral_indicator_const hs,
  measure.map_apply hf hs]

/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` wich
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
lemma _root_.measurable_embedding.lintegral_map [measurable_space β] {g : α → β}
  (hg : measurable_embedding g) (f : β → ℝ≥0∞) :
  ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
begin
  rw [lintegral, lintegral],
  refine le_antisymm (supr₂_le $ λ f₀ hf₀, _) (supr₂_le $ λ f₀ hf₀, _),
  { rw [simple_func.lintegral_map _ hg.measurable],
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g, from λ x, hf₀ (g x),
    exact le_supr_of_le (comp f₀ g hg.measurable) (le_supr _ this) },
  { rw [← f₀.extend_comp_eq hg (const _ 0), ← simple_func.lintegral_map,
      ← simple_func.lintegral_eq_lintegral, ← lintegral],
    refine lintegral_mono_ae (hg.ae_map_iff.2 $ eventually_of_forall $ λ x, _),
    exact (extend_apply _ _ _ _).trans_le (hf₀ _) }
end

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
lemma lintegral_map_equiv [measurable_space β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
  ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
g.measurable_embedding.lintegral_map f

lemma measure_preserving.lintegral_comp {mb : measurable_space β} {ν : measure β} {g : α → β}
  (hg : measure_preserving g μ ν) {f : β → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν :=
by rw [← hg.map_eq, lintegral_map hf hg.measurable]

lemma measure_preserving.lintegral_comp_emb {mb : measurable_space β} {ν : measure β} {g : α → β}
  (hg : measure_preserving g μ ν) (hge : measurable_embedding g) (f : β → ℝ≥0∞) :
  ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν :=
by rw [← hg.map_eq, hge.lintegral_map]

lemma measure_preserving.set_lintegral_comp_preimage {mb : measurable_space β} {ν : measure β}
  {g : α → β} (hg : measure_preserving g μ ν) {s : set β} (hs : measurable_set s)
  {f : β → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν :=
by rw [← hg.map_eq, set_lintegral_map hs hf hg.measurable]

lemma measure_preserving.set_lintegral_comp_preimage_emb {mb : measurable_space β} {ν : measure β}
  {g : α → β} (hg : measure_preserving g μ ν) (hge : measurable_embedding g) (f : β → ℝ≥0∞)
  (s : set β) :
  ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν :=
by rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]

lemma measure_preserving.set_lintegral_comp_emb {mb : measurable_space β} {ν : measure β}
  {g : α → β} (hg : measure_preserving g μ ν) (hge : measurable_embedding g) (f : β → ℝ≥0∞)
  (s : set α) :
  ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν :=
by rw [← hg.set_lintegral_comp_preimage_emb hge, preimage_image_eq _ hge.injective]

section dirac_and_count

@[priority 10]
instance _root_.measurable_space.top.measurable_singleton_class {α : Type*} :
  @measurable_singleton_class α (⊤ : measurable_space α) :=
{ measurable_set_singleton := λ i, measurable_space.measurable_set_top, }

variable [measurable_space α]

lemma lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂(dirac a) = f a :=
by simp [lintegral_congr_ae (ae_eq_dirac' hf)]

lemma lintegral_dirac [measurable_singleton_class α] (a : α) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂(dirac a) = f a :=
by simp [lintegral_congr_ae (ae_eq_dirac f)]

lemma lintegral_count' {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂count = ∑' a, f a :=
begin
  rw [count, lintegral_sum_measure],
  congr,
  exact funext (λ a, lintegral_dirac' a hf),
end

lemma lintegral_count [measurable_singleton_class α] (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂count = ∑' a, f a :=
begin
  rw [count, lintegral_sum_measure],
  congr,
  exact funext (λ a, lintegral_dirac a f),
end

lemma _root_.ennreal.tsum_const_eq [measurable_singleton_class α] (c : ℝ≥0∞) :
  (∑' (i : α), c) = c * (measure.count (univ : set α)) :=
by rw [← lintegral_count, lintegral_const]

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0∞`. -/
lemma _root_.ennreal.count_const_le_le_of_tsum_le [measurable_singleton_class α]
  {a : α → ℝ≥0∞} (a_mble : measurable a) {c : ℝ≥0∞} (tsum_le_c : ∑' i, a i ≤ c)
  {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) (ε_ne_top : ε ≠ ∞) :
  measure.count {i : α | ε ≤ a i} ≤ c / ε :=
begin
  rw ← lintegral_count at tsum_le_c,
  apply (measure_theory.meas_ge_le_lintegral_div a_mble.ae_measurable ε_ne_zero ε_ne_top).trans,
  exact ennreal.div_le_div tsum_le_c rfl.le,
end

/-- Markov's inequality for counting measure with hypothesis using `tsum` in `ℝ≥0`. -/
lemma _root_.nnreal.count_const_le_le_of_tsum_le [measurable_singleton_class α]
  {a : α → ℝ≥0} (a_mble : measurable a) (a_summable : summable a)
  {c : ℝ≥0} (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0} (ε_ne_zero : ε ≠ 0) :
  measure.count {i : α | ε ≤ a i} ≤ c / ε :=
begin
  rw [show (λ i, ε ≤ a i) = (λ i, (ε : ℝ≥0∞) ≤ (coe ∘ a) i),
        by { funext i, simp only [ennreal.coe_le_coe], }],
  apply ennreal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble)
          _ (by exact_mod_cast ε_ne_zero) (@ennreal.coe_ne_top ε),
  convert ennreal.coe_le_coe.mpr tsum_le_c,
  rw ennreal.tsum_coe_eq a_summable.has_sum,
end

end dirac_and_count

section countable
/-!
### Lebesgue integral over finite and countable types and sets
-/

lemma lintegral_countable' [countable α] [measurable_singleton_class α] (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} :=
begin
  conv_lhs { rw [← sum_smul_dirac μ, lintegral_sum_measure] },
  congr' 1 with a : 1,
  rw [lintegral_smul_measure, lintegral_dirac, mul_comm],
end

lemma lintegral_singleton' {f : α → ℝ≥0∞} (hf : measurable f) (a : α) :
  ∫⁻ x in {a}, f x ∂μ = f a * μ {a} :=
by simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac' _ hf, mul_comm]

lemma lintegral_singleton [measurable_singleton_class α] (f : α → ℝ≥0∞) (a : α) :
  ∫⁻ x in {a}, f x ∂μ = f a * μ {a} :=
by simp only [restrict_singleton, lintegral_smul_measure, lintegral_dirac, mul_comm]

lemma lintegral_countable [measurable_singleton_class α] (f : α → ℝ≥0∞) {s : set α}
  (hs : s.countable) :
  ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)} :=
calc ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x ∈ s, {x}, f a ∂μ : by rw [bUnion_of_singleton]
... = ∑' a : s, ∫⁻ x in {a}, f x ∂μ :
  lintegral_bUnion hs (λ _ _, measurable_set_singleton _) (pairwise_disjoint_fiber id s) _
... = ∑' a : s, f a * μ {(a : α)} : by simp only [lintegral_singleton]

lemma lintegral_insert [measurable_singleton_class α]
  {a : α} {s : set α} (h : a ∉ s) (f : α → ℝ≥0∞) :
  ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, f x ∂μ :=
begin
  rw [← union_singleton, lintegral_union (measurable_set_singleton a), lintegral_singleton,
    add_comm],
  rwa disjoint_singleton_right
end

lemma lintegral_finset [measurable_singleton_class α] (s : finset α) (f : α → ℝ≥0∞) :
  ∫⁻ x in s, f x ∂μ = ∑ x in s, f x * μ {x} :=
by simp only [lintegral_countable _ s.countable_to_set, ← s.tsum_subtype']

lemma lintegral_fintype [measurable_singleton_class α] [fintype α] (f : α → ℝ≥0∞) :
  ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x} :=
by rw [← lintegral_finset, finset.coe_univ, measure.restrict_univ]

lemma lintegral_unique [unique α] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = f default * μ univ :=
calc ∫⁻ x, f x ∂μ = ∫⁻ x, f default ∂μ : lintegral_congr $ unique.forall_iff.2 rfl
... = f default * μ univ : lintegral_const _

end countable

lemma ae_lt_top {f : α → ℝ≥0∞} (hf : measurable f) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
  ∀ᵐ x ∂μ, f x < ∞ :=
begin
  simp_rw [ae_iff, ennreal.not_lt_top], by_contra h, apply h2f.lt_top.not_le,
  have : (f ⁻¹' {∞}).indicator ⊤ ≤ f,
  { intro x, by_cases hx : x ∈ f ⁻¹' {∞}; [simpa [hx], simp [hx]] },
  convert lintegral_mono this,
  rw [lintegral_indicator _ (hf (measurable_set_singleton ∞))], simp [ennreal.top_mul, preimage, h]
end

lemma ae_lt_top' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
  ∀ᵐ x ∂μ, f x < ∞ :=
begin
  have h2f_meas : ∫⁻ x, hf.mk f x ∂μ ≠ ∞, by rwa ← lintegral_congr_ae hf.ae_eq_mk,
  exact (ae_lt_top hf.measurable_mk h2f_meas).mp (hf.ae_eq_mk.mono (λ x hx h, by rwa hx)),
end

lemma set_lintegral_lt_top_of_bdd_above
  {s : set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0} (hf : measurable f) (hbdd : bdd_above (f '' s)) :
  ∫⁻ x in s, f x ∂μ < ∞ :=
begin
  obtain ⟨M, hM⟩ := hbdd,
  rw mem_upper_bounds at hM,
  refine lt_of_le_of_lt (set_lintegral_mono hf.coe_nnreal_ennreal
    (@measurable_const _ _ _ _ ↑M) _) _,
  { simpa using hM },
  { rw lintegral_const,
    refine ennreal.mul_lt_top ennreal.coe_lt_top.ne _,
    simp [hs] }
end

lemma set_lintegral_lt_top_of_is_compact [topological_space α] [opens_measurable_space α]
  {s : set α} (hs : μ s ≠ ∞) (hsc : is_compact s) {f : α → ℝ≥0} (hf : continuous f) :
  ∫⁻ x in s, f x ∂μ < ∞ :=
set_lintegral_lt_top_of_bdd_above hs hf.measurable (hsc.image hf).bdd_above

lemma _root_.is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal {α : Type*}
  [measurable_space α] (μ : measure α) [μ_fin : is_finite_measure μ]
  {f : α → ℝ≥0∞} (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ :=
begin
  cases f_bdd with c hc,
  apply lt_of_le_of_lt (@lintegral_mono _ _ μ _ _ hc),
  rw lintegral_const,
  exact ennreal.mul_lt_top ennreal.coe_lt_top.ne μ_fin.measure_univ_lt_top.ne,
end

/-- Given a measure `μ : measure α` and a function `f : α → ℝ≥0∞`, `μ.with_density f` is the
measure such that for a measurable set `s` we have `μ.with_density f s = ∫⁻ a in s, f a ∂μ`. -/
def measure.with_density {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞) : measure α :=
measure.of_measurable (λs hs, ∫⁻ a in s, f a ∂μ) (by simp) (λ s hs hd, lintegral_Union hs hd _)

@[simp] lemma with_density_apply (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  μ.with_density f s = ∫⁻ a in s, f a ∂μ :=
measure.of_measurable_apply s hs

lemma with_density_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
  μ.with_density f = μ.with_density g :=
begin
  apply measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, with_density_apply _ hs],
  exact lintegral_congr_ae (ae_restrict_of_ae h)
end

lemma with_density_add_left {f : α → ℝ≥0∞} (hf : measurable f) (g : α → ℝ≥0∞) :
  μ.with_density (f + g) = μ.with_density f + μ.with_density g :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.add_apply,
      with_density_apply _ hs, with_density_apply _ hs, ← lintegral_add_left hf],
  refl,
end

lemma with_density_add_right (f : α → ℝ≥0∞) {g : α → ℝ≥0∞} (hg : measurable g) :
  μ.with_density (f + g) = μ.with_density f + μ.with_density g :=
by simpa only [add_comm] using with_density_add_left hg f

lemma with_density_add_measure {m : measurable_space α} (μ ν : measure α) (f : α → ℝ≥0∞) :
  (μ + ν).with_density f = μ.with_density f + ν.with_density f :=
begin
  ext1 s hs,
  simp only [with_density_apply f hs, restrict_add, lintegral_add_measure, measure.add_apply],
end

lemma with_density_sum {ι : Type*} {m : measurable_space α} (μ : ι → measure α) (f : α → ℝ≥0∞) :
  (sum μ).with_density f = sum (λ n, (μ n).with_density f) :=
begin
  ext1 s hs,
  simp_rw [sum_apply _ hs, with_density_apply f hs, restrict_sum μ hs, lintegral_sum_measure],
end

lemma with_density_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  μ.with_density (r • f) = r • μ.with_density f :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_smul, pi.smul_apply,
      with_density_apply _ hs, smul_eq_mul, ← lintegral_const_mul r hf],
  refl,
end

lemma with_density_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
  μ.with_density (r • f) = r • μ.with_density f :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_smul, pi.smul_apply,
      with_density_apply _ hs, smul_eq_mul, ← lintegral_const_mul' r f hr],
  refl,
end

lemma is_finite_measure_with_density {f : α → ℝ≥0∞}
  (hf : ∫⁻ a, f a ∂μ ≠ ∞) : is_finite_measure (μ.with_density f) :=
{ measure_univ_lt_top :=
    by rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ, lt_top_iff_ne_top] }

lemma with_density_absolutely_continuous
  {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞) : μ.with_density f ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs₁ hs₂, _),
  rw with_density_apply _ hs₁,
  exact set_lintegral_measure_zero _ _ hs₂
end

@[simp]
lemma with_density_zero : μ.with_density 0 = 0 :=
begin
  ext1 s hs,
  simp [with_density_apply _ hs],
end

@[simp]
lemma with_density_one : μ.with_density 1 = μ :=
begin
  ext1 s hs,
  simp [with_density_apply _ hs],
end

lemma with_density_tsum {f : ℕ → α → ℝ≥0∞} (h : ∀ i, measurable (f i)) :
  μ.with_density (∑' n, f n) = sum (λ n, μ.with_density (f n)) :=
begin
  ext1 s hs,
  simp_rw [sum_apply _ hs, with_density_apply _ hs],
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' (i : ℕ), ∫⁻ x, f i x ∂(μ.restrict s),
  rw ← lintegral_tsum (λ i, (h i).ae_measurable),
  refine lintegral_congr (λ x, tsum_apply (pi.summable.2 (λ _, ennreal.summable))),
end

lemma with_density_indicator {s : set α} (hs : measurable_set s) (f : α → ℝ≥0∞) :
  μ.with_density (s.indicator f) = (μ.restrict s).with_density f :=
begin
  ext1 t ht,
  rw [with_density_apply _ ht, lintegral_indicator _ hs,
      restrict_comm hs, ← with_density_apply _ ht]
end

lemma with_density_indicator_one {s : set α} (hs : measurable_set s) :
  μ.with_density (s.indicator 1) = μ.restrict s :=
by rw [with_density_indicator hs, with_density_one]

lemma with_density_of_real_mutually_singular {f : α → ℝ} (hf : measurable f) :
  μ.with_density (λ x, ennreal.of_real $ f x) ⟂ₘ μ.with_density (λ x, ennreal.of_real $ -f x) :=
begin
  set S : set α := { x | f x < 0 } with hSdef,
  have hS : measurable_set S := measurable_set_lt hf measurable_const,
  refine ⟨S, hS, _, _⟩,
  { rw [with_density_apply _ hS, lintegral_eq_zero_iff hf.ennreal_of_real, eventually_eq],
    exact (ae_restrict_mem hS).mono (λ x hx, ennreal.of_real_eq_zero.2 (le_of_lt hx)) },
  { rw [with_density_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_of_real, eventually_eq],
    exact (ae_restrict_mem hS.compl).mono (λ x hx, ennreal.of_real_eq_zero.2
      (not_lt.1 $ mt neg_pos.1 hx)) },
end

lemma restrict_with_density {s : set α} (hs : measurable_set s) (f : α → ℝ≥0∞) :
  (μ.with_density f).restrict s = (μ.restrict s).with_density f :=
begin
  ext1 t ht,
  rw [restrict_apply ht, with_density_apply _ ht,
      with_density_apply _ (ht.inter hs), restrict_restrict ht],
end

lemma with_density_eq_zero {f : α → ℝ≥0∞}
  (hf : ae_measurable f μ) (h : μ.with_density f = 0) :
  f =ᵐ[μ] 0 :=
by rw [← lintegral_eq_zero_iff' hf, ← set_lintegral_univ,
       ← with_density_apply _ measurable_set.univ, h, measure.coe_zero, pi.zero_apply]

lemma with_density_apply_eq_zero {f : α → ℝ≥0∞} {s : set α} (hf : measurable f) :
  μ.with_density f s = 0 ↔ μ ({x | f x ≠ 0} ∩ s) = 0 :=
begin
  split,
  { assume hs,
    let t := to_measurable (μ.with_density f) s,
    apply measure_mono_null
      (inter_subset_inter_right _ (subset_to_measurable (μ.with_density f) s)),
    have A : μ.with_density f t = 0, by rw [measure_to_measurable, hs],
    rw [with_density_apply f (measurable_set_to_measurable _ s), lintegral_eq_zero_iff hf,
        eventually_eq, ae_restrict_iff, ae_iff] at A,
    swap, { exact hf (measurable_set_singleton 0) },
    simp only [pi.zero_apply, mem_set_of_eq, filter.mem_mk] at A,
    convert A,
    ext x,
    simp only [and_comm, exists_prop, mem_inter_iff, iff_self, mem_set_of_eq, mem_compl_iff,
               not_forall] },
  { assume hs,
    let t := to_measurable μ ({x | f x ≠ 0} ∩ s),
    have A : s ⊆ t ∪ {x | f x = 0},
    { assume x hx,
      rcases eq_or_ne (f x) 0 with fx|fx,
      { simp only [fx, mem_union, mem_set_of_eq, eq_self_iff_true, or_true] },
      { left,
        apply subset_to_measurable _ _,
        exact ⟨fx, hx⟩ } },
    apply measure_mono_null A (measure_union_null _ _),
    { apply with_density_absolutely_continuous,
      rwa measure_to_measurable },
    { have M : measurable_set {x : α | f x = 0} := hf (measurable_set_singleton _),
      rw [with_density_apply _ M, (lintegral_eq_zero_iff hf)],
      filter_upwards [ae_restrict_mem M],
      simp only [imp_self, pi.zero_apply, implies_true_iff] } }
end

lemma ae_with_density_iff {p : α → Prop} {f : α → ℝ≥0∞} (hf : measurable f) :
  (∀ᵐ x ∂(μ.with_density f), p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x :=
begin
  rw [ae_iff, ae_iff, with_density_apply_eq_zero hf],
  congr',
  ext x,
  simp only [exists_prop, mem_inter_iff, iff_self, mem_set_of_eq, not_forall],
end

lemma ae_with_density_iff_ae_restrict {p : α → Prop} {f : α → ℝ≥0∞} (hf : measurable f) :
  (∀ᵐ x ∂(μ.with_density f), p x) ↔ (∀ᵐ x ∂(μ.restrict {x | f x ≠ 0}), p x) :=
begin
  rw [ae_with_density_iff hf, ae_restrict_iff'],
  { refl },
  { exact hf (measurable_set_singleton 0).compl },
end

lemma ae_measurable_with_density_iff {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
  {f : α → ℝ≥0} (hf : measurable f) {g : α → E} :
  ae_measurable g (μ.with_density (λ x, (f x : ℝ≥0∞))) ↔ ae_measurable (λ x, (f x : ℝ) • g x) μ :=
begin
  split,
  { rintros ⟨g', g'meas, hg'⟩,
    have A : measurable_set {x : α | f x ≠ 0} := (hf (measurable_set_singleton 0)).compl,
    refine ⟨λ x, (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, _⟩,
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ {x | f x ≠ 0},
    { rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg',
      rw ae_restrict_iff' A,
      filter_upwards [hg'],
      assume a ha h'a,
      have : (f a : ℝ≥0∞) ≠ 0, by simpa only [ne.def, coe_eq_zero] using h'a,
      rw ha this },
    { filter_upwards [ae_restrict_mem A.compl],
      assume x hx,
      simp only [not_not, mem_set_of_eq, mem_compl_iff] at hx,
      simp [hx] } },
  { rintros ⟨g', g'meas, hg'⟩,
    refine ⟨λ x, (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, _⟩,
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal],
    filter_upwards [hg'],
    assume x hx h'x,
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul],
    simp only [ne.def, coe_eq_zero] at h'x,
    simpa only [nnreal.coe_eq_zero, ne.def] using h'x }
end

lemma ae_measurable_with_density_ennreal_iff {f : α → ℝ≥0} (hf : measurable f) {g : α → ℝ≥0∞} :
  ae_measurable g (μ.with_density (λ x, (f x : ℝ≥0∞))) ↔
    ae_measurable (λ x, (f x : ℝ≥0∞) * g x) μ :=
begin
  split,
  { rintros ⟨g', g'meas, hg'⟩,
    have A : measurable_set {x : α | f x ≠ 0} := (hf (measurable_set_singleton 0)).compl,
    refine ⟨λ x, f x * g' x, hf.coe_nnreal_ennreal.smul g'meas, _⟩,
    apply ae_of_ae_restrict_of_ae_restrict_compl {x | f x ≠ 0},
    { rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg',
      rw ae_restrict_iff' A,
      filter_upwards [hg'],
      assume a ha h'a,
      have : (f a : ℝ≥0∞) ≠ 0, by simpa only [ne.def, coe_eq_zero] using h'a,
      rw ha this },
    { filter_upwards [ae_restrict_mem A.compl],
      assume x hx,
      simp only [not_not, mem_set_of_eq, mem_compl_iff] at hx,
      simp [hx] } },
  { rintros ⟨g', g'meas, hg'⟩,
    refine ⟨λ x, (f x)⁻¹ * g' x, hf.coe_nnreal_ennreal.inv.smul g'meas, _⟩,
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal],
    filter_upwards [hg'],
    assume x hx h'x,
    rw [← hx, ← mul_assoc, ennreal.inv_mul_cancel h'x ennreal.coe_ne_top, one_mul] }
end

end lintegral

open measure_theory.simple_func

variables {m m0 : measurable_space α}

include m

/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.with_density f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.with_density f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
lemma lintegral_with_density_eq_lintegral_mul (μ : measure α)
  {f : α → ℝ≥0∞} (h_mf : measurable f) : ∀ {g : α → ℝ≥0∞}, measurable g →
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  apply measurable.ennreal_induction,
  { intros c s h_ms,
    simp [*, mul_comm _ c, ← indicator_mul_right], },
  { intros g h h_univ h_mea_g h_mea_h h_ind_g h_ind_h,
    simp [mul_add, *, measurable.mul] },
  { intros g h_mea_g h_mono_g h_ind,
    have : monotone (λ n a, f a * g n a) := λ m n hmn x, mul_le_mul_left' (h_mono_g hmn x) _,
    simp [lintegral_supr, ennreal.mul_supr, h_mf.mul (h_mea_g _), *] }
end

lemma set_lintegral_with_density_eq_set_lintegral_mul (μ : measure α) {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) {s : set α} (hs : measurable_set s) :
  ∫⁻ x in s, g x ∂μ.with_density f = ∫⁻ x in s, (f * g) x ∂μ :=
by rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul _ hf hg]

/-- The Lebesgue integral of `g` with respect to the measure `μ.with_density f` coincides with
the integral of `f * g`. This version assumes that `g` is almost everywhere measurable. For a
version without conditions on `g` but requiring that `f` is almost everywhere finite, see
`lintegral_with_density_eq_lintegral_mul_non_measurable` -/
lemma lintegral_with_density_eq_lintegral_mul₀' {μ : measure α} {f : α → ℝ≥0∞}
  (hf : ae_measurable f μ) {g : α → ℝ≥0∞} (hg : ae_measurable g (μ.with_density f)) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  let f' := hf.mk f,
  have : μ.with_density f = μ.with_density f' := with_density_congr_ae hf.ae_eq_mk,
  rw this at ⊢ hg,
  let g' := hg.mk g,
  calc ∫⁻ a, g a ∂(μ.with_density f') = ∫⁻ a, g' a ∂(μ.with_density f') :
    lintegral_congr_ae hg.ae_eq_mk
  ... = ∫⁻ a, (f' * g') a ∂μ :
    lintegral_with_density_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk
  ... = ∫⁻ a, (f' * g) a ∂μ :
    begin
      apply lintegral_congr_ae,
      apply ae_of_ae_restrict_of_ae_restrict_compl {x | f' x ≠ 0},
      { have Z := hg.ae_eq_mk,
        rw [eventually_eq, ae_with_density_iff_ae_restrict hf.measurable_mk] at Z,
        filter_upwards [Z],
        assume x hx,
        simp only [hx, pi.mul_apply] },
      { have M : measurable_set {x : α | f' x ≠ 0}ᶜ :=
          (hf.measurable_mk (measurable_set_singleton 0).compl).compl,
        filter_upwards [ae_restrict_mem M],
        assume x hx,
        simp only [not_not, mem_set_of_eq, mem_compl_iff] at hx,
        simp only [hx, zero_mul, pi.mul_apply] }
    end
  ... = ∫⁻ (a : α), (f * g) a ∂μ :
    begin
      apply lintegral_congr_ae,
      filter_upwards [hf.ae_eq_mk],
      assume x hx,
      simp only [hx, pi.mul_apply],
    end
end

lemma lintegral_with_density_eq_lintegral_mul₀ {μ : measure α} {f : α → ℝ≥0∞}
  (hf : ae_measurable f μ) {g : α → ℝ≥0∞} (hg : ae_measurable g μ) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
lintegral_with_density_eq_lintegral_mul₀' hf (hg.mono' (with_density_absolutely_continuous μ f))

lemma lintegral_with_density_le_lintegral_mul (μ : measure α)
  {f : α → ℝ≥0∞} (f_meas : measurable f) (g : α → ℝ≥0∞) :
  ∫⁻ a, g a ∂(μ.with_density f) ≤ ∫⁻ a, (f * g) a ∂μ :=
begin
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral],
  refine supr₂_le (λ i i_meas, supr_le (λ hi, _)),
  have A : f * i ≤ f * g := λ x, mul_le_mul_left' (hi x) _,
  refine le_supr₂_of_le (f * i) (f_meas.mul i_meas) _,
  exact le_supr_of_le A (le_of_eq (lintegral_with_density_eq_lintegral_mul _ f_meas i_meas))
end

lemma lintegral_with_density_eq_lintegral_mul_non_measurable (μ : measure α)
  {f : α → ℝ≥0∞} (f_meas : measurable f) (hf : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  refine le_antisymm (lintegral_with_density_le_lintegral_mul μ f_meas g) _,
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral],
  refine supr₂_le (λ i i_meas, supr_le $ λ hi, _),
  have A : (λ x, (f x)⁻¹ * i x) ≤ g,
  { assume x,
    dsimp,
    rw [mul_comm, ← div_eq_mul_inv],
    exact div_le_of_le_mul' (hi x), },
  refine le_supr_of_le (λ x, (f x)⁻¹ * i x) (le_supr_of_le (f_meas.inv.mul i_meas) _),
  refine le_supr_of_le A _,
  rw lintegral_with_density_eq_lintegral_mul _ f_meas (f_meas.inv.mul i_meas),
  apply lintegral_mono_ae,
  filter_upwards [hf],
  assume x h'x,
  rcases eq_or_ne (f x) 0 with hx|hx,
  { have := hi x,
    simp only [hx, zero_mul, pi.mul_apply, nonpos_iff_eq_zero] at this,
    simp [this] },
  { apply le_of_eq _,
    dsimp,
    rw [← mul_assoc, ennreal.mul_inv_cancel hx h'x.ne, one_mul] }
end

lemma set_lintegral_with_density_eq_set_lintegral_mul_non_measurable (μ : measure α)
  {f : α → ℝ≥0∞} (f_meas : measurable f) (g : α → ℝ≥0∞)
  {s : set α} (hs : measurable_set s) (hf : ∀ᵐ x ∂(μ.restrict s), f x < ∞) :
  ∫⁻ a in s, g a ∂(μ.with_density f) = ∫⁻ a in s, (f * g) a ∂μ :=
by rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul_non_measurable _ f_meas hf]

lemma lintegral_with_density_eq_lintegral_mul_non_measurable₀ (μ : measure α)
  {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (h'f : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  let f' := hf.mk f,
  calc
  ∫⁻ a, g a ∂(μ.with_density f)
      = ∫⁻ a, g a ∂(μ.with_density f') : by rw with_density_congr_ae hf.ae_eq_mk
  ... = ∫⁻ a, (f' * g) a ∂μ :
    begin
      apply lintegral_with_density_eq_lintegral_mul_non_measurable _ hf.measurable_mk,
      filter_upwards [h'f, hf.ae_eq_mk],
      assume x hx h'x,
      rwa ← h'x,
    end
  ... = ∫⁻ a, (f * g) a ∂μ :
    begin
      apply lintegral_congr_ae,
      filter_upwards [hf.ae_eq_mk],
      assume x hx,
      simp only [hx, pi.mul_apply],
    end
end

lemma set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀ (μ : measure α)
  {f : α → ℝ≥0∞} {s : set α} (hf : ae_measurable f (μ.restrict s)) (g : α → ℝ≥0∞)
  (hs : measurable_set s) (h'f : ∀ᵐ x ∂(μ.restrict s), f x < ∞) :
  ∫⁻ a in s, g a ∂(μ.with_density f) = ∫⁻ a in s, (f * g) a ∂μ :=
by rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul_non_measurable₀ _ hf h'f]

lemma with_density_mul (μ : measure α) {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  μ.with_density (f * g) = (μ.with_density f).with_density g :=
begin
  ext1 s hs,
  simp [with_density_apply _ hs, restrict_with_density hs,
        lintegral_with_density_eq_lintegral_mul _ hf hg],
end

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
lemma exists_pos_lintegral_lt_of_sigma_finite
  (μ : measure α) [sigma_finite μ] {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
  ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ measurable g ∧ (∫⁻ x, g x ∂μ < ε) :=
begin
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
  `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
   is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → set α := disjointed (spanning_sets μ),
  have : ∀ n, μ (s n) < ∞,
    from λ n, (measure_mono $ disjointed_subset _ _).trans_lt (measure_spanning_sets_lt_top μ n),
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ ∑' i, μ (s i) * δ i < ε,
    from ennreal.exists_pos_tsum_mul_lt_of_countable ε0 _ (λ n, (this n).ne),
  set N : α → ℕ := spanning_sets_index μ,
  have hN_meas : measurable N := measurable_spanning_sets_index μ,
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanning_sets_index_singleton μ,
  refine ⟨δ ∘ N, λ x, δpos _, measurable_from_nat.comp hN_meas, _⟩,
  simpa [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas, hNs,
    lintegral_countable', measurable_spanning_sets_index, mul_comm] using δsum,
end

lemma lintegral_trim {μ : measure α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : measurable[m] f) :
  ∫⁻ a, f a ∂(μ.trim hm) = ∫⁻ a, f a ∂μ :=
begin
  refine @measurable.ennreal_induction α m (λ f, ∫⁻ a, f a ∂(μ.trim hm) = ∫⁻ a, f a ∂μ) _ _ _ f hf,
  { intros c s hs,
    rw [lintegral_indicator _ hs, lintegral_indicator _ (hm s hs),
      set_lintegral_const, set_lintegral_const],
    suffices h_trim_s : μ.trim hm s = μ s, by rw h_trim_s,
    exact trim_measurable_set_eq hm hs, },
  { intros f g hfg hf hg hf_prop hg_prop,
    have h_m := lintegral_add_left hf g,
    have h_m0 := lintegral_add_left (measurable.mono hf hm le_rfl) g,
    rwa [hf_prop, hg_prop, ← h_m0] at h_m, },
  { intros f hf hf_mono hf_prop,
    rw lintegral_supr hf hf_mono,
    rw lintegral_supr (λ n, measurable.mono (hf n) hm le_rfl) hf_mono,
    congr,
    exact funext (λ n, hf_prop n), },
end

lemma lintegral_trim_ae {μ : measure α} (hm : m ≤ m0)
  {f : α → ℝ≥0∞} (hf : ae_measurable f (μ.trim hm)) :
  ∫⁻ a, f a ∂(μ.trim hm) = ∫⁻ a, f a ∂μ :=
by rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk),
  lintegral_congr_ae hf.ae_eq_mk, lintegral_trim hm hf.measurable_mk]

section sigma_finite

variables {E : Type*} [normed_add_comm_group E] [measurable_space E]
  [opens_measurable_space E]

lemma univ_le_of_forall_fin_meas_le {μ : measure α} (hm : m ≤ m0) [sigma_finite (μ.trim hm)]
  (C : ℝ≥0∞) {f : set α → ℝ≥0∞} (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → f s ≤ C)
  (h_F_lim : ∀ S : ℕ → set α,
    (∀ n, measurable_set[m] (S n)) → monotone S → f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
  f univ ≤ C :=
begin
  let S := @spanning_sets _ m (μ.trim hm) _,
  have hS_mono : monotone S, from @monotone_spanning_sets _ m (μ.trim hm) _,
  have hS_meas : ∀ n, measurable_set[m] (S n), from @measurable_spanning_sets _ m (μ.trim hm) _,
  rw ← @Union_spanning_sets _ m (μ.trim hm),
  refine (h_F_lim S hS_meas hS_mono).trans _,
  refine supr_le (λ n, hf (S n) (hS_meas n) _),
  exact ((le_trim hm).trans_lt (@measure_spanning_sets_lt_top _ m (μ.trim hm) _ n)).ne,
end

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `ae_measurable` version. -/
lemma lintegral_le_of_forall_fin_meas_le_of_measurable {μ : measure α} (hm : m ≤ m0)
  [sigma_finite (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : measurable f)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) :
  ∫⁻ x, f x ∂μ ≤ C :=
begin
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ, by simp only [measure.restrict_univ],
  rw ← this,
  refine univ_le_of_forall_fin_meas_le hm C hf (λ S hS_meas hS_mono, _),
  rw ← lintegral_indicator,
  swap, { exact hm (⋃ n, S n) (@measurable_set.Union _ _ m _ _ hS_meas), },
  have h_integral_indicator : (⨆ n, ∫⁻ x in S n, f x ∂μ) = ⨆ n, ∫⁻ x, (S n).indicator f x ∂μ,
  { congr,
    ext1 n,
    rw lintegral_indicator _ (hm _ (hS_meas n)), },
  rw [h_integral_indicator,  ← lintegral_supr],
  { refine le_of_eq (lintegral_congr (λ x, _)),
    simp_rw indicator_apply,
    by_cases hx_mem : x ∈ Union S,
    { simp only [hx_mem, if_true],
      obtain ⟨n, hxn⟩ := mem_Union.mp hx_mem,
      refine le_antisymm (trans _ (le_supr _ n)) (supr_le (λ i, _)),
      { simp only [hxn, le_refl, if_true], },
      { by_cases hxi : x ∈ S i; simp [hxi], }, },
    { simp only [hx_mem, if_false],
      rw mem_Union at hx_mem,
      push_neg at hx_mem,
      refine le_antisymm (zero_le _) (supr_le (λ n, _)),
      simp only [hx_mem n, if_false, nonpos_iff_eq_zero], }, },
  { exact λ n, hf_meas.indicator (hm _ (hS_meas n)), },
  { intros n₁ n₂ hn₁₂ a,
    simp_rw indicator_apply,
    split_ifs,
    { exact le_rfl, },
    { exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1, },
    { exact zero_le _, },
    { exact le_rfl, }, },
end

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
lemma lintegral_le_of_forall_fin_meas_le' {μ : measure α} (hm : m ≤ m0)
  [sigma_finite (μ.trim hm)] (C : ℝ≥0∞) {f : _ → ℝ≥0∞} (hf_meas : ae_measurable f μ)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) :
  ∫⁻ x, f x ∂μ ≤ C :=
begin
  let f' := hf_meas.mk f,
  have hf' : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, f' x ∂μ ≤ C,
  { refine λ s hs hμs, (le_of_eq _).trans (hf s hs hμs),
    refine lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono (λ x hx, _))),
    rw hx, },
  rw lintegral_congr_ae hf_meas.ae_eq_mk,
  exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf',
end

omit m

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
lemma lintegral_le_of_forall_fin_meas_le [measurable_space α] {μ : measure α} [sigma_finite μ]
  (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : ae_measurable f μ)
  (hf : ∀ s, measurable_set s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) :
  ∫⁻ x, f x ∂μ ≤ C :=
@lintegral_le_of_forall_fin_meas_le' _ _ _ _ _ (by rwa trim_eq_self) C _ hf_meas hf

local infixr ` →ₛ `:25 := simple_func

lemma simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral
  {m : measurable_space α} {μ : measure α} [sigma_finite μ] {f : α →ₛ ℝ≥0}
  {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
  ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ (∫⁻ x, g x ∂μ < ∞) ∧ (L < ∫⁻ x, g x ∂μ) :=
begin
  induction f using measure_theory.simple_func.induction with c s hs f₁ f₂ H h₁ h₂ generalizing L,
  { simp only [hs, const_zero, coe_piecewise, coe_const, simple_func.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, measure.restrict_apply',
      coe_indicator, function.const_apply] at hL,
    have c_ne_zero : c ≠ 0,
    { assume hc, simpa only [hc, ennreal.coe_zero, zero_mul, not_lt_zero] using hL },
    have : L / c < μ s,
    { rwa [ennreal.div_lt_iff, mul_comm],
      { simp only [c_ne_zero, ne.def, coe_eq_zero, not_false_iff, true_or] },
      { simp only [ne.def, coe_ne_top, not_false_iff, true_or] } },
    obtain ⟨t, ht, ts, mut, t_top⟩ :
      ∃ (t : set α), measurable_set t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
        measure.exists_subset_measure_lt_top hs this,
    refine ⟨piecewise t ht (const α c) (const α 0), λ x, _, _, _⟩,
    { apply indicator_le_indicator_of_subset ts (λ x, _), exact zero_le _ },
    { simp only [ht, const_zero, coe_piecewise, coe_const, simple_func.coe_zero, univ_inter,
        piecewise_eq_indicator, coe_indicator, function.const_apply, lintegral_indicator,
        lintegral_const, measure.restrict_apply', ennreal.mul_lt_top ennreal.coe_ne_top t_top.ne] },
    { simp only [ht, const_zero, coe_piecewise, coe_const, simple_func.coe_zero,
        piecewise_eq_indicator, coe_indicator, function.const_apply, lintegral_indicator,
        lintegral_const, measure.restrict_apply', univ_inter],
      rwa [mul_comm, ← ennreal.div_lt_iff],
      { simp only [c_ne_zero, ne.def, coe_eq_zero, not_false_iff, true_or] },
      { simp only [ne.def, coe_ne_top, not_false_iff, true_or] } } },
  { replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ,
    { rwa ← lintegral_add_left f₁.measurable.coe_nnreal_ennreal },
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0,
    { simp only [hf₁, zero_add] at hL,
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩,
      refine ⟨g, λ x, (g_le x).trans _, g_top, gL⟩,
      simp only [simple_func.coe_add, pi.add_apply, le_add_iff_nonneg_left, zero_le'] },
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0,
    { simp only [hf₂, add_zero] at hL,
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩,
      refine ⟨g, λ x, (g_le x).trans _, g_top, gL⟩,
      simp only [simple_func.coe_add, pi.add_apply, le_add_iff_nonneg_right, zero_le'] },
    obtain ⟨L₁, L₂, hL₁, hL₂, hL⟩ :
      ∃ (L₁ L₂ : ℝ≥0∞), L₁ < ∫⁻ x, f₁ x ∂μ ∧ L₂ < ∫⁻ x, f₂ x ∂μ ∧ L < L₁ + L₂ :=
      ennreal.exists_lt_add_of_lt_add hL hf₁ hf₂,
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩,
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩,
    refine ⟨g₁ + g₂, λ x, add_le_add (g₁_le x) (g₂_le x), _, _⟩,
    { apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩),
      rw ← lintegral_add_left g₁.measurable.coe_nnreal_ennreal,
      exact le_rfl },
    { apply hL.trans ((ennreal.add_lt_add hg₁ hg₂).trans_le _),
      rw ← lintegral_add_left g₁.measurable.coe_nnreal_ennreal,
      exact le_rfl } }
end

lemma exists_lt_lintegral_simple_func_of_lt_lintegral
  {m : measurable_space α} {μ : measure α} [sigma_finite μ] {f : α → ℝ≥0}
  {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
  ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ (∫⁻ x, g x ∂μ < ∞) ∧ (L < ∫⁻ x, g x ∂μ) :=
begin
  simp_rw [lintegral_eq_nnreal, lt_supr_iff] at hL,
  rcases hL with ⟨g₀, hg₀, g₀L⟩,
  have h'L : L < ∫⁻ x, g₀ x ∂μ,
  { convert g₀L,
    rw ← simple_func.lintegral_eq_lintegral,
    refl },
  rcases simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩,
  exact ⟨g, λ x, (hg x).trans (coe_le_coe.1 (hg₀ x)), gL, gtop⟩,
end

/-- A sigma-finite measure is absolutely continuous with respect to some finite measure. -/
lemma exists_absolutely_continuous_is_finite_measure
  {m : measurable_space α} (μ : measure α) [sigma_finite μ] :
  ∃ (ν : measure α), is_finite_measure ν ∧ μ ≪ ν :=
begin
  obtain ⟨g, gpos, gmeas, hg⟩ : ∃ (g : α → ℝ≥0), (∀ (x : α), 0 < g x) ∧
    measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < 1 :=
      exists_pos_lintegral_lt_of_sigma_finite μ one_ne_zero,
  refine ⟨μ.with_density (λ x, g x), is_finite_measure_with_density hg.ne_top, _⟩,
  have : μ = (μ.with_density (λ x, g x)).with_density (λ x, (g x)⁻¹),
  { have A : (λ (x : α), (g x : ℝ≥0∞)) * (λ (x : α), (↑(g x))⁻¹) = 1,
    { ext1 x,
      exact ennreal.mul_inv_cancel (ennreal.coe_ne_zero.2 ((gpos x).ne')) ennreal.coe_ne_top },
    rw [← with_density_mul _ gmeas.coe_nnreal_ennreal gmeas.coe_nnreal_ennreal.inv, A,
        with_density_one] },
  conv_lhs { rw this },
  exact with_density_absolutely_continuous _ _,
end

end sigma_finite

end measure_theory
