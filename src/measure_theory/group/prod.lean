/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.constructions.prod
import measure_theory.group.measure

/-!
# Measure theory in the product of groups
In this file we show properties about measure theory in products of measurable groups
and properties of iterated integrals in measurable groups.

These lemmas show the uniqueness of left invariant measures on measurable groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(F) = c * μ(E)`
for two sets `E` and `F`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `E` and `F`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ.prod ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' E)`, we can rewrite the RHS to
`μ(F)`, and the LHS to `c * μ(E)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (F) / μ (E) = ν (F) / ν (E)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`measure_theory.measure_lintegral_div_measure`.

-/

noncomputable theory
open set (hiding prod_eq) function measure_theory
open_locale classical ennreal pointwise measure_theory

variables (G : Type*) [measurable_space G]
variables [group G] [has_measurable_mul₂ G]
variables (μ ν : measure G) [sigma_finite ν] [sigma_finite μ]

/-- The map `(x, y) ↦ (x, xy)` as a `measurable_equiv`. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a `measurable_equiv`.
This is a shear mapping."]
protected def measurable_equiv.shear_mul_right [has_measurable_inv G] : G × G ≃ᵐ G × G :=
{ measurable_to_fun  := measurable_fst.prod_mk measurable_mul,
  measurable_inv_fun := measurable_fst.prod_mk $ measurable_fst.inv.mul measurable_snd,
  .. equiv.prod_shear (equiv.refl _) equiv.mul_left }

variables {G}

namespace measure_theory

open measure

/-- This condition is part of the definition of a measurable group in [Halmos, §59].
  There, the map in this lemma is called `S`. -/
@[to_additive map_prod_sum_eq]
lemma map_prod_mul_eq [is_mul_left_invariant ν] :
  map (λ z : G × G, (z.1, z.1 * z.2)) (μ.prod ν) = μ.prod ν :=
begin
  refine (prod_eq _).symm, intros s t hs ht,
  simp_rw [map_apply (measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht),
    prod_apply ((measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht)),
    preimage_preimage],
  conv_lhs { congr, skip, funext, rw [mk_preimage_prod_right_fn_eq_if ((*) x), measure_if] },
  simp_rw [measure_preimage_mul, lintegral_indicator _ hs, set_lintegral_const, mul_comm]
end

/-- The function we are mapping along is `SR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_add_eq_swap]
lemma map_prod_mul_eq_swap [is_mul_left_invariant μ] :
  map (λ z : G × G, (z.2, z.2 * z.1)) (μ.prod ν) = ν.prod μ :=
begin
  rw [← prod_swap],
  simp_rw [map_map (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)) measurable_swap],
  exact map_prod_mul_eq ν μ
end

@[to_additive]
lemma measurable_measure_mul_right {E : set G} (hE : measurable_set E) :
  measurable (λ x, μ ((λ y, y * x) ⁻¹' E)) :=
begin
  suffices : measurable (λ y,
    μ ((λ x, (x, y)) ⁻¹' ((λ z : G × G, ((1 : G), z.1 * z.2)) ⁻¹' ((univ : set G) ×ˢ E)))),
  { convert this, ext1 x, congr' 1 with y : 1, simp },
  apply measurable_measure_prod_mk_right,
  exact measurable_const.prod_mk (measurable_fst.mul measurable_snd) (measurable_set.univ.prod hE)
end

variables [has_measurable_inv G]

/-- The function we are mapping along is `S⁻¹` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq`. -/
@[to_additive map_prod_neg_add_eq]
lemma map_prod_inv_mul_eq [is_mul_left_invariant ν] :
  map (λ z : G × G, (z.1, z.1⁻¹ * z.2)) (μ.prod ν) = μ.prod ν :=
(measurable_equiv.shear_mul_right G).map_apply_eq_iff_map_symm_apply_eq.mp $ map_prod_mul_eq μ ν

/-- The function we are mapping along is `S⁻¹R` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_neg_add_eq_swap]
lemma map_prod_inv_mul_eq_swap [is_mul_left_invariant μ] :
  map (λ z : G × G, (z.2, z.2⁻¹ * z.1)) (μ.prod ν) = ν.prod μ :=
begin
  rw [← prod_swap],
  simp_rw
    [map_map (measurable_snd.prod_mk $ measurable_snd.inv.mul measurable_fst) measurable_swap],
  exact map_prod_inv_mul_eq ν μ
end

/-- The function we are mapping along is `S⁻¹RSR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_add_neg_eq]
lemma map_prod_mul_inv_eq [is_mul_left_invariant μ] [is_mul_left_invariant ν] :
  map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod ν) = μ.prod ν :=
begin
  suffices : map ((λ z : G × G, (z.2, z.2⁻¹ * z.1)) ∘ (λ z : G × G, (z.2, z.2 * z.1))) (μ.prod ν) =
    μ.prod ν,
  { convert this, ext1 ⟨x, y⟩, simp },
  simp_rw [← map_map (measurable_snd.prod_mk (measurable_snd.inv.mul measurable_fst))
    (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)), map_prod_mul_eq_swap μ ν,
    map_prod_inv_mul_eq_swap ν μ]
end

@[to_additive] lemma quasi_measure_preserving_inv [is_mul_left_invariant μ] :
  quasi_measure_preserving (has_inv.inv : G → G) μ μ :=
begin
  refine ⟨measurable_inv, absolutely_continuous.mk $ λ s hsm hμs, _⟩,
  rw [map_apply measurable_inv hsm, inv_preimage],
  have hf : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv,
  suffices : map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0,
  { simpa only [map_prod_mul_inv_eq μ μ, prod_prod, mul_eq_zero, or_self] using this },
  have hsm' : measurable_set (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv,
  simp_rw [map_apply hf hsm', prod_apply_symm (hf hsm'), preimage_preimage, mk_preimage_prod,
    inv_preimage, inv_inv, measure_mono_null (inter_subset_right _ _) hμs, lintegral_zero]
end

@[to_additive]
lemma measure_inv_null [is_mul_left_invariant μ] {E : set G} :
  μ ((λ x, x⁻¹) ⁻¹' E) = 0 ↔ μ E = 0 :=
begin
  refine ⟨λ hE, _, (quasi_measure_preserving_inv μ).preimage_null⟩,
  convert (quasi_measure_preserving_inv μ).preimage_null hE,
  exact (inv_inv _).symm
end

@[to_additive]
lemma lintegral_lintegral_mul_inv [is_mul_left_invariant μ] [is_mul_left_invariant ν]
  (f : G → G → ℝ≥0∞) (hf : ae_measurable (uncurry f) (μ.prod ν)) :
  ∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ :=
begin
  have h : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
  (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv,
  have h2f : ae_measurable (uncurry $ λ x y, f (y * x) x⁻¹) (μ.prod ν),
  { apply hf.comp_measurable' h (map_prod_mul_inv_eq μ ν).absolutely_continuous },
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf],
  conv_rhs { rw [← map_prod_mul_inv_eq μ ν] },
  symmetry,
  exact lintegral_map' (hf.mono' (map_prod_mul_inv_eq μ ν).absolutely_continuous) h,
end

@[to_additive]
lemma measure_mul_right_null [is_mul_left_invariant μ] {E : set G} (y : G) :
  μ ((λ x, x * y) ⁻¹' E) = 0 ↔ μ E = 0 :=
calc μ ((λ x, x * y) ⁻¹' E) = 0 ↔ μ (has_inv.inv ⁻¹' ((λ x, y⁻¹ * x) ⁻¹' (has_inv.inv ⁻¹' E))) = 0 :
  by simp only [preimage_preimage, mul_inv_rev, inv_inv]
... ↔ μ E = 0 : by simp only [measure_inv_null μ, measure_preimage_mul]

@[to_additive]
lemma measure_mul_right_ne_zero [is_mul_left_invariant μ] {E : set G}
  (h2E : μ E ≠ 0) (y : G) : μ ((λ x, x * y) ⁻¹' E) ≠ 0 :=
(not_iff_not_of_iff (measure_mul_right_null μ y)).mpr h2E

/-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/
@[to_additive]
lemma measure_mul_lintegral_eq [is_mul_left_invariant μ]
  [is_mul_left_invariant ν] {E : set G} (Em : measurable_set E) (f : G → ℝ≥0∞) (hf : measurable f) :
  μ E * ∫⁻ y, f y ∂ν = ∫⁻ x, ν ((λ z, z * x) ⁻¹' E) * f (x⁻¹) ∂μ :=
begin
  rw [← set_lintegral_one, ← lintegral_indicator _ Em,
    ← lintegral_lintegral_mul (measurable_const.indicator Em).ae_measurable hf.ae_measurable,
    ← lintegral_lintegral_mul_inv μ ν],
  swap, { exact (((measurable_const.indicator Em).comp measurable_fst).mul
      (hf.comp measurable_snd)).ae_measurable },
  have mE : ∀ x : G, measurable (λ y, ((λ z, z * x) ⁻¹' E).indicator (λ z, (1 : ℝ≥0∞)) y) :=
  λ x, measurable_const.indicator (measurable_mul_const _ Em),
  have : ∀ x y, E.indicator (λ (z : G), (1 : ℝ≥0∞)) (y * x) =
    ((λ z, z * x) ⁻¹' E).indicator (λ (b : G), 1) y,
  { intros x y, symmetry, convert indicator_comp_right (λ y, y * x), ext1 z, refl },
  simp_rw [this, lintegral_mul_const _ (mE _), lintegral_indicator _ (measurable_mul_const _ Em),
    set_lintegral_one],
end

/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/
@[to_additive]
lemma absolutely_continuous_of_is_mul_left_invariant
  [is_mul_left_invariant μ] [is_mul_left_invariant ν] (hν : ν ≠ 0) : μ ≪ ν :=
begin
  refine absolutely_continuous.mk (λ E Em hνE, _),
  have h1 := measure_mul_lintegral_eq μ ν Em 1 measurable_one,
  simp_rw [pi.one_apply, lintegral_one, mul_one, (measure_mul_right_null ν _).mpr hνE,
    lintegral_zero, mul_eq_zero, measure_univ_eq_zero.not.mpr hν, or_false] at h1,
  exact h1
end

@[to_additive]
lemma ae_measure_preimage_mul_right_lt_top [is_mul_left_invariant μ] [is_mul_left_invariant ν]
  {E : set G} (Em : measurable_set E) (hμE : μ E ≠ ∞) :
  ∀ᵐ x ∂μ, ν ((λ y, y * x) ⁻¹' E) < ∞ :=
begin
  refine ae_of_forall_measure_lt_top_ae_restrict' ν.inv _ _,
  intros A hA h2A h3A,
  simp only [ν.inv_apply] at h3A,
  apply ae_lt_top (measurable_measure_mul_right ν Em),
  have h1 := measure_mul_lintegral_eq μ ν Em (A⁻¹.indicator 1) (measurable_one.indicator hA.inv),
  rw [lintegral_indicator _ hA.inv] at h1,
  simp_rw [pi.one_apply, set_lintegral_one, ← image_inv, indicator_image inv_injective, image_inv,
    ← indicator_mul_right _ (λ x, ν ((λ y, y * x) ⁻¹' E)), function.comp, pi.one_apply,
    mul_one] at h1,
  rw [← lintegral_indicator _ hA, ← h1],
  exact ennreal.mul_ne_top hμE h3A.ne,
end

@[to_additive]
lemma ae_measure_preimage_mul_right_lt_top_of_ne_zero [is_mul_left_invariant μ]
  [is_mul_left_invariant ν] {E : set G} (Em : measurable_set E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) :
  ∀ᵐ x ∂μ, ν ((λ y, y * x) ⁻¹' E) < ∞ :=
begin
  refine (ae_measure_preimage_mul_right_lt_top ν ν Em h3E).filter_mono _,
  refine (absolutely_continuous_of_is_mul_left_invariant μ ν _).ae_le,
  refine mt _ h2E,
  intro hν,
  rw [hν, measure.coe_zero, pi.zero_apply]
end

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `F` this states that
  `μ F = c * μ E` for a constant `c` that does not depend on `μ`.

  Note: There is a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(Ex⁻¹) = f(x)` holds if we can prove that
  `0 < ν(Ex⁻¹) < ∞`. The first inequality follows from §59, Th. D, but the second inequality is
  not justified. We prove this inequality for almost all `x` in
  `measure_theory.ae_measure_preimage_mul_right_lt_top_of_ne_zero`. -/
@[to_additive]
lemma measure_lintegral_div_measure [is_mul_left_invariant μ]
  [is_mul_left_invariant ν] {E : set G} (Em : measurable_set E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞)
  (f : G → ℝ≥0∞) (hf : measurable f) :
  μ E * ∫⁻ y, f y⁻¹ / ν ((λ x, x * y⁻¹) ⁻¹' E) ∂ν = ∫⁻ x, f x ∂μ :=
begin
  set g := λ y, f y⁻¹ / ν ((λ x, x * y⁻¹) ⁻¹' E),
  have hg : measurable g := (hf.comp measurable_inv).div
    ((measurable_measure_mul_right ν Em).comp measurable_inv),
  simp_rw [measure_mul_lintegral_eq μ ν Em g hg, g, inv_inv],
  refine lintegral_congr_ae _,
  refine (ae_measure_preimage_mul_right_lt_top_of_ne_zero μ ν Em h2E h3E).mono (λ x hx , _),
  simp_rw [ennreal.mul_div_cancel' (measure_mul_right_ne_zero ν h2E _) hx.ne]
end

@[to_additive]
lemma measure_mul_measure_eq [is_mul_left_invariant μ]
  [is_mul_left_invariant ν] {E F : set G}
  (hE : measurable_set E) (hF : measurable_set F) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) :
    μ E * ν F = ν E * μ F :=
begin
  have h1 := measure_lintegral_div_measure ν ν hE h2E h3E (F.indicator (λ x, 1))
    (measurable_const.indicator hF),
  have h2 := measure_lintegral_div_measure μ ν hE h2E h3E (F.indicator (λ x, 1))
    (measurable_const.indicator hF),
  rw [lintegral_indicator _ hF, set_lintegral_one] at h1 h2,
  rw [← h1, mul_left_comm, h2],
end

/-- Left invariant Borel measures on a measurable group are unique (up to a scalar). -/
@[to_additive]
lemma measure_eq_div_smul [is_mul_left_invariant μ]
  [is_mul_left_invariant ν] {E : set G}
  (hE : measurable_set E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) : μ = (μ E / ν E) • ν :=
begin
  ext1 F hF,
  rw [smul_apply, smul_eq_mul, mul_comm, ← mul_div_assoc, mul_comm,
    measure_mul_measure_eq μ ν hE hF h2E h3E, mul_div_assoc, ennreal.mul_div_cancel' h2E h3E]
end

end measure_theory
