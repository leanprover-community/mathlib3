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
preserves the measure `μ × ν`, which means that
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
open set (hiding prod_eq) function measure_theory filter (hiding map)
open_locale classical ennreal pointwise measure_theory

variables (G : Type*) [measurable_space G]
variables [group G] [has_measurable_mul₂ G]
variables (μ ν : measure G) [sigma_finite ν] [sigma_finite μ] {E : set G}

/-- The map `(x, y) ↦ (x, xy)` as a `measurable_equiv`. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a `measurable_equiv`."]
protected def measurable_equiv.shear_mul_right [has_measurable_inv G] : G × G ≃ᵐ G × G :=
{ measurable_to_fun  := measurable_fst.prod_mk measurable_mul,
  measurable_inv_fun := measurable_fst.prod_mk $ measurable_fst.inv.mul measurable_snd,
  .. equiv.prod_shear (equiv.refl _) equiv.mul_left }

/-- The map `(x, y) ↦ (x, yx)` as a `measurable_equiv` with as inverse `(x, y) ↦ (x, y / x)` -/
@[to_additive
  "The map `(x, y) ↦ (x, y + x)` as a `measurable_equiv` with as inverse `(x, y) ↦ (x, y - x)`."]
protected def measurable_equiv.shear_mul_left [has_measurable_inv G] : G × G ≃ᵐ G × G :=
{ measurable_to_fun  := measurable_fst.prod_mk $ measurable_snd.mul measurable_fst,
  measurable_inv_fun := measurable_fst.prod_mk $ measurable_snd.div measurable_fst,
  .. equiv.prod_shear (equiv.refl _) (λ x, (equiv.div_right x).symm) }

variables {G}

namespace measure_theory

open measure

section left_invariant

/-- The multiplicative shear mapping `(x, y) ↦ (x, xy)` preserves the measure `μ × ν`.
This condition is part of the definition of a measurable group in [Halmos, §59].
There, the map in this lemma is called `S`. -/
@[to_additive measure_preserving_prod_add
  /-" The shear mapping `(x, y) ↦ (x, x + y)` preserves the measure `μ × ν`. "-/]
lemma measure_preserving_prod_mul [is_mul_left_invariant ν] :
  measure_preserving (λ z : G × G, (z.1, z.1 * z.2)) (μ.prod ν) (μ.prod ν) :=
(measure_preserving.id μ).skew_product measurable_mul $
  filter.eventually_of_forall $ map_mul_left_eq_self ν

/-- The map `(x, y) ↦ (y, yx)` sends the measure `μ × ν` to `ν × μ`.
This is the map `SR` in [Halmos, §59].
`S` is the map `(x, y) ↦ (x, xy)` and `R` is `prod.swap`. -/
@[to_additive measure_preserving_prod_add_swap
  /-" The map `(x, y) ↦ (y, y + x)` sends the measure `μ × ν` to `ν × μ`. "-/]
lemma measure_preserving_prod_mul_swap [is_mul_left_invariant μ] :
  measure_preserving (λ z : G × G, (z.2, z.2 * z.1)) (μ.prod ν) (ν.prod μ) :=
(measure_preserving_prod_mul ν μ).comp measure_preserving_swap

@[to_additive]
lemma measurable_measure_mul_right (hE : measurable_set E) :
  measurable (λ x, μ ((λ y, y * x) ⁻¹' E)) :=
begin
  suffices : measurable (λ y,
    μ ((λ x, (x, y)) ⁻¹' ((λ z : G × G, ((1 : G), z.1 * z.2)) ⁻¹' (univ ×ˢ E)))),
  { convert this, ext1 x, congr' 1 with y : 1, simp },
  apply measurable_measure_prod_mk_right,
  exact measurable_const.prod_mk measurable_mul (measurable_set.univ.prod hE)
end

variables [has_measurable_inv G]

/-- The map `(x, y) ↦ (x, x⁻¹y)` is measure-preserving.
This is the function `S⁻¹` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)`. -/
@[to_additive measure_preserving_prod_neg_add
  "The map `(x, y) ↦ (x, - x + y)` is measure-preserving."]
lemma measure_preserving_prod_inv_mul [is_mul_left_invariant ν] :
  measure_preserving (λ z : G × G, (z.1, z.1⁻¹ * z.2)) (μ.prod ν) (μ.prod ν) :=
(measure_preserving_prod_mul μ ν).symm $ measurable_equiv.shear_mul_right G

variables [is_mul_left_invariant μ]

/-- The map `(x, y) ↦ (y, y⁻¹x)` sends `μ × ν` to `ν × μ`.
This is the function `S⁻¹R` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `prod.swap`. -/
@[to_additive measure_preserving_prod_neg_add_swap
  "The map `(x, y) ↦ (y, - y + x)` sends `μ × ν` to `ν × μ`."]
lemma measure_preserving_prod_inv_mul_swap :
  measure_preserving (λ z : G × G, (z.2, z.2⁻¹ * z.1)) (μ.prod ν) (ν.prod μ) :=
(measure_preserving_prod_inv_mul ν μ).comp measure_preserving_swap

/-- The map `(x, y) ↦ (yx, x⁻¹)` is measure-preserving.
This is the function `S⁻¹RSR` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `prod.swap`. -/
@[to_additive measure_preserving_add_prod_neg
  "The map `(x, y) ↦ (y + x, - x)` is measure-preserving."]
lemma measure_preserving_mul_prod_inv [is_mul_left_invariant ν] :
  measure_preserving (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod ν) (μ.prod ν) :=
begin
  convert (measure_preserving_prod_inv_mul_swap ν μ).comp
    (measure_preserving_prod_mul_swap μ ν),
  ext1 ⟨x, y⟩,
  simp_rw [function.comp_apply, mul_inv_rev, inv_mul_cancel_right]
end

@[to_additive] lemma quasi_measure_preserving_inv :
  quasi_measure_preserving (has_inv.inv : G → G) μ μ :=
begin
  refine ⟨measurable_inv, absolutely_continuous.mk $ λ s hsm hμs, _⟩,
  rw [map_apply measurable_inv hsm, inv_preimage],
  have hf : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv,
  suffices : map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0,
  { simpa only [(measure_preserving_mul_prod_inv μ μ).map_eq,
      prod_prod, mul_eq_zero, or_self] using this },
  have hsm' : measurable_set (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv,
  simp_rw [map_apply hf hsm', prod_apply_symm (hf hsm'), preimage_preimage, mk_preimage_prod,
    inv_preimage, inv_inv, measure_mono_null (inter_subset_right _ _) hμs, lintegral_zero]
end

@[to_additive]
lemma measure_inv_null : μ E⁻¹ = 0 ↔ μ E = 0 :=
begin
  refine ⟨λ hE, _, (quasi_measure_preserving_inv μ).preimage_null⟩,
  convert (quasi_measure_preserving_inv μ).preimage_null hE,
  exact (inv_inv _).symm
end

@[to_additive]
lemma absolutely_continuous_map_inv : μ ≪ map has_inv.inv μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  simp_rw [map_apply measurable_inv hs, inv_preimage, measure_inv_null, imp_self]
end

@[to_additive]
lemma lintegral_lintegral_mul_inv [is_mul_left_invariant ν]
  (f : G → G → ℝ≥0∞) (hf : ae_measurable (uncurry f) (μ.prod ν)) :
  ∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ :=
begin
  have h : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
  (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv,
  have h2f : ae_measurable (uncurry $ λ x y, f (y * x) x⁻¹) (μ.prod ν) :=
    hf.comp_quasi_measure_preserving (measure_preserving_mul_prod_inv μ ν).quasi_measure_preserving,
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf],
  conv_rhs { rw [← (measure_preserving_mul_prod_inv μ ν).map_eq] },
  symmetry,
  exact lintegral_map' (hf.mono' (measure_preserving_mul_prod_inv μ ν).map_eq.absolutely_continuous)
    h.ae_measurable,
end

@[to_additive]
lemma measure_mul_right_null (y : G) :
  μ ((λ x, x * y) ⁻¹' E) = 0 ↔ μ E = 0 :=
calc μ ((λ x, x * y) ⁻¹' E) = 0 ↔ μ ((λ x, y⁻¹ * x) ⁻¹' E⁻¹)⁻¹ = 0 :
  by simp_rw [← inv_preimage, preimage_preimage, mul_inv_rev, inv_inv]
... ↔ μ E = 0 : by simp only [measure_inv_null μ, measure_preimage_mul]

@[to_additive]
lemma measure_mul_right_ne_zero
  (h2E : μ E ≠ 0) (y : G) : μ ((λ x, x * y) ⁻¹' E) ≠ 0 :=
(not_iff_not_of_iff (measure_mul_right_null μ y)).mpr h2E

/-- A *left*-invariant measure is quasi-preserved by *right*-multiplication.
This should not be confused with `(measure_preserving_mul_right μ g).quasi_measure_preserving`. -/
@[to_additive /-"A *left*-invariant measure is quasi-preserved by *right*-addition.
This should not be confused with `(measure_preserving_add_right μ g).quasi_measure_preserving`. "-/]
lemma quasi_measure_preserving_mul_right (g : G) :
  quasi_measure_preserving (λ h : G, h * g) μ μ :=
begin
  refine ⟨measurable_mul_const g, absolutely_continuous.mk $ λ s hs, _⟩,
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id,
end

@[to_additive]
lemma absolutely_continuous_map_mul_right (g : G) : μ ≪ map (* g) μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id
end

@[to_additive] lemma quasi_measure_preserving_div_left (g : G) :
  quasi_measure_preserving (λ h : G, g / h) μ μ :=
begin
  simp_rw [div_eq_mul_inv],
  exact (measure_preserving_mul_left μ g).quasi_measure_preserving.comp
    (quasi_measure_preserving_inv μ)
end

@[to_additive]
lemma absolutely_continuous_map_div_left (g : G) : μ ≪ map (λ h, g / h) μ :=
begin
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  conv_lhs { rw [← map_mul_left_eq_self μ g] },
  exact (absolutely_continuous_map_inv μ).map (measurable_const_mul g)
end

/-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/
@[to_additive "This is the computation performed in the proof of [Halmos, §60 Th. A]."]
lemma measure_mul_lintegral_eq
  [is_mul_left_invariant ν] (Em : measurable_set E) (f : G → ℝ≥0∞) (hf : measurable f) :
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
@[to_additive /-" Any two nonzero left-invariant measures are absolutely continuous w.r.t. each
other. "-/]
lemma absolutely_continuous_of_is_mul_left_invariant [is_mul_left_invariant ν] (hν : ν ≠ 0) :
  μ ≪ ν :=
begin
  refine absolutely_continuous.mk (λ E Em hνE, _),
  have h1 := measure_mul_lintegral_eq μ ν Em 1 measurable_one,
  simp_rw [pi.one_apply, lintegral_one, mul_one, (measure_mul_right_null ν _).mpr hνE,
    lintegral_zero, mul_eq_zero, measure_univ_eq_zero.not.mpr hν, or_false] at h1,
  exact h1
end

@[to_additive]
lemma ae_measure_preimage_mul_right_lt_top [is_mul_left_invariant ν]
  (Em : measurable_set E) (hμE : μ E ≠ ∞) :
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
lemma ae_measure_preimage_mul_right_lt_top_of_ne_zero [is_mul_left_invariant ν]
  (Em : measurable_set E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) :
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
@[to_additive "A technical lemma relating two different measures. This is basically
[Halmos, §60 Th. A]. Note that if `f` is the characteristic function of a measurable set `F` this
states that `μ F = c * μ E` for a constant `c` that does not depend on `μ`.

Note: There is a gap in the last step of the proof in [Halmos]. In the last line, the equality
`g(-x) + ν(E - x) = f(x)` holds if we can prove that `0 < ν(E - x) < ∞`. The first inequality
follows from §59, Th. D, but the second inequality is not justified. We prove this inequality for
almost all `x` in `measure_theory.ae_measure_preimage_add_right_lt_top_of_ne_zero`."]
lemma measure_lintegral_div_measure [is_mul_left_invariant ν]
  (Em : measurable_set E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞)
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
lemma measure_mul_measure_eq [is_mul_left_invariant ν] {E F : set G}
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
@[to_additive /-" Left invariant Borel measures on an additive measurable group are unique
  (up to a scalar). "-/]
lemma measure_eq_div_smul [is_mul_left_invariant ν]
  (hE : measurable_set E) (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) : μ = (μ E / ν E) • ν :=
begin
  ext1 F hF,
  rw [smul_apply, smul_eq_mul, mul_comm, ← mul_div_assoc, mul_comm,
    measure_mul_measure_eq μ ν hE hF h2E h3E, mul_div_assoc, ennreal.mul_div_cancel' h2E h3E]
end

end left_invariant

section right_invariant

@[to_additive measure_preserving_prod_add_right]
lemma measure_preserving_prod_mul_right [is_mul_right_invariant ν] :
  measure_preserving (λ z : G × G, (z.1, z.2 * z.1)) (μ.prod ν) (μ.prod ν) :=
(measure_preserving.id μ).skew_product (by exact measurable_snd.mul measurable_fst) $
  filter.eventually_of_forall $ map_mul_right_eq_self ν

/-- The map `(x, y) ↦ (y, xy)` sends the measure `μ × ν` to `ν × μ`. -/
@[to_additive measure_preserving_prod_add_swap_right
  /-" The map `(x, y) ↦ (y, x + y)` sends the measure `μ × ν` to `ν × μ`. "-/]
lemma measure_preserving_prod_mul_swap_right [is_mul_right_invariant μ] :
  measure_preserving (λ z : G × G, (z.2, z.1 * z.2)) (μ.prod ν) (ν.prod μ) :=
(measure_preserving_prod_mul_right ν μ).comp measure_preserving_swap

/-- The map `(x, y) ↦ (xy, y)` preserves the measure `μ × ν`. -/
@[to_additive measure_preserving_add_prod
  /-" The map `(x, y) ↦ (x + y, y)` preserves the measure `μ × ν`. "-/]
lemma measure_preserving_mul_prod [is_mul_right_invariant μ] :
  measure_preserving (λ z : G × G, (z.1 * z.2, z.2)) (μ.prod ν) (μ.prod ν) :=
measure_preserving_swap.comp $ by apply measure_preserving_prod_mul_swap_right μ ν

variables [has_measurable_inv G]

@[to_additive]
lemma quasi_measure_preserving_div [is_mul_right_invariant μ] :
  quasi_measure_preserving (λ (p : G × G), p.1 / p.2) (μ.prod ν) μ :=
begin
  refine quasi_measure_preserving.prod_of_left measurable_div (eventually_of_forall $ λ y, _),
  exact (measure_preserving_div_right μ y).quasi_measure_preserving
end

/-- The map `(x, y) ↦ (x, y / x)` is measure-preserving. -/
@[to_additive measure_preserving_prod_sub
  "The map `(x, y) ↦ (x, y - x)` is measure-preserving."]
lemma measure_preserving_prod_div [is_mul_right_invariant ν] :
  measure_preserving (λ z : G × G, (z.1, z.2 / z.1)) (μ.prod ν) (μ.prod ν) :=
(measure_preserving_prod_mul_right μ ν).symm (measurable_equiv.shear_mul_left G)

/-- The map `(x, y) ↦ (y, x / y)` sends `μ × ν` to `ν × μ`. -/
@[to_additive measure_preserving_prod_sub_swap
  "The map `(x, y) ↦ (y, x - y)` sends `μ × ν` to `ν × μ`."]
lemma measure_preserving_prod_div_swap [is_mul_right_invariant μ] :
  measure_preserving (λ z : G × G, (z.2, z.1 / z.2)) (μ.prod ν) (ν.prod μ) :=
(measure_preserving_prod_div ν μ).comp measure_preserving_swap

/-- The map `(x, y) ↦ (x / y, y)` preserves the measure `μ × ν`. -/
@[to_additive measure_preserving_sub_prod
  /-" The map `(x, y) ↦ (x - y, y)` preserves the measure `μ × ν`. "-/]
lemma measure_preserving_div_prod [is_mul_right_invariant μ] :
  measure_preserving (λ z : G × G, (z.1 / z.2, z.2)) (μ.prod ν) (μ.prod ν) :=
measure_preserving_swap.comp $ by apply measure_preserving_prod_div_swap μ ν

/-- The map `(x, y) ↦ (xy, x⁻¹)` is measure-preserving. -/
@[to_additive measure_preserving_add_prod_neg_right
  "The map `(x, y) ↦ (x + y, - x)` is measure-preserving."]
lemma measure_preserving_mul_prod_inv_right [is_mul_right_invariant μ] [is_mul_right_invariant ν] :
  measure_preserving (λ z : G × G, (z.1 * z.2, z.1⁻¹)) (μ.prod ν) (μ.prod ν) :=
begin
  convert (measure_preserving_prod_div_swap ν μ).comp
    (measure_preserving_prod_mul_swap_right μ ν),
  ext1 ⟨x, y⟩,
  simp_rw [function.comp_apply, div_mul_eq_div_div_swap, div_self', one_div]
end

end right_invariant

end measure_theory
