/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.special_functions.complex.circle
import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.group.integration
import measure_theory.integral.periodic
import topology.metric_space.emetric_paracompact
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the circle

This file contains basic results on Fourier series.

## Main definitions

* for `n : ℤ`, `fourier n` is the monomial `λ z, z ^ n`, bundled as a continuous map from `circle`
  to `ℂ`
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_circle`, via the embedding
  `continuous_map.to_Lp`
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`
  induced by taking Fourier series

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from
the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in `Lp ℂ p haar_circle`, i.e. that its `submodule.topological_closure` is
`⊤`.  This follows from the previous theorem using general theory on approximation of Lᵖ functions
by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal
set (in the L² space of the circle).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/

noncomputable theory
open_locale ennreal complex_conjugate classical real
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

/-! ### Monomials on the circle -/

section

section
variables {𝕜 : Type*} [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜]
variables {p : 𝕜} {β : Type*} [topological_space β]

lemma function.periodic.copy {α β : Type*} [add_group α] {f : α → β} {c d : α}
  (hf : function.periodic f c) (h : c = d) :
  function.periodic f d :=
by subst h; assumption

/-- An induction principle to deduce results for `add_circle` from those for `𝕜`, used with
`induction θ using add_circle.induction_on`. -/
@[elab_as_eliminator]
protected lemma add_circle.induction_on {P : add_circle p → Prop} (θ : add_circle p)
  (h : ∀ x : 𝕜, P x) : P θ :=
quotient.induction_on' θ h
end

def unit_add_circle.to_circle : C(unit_add_circle, circle) :=
{ to_fun := ((periodic_exp_map_circle.mul_const _).copy (mul_inv_cancel real.two_pi_pos.ne')).lift,
  continuous_to_fun :=
    continuous_coinduced_dom.mpr $ exp_map_circle.continuous.comp (continuous_mul_right _) }

lemma unit_add_circle.injective_to_circle : function.injective unit_add_circle.to_circle :=
sorry

@[simp] lemma unit_add_circle.coe_to_circle_coe (t : ℝ) :
  ↑(unit_add_circle.to_circle t) = complex.exp (t * (2 * π) * complex.I) :=
by simp [unit_add_circle.to_circle]

@[simps] def continuous_map.smul {Γ : Type*} {T : Type*} [topological_space T] [has_smul Γ T]
  [has_continuous_const_smul Γ T] (g : Γ) : C(T, T) :=
{ to_fun := has_smul.smul g,
  continuous_to_fun := continuous_const_smul g }

@[simps] def continuous_map.coe {X : Type*} [topological_space X] {α : Type*} [set_like α X] (s : α) :
  C(s, X) :=
{ to_fun := coe,
  continuous_to_fun := continuous_subtype_coe }


end

section functions

/-- The family of functions `λ z, exp (n * t * (2 * π) * I)`, considered as bundled continuous maps
from `unit_add_circle` to `ℂ`. -/
def fourier (n : ℤ) : C(unit_add_circle, ℂ) :=
(continuous_map.coe circle).comp $ unit_add_circle.to_circle.comp $ continuous_map.smul n

lemma fourier_apply (n : ℤ) (t : unit_add_circle) :
  fourier n t = unit_add_circle.to_circle (n • t) :=
rfl

@[simp] lemma fourier_apply_coe (n : ℤ) (t : ℝ) :
  fourier n t = complex.exp (n * t * (2 * π) * complex.I) :=
begin
  have : (↑(n • t) : unit_add_circle) = n • t := rfl,
  simp [fourier, ← this],
end

@[simp] lemma fourier_zero {t : unit_add_circle} : fourier 0 t = 1 :=
begin
  induction t using add_circle.induction_on,
  simp
end

@[simp] lemma fourier_neg {n : ℤ} {t : unit_add_circle} : fourier (-n) t = conj (fourier n t) :=
begin
  induction t using add_circle.induction_on,
  simp [← complex.exp_conj],
end

@[simp] lemma fourier_add {m n : ℤ} {t : unit_add_circle} :
  fourier (m + n) t = (fourier m t) * (fourier n t) :=
begin
  induction t using add_circle.induction_on,
  simp [complex.exp_add, mul_add, add_mul],
end

/-- The subalgebra of `C(unit_add_circle, ℂ)` generated by `exp (n * t * (2 * π) * I)` for `n ∈ ℤ`.
-/
def fourier_subalgebra : subalgebra ℂ C(unit_add_circle, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(unit_add_circle, ℂ)` generated by `exp (n * t * (2 * π) * I)` for `n ∈ ℤ`
is in fact the linear span of these functions. -/
lemma fourier_subalgebra_coe : fourier_subalgebra.to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, ext $ by simp⟩,
  rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨m + n, _⟩,
  ext1 z,
  exact fourier_add,
end

/-- The subalgebra of `C(unit_add_circle, ℂ)` generated by `exp (n * t * (2 * π) * I)` for `n ∈ ℤ`
separates points. -/
lemma fourier_subalgebra_separates_points : fourier_subalgebra.separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, _, rfl⟩, _⟩,
  { exact subset_adjoin ⟨1, rfl⟩ },
  { simpa [fourier_apply]
      using (subtype.coe_injective.comp unit_add_circle.injective_to_circle).ne hxy }
end

/-- The subalgebra of `C(unit_add_circle, ℂ)` generated by `exp (n * t * (2 * π) * I)` for `n ∈ ℤ`
is invariant under complex conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra (fourier_subalgebra.restrict_scalars ℝ) :=
begin
  rintros _ ⟨f, hf, rfl⟩,
  change _ ∈ fourier_subalgebra,
  change _ ∈ fourier_subalgebra at hf,
  apply adjoin_induction hf,
  { rintros _ ⟨n, rfl⟩,
    suffices : fourier (-n) ∈ fourier_subalgebra,
    { convert this,
      ext1,
      simp },
    exact subset_adjoin ⟨-n, rfl⟩ },
  { intros c,
    exact fourier_subalgebra.algebra_map_mem (conj c) },
  { intros f g hf hg,
    convert fourier_subalgebra.add_mem hf hg,
    exact alg_hom.map_add _ f g, },
  { intros f g hf hg,
    convert fourier_subalgebra.mul_mem hf hg,
    exact alg_hom.map_mul _ f g, }
end

/-- The subalgebra of `C(unit_add_circle, ℂ)` generated by `exp (n * t * (2 * π) * I)` for `n ∈ ℤ`
is dense. -/
lemma fourier_subalgebra_closure_eq_top : fourier_subalgebra.topological_closure = ⊤ :=
continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
  fourier_subalgebra
  fourier_subalgebra_separates_points
  fourier_subalgebra_conj_invariant

/-- The linear span of the functions `exp (n * t * (2 * π) * I)` is dense in
`C(unit_add_circle, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range fourier)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of functions `λ z, exp (n * t * (2 * π) * I)`, parametrized by `n : ℤ` and considered
as elements of the `Lp` space of functions on `unit_add_circle` taking values in `ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p volume :=
to_Lp p volume ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  ⇑(fourier_Lp p n) =ᵐ[volume] fourier n :=
coe_fn_to_Lp volume (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the functions `exp (n * t * (2 * π) * I)` is dense in
`Lp ℂ p volume`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (fourier_Lp p))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp volume ℂ).topological_closure_map_submodule
    span_fourier_closure_eq_top,
  rw [map_span, range_comp],
  simp
end

/-- For `n ≠ 0`, adding `(2 * n)⁻¹` negates the function `exp (n * t * (2 * π) * I)`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (z : unit_add_circle) :
  fourier n (↑((2 * n)⁻¹ : ℝ) + z) = - fourier n z :=
begin
  induction z using add_circle.induction_on,
  have hn : (n:ℂ) * (n⁻¹ * 2⁻¹) * (2 * π) = π,
  { have : (n:ℂ) ≠ 0 := by exact_mod_cast hn,
    field_simp,
    ring },
  simp [← quotient_add_group.coe_add, mul_add, add_mul, hn, complex.exp_add, complex.exp_pi_mul_I],
end

/-- The monomials `z ^ n` are an orthonormal set with respect to Haar measure on ℝ / ℤ. -/
lemma orthonormal_fourier : orthonormal ℂ (fourier_Lp 2) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp volume (fourier i) (fourier j),
  split_ifs,
  { simp [h, is_probability_measure.measure_univ, ← fourier_neg, ← fourier_add, -fourier_apply] },
  simp only [← fourier_add, ← fourier_neg],
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  exact integral_eq_zero_of_add_left_eq_neg (fourier_add_half_inv_index hij)
end

end functions

section fourier

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 volume`, which by
definition is an isometric isomorphism from `Lp ℂ 2 volume` to `ℓ²(ℤ, ℂ)`. -/
def fourier_series : hilbert_basis ℤ ℂ (Lp ℂ 2 volume) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge

/-- The elements of the Hilbert basis `fourier_series` for `Lp ℂ 2 volume` are the functions
`fourier_Lp 2`, the monomials `λ z, z ^ n` on ℝ / ℤ considered as elements of `L2`. -/
@[simp] lemma coe_fourier_series : ⇑fourier_series = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 volume` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over ℝ / ℤ of
`λ t, unit_add_circle.to_circle (- i • t)`. -/
lemma fourier_series_repr (f : Lp ℂ 2 volume) (i : ℤ) :
  fourier_series.repr f i = ∫ t : unit_add_circle, unit_add_circle.to_circle (-i • t) * f t :=
begin
  transitivity ∫ t : unit_add_circle, conj ((fourier_Lp 2 i : unit_add_circle → ℂ) t) * f t,
  { simp [fourier_series.repr_apply_apply f i, measure_theory.L2.inner_def] },
  apply integral_congr_ae,
  filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
  rw [ht, ← fourier_neg],
  simp [-fourier_neg, fourier_apply]
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L2` topology on ℝ / ℤ. -/
lemma has_sum_fourier_series (f : Lp ℂ 2 volume) :
  has_sum (λ i, fourier_series.repr f i • fourier_Lp 2 i) f :=
by simpa using hilbert_basis.has_sum_repr fourier_series f

/-- **Parseval's identity**: the sum of the squared norms of the Fourier coefficients equals the
`L2` norm of the function. -/
lemma tsum_sq_fourier_series_repr (f : Lp ℂ 2 volume) :
  ∑' i : ℤ, ∥fourier_series.repr f i∥ ^ 2 = ∫ t : unit_add_circle, ∥f t∥ ^ 2 :=
begin
  have H₁ : ∥fourier_series.repr f∥ ^ 2 = ∑' i, ∥fourier_series.repr f i∥ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_series.repr f),
    norm_num },
  have H₂ : ∥fourier_series.repr f∥ ^ 2 = ∥f∥ ^2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def unit_add_circle ℂ ℂ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂],
    exact H₃ },
  { exact L2.integrable_inner f f },
end

end fourier
