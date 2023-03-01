/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.complex.module
import data.complex.exponential
import data.is_R_or_C.basic
import topology.algebra.infinite_sum.module
import topology.instances.real_vector_space

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `re_clm`
* `im_clm`
* `of_real_clm`
* `conj_cle`

They are bundled versions of the real part, the imaginary part, the embedding of `ℝ` in `ℂ`, and
the complex conjugate as continuous `ℝ`-linear maps. The last two are also bundled as linear
isometries in `of_real_li` and `conj_lie`.

We also register the fact that `ℂ` is an `is_R_or_C` field.
-/

assert_not_exists absorbs

noncomputable theory

namespace complex

open_locale complex_conjugate topology

instance : has_norm ℂ := ⟨abs⟩

@[simp] lemma norm_eq_abs (z : ℂ) : ‖z‖ = abs z := rfl

lemma norm_exp_of_real_mul_I (t : ℝ) : ‖exp (t * I)‖ = 1 :=
by simp only [norm_eq_abs, abs_exp_of_real_mul_I]

instance : normed_add_comm_group ℂ :=
add_group_norm.to_normed_add_comm_group
{ map_zero' := map_zero abs,
  neg' := abs.map_neg,
  eq_zero_of_map_eq_zero' := λ _, abs.eq_zero.1,
  ..abs }

instance : normed_field ℂ :=
{ norm := abs,
  dist_eq := λ _ _, rfl,
  norm_mul' := map_mul abs,
  .. complex.field, .. complex.normed_add_comm_group }

instance : densely_normed_field ℂ :=
{ lt_norm_lt := λ r₁ r₂ h₀ hr, let ⟨x, h⟩ := normed_field.exists_lt_norm_lt ℝ h₀ hr in
    have this : ‖(‖x‖ : ℂ)‖ = ‖(‖x‖)‖, by simp only [norm_eq_abs, abs_of_real, real.norm_eq_abs],
    ⟨‖x‖, by rwa [this, norm_norm]⟩ }

instance {R : Type*} [normed_field R] [normed_algebra R ℝ] : normed_algebra R ℂ :=
{ norm_smul_le := λ r x, begin
    rw [norm_eq_abs, norm_eq_abs, ←algebra_map_smul ℝ r x, algebra.smul_def, map_mul,
        ←norm_algebra_map' ℝ r, coe_algebra_map, abs_of_real],
    refl,
  end,
  to_algebra := complex.algebra }

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E]

/-- The module structure from `module.complex_to_real` is a normed space. -/
@[priority 900] -- see Note [lower instance priority]
instance _root_.normed_space.complex_to_real : normed_space ℝ E :=
normed_space.restrict_scalars ℝ ℂ E

lemma dist_eq (z w : ℂ) : dist z w = abs (z - w) := rfl

lemma dist_eq_re_im (z w : ℂ) : dist z w = real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) :=
by { rw [sq, sq], refl }

@[simp] lemma dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
  dist (mk x₁ y₁) (mk x₂ y₂) = real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
dist_eq_re_im _ _

lemma dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im :=
by rw [dist_eq_re_im, h, sub_self, zero_pow two_pos, zero_add, real.sqrt_sq_eq_abs, real.dist_eq]

lemma nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
nnreal.eq $ dist_of_re_eq h

lemma edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im :=
by rw [edist_nndist, edist_nndist, nndist_of_re_eq h]

lemma dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re :=
by rw [dist_eq_re_im, h, sub_self, zero_pow two_pos, add_zero, real.sqrt_sq_eq_abs, real.dist_eq]

lemma nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
nnreal.eq $ dist_of_im_eq h

lemma edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re :=
by rw [edist_nndist, edist_nndist, nndist_of_im_eq h]

lemma dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| :=
by rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, real.dist_eq, sub_neg_eq_add, ← two_mul,
  _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]

lemma nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * real.nnabs z.im :=
nnreal.eq $ by rw [← dist_nndist, nnreal.coe_mul, nnreal.coe_two, real.coe_nnabs, dist_conj_self]

lemma dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| :=
by rw [dist_comm, dist_conj_self]

lemma nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * real.nnabs z.im :=
by rw [nndist_comm, nndist_conj_self]

@[simp] lemma comap_abs_nhds_zero : filter.comap abs (𝓝 0) = 𝓝 0 := comap_norm_nhds_zero

lemma norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := abs_of_real _

@[simp] lemma norm_rat (r : ℚ) : ‖(r : ℂ)‖ = |(r : ℝ)| :=
by { rw ← of_real_rat_cast, exact norm_real _ }

@[simp] lemma norm_nat (n : ℕ) : ‖(n : ℂ)‖ = n := abs_of_nat _

@[simp] lemma norm_int {n : ℤ} : ‖(n : ℂ)‖ = |n| :=
by simp [← rat.cast_coe_int] {single_pass := tt}

lemma norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n :=
by simp [hn]

@[continuity] lemma continuous_abs : continuous abs := continuous_norm

@[continuity] lemma continuous_norm_sq : continuous norm_sq :=
by simpa [← norm_sq_eq_abs] using continuous_abs.pow 2

@[simp, norm_cast] lemma nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ :=
subtype.ext $ norm_real r

@[simp, norm_cast] lemma nnnorm_nat (n : ℕ) : ‖(n : ℂ)‖₊ = n :=
subtype.ext $ by simp

@[simp, norm_cast] lemma nnnorm_int (n : ℤ) : ‖(n : ℂ)‖₊ = ‖n‖₊ :=
subtype.ext $ by simp only [coe_nnnorm, norm_int, int.norm_eq_abs]

lemma nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ‖ζ‖₊ = 1 :=
begin
  refine (@pow_left_inj nnreal _ _ _ _ zero_le' zero_le' hn.bot_lt).mp _,
  rw [←nnnorm_pow, h, nnnorm_one, one_pow],
end

lemma norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) :
  ‖ζ‖ = 1 :=
congr_arg coe (nnnorm_eq_one_of_pow_eq_one h hn)

lemma equiv_real_prod_apply_le (z : ℂ) : ‖equiv_real_prod z‖ ≤ abs z :=
by simp [prod.norm_def, abs_re_le_abs, abs_im_le_abs]

lemma equiv_real_prod_apply_le' (z : ℂ) : ‖equiv_real_prod z‖ ≤ 1 * abs z :=
by simpa using equiv_real_prod_apply_le z

lemma lipschitz_equiv_real_prod : lipschitz_with 1 equiv_real_prod :=
by simpa using
  add_monoid_hom_class.lipschitz_of_bound equiv_real_prod_lm 1 equiv_real_prod_apply_le'

lemma antilipschitz_equiv_real_prod : antilipschitz_with (nnreal.sqrt 2) equiv_real_prod :=
by simpa using
  add_monoid_hom_class.antilipschitz_of_bound equiv_real_prod_lm abs_le_sqrt_two_mul_max

lemma uniform_embedding_equiv_real_prod : uniform_embedding equiv_real_prod :=
antilipschitz_equiv_real_prod.uniform_embedding lipschitz_equiv_real_prod.uniform_continuous

instance : complete_space ℂ :=
(complete_space_congr uniform_embedding_equiv_real_prod).mpr infer_instance

/-- The natural `continuous_linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps apply symm_apply_re symm_apply_im { simp_rhs := tt }]
def equiv_real_prod_clm : ℂ ≃L[ℝ] ℝ × ℝ :=
equiv_real_prod_lm.to_continuous_linear_equiv_of_bounds 1 (real.sqrt 2)
equiv_real_prod_apply_le'
(λ p, abs_le_sqrt_two_mul_max (equiv_real_prod.symm p))

instance : proper_space ℂ :=
(id lipschitz_equiv_real_prod : lipschitz_with 1 equiv_real_prod_clm.to_homeomorph).proper_space

/-- The `abs` function on `ℂ` is proper. -/
lemma tendsto_abs_cocompact_at_top : filter.tendsto abs (filter.cocompact ℂ) filter.at_top :=
tendsto_norm_cocompact_at_top

/-- The `norm_sq` function on `ℂ` is proper. -/
lemma tendsto_norm_sq_cocompact_at_top :
  filter.tendsto norm_sq (filter.cocompact ℂ) filter.at_top :=
by simpa [mul_self_abs] using
  tendsto_abs_cocompact_at_top.at_top_mul_at_top tendsto_abs_cocompact_at_top

open continuous_linear_map

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_clm : ℂ →L[ℝ] ℝ := re_lm.mk_continuous 1 (λ x, by simp [abs_re_le_abs])

@[continuity] lemma continuous_re : continuous re := re_clm.continuous

@[simp] lemma re_clm_coe : (coe (re_clm) : ℂ →ₗ[ℝ] ℝ) = re_lm := rfl

@[simp] lemma re_clm_apply (z : ℂ) : (re_clm : ℂ → ℝ) z = z.re := rfl

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def im_clm : ℂ →L[ℝ] ℝ := im_lm.mk_continuous 1 (λ x, by simp [abs_im_le_abs])

@[continuity] lemma continuous_im : continuous im := im_clm.continuous

@[simp] lemma im_clm_coe : (coe (im_clm) : ℂ →ₗ[ℝ] ℝ) = im_lm := rfl

@[simp] lemma im_clm_apply (z : ℂ) : (im_clm : ℂ → ℝ) z = z.im := rfl

lemma restrict_scalars_one_smul_right' (x : E) :
  continuous_linear_map.restrict_scalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] E) =
    re_clm.smul_right x + I • im_clm.smul_right x :=
by { ext ⟨a, b⟩, simp [mk_eq_add_mul_I, add_smul, mul_smul, smul_comm I] }

lemma restrict_scalars_one_smul_right (x : ℂ) :
  continuous_linear_map.restrict_scalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] ℂ) = x • 1 :=
by { ext1 z, dsimp, apply mul_comm }

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conj_lie : ℂ ≃ₗᵢ[ℝ] ℂ := ⟨conj_ae.to_linear_equiv, abs_conj⟩

@[simp] lemma conj_lie_apply (z : ℂ) : conj_lie z = conj z := rfl

@[simp] lemma conj_lie_symm : conj_lie.symm = conj_lie := rfl

lemma isometry_conj : isometry (conj : ℂ → ℂ) := conj_lie.isometry

@[simp] lemma dist_conj_conj (z w : ℂ) : dist (conj z) (conj w) = dist z w :=
isometry_conj.dist_eq z w

@[simp] lemma nndist_conj_conj (z w : ℂ) : nndist (conj z) (conj w) = nndist z w :=
isometry_conj.nndist_eq z w

lemma dist_conj_comm (z w : ℂ) : dist (conj z) w = dist z (conj w) :=
by rw [← dist_conj_conj, conj_conj]

lemma nndist_conj_comm (z w : ℂ) : nndist (conj z) w = nndist z (conj w) :=
subtype.ext $ dist_conj_comm _ _

instance : has_continuous_star ℂ := ⟨conj_lie.continuous⟩

@[continuity] lemma continuous_conj : continuous (conj : ℂ → ℂ) := continuous_star

/-- The only continuous ring homomorphisms from `ℂ` to `ℂ` are the identity and the complex
conjugation. -/
lemma ring_hom_eq_id_or_conj_of_continuous {f : ℂ →+* ℂ} (hf : continuous f) :
  f = ring_hom.id ℂ ∨ f = conj :=
begin
  refine (real_alg_hom_eq_id_or_conj $ alg_hom.mk' f $ map_real_smul f hf).imp (λ h, _) (λ h, _),
  all_goals { convert congr_arg alg_hom.to_ring_hom h, ext1, refl, },
end

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`. -/
def conj_cle : ℂ ≃L[ℝ] ℂ := conj_lie

@[simp] lemma conj_cle_coe : conj_cle.to_linear_equiv = conj_ae.to_linear_equiv := rfl

@[simp] lemma conj_cle_apply (z : ℂ) : conj_cle z = conj z := rfl

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_li : ℝ →ₗᵢ[ℝ] ℂ := ⟨of_real_am.to_linear_map, norm_real⟩

lemma isometry_of_real : isometry (coe : ℝ → ℂ) := of_real_li.isometry

@[continuity] lemma continuous_of_real : continuous (coe : ℝ → ℂ) := of_real_li.continuous

/-- The only continuous ring homomorphism from `ℝ` to `ℂ` is the identity. -/
lemma ring_hom_eq_of_real_of_continuous {f : ℝ →+* ℂ} (h : continuous f) :
  f = complex.of_real :=
begin
  convert congr_arg alg_hom.to_ring_hom
    (subsingleton.elim (alg_hom.mk' f $ map_real_smul f h) $ algebra.of_id ℝ ℂ),
  ext1, refl,
end

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_clm : ℝ →L[ℝ] ℂ := of_real_li.to_continuous_linear_map

@[simp] lemma of_real_clm_coe : (of_real_clm : ℝ →ₗ[ℝ] ℂ) = of_real_am.to_linear_map := rfl

@[simp] lemma of_real_clm_apply (x : ℝ) : of_real_clm x = x := rfl

noncomputable instance : is_R_or_C ℂ :=
{ re := ⟨complex.re, complex.zero_re, complex.add_re⟩,
  im := ⟨complex.im, complex.zero_im, complex.add_im⟩,
  I := complex.I,
  I_re_ax := by simp only [add_monoid_hom.coe_mk, complex.I_re],
  I_mul_I_ax := by simp only [complex.I_mul_I, eq_self_iff_true, or_true],
  re_add_im_ax := λ z, by simp only [add_monoid_hom.coe_mk, complex.re_add_im,
                                     complex.coe_algebra_map, complex.of_real_eq_coe],
  of_real_re_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_re,
                                      complex.coe_algebra_map, complex.of_real_eq_coe],
  of_real_im_ax := λ r, by simp only [add_monoid_hom.coe_mk, complex.of_real_im,
                                      complex.coe_algebra_map, complex.of_real_eq_coe],
  mul_re_ax := λ z w, by simp only [complex.mul_re, add_monoid_hom.coe_mk],
  mul_im_ax := λ z w, by simp only [add_monoid_hom.coe_mk, complex.mul_im],
  conj_re_ax := λ z, rfl,
  conj_im_ax := λ z, rfl,
  conj_I_ax := by simp only [complex.conj_I, ring_hom.coe_mk],
  norm_sq_eq_def_ax := λ z, by simp only [←complex.norm_sq_eq_abs, ←complex.norm_sq_apply,
    add_monoid_hom.coe_mk, complex.norm_eq_abs],
  mul_im_I_ax := λ z, by simp only [mul_one, add_monoid_hom.coe_mk, complex.I_im],
  inv_def_ax := λ z, by simp only [complex.inv_def, complex.norm_sq_eq_abs, complex.coe_algebra_map,
    complex.of_real_eq_coe, complex.norm_eq_abs],
  div_I_ax := complex.div_I }

lemma _root_.is_R_or_C.re_eq_complex_re : ⇑(is_R_or_C.re : ℂ →+ ℝ) = complex.re := rfl
lemma _root_.is_R_or_C.im_eq_complex_im : ⇑(is_R_or_C.im : ℂ →+ ℝ) = complex.im := rfl

section complex_order
open_locale complex_order

lemma eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑‖z‖ :=
by rw [eq_re_of_real_le hz, is_R_or_C.norm_of_real, real.norm_of_nonneg (complex.le_def.2 hz).1]

end complex_order

end complex

namespace is_R_or_C

open_locale complex_conjugate

local notation `reC` := @is_R_or_C.re ℂ _
local notation `imC` := @is_R_or_C.im ℂ _
local notation `IC` := @is_R_or_C.I ℂ _
local notation `absC` := @is_R_or_C.abs ℂ _
local notation `norm_sqC` := @is_R_or_C.norm_sq ℂ _

@[simp] lemma re_to_complex {x : ℂ} : reC x = x.re := rfl
@[simp] lemma im_to_complex {x : ℂ} : imC x = x.im := rfl
@[simp] lemma I_to_complex : IC = complex.I := rfl
@[simp] lemma norm_sq_to_complex {x : ℂ} : norm_sqC x = complex.norm_sq x :=
by simp [is_R_or_C.norm_sq, complex.norm_sq]
@[simp] lemma abs_to_complex {x : ℂ} : absC x = complex.abs x :=
by simp [is_R_or_C.abs, complex.abs]

section tsum
variables {α : Type*} (𝕜 : Type*) [is_R_or_C 𝕜]

@[simp] lemma has_sum_conj {f : α → 𝕜} {x : 𝕜} :
  has_sum (λ x, conj (f x)) x ↔ has_sum f (conj x) :=
conj_cle.has_sum

lemma has_sum_conj' {f : α → 𝕜} {x : 𝕜} : has_sum (λ x, conj (f x)) (conj x) ↔ has_sum f x :=
conj_cle.has_sum'

@[simp] lemma summable_conj {f : α → 𝕜} : summable (λ x, conj (f x)) ↔ summable f :=
summable_star_iff

variables {𝕜}

lemma conj_tsum (f : α → 𝕜) : conj (∑' a, f a) = ∑' a, conj (f a) :=
tsum_star

variables (𝕜)

@[simp, norm_cast] lemma has_sum_of_real {f : α → ℝ} {x : ℝ} :
  has_sum (λ x, (f x : 𝕜)) x ↔ has_sum f x :=
⟨λ h, by simpa only [is_R_or_C.re_clm_apply, is_R_or_C.of_real_re] using re_clm.has_sum h,
  of_real_clm.has_sum⟩

@[simp, norm_cast] lemma summable_of_real {f : α → ℝ} : summable (λ x, (f x : 𝕜)) ↔ summable f :=
⟨λ h, by simpa only [is_R_or_C.re_clm_apply, is_R_or_C.of_real_re] using re_clm.summable h,
  of_real_clm.summable⟩

@[norm_cast] lemma of_real_tsum (f : α → ℝ) : (↑(∑' a, f a) : 𝕜) = ∑' a, f a :=
begin
  by_cases h : summable f,
  { exact continuous_linear_map.map_tsum of_real_clm h },
  { rw [tsum_eq_zero_of_not_summable h,
    tsum_eq_zero_of_not_summable ((summable_of_real _).not.mpr h), of_real_zero] }
end

lemma has_sum_re {f : α → 𝕜} {x : 𝕜} (h : has_sum f x) : has_sum (λ x, re (f x)) (re x) :=
re_clm.has_sum h

lemma has_sum_im {f : α → 𝕜} {x : 𝕜} (h : has_sum f x) : has_sum (λ x, im (f x)) (im x) :=
im_clm.has_sum h

lemma re_tsum {f : α → 𝕜} (h : summable f) : re (∑' a, f a) = ∑' a, re (f a) :=
re_clm.map_tsum h

lemma im_tsum {f : α → 𝕜} (h : summable f) : im (∑' a, f a) = ∑' a, im (f a) :=
im_clm.map_tsum h

variables {𝕜}

lemma has_sum_iff (f : α → 𝕜) (c : 𝕜) :
  has_sum f c ↔ has_sum (λ x, re (f x)) (re c) ∧ has_sum (λ x, im (f x)) (im c) :=
begin
  refine ⟨λ h, ⟨has_sum_re _ h, has_sum_im _ h⟩, _⟩,
  rintro ⟨h₁, h₂⟩,
  rw ←is_R_or_C.re_add_im c,
  convert ((has_sum_of_real 𝕜).mpr h₁).add (((has_sum_of_real 𝕜).mpr h₂).mul_right I),
  simp_rw is_R_or_C.re_add_im,
end

end tsum

end is_R_or_C

namespace complex
/-!
We have to repeat the lemmas about `is_R_or_C.re` and `is_R_or_C.im` as they are not syntactic
matches for `complex.re` and `complex.im`.

We do not have this problem with `of_real` and `conj`, although we repeat them anyway for
discoverability and to avoid the need to unify `𝕜`.
-/
section tsum
variables {α : Type*}

open_locale complex_conjugate

@[simp] lemma has_sum_conj {f : α → ℂ} {x : ℂ} :
  has_sum (λ x, conj (f x)) x ↔ has_sum f (conj x) :=
is_R_or_C.has_sum_conj _

lemma has_sum_conj' {f : α → ℂ} {x : ℂ} : has_sum (λ x, conj (f x)) (conj x) ↔ has_sum f x :=
is_R_or_C.has_sum_conj' _

@[simp] lemma summable_conj {f : α → ℂ} : summable (λ x, conj (f x)) ↔ summable f :=
is_R_or_C.summable_conj _

lemma conj_tsum (f : α → ℂ) : conj (∑' a, f a) = ∑' a, conj (f a) :=
is_R_or_C.conj_tsum _

@[simp, norm_cast] lemma has_sum_of_real {f : α → ℝ} {x : ℝ} :
  has_sum (λ x, (f x : ℂ)) x ↔ has_sum f x :=
is_R_or_C.has_sum_of_real _

@[simp, norm_cast] lemma summable_of_real {f : α → ℝ} : summable (λ x, (f x : ℂ)) ↔ summable f :=
is_R_or_C.summable_of_real _

@[norm_cast] lemma of_real_tsum (f : α → ℝ) : (↑(∑' a, f a) : ℂ) = ∑' a, f a :=
is_R_or_C.of_real_tsum _ _

lemma has_sum_re {f : α → ℂ} {x : ℂ} (h : has_sum f x) : has_sum (λ x, (f x).re) x.re :=
is_R_or_C.has_sum_re _ h

lemma has_sum_im {f : α → ℂ} {x : ℂ} (h : has_sum f x) : has_sum (λ x, (f x).im) x.im :=
is_R_or_C.has_sum_im _ h

lemma re_tsum {f : α → ℂ} (h : summable f) : (∑' a, f a).re = ∑' a, (f a).re :=
is_R_or_C.re_tsum _ h

lemma im_tsum {f : α → ℂ} (h : summable f) : (∑' a, f a).im = ∑' a, (f a).im :=
is_R_or_C.im_tsum _ h

lemma has_sum_iff (f : α → ℂ) (c : ℂ) :
  has_sum f c ↔ has_sum (λ x, (f x).re) c.re ∧ has_sum (λ x, (f x).im) c.im :=
is_R_or_C.has_sum_iff _ _

end tsum

end complex
