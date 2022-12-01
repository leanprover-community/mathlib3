/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import group_theory.divisible
import group_theory.order_of_element
import ring_theory.int.basic
import algebra.order.floor
import algebra.order.to_interval_mod
import topology.instances.real

/-!
# The additive circle

We define the additive circle `add_circle p` as the quotient `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`.

See also `circle` and `real.angle`.  For the normed group structure on `add_circle`, see
`add_circle.normed_add_comm_group` in a later file.

## Main definitions:

 * `add_circle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `unit_add_circle`: the special case `ℝ ⧸ ℤ`
 * `add_circle.equiv_add_circle`: the rescaling equivalence `add_circle p ≃+ add_circle q`
 * `add_circle.equiv_Ico`: the natural equivalence `add_circle p ≃ Ico 0 p`
 * `add_circle.add_order_of_div_of_gcd_eq_one`: rational points have finite order
 * `add_circle.exists_gcd_eq_one_of_is_of_fin_add_order`: finite-order points are rational

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `circle`

-/

noncomputable theory

open set add_subgroup topological_space

variables {𝕜 : Type*}

/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `circle` and `real.angle`. -/
@[derive [add_comm_group, topological_space, topological_add_group, inhabited, has_coe_t 𝕜],
  nolint unused_arguments]
def add_circle [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p : 𝕜) :=
𝕜 ⧸ zmultiples p

namespace add_circle

section linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p : 𝕜)

lemma coe_nsmul {n : ℕ} {x : 𝕜} : (↑(n • x) : add_circle p) = n • (x : add_circle p) := rfl

lemma coe_zsmul {n : ℤ} {x : 𝕜} : (↑(n • x) : add_circle p) = n • (x : add_circle p) := rfl

lemma coe_neg {x : 𝕜} : (↑(-x) : add_circle p) = -(x : add_circle p) := rfl

lemma coe_eq_zero_iff {x : 𝕜} : (x : add_circle p) = 0 ↔ ∃ (n : ℤ), n • p = x :=
by simp [add_subgroup.mem_zmultiples_iff]

lemma coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
  (x : add_circle p) = 0 ↔ ∃ (n : ℕ), n • p = x :=
begin
  rw coe_eq_zero_iff,
  split;
  rintros ⟨n, rfl⟩,
  { replace hx : 0 < n,
    { contrapose! hx,
      simpa only [←neg_nonneg, ←zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx) },
    exact ⟨n.to_nat, by rw [← coe_nat_zsmul, int.to_nat_of_nonneg hx.le]⟩, },
  { exact ⟨(n : ℤ), by simp⟩, },
end

@[continuity, nolint unused_arguments] protected lemma continuous_mk' :
  continuous (quotient_add_group.mk' (zmultiples p) : 𝕜 → add_circle p) :=
continuous_coinduced_rng

variables [hp : fact (0 < p)]
include hp

variables [archimedean 𝕜]

/-- The natural equivalence between `add_circle p` and the half-open interval `[0, p)`. -/
def equiv_Ico : add_circle p ≃ Ico 0 p :=
(quotient_add_group.equiv_Ico_mod 0 hp.out).trans $ equiv.set.of_eq $ by rw zero_add

@[continuity] lemma continuous_equiv_Ico_symm : continuous (equiv_Ico p).symm :=
continuous_quotient_mk.comp continuous_subtype_coe

/-- The image of the closed-open interval `[0, p)` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp] lemma coe_image_Ico_eq : (coe : 𝕜 → add_circle p) '' Ico 0 p = univ :=
by { rw image_eq_range, exact (equiv_Ico p).symm.range_eq_univ }

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp] lemma coe_image_Icc_eq : (coe : 𝕜 → add_circle p) '' Icc 0 p = univ :=
eq_top_mono (image_subset _ Ico_subset_Icc_self) $ coe_image_Ico_eq _

end linear_ordered_add_comm_group

section linear_ordered_field
variables [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p q : 𝕜)

/-- An auxiliary definition used only for constructing `add_circle.equiv_add_circle`. -/
private def equiv_add_circle_aux (hp : p ≠ 0) : add_circle p →+ add_circle q :=
quotient_add_group.lift _
  ((quotient_add_group.mk' (zmultiples q)).comp $ add_monoid_hom.mul_right (p⁻¹ * q))
  (λ x h, by obtain ⟨z, rfl⟩ := mem_zmultiples_iff.1 h; simp [hp, mul_assoc (z : 𝕜), ← mul_assoc p])

/-- The rescaling equivalence between additive circles with different periods. -/
def equiv_add_circle (hp : p ≠ 0) (hq : q ≠ 0) : add_circle p ≃+ add_circle q :=
{ to_fun := equiv_add_circle_aux p q hp,
  inv_fun := equiv_add_circle_aux q p hq,
  left_inv := by { rintros ⟨x⟩, show quotient_add_group.mk _ = _, congr, field_simp [hp, hq], },
  right_inv := by { rintros ⟨x⟩, show quotient_add_group.mk _ = _, congr, field_simp [hp, hq], },
  .. equiv_add_circle_aux p q hp }

@[simp] lemma equiv_add_circle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
  equiv_add_circle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
rfl

@[simp] lemma equiv_add_circle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
  (equiv_add_circle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
rfl

variables [hp : fact (0 < p)]
include hp

section floor_ring

variables [floor_ring 𝕜]

@[simp] lemma coe_equiv_Ico_mk_apply (x : 𝕜) :
  (equiv_Ico p $ quotient_add_group.mk x : 𝕜) = int.fract (x / p) * p :=
to_Ico_mod_eq_fract_mul _ x

instance : divisible_by (add_circle p) ℤ :=
{ div := λ x n, (↑(((n : 𝕜)⁻¹) * (equiv_Ico p x : 𝕜)) : add_circle p),
  div_zero := λ x,
    by simp only [algebra_map.coe_zero, quotient_add_group.coe_zero, inv_zero, zero_mul],
  div_cancel := λ n x hn,
  begin
    replace hn : (n : 𝕜) ≠ 0, { norm_cast, assumption, },
    change n • quotient_add_group.mk' _ ((n : 𝕜)⁻¹ * ↑(equiv_Ico p x)) = x,
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul],
    exact (equiv_Ico p).symm_apply_apply x,
  end, }

end floor_ring

section finite_order_points

variables {p}

lemma add_order_of_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : gcd m n = 1) :
  add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  rcases m.eq_zero_or_pos with rfl | hm, { rw [gcd_zero_left, normalize_eq] at h, simp [h], },
  set x : add_circle p := ↑(↑m / ↑n * p),
  have hn₀ : (n : 𝕜) ≠ 0, { norm_cast, exact ne_of_gt hn, },
  have hnx : n • x = 0,
  { rw [← coe_nsmul, nsmul_eq_mul, ← mul_assoc, mul_div, mul_div_cancel_left _ hn₀,
      ← nsmul_eq_mul, quotient_add_group.eq_zero_iff],
    exact nsmul_mem_zmultiples p m, },
  apply nat.dvd_antisymm (add_order_of_dvd_of_nsmul_eq_zero hnx),
  suffices : ∃ (z : ℕ), z * n = (add_order_of x) * m,
  { obtain ⟨z, hz⟩ := this,
    simpa only [h, mul_one, gcd_comm n] using dvd_mul_gcd_of_dvd_mul (dvd.intro_left z hz), },
  replace hp := hp.out,
  have : 0 < add_order_of x • (↑m / ↑n * p) := smul_pos
    (add_order_of_pos' $ (is_of_fin_add_order_iff_nsmul_eq_zero _).2 ⟨n, hn, hnx⟩) (by positivity),
  obtain ⟨z, hz⟩ := (coe_eq_zero_of_pos_iff p hp this).mp (add_order_of_nsmul_eq_zero x),
  rw [← smul_mul_assoc, nsmul_eq_mul, nsmul_eq_mul, mul_left_inj' hp.ne.symm, mul_div,
    eq_div_iff hn₀] at hz,
  norm_cast at hz,
  exact ⟨z, hz⟩,
end

lemma add_order_of_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : gcd m.nat_abs n = 1) :
  add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  induction m,
  { simp only [int.of_nat_eq_coe, int.cast_coe_nat, int.nat_abs_of_nat] at h ⊢,
    exact add_order_of_div_of_gcd_eq_one hn h, },
  { simp only [int.cast_neg_succ_of_nat, neg_div, neg_mul, coe_neg, order_of_neg],
    exact add_order_of_div_of_gcd_eq_one hn h, },
end

lemma add_order_of_coe_rat {q : ℚ} : add_order_of (↑(↑q * p) : add_circle p) = q.denom :=
begin
  have : (↑(q.denom : ℤ) : 𝕜) ≠ 0, { norm_cast, exact q.pos.ne.symm, },
  rw [← @rat.num_denom q, rat.cast_mk_of_ne_zero _ _ this, int.cast_coe_nat, rat.num_denom,
    add_order_of_div_of_gcd_eq_one' q.pos q.cop],
  apply_instance,
end

variables (p)

lemma gcd_mul_add_order_of_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
  gcd m n * add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  let n' := n / gcd m n,
  let m' := m / gcd m n,
  have h₀ : 0 < gcd m n,
  { rw zero_lt_iff at hn ⊢, contrapose! hn, exact ((gcd_eq_zero_iff m n).mp hn).2, },
  have hk' : 0 < n' := nat.div_pos (nat.le_of_dvd hn $ gcd_dvd_right m n) h₀,
  have hgcd : gcd m' n' = 1 := nat.coprime_div_gcd_div_gcd h₀,
  simp only [mul_left_inj' hp.out.ne.symm,
    ← nat.cast_div_div_div_cancel_right (gcd_dvd_right m n) (gcd_dvd_left m n),
    add_order_of_div_of_gcd_eq_one hk' hgcd, mul_comm _ n', nat.div_mul_cancel (gcd_dvd_right m n)],
end

variables {p} [floor_ring 𝕜]

lemma exists_gcd_eq_one_of_is_of_fin_add_order {u : add_circle p} (h : is_of_fin_add_order u) :
  ∃ m, gcd m (add_order_of u) = 1 ∧
       m < (add_order_of u) ∧
       ↑(((m : 𝕜) / add_order_of u) * p) = u :=
begin
  rcases eq_or_ne u 0 with rfl | hu, { exact ⟨0, by simp⟩, },
  set n := add_order_of u,
  change ∃ m, gcd m n = 1 ∧ m < n ∧ ↑((↑m / ↑n) * p) = u,
  have hn : 0 < n := add_order_of_pos' h,
  have hn₀ : (n : 𝕜) ≠ 0, { norm_cast, exact ne_of_gt hn, },
  let x := (equiv_Ico p u : 𝕜),
  have hxu : (x : add_circle p) = u := (equiv_Ico p).symm_apply_apply u,
  have hx₀ : 0 < (add_order_of (x : add_circle p)), { rw ← hxu at h, exact add_order_of_pos' h, },
  have hx₁ : 0 < x,
  { refine lt_of_le_of_ne (equiv_Ico p u).2.1 _,
    contrapose! hu,
    rw [← hxu, ← hu, quotient_add_group.coe_zero], },
  obtain ⟨m, hm : m • p = add_order_of ↑x • x⟩ := (coe_eq_zero_of_pos_iff p hp.out
    (by positivity)).mp (add_order_of_nsmul_eq_zero (x : add_circle p)),
  replace hm : ↑m * p = ↑n * x, { simpa only [hxu, nsmul_eq_mul] using hm, },
  have hux : ↑(↑m / ↑n * p) = u,
  { rw [← hxu, ← mul_div_right_comm, hm, mul_comm _ x, mul_div_cancel x hn₀], },
  refine ⟨m, (_ : gcd m n = 1), (_ : m < n), hux⟩,
  { have := gcd_mul_add_order_of_div_eq p m hn,
    rwa [hux, nat.mul_left_eq_self_iff hn] at this, },
  { have : n • x < n • p := smul_lt_smul_of_pos (equiv_Ico p u).2.2 hn,
    rwa [nsmul_eq_mul, nsmul_eq_mul, ← hm, mul_lt_mul_right hp.out, nat.cast_lt] at this, },
end

end finite_order_points

end linear_ordered_field

variables (p : ℝ)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compact_space [fact (0 < p)] : compact_space $ add_circle p :=
begin
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p],
  exact is_compact_Icc.image (add_circle.continuous_mk' p),
end

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
instance : properly_discontinuous_vadd (zmultiples p).opposite ℝ :=
(zmultiples p).properly_discontinuous_vadd_opposite_of_tendsto_cofinite
  (add_subgroup.tendsto_zmultiples_subtype_cofinite p)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is Hausdorff. -/
instance : t2_space (add_circle p) := t2_space_of_properly_discontinuous_vadd_of_t2_space

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is normal. -/
instance [fact (0 < p)] : normal_space (add_circle p) := normal_of_compact_t2

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is second-countable. -/
instance : second_countable_topology (add_circle p) := quotient_add_group.second_countable_topology

end add_circle

private lemma fact_zero_lt_one : fact ((0:ℝ) < 1) := ⟨zero_lt_one⟩
local attribute [instance] fact_zero_lt_one

/-- The unit circle `ℝ ⧸ ℤ`. -/
@[derive [compact_space, normal_space, second_countable_topology]]
abbreviation unit_add_circle := add_circle (1 : ℝ)
