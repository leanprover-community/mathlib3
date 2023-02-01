/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.nat.totient
import algebra.ring.add_aut
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

## Main definitions and results:

 * `add_circle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `unit_add_circle`: the special case `ℝ ⧸ ℤ`
 * `add_circle.equiv_add_circle`: the rescaling equivalence `add_circle p ≃+ add_circle q`
 * `add_circle.equiv_Ico`: the natural equivalence `add_circle p ≃ Ico a (a + p)`
 * `add_circle.add_order_of_div_of_gcd_eq_one`: rational points have finite order
 * `add_circle.exists_gcd_eq_one_of_is_of_fin_add_order`: finite-order points are rational
 * `add_circle.homeo_Icc_quot`: the natural topological equivalence between `add_circle p` and
   `Icc a (a + p)` with its endpoints identified.
 * `add_circle.lift_Ico_continuous`: if `f : ℝ → B` is continuous, and `f a = f (a + p)` for
   some `a`, then there is a continuous function `add_circle p → B` which agrees with `f` on
   `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `circle`

-/

noncomputable theory

open set function add_subgroup topological_space
open_locale topology

variables {𝕜 B : Type*}

section continuity

variables [linear_ordered_add_comm_group 𝕜] [archimedean 𝕜]
  [topological_space 𝕜] [order_topology 𝕜] (a : 𝕜) {p : 𝕜} (hp : 0 < p) (x : 𝕜)

lemma continuous_right_to_Ico_mod : continuous_within_at (to_Ico_mod a hp) (Ici x) x :=
begin
  intros s h,
  rw [filter.mem_map, mem_nhds_within_iff_exists_mem_nhds_inter],
  haveI : nontrivial 𝕜 := ⟨⟨0, p, hp.ne⟩⟩,
  simp_rw mem_nhds_iff_exists_Ioo_subset at h ⊢,
  obtain ⟨l, u, hxI, hIs⟩ := h,
  let d := to_Ico_div a hp x • p,
  have hd := to_Ico_mod_mem_Ico a hp x,
  simp_rw [subset_def, mem_inter_iff],
  refine ⟨_, ⟨l + d, min (a + p) u + d, _, λ x, id⟩, λ y, _⟩;
    simp_rw [← sub_mem_Ioo_iff_left, mem_Ioo, lt_min_iff],
  { exact ⟨hxI.1, hd.2, hxI.2⟩ },
  { rintro ⟨h, h'⟩, apply hIs,
    rw [← to_Ico_mod_sub_zsmul, (to_Ico_mod_eq_self _).2],
    exacts [⟨h.1, h.2.2⟩, ⟨hd.1.trans (sub_le_sub_right h' _), h.2.1⟩] },
end

lemma continuous_left_to_Ioc_mod : continuous_within_at (to_Ioc_mod a hp) (Iic x) x :=
begin
  rw (funext (λ y, eq.trans (by rw neg_neg) $ to_Ioc_mod_neg _ _ _) :
    to_Ioc_mod a hp = (λ x, p - x) ∘ to_Ico_mod (-a) hp ∘ has_neg.neg),
  exact ((continuous_sub_left _).continuous_at.comp_continuous_within_at $
    (continuous_right_to_Ico_mod _ _ _).comp continuous_neg.continuous_within_at $ λ y, neg_le_neg),
end

variables {x} (hx : (x : 𝕜 ⧸ zmultiples p) ≠ a)

lemma to_Ico_mod_eventually_eq_to_Ioc_mod : to_Ico_mod a hp =ᶠ[𝓝 x] to_Ioc_mod a hp :=
is_open.mem_nhds (by {rw Ico_eq_locus_Ioc_eq_Union_Ioo, exact is_open_Union (λ i, is_open_Ioo)}) $
  (mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod hp).1 ((mem_Ioo_mod_iff_ne_mod_zmultiples hp).2 hx)

lemma continuous_at_to_Ico_mod : continuous_at (to_Ico_mod a hp) x :=
let h := to_Ico_mod_eventually_eq_to_Ioc_mod a hp hx in continuous_at_iff_continuous_left_right.2 $
  ⟨(continuous_left_to_Ioc_mod a hp x).congr_of_eventually_eq
    (h.filter_mono nhds_within_le_nhds) h.eq_of_nhds, continuous_right_to_Ico_mod a hp x⟩

lemma continuous_at_to_Ioc_mod : continuous_at (to_Ioc_mod a hp) x :=
let h := to_Ico_mod_eventually_eq_to_Ioc_mod a hp hx in continuous_at_iff_continuous_left_right.2 $
  ⟨continuous_left_to_Ioc_mod a hp x, (continuous_right_to_Ico_mod a hp x).congr_of_eventually_eq
    (h.symm.filter_mono nhds_within_le_nhds) h.symm.eq_of_nhds⟩

end continuity

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

lemma coe_add (x y : 𝕜) : (↑(x + y) : add_circle p) = (x : add_circle p) + (y : add_circle p) := rfl

lemma coe_sub (x y : 𝕜) : (↑(x - y) : add_circle p) = (x : add_circle p) - (y : add_circle p) := rfl

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

lemma coe_period : (p : add_circle p) = 0 :=
(quotient_add_group.eq_zero_iff p).2 $ mem_zmultiples p

@[simp] lemma coe_add_period (x : 𝕜) : ((x + p : 𝕜) : add_circle p) = x :=
by rw [coe_add, ←eq_sub_iff_add_eq', sub_self, coe_period]

@[continuity, nolint unused_arguments] protected lemma continuous_mk' :
  continuous (quotient_add_group.mk' (zmultiples p) : 𝕜 → add_circle p) :=
continuous_coinduced_rng

variables [hp : fact (0 < p)]
include hp

variables (a : 𝕜) [archimedean 𝕜]

/-- The equivalence between `add_circle p` and the half-open interval `[a, a + p)`, whose inverse
is the natural quotient map. -/
def equiv_Ico : add_circle p ≃ Ico a (a + p) := quotient_add_group.equiv_Ico_mod a hp.out

/-- The equivalence between `add_circle p` and the half-open interval `(a, a + p]`, whose inverse
is the natural quotient map. -/
def equiv_Ioc : add_circle p ≃ Ioc a (a + p) := quotient_add_group.equiv_Ioc_mod a hp.out

/-- Given a function on `𝕜`, return the unique function on `add_circle p` agreeing with `f` on
`[a, a + p)`. -/
def lift_Ico (f : 𝕜 → B) : add_circle p → B := restrict _ f ∘ add_circle.equiv_Ico p a

/-- Given a function on `𝕜`, return the unique function on `add_circle p` agreeing with `f` on
`(a, a + p]`. -/
def lift_Ioc (f : 𝕜 → B) : add_circle p → B := restrict _ f ∘ add_circle.equiv_Ioc p a

variables {p a}

lemma coe_eq_coe_iff_of_mem_Ico {x y : 𝕜}
  (hx : x ∈ Ico a (a + p)) (hy : y ∈ Ico a (a + p)) : (x : add_circle p) = y ↔ x = y :=
begin
  refine ⟨λ h, _, by tauto⟩,
  suffices : (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩, by exact subtype.mk.inj this,
  apply_fun equiv_Ico p a at h,
  rw [←(equiv_Ico p a).right_inv ⟨x, hx⟩, ←(equiv_Ico p a).right_inv ⟨y, hy⟩],
  exact h
end

lemma lift_Ico_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico a (a + p)) : lift_Ico p a f ↑x = f x :=
begin
  have : (equiv_Ico p a) x = ⟨x, hx⟩,
  { rw equiv.apply_eq_iff_eq_symm_apply,
    refl, },
  rw [lift_Ico, comp_apply, this],
  refl,
end

lemma lift_Ioc_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc a (a + p)) : lift_Ioc p a f ↑x = f x :=
begin
  have : (equiv_Ioc p a) x = ⟨x, hx⟩,
  { rw equiv.apply_eq_iff_eq_symm_apply,
    refl, },
  rw [lift_Ioc, comp_apply, this],
  refl,
end

variables (p a)

section continuity

@[continuity] lemma continuous_equiv_Ico_symm : continuous (equiv_Ico p a).symm :=
continuous_quotient_mk.comp continuous_subtype_coe

@[continuity] lemma continuous_equiv_Ioc_symm : continuous (equiv_Ioc p a).symm :=
continuous_quotient_mk.comp continuous_subtype_coe

variables {x : add_circle p} (hx : x ≠ a)
include hx

lemma continuous_at_equiv_Ico : continuous_at (equiv_Ico p a) x :=
begin
  induction x using quotient_add_group.induction_on',
  rw [continuous_at, filter.tendsto, quotient_add_group.nhds_eq, filter.map_map],
  apply continuous_at.cod_restrict, exact continuous_at_to_Ico_mod a hp.out hx,
end

lemma continuous_at_equiv_Ioc : continuous_at (equiv_Ioc p a) x :=
begin
  induction x using quotient_add_group.induction_on',
  rw [continuous_at, filter.tendsto, quotient_add_group.nhds_eq, filter.map_map],
  apply continuous_at.cod_restrict, exact continuous_at_to_Ioc_mod a hp.out hx,
end

end continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → add_circle p` is
the entire space. -/
@[simp] lemma coe_image_Ico_eq : (coe : 𝕜 → add_circle p) '' Ico a (a + p) = univ :=
by { rw image_eq_range, exact (equiv_Ico p a).symm.range_eq_univ }

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → add_circle p` is
the entire space. -/
@[simp] lemma coe_image_Ioc_eq : (coe : 𝕜 → add_circle p) '' Ioc a (a + p) = univ :=
by { rw image_eq_range, exact (equiv_Ioc p a).symm.range_eq_univ }

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp] lemma coe_image_Icc_eq : (coe : 𝕜 → add_circle p) '' Icc a (a + p) = univ :=
eq_top_mono (image_subset _ Ico_subset_Icc_self) $ coe_image_Ico_eq _ _

end linear_ordered_add_comm_group

section linear_ordered_field
variables [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p q : 𝕜)

/-- The rescaling equivalence between additive circles with different periods. -/
def equiv_add_circle (hp : p ≠ 0) (hq : q ≠ 0) : add_circle p ≃+ add_circle q :=
quotient_add_group.congr _ _ (add_aut.mul_right $ (units.mk0 p hp)⁻¹ * units.mk0 q hq) $
  by rw [add_monoid_hom.map_zmultiples, add_monoid_hom.coe_coe, add_aut.mul_right_apply,
    units.coe_mul, units.coe_mk0, units.coe_inv, units.coe_mk0, mul_inv_cancel_left₀ hp]

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
  (equiv_Ico p 0 $ quotient_add_group.mk x : 𝕜) = int.fract (x / p) * p :=
to_Ico_mod_eq_fract_mul _ x

instance : divisible_by (add_circle p) ℤ :=
{ div := λ x n, (↑(((n : 𝕜)⁻¹) * (equiv_Ico p 0 x : 𝕜)) : add_circle p),
  div_zero := λ x,
    by simp only [algebra_map.coe_zero, quotient_add_group.coe_zero, inv_zero, zero_mul],
  div_cancel := λ n x hn,
  begin
    replace hn : (n : 𝕜) ≠ 0, { norm_cast, assumption, },
    change n • quotient_add_group.mk' _ ((n : 𝕜)⁻¹ * ↑(equiv_Ico p 0 x)) = x,
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul],
    exact (equiv_Ico p 0).symm_apply_apply x,
  end, }

end floor_ring

section finite_order_points

variables {p}

lemma add_order_of_period_div {n : ℕ} (h : 0 < n) : add_order_of ((p / n : 𝕜) : add_circle p) = n :=
begin
  rw [add_order_of_eq_iff h],
  replace h : 0 < (n : 𝕜) := nat.cast_pos.2 h,
  refine ⟨_, λ m hn h0, _⟩; simp only [ne, ← coe_nsmul, nsmul_eq_mul],
  { rw [mul_div_cancel' _ h.ne', coe_period] },
  rw coe_eq_zero_of_pos_iff p hp.out (mul_pos (nat.cast_pos.2 h0) $ div_pos hp.out h),
  rintro ⟨k, hk⟩,
  rw [mul_div, eq_div_iff h.ne', nsmul_eq_mul, mul_right_comm, ← nat.cast_mul,
      (mul_left_injective₀ hp.out.ne').eq_iff, nat.cast_inj, mul_comm] at hk,
  exact (nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_lt hn,
end

variables (p)

lemma gcd_mul_add_order_of_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
  m.gcd n * add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  rw [mul_comm_div, ← nsmul_eq_mul, coe_nsmul, add_order_of_nsmul''],
  { rw [add_order_of_period_div hn, nat.gcd_comm, nat.mul_div_cancel'],
    exacts [n.gcd_dvd_left m, hp] },
  { rw [← add_order_of_pos_iff, add_order_of_period_div hn], exacts [hn, hp] },
end

variable {p}

lemma add_order_of_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : m.gcd n = 1) :
  add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
by { convert gcd_mul_add_order_of_div_eq p m hn, rw [h, one_mul] }

lemma add_order_of_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : m.nat_abs.gcd n = 1) :
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

lemma add_order_of_eq_pos_iff {u : add_circle p} {n : ℕ} (h : 0 < n) :
  add_order_of u = n ↔ ∃ m < n, m.gcd n = 1 ∧ ↑(↑m / ↑n * p) = u :=
begin
  refine ⟨quotient_add_group.induction_on' u (λ k hk, _), _⟩, swap,
  { rintros ⟨m, h₀, h₁, rfl⟩, exact add_order_of_div_of_gcd_eq_one h h₁ },
  have h0 := add_order_of_nsmul_eq_zero (k : add_circle p),
  rw [hk, ← coe_nsmul, coe_eq_zero_iff] at h0,
  obtain ⟨a, ha⟩ := h0,
  have h0 : (_ : 𝕜) ≠ 0 := nat.cast_ne_zero.2 h.ne',
  rw [nsmul_eq_mul, mul_comm, ← div_eq_iff h0, ← a.div_add_mod' n, add_smul, add_div, zsmul_eq_mul,
    int.cast_mul, int.cast_coe_nat, mul_assoc, ← mul_div, mul_comm _ p, mul_div_cancel p h0] at ha,
  have han : _ = a % n := int.to_nat_of_nonneg (int.mod_nonneg _ $ by exact_mod_cast h.ne'),
  have he := _, refine ⟨(a % n).to_nat, _, _, he⟩,
  { rw [← int.coe_nat_lt, han],
    exact int.mod_lt_of_pos _ (int.coe_nat_lt.2 h) },
  { have := (gcd_mul_add_order_of_div_eq p _ h).trans ((congr_arg add_order_of he).trans hk).symm,
    rw [he, nat.mul_left_eq_self_iff] at this, { exact this }, { rwa hk } },
  convert congr_arg coe ha using 1,
  rw [coe_add, ← int.cast_coe_nat, han, zsmul_eq_mul, mul_div_right_comm,
      eq_comm, add_left_eq_self, ← zsmul_eq_mul, coe_zsmul, coe_period, smul_zero],
end

lemma exists_gcd_eq_one_of_is_of_fin_add_order {u : add_circle p} (h : is_of_fin_add_order u) :
  ∃ m : ℕ, m.gcd (add_order_of u) = 1 ∧
           m < (add_order_of u) ∧
           ↑(((m : 𝕜) / add_order_of u) * p) = u :=
let ⟨m, hl, hg, he⟩ := (add_order_of_eq_pos_iff $ add_order_of_pos' h).1 rfl in ⟨m, hg, hl, he⟩

variables (p)

/-- The natural bijection between points of order `n` and natural numbers less than and coprime to
`n`. The inverse of the map sends `m ↦ (m/n * p : add_circle p)` where `m` is coprime to `n` and
satisfies `0 ≤ m < n`. -/
def set_add_order_of_equiv {n : ℕ} (hn : 0 < n) :
  {u : add_circle p | add_order_of u = n} ≃ {m | m < n ∧ m.gcd n = 1} :=
equiv.symm $ equiv.of_bijective
  (λ m, ⟨↑((m : 𝕜) / n * p), add_order_of_div_of_gcd_eq_one hn (m.prop.2)⟩)
begin
  refine ⟨λ m₁ m₂ h, subtype.ext _, λ u, _⟩,
  { simp_rw [subtype.ext_iff, subtype.coe_mk] at h,
    rw [← sub_eq_zero, ← coe_sub, ← sub_mul, ← sub_div, coe_coe, coe_coe, ← int.cast_coe_nat m₁,
        ← int.cast_coe_nat m₂, ← int.cast_sub, coe_eq_zero_iff] at h,
    obtain ⟨m, hm⟩ := h,
    rw [← mul_div_right_comm, eq_div_iff, mul_comm, ← zsmul_eq_mul, mul_smul_comm, ← nsmul_eq_mul,
      ← coe_nat_zsmul, smul_smul, (zsmul_strict_mono_left hp.out).injective.eq_iff, mul_comm] at hm,
    swap, { exact nat.cast_ne_zero.2 hn.ne' },
    rw [← @nat.cast_inj ℤ, ← sub_eq_zero],
    refine int.eq_zero_of_abs_lt_dvd ⟨_, hm.symm⟩ (abs_sub_lt_iff.2 ⟨_, _⟩);
    apply (int.sub_le_self _ $ nat.cast_nonneg _).trans_lt (nat.cast_lt.2 _),
    exacts [m₁.2.1, m₂.2.1] },
  obtain ⟨m, hmn, hg, he⟩ := (add_order_of_eq_pos_iff hn).mp u.2,
  exact ⟨⟨m, hmn, hg⟩, subtype.ext he⟩,
end

@[simp] lemma card_add_order_of_eq_totient {n : ℕ} :
  nat.card {u : add_circle p // add_order_of u = n} = n.totient :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [nat.totient_zero, add_order_of_eq_zero_iff],
    rcases em (∃ (u : add_circle p), ¬ is_of_fin_add_order u) with ⟨u, hu⟩ | h,
    { haveI : infinite {u : add_circle p // ¬is_of_fin_add_order u},
      { erw infinite_coe_iff,
        exact infinite_not_is_of_fin_add_order hu, },
      exact nat.card_eq_zero_of_infinite, },
    { haveI : is_empty {u : add_circle p // ¬is_of_fin_add_order u}, { simpa using h, },
      exact nat.card_of_is_empty, }, },
  { rw [← coe_set_of, nat.card_congr (set_add_order_of_equiv p hn),
      n.totient_eq_card_lt_and_coprime],
    simp only [nat.gcd_comm], },
end

lemma finite_set_of_add_order_eq {n : ℕ} (hn : 0 < n) :
  {u : add_circle p | add_order_of u = n}.finite :=
finite_coe_iff.mp $ nat.finite_of_card_ne_zero $ by simpa only [coe_set_of,
  card_add_order_of_eq_totient p] using (nat.totient_pos hn).ne'

end finite_order_points

end linear_ordered_field

variables (p : ℝ)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compact_space [fact (0 < p)] : compact_space $ add_circle p :=
begin
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p 0],
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

local attribute [instance] real.fact_zero_lt_one

/-- The unit circle `ℝ ⧸ ℤ`. -/
@[derive [compact_space, normal_space, second_countable_topology]]
abbreviation unit_add_circle := add_circle (1 : ℝ)

section identify_Icc_ends
/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ 𝕜` to `add_circle p`
gives an identification of `add_circle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/

namespace add_circle

variables [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜]
(p a : 𝕜) [hp : fact (0 < p)]

include hp

local notation `𝕋` := add_circle p

/-- The relation identifying the endpoints of `Icc a (a + p)`. -/
inductive endpoint_ident : Icc a (a + p) → Icc a (a + p) → Prop
| mk : endpoint_ident
    ⟨a,      left_mem_Icc.mpr $ le_add_of_nonneg_right hp.out.le⟩
    ⟨a + p, right_mem_Icc.mpr $ le_add_of_nonneg_right hp.out.le⟩

variables [archimedean 𝕜]

/-- The equivalence between `add_circle p` and the quotient of `[a, a + p]` by the relation
identifying the endpoints. -/
def equiv_Icc_quot : 𝕋 ≃ quot (endpoint_ident p a) :=
{ to_fun := λ x, quot.mk _ $ inclusion Ico_subset_Icc_self (equiv_Ico _ _ x),
  inv_fun := λ x, quot.lift_on x coe $ by { rintro _ _ ⟨_⟩, exact (coe_add_period p a).symm },
  left_inv := (equiv_Ico p a).symm_apply_apply,
  right_inv := quot.ind $ by
  { rintro ⟨x, hx⟩,
    have := _,
    rcases ne_or_eq x (a + p) with h | rfl,
    { revert x, exact this },
    { rw ← quot.sound endpoint_ident.mk, exact this _ _ (lt_add_of_pos_right a hp.out).ne },
    intros x hx h,
    congr, ext1,
    apply congr_arg subtype.val ((equiv_Ico p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩) } }

lemma equiv_Icc_quot_comp_mk_eq_to_Ico_mod : equiv_Icc_quot p a ∘ quotient.mk' =
  λ x, quot.mk _ ⟨to_Ico_mod a hp.out x, Ico_subset_Icc_self $ to_Ico_mod_mem_Ico a _ x⟩ := rfl

lemma equiv_Icc_quot_comp_mk_eq_to_Ioc_mod : equiv_Icc_quot p a ∘ quotient.mk' =
  λ x, quot.mk _ ⟨to_Ioc_mod a hp.out x, Ioc_subset_Icc_self $ to_Ioc_mod_mem_Ioc a _ x⟩ :=
begin
  rw equiv_Icc_quot_comp_mk_eq_to_Ico_mod, funext,
  by_cases mem_Ioo_mod a p x,
  { simp_rw (mem_Ioo_mod_iff_to_Ico_mod_eq_to_Ioc_mod hp.out).1 h },
  { simp_rw [not_imp_comm.1 (mem_Ioo_mod_iff_to_Ico_mod_ne_left hp.out).2 h,
             not_imp_comm.1 (mem_Ioo_mod_iff_to_Ioc_mod_ne_right hp.out).2 h],
    exact quot.sound endpoint_ident.mk },
end

/-- The natural map from `[a, a + p] ⊂ 𝕜` with endpoints identified to `𝕜 / ℤ • p`, as a
homeomorphism of topological spaces. -/
def homeo_Icc_quot : 𝕋 ≃ₜ quot (endpoint_ident p a) :=
{ to_equiv := equiv_Icc_quot p a,
  continuous_to_fun := begin
    simp_rw [quotient_map_quotient_mk.continuous_iff,
      continuous_iff_continuous_at, continuous_at_iff_continuous_left_right],
    intro x, split,
    work_on_goal 1 { erw equiv_Icc_quot_comp_mk_eq_to_Ioc_mod },
    work_on_goal 2 { erw equiv_Icc_quot_comp_mk_eq_to_Ico_mod },
    all_goals { apply continuous_quot_mk.continuous_at.comp_continuous_within_at,
      rw inducing_coe.continuous_within_at_iff },
    { apply continuous_left_to_Ioc_mod },
    { apply continuous_right_to_Ico_mod },
  end,
  continuous_inv_fun := continuous_quot_lift _
    ((add_circle.continuous_mk' p).comp continuous_subtype_coe) }

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is the
pullback of a continuous function on `add_circle p`. -/

variables {p a}

lemma lift_Ico_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) : lift_Ico p a f =
  quot.lift (restrict (Icc a $ a + p) f) (by { rintro _ _ ⟨_⟩, exact h }) ∘ equiv_Icc_quot p a :=
rfl

lemma lift_Ico_continuous [topological_space B] {f : 𝕜 → B} (hf : f a = f (a + p))
  (hc : continuous_on f $ Icc a (a + p)) : continuous (lift_Ico p a f) :=
begin
  rw lift_Ico_eq_lift_Icc hf,
  refine continuous.comp _ (homeo_Icc_quot p a).continuous_to_fun,
  exact continuous_coinduced_dom.mpr (continuous_on_iff_continuous_restrict.mp hc),
end

section zero_based

lemma lift_Ico_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico 0 p) :
  lift_Ico p 0 f ↑x = f x := lift_Ico_coe_apply (by rwa zero_add)

lemma lift_Ico_zero_continuous [topological_space B] {f : 𝕜 → B}
  (hf : f 0 = f p) (hc : continuous_on f $ Icc 0 p) : continuous (lift_Ico p 0 f) :=
lift_Ico_continuous (by rwa zero_add : f 0 = f (0 + p)) (by rwa zero_add)

end zero_based

end add_circle

end identify_Icc_ends
