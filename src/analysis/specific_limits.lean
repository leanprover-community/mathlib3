/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

A collection of specific limit computations.
-/
import analysis.normed_space.basic
import algebra.geom_sum
import topology.instances.ennreal
import tactic.ring_exp

noncomputable theory
open_locale classical topological_space

open classical function filter finset metric

open_locale big_operators

variables {α : Type*} {β : Type*} {ι : Type*}

lemma tendsto_norm_at_top_at_top : tendsto (norm : ℝ → ℝ) at_top at_top :=
tendsto_abs_at_top_at_top

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `tendsto_at_top_mul_left'`). -/
lemma tendsto_at_top_mul_left [decidable_linear_ordered_semiring α] [archimedean α]
  {l : filter β} {r : α} (hr : 0 < r) {f : β → α} (hf : tendsto f l at_top) :
  tendsto (λx, r * f x) l at_top :=
begin
  apply (tendsto_at_top _ _).2 (λb, _),
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1 : α) ≤ n • r := archimedean.arch 1 hr,
  have hn' : 1 ≤ r * n, by rwa nsmul_eq_mul' at hn,
  filter_upwards [(tendsto_at_top _ _).1 hf (n * max b 0)],
  assume x hx,
  calc b ≤ 1 * max b 0 : by { rw [one_mul], exact le_max_left _ _ }
  ... ≤ (r * n) * max b 0 : mul_le_mul_of_nonneg_right hn' (le_max_right _ _)
  ... = r * (n * max b 0) : by rw [mul_assoc]
  ... ≤ r * f x : mul_le_mul_of_nonneg_left hx (le_of_lt hr)
end

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `tendsto_at_top_mul_right'`). -/
lemma tendsto_at_top_mul_right [decidable_linear_ordered_semiring α] [archimedean α]
  {l : filter β} {r : α} (hr : 0 < r) {f : β → α} (hf : tendsto f l at_top) :
  tendsto (λx, f x * r) l at_top :=
begin
  apply (tendsto_at_top _ _).2 (λb, _),
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1 : α) ≤ n • r := archimedean.arch 1 hr,
  have hn' : 1 ≤ (n : α) * r, by rwa nsmul_eq_mul at hn,
  filter_upwards [(tendsto_at_top _ _).1 hf (max b 0 * n)],
  assume x hx,
  calc b ≤ max b 0 * 1 : by { rw [mul_one], exact le_max_left _ _ }
  ... ≤ max b 0 * (n * r) : mul_le_mul_of_nonneg_left hn' (le_max_right _ _)
  ... = (max b 0 * n) * r : by rw [mul_assoc]
  ... ≤ f x * r : mul_le_mul_of_nonneg_right hx (le_of_lt hr)
end

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. For a version working in `ℕ` or `ℤ`, use
`tendsto_at_top_mul_left` instead. -/
lemma tendsto_at_top_mul_left' [linear_ordered_field α]
  {l : filter β} {r : α} (hr : 0 < r) {f : β → α} (hf : tendsto f l at_top) :
  tendsto (λx, r * f x) l at_top :=
begin
  apply (tendsto_at_top _ _).2 (λb, _),
  filter_upwards [(tendsto_at_top _ _).1 hf (b/r)],
  assume x hx,
  simpa [div_le_iff' hr] using hx
end

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. For a version working in `ℕ` or `ℤ`, use
`tendsto_at_top_mul_right` instead. -/
lemma tendsto_at_top_mul_right' [linear_ordered_field α]
  {l : filter β} {r : α} (hr : 0 < r) {f : β → α} (hf : tendsto f l at_top) :
  tendsto (λx, f x * r) l at_top :=
by simpa [mul_comm] using tendsto_at_top_mul_left' hr hf

/-- If a function tends to infinity along a filter, then this function divided by a positive
constant also tends to infinity. -/
lemma tendsto_at_top_div [linear_ordered_field α]
  {l : filter β} {r : α} (hr : 0 < r) {f : β → α} (hf : tendsto f l at_top) :
  tendsto (λx, f x / r) l at_top :=
tendsto_at_top_mul_right' (inv_pos.2 hr) hf

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
lemma tendsto_inv_zero_at_top [discrete_linear_ordered_field α] [topological_space α]
  [order_topology α] : tendsto (λx:α, x⁻¹) (nhds_within (0 : α) (set.Ioi 0)) at_top :=
begin
  apply (tendsto_at_top _ _).2 (λb, _),
  refine mem_nhds_within_Ioi_iff_exists_Ioo_subset.2 ⟨(max b 1)⁻¹, by simp [zero_lt_one], λx hx, _⟩,
  calc b ≤ max b 1 : le_max_left _ _
  ... ≤ x⁻¹ : begin
    apply (le_inv _ hx.1).2 (le_of_lt hx.2),
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  end
end

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
lemma tendsto_inv_at_top_zero' [discrete_linear_ordered_field α] [topological_space α]
  [order_topology α] : tendsto (λr:α, r⁻¹) at_top (nhds_within (0 : α) (set.Ioi 0)) :=
begin
  assume s hs,
  rw mem_nhds_within_Ioi_iff_exists_Ioc_subset at hs,
  rcases hs with ⟨C, C0, hC⟩,
  change 0 < C at C0,
  refine filter.mem_map.2 (mem_sets_of_superset (mem_at_top C⁻¹) (λ x hx, hC _)),
  have : 0 < x, from lt_of_lt_of_le (inv_pos.2 C0) hx,
  exact ⟨inv_pos.2 this, (inv_le C0 this).1 hx⟩
end

lemma tendsto_inv_at_top_zero [discrete_linear_ordered_field α] [topological_space α]
  [order_topology α] : tendsto (λr:α, r⁻¹) at_top (𝓝 0) :=
tendsto_le_right inf_le_left tendsto_inv_at_top_zero'

lemma summable_of_absolute_convergence_real {f : ℕ → ℝ} :
  (∃r, tendsto (λn, (∑ i in range n, abs (f i))) at_top (𝓝 r)) → summable f
| ⟨r, hr⟩ :=
  begin
    refine summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩,
    exact assume i, norm_nonneg _,
    simpa only using hr
  end

lemma tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : ℝ)⁻¹) at_top (𝓝 0) :=
tendsto_inv_at_top_zero.comp (tendsto_coe_nat_real_at_top_iff.2 tendsto_id)

lemma tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat

lemma nnreal.tendsto_inverse_at_top_nhds_0_nat : tendsto (λ n : ℕ, (n : nnreal)⁻¹) at_top (𝓝 0) :=
by { rw ← nnreal.tendsto_coe, convert tendsto_inverse_at_top_nhds_0_nat, simp }

lemma nnreal.tendsto_const_div_at_top_nhds_0_nat (C : nnreal) :
  tendsto (λ n : ℕ, C / n) at_top (𝓝 0) :=
by simpa using tendsto_const_nhds.mul nnreal.tendsto_inverse_at_top_nhds_0_nat

lemma tendsto_one_div_add_at_top_nhds_0_nat :
  tendsto (λ n : ℕ, 1 / ((n : ℝ) + 1)) at_top (𝓝 0) :=
suffices tendsto (λ n : ℕ, 1 / (↑(n + 1) : ℝ)) at_top (𝓝 0), by simpa,
(tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

/-! ### Powers -/

lemma tendsto_add_one_pow_at_top_at_top_of_pos [linear_ordered_semiring α] [archimedean α] {r : α}
  (h : 0 < r) :
  tendsto (λ n:ℕ, (r + 1)^n) at_top at_top :=
tendsto_at_top_at_top_of_monotone' (λ n m, pow_le_pow (le_add_of_nonneg_left' (le_of_lt h))) $
  not_bdd_above_iff.2 $ λ x, set.exists_range_iff.2 $ add_one_pow_unbounded_of_pos _ h

lemma tendsto_pow_at_top_at_top_of_one_lt [linear_ordered_ring α] [archimedean α]
  {r : α} (h : 1 < r) :
  tendsto (λn:ℕ, r ^ n) at_top at_top :=
sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (sub_pos.2 h)

lemma nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) :
  tendsto (λn:ℕ, m ^ n) at_top at_top :=
begin
  simp only [← nat.pow_eq_pow],
  exact nat.sub_add_cancel (le_of_lt h) ▸
    tendsto_add_one_pow_at_top_at_top_of_pos (nat.sub_pos_of_lt h)
end

lemma lim_norm_zero' {𝕜 : Type*} [normed_group 𝕜] :
  tendsto (norm : 𝕜 → ℝ) (nhds_within 0 {x | x ≠ 0}) (nhds_within 0 (set.Ioi 0)) :=
lim_norm_zero.inf $ tendsto_principal_principal.2 $ λ x hx, norm_pos_iff.2 hx

lemma normed_field.tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type*} [normed_field 𝕜] :
  tendsto (λ x:𝕜, ∥x⁻¹∥) (nhds_within 0 {x | x ≠ 0}) at_top :=
(tendsto_inv_zero_at_top.comp lim_norm_zero').congr $ λ x, (normed_field.norm_inv x).symm

lemma tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
by_cases
  (assume : r = 0, (tendsto_add_at_top_iff_nat 1).mp $ by simp [pow_succ, this, tendsto_const_nhds])
  (assume : r ≠ 0,
    have tendsto (λn, (r⁻¹ ^ n)⁻¹) at_top (𝓝 0),
      from tendsto_inv_at_top_zero.comp
        (tendsto_pow_at_top_at_top_of_one_lt $ one_lt_inv (lt_of_le_of_ne h₁ this.symm) h₂),
    tendsto.congr' (univ_mem_sets' $ by simp *) this)

lemma geom_lt {u : ℕ → ℝ} {k : ℝ} (hk : 0 < k) {n : ℕ} (h : ∀ m ≤ n, k*u m < u (m + 1)) :
  k^(n + 1) *u 0 < u (n + 1) :=
begin
 induction n with n ih,
 { simpa using h 0 (le_refl _) },
 have : (∀ (m : ℕ), m ≤ n → k * u m < u (m + 1)),
   intros m hm, apply h, exact nat.le_succ_of_le hm,
 specialize ih this,
 change k ^ (n + 2) * u 0 < u (n + 2),
 replace h : k * u (n + 1) < u (n + 2) := h (n+1) (le_refl _),
 calc k ^ (n + 2) * u 0 = k*(k ^ (n + 1) * u 0) : by ring_exp
  ... < k*(u (n + 1)) : mul_lt_mul_of_pos_left ih hk
  ... < u (n + 2) : h,
end

/-- If a sequence `v` of real numbers satisfies `k*v n < v (n+1)` with `1 < k`,
then it goes to +∞. -/
lemma tendsto_at_top_of_geom_lt {v : ℕ → ℝ} {k : ℝ} (h₀ : 0 < v 0) (hk : 1 < k)
  (hu : ∀ n, k*v n < v (n+1)) : tendsto v at_top at_top :=
begin
  apply tendsto_at_top_mono,
  show ∀ n, k^n*v 0 ≤ v n,
  { intro n,
    induction n with n ih,
    { simp },
    calc
    k ^ (n + 1) * v 0 = k*(k^n*v 0) : by ring_exp
                  ... ≤ k*v n       : mul_le_mul_of_nonneg_left ih (by linarith)
                  ... ≤ v (n + 1)   : le_of_lt (hu n) },
  apply tendsto_at_top_mul_right h₀,
  exact tendsto_pow_at_top_at_top_of_one_lt hk,
end

lemma nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : nnreal} (hr : r < 1) :
  tendsto (λ n:ℕ, r^n) at_top (𝓝 0) :=
nnreal.tendsto_coe.1 $ by simp only [nnreal.coe_pow, nnreal.coe_zero,
  tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg hr]

lemma ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ennreal} (hr : r < 1) :
  tendsto (λ n:ℕ, r^n) at_top (𝓝 0) :=
begin
  rcases ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩,
  rw [← ennreal.coe_zero],
  norm_cast at *,
  apply nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 hr
end

lemma tendsto_pow_at_top_nhds_0_of_norm_lt_1 {K : Type*} [normed_field K] {ξ : K}
  (_ : ∥ξ∥ < 1) : tendsto (λ n : ℕ, ξ^n) at_top (𝓝 0) :=
begin
  rw [tendsto_iff_norm_tendsto_zero],
  convert tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg ξ) ‹∥ξ∥ < 1›,
  ext n,
  simp
end

lemma tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : abs r < 1) :
  tendsto (λn:ℕ, r^n) at_top (𝓝 0) :=
tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/
section geometric

lemma has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
  has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
have r ≠ 1, from ne_of_lt h₂,
have r + -1 ≠ 0,
  by rw [←sub_eq_add_neg, ne, sub_eq_iff_eq_add]; simp; assumption,
have tendsto (λn, (r ^ n - 1) * (r - 1)⁻¹) at_top (𝓝 ((0 - 1) * (r - 1)⁻¹)),
  from ((tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds,
have (λ n, (∑ i in range n, r ^ i)) = (λ n, geom_series r n) := rfl,
(has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr $
  by simp [neg_inv, geom_sum, div_eq_mul_inv, *] at *

lemma summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, has_sum_geometric_of_lt_1 h₁ h₂⟩

lemma tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : (∑'n:ℕ, r ^ n) = (1 - r)⁻¹ :=
tsum_eq_has_sum (has_sum_geometric_of_lt_1 h₁ h₂)

lemma has_sum_geometric_two : has_sum (λn:ℕ, ((1:ℝ)/2) ^ n) 2 :=
by convert has_sum_geometric_of_lt_1 _ _; norm_num

lemma summable_geometric_two : summable (λn:ℕ, ((1:ℝ)/2) ^ n) :=
⟨_, has_sum_geometric_two⟩

lemma tsum_geometric_two : (∑'n:ℕ, ((1:ℝ)/2) ^ n) = 2 :=
tsum_eq_has_sum has_sum_geometric_two

lemma sum_geometric_two_le (n : ℕ) : ∑ (i : ℕ) in range n, (1 / (2 : ℝ)) ^ i ≤ 2 :=
begin
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i,
  { intro i, apply pow_nonneg, norm_num },
  convert sum_le_tsum (range n) (λ i _, this i) summable_geometric_two,
  exact tsum_geometric_two.symm
end

lemma has_sum_geometric_two' (a : ℝ) : has_sum (λn:ℕ, (a / 2) / 2 ^ n) a :=
begin
  convert has_sum.mul_left (a / 2) (has_sum_geometric_of_lt_1
    (le_of_lt one_half_pos) one_half_lt_one),
  { funext n, simp, refl, },
  { norm_num }
end

lemma summable_geometric_two' (a : ℝ) : summable (λ n:ℕ, (a / 2) / 2 ^ n) :=
⟨a, has_sum_geometric_two' a⟩

lemma tsum_geometric_two' (a : ℝ) : (∑' n:ℕ, (a / 2) / 2^n) = a :=
tsum_eq_has_sum $ has_sum_geometric_two' a

lemma nnreal.has_sum_geometric {r : nnreal} (hr : r < 1) :
  has_sum (λ n : ℕ, r ^ n) (1 - r)⁻¹ :=
begin
  apply nnreal.has_sum_coe.1,
  push_cast,
  rw [nnreal.coe_sub (le_of_lt hr)],
  exact has_sum_geometric_of_lt_1 r.coe_nonneg hr
end

lemma nnreal.summable_geometric {r : nnreal} (hr : r < 1) : summable (λn:ℕ, r ^ n) :=
⟨_, nnreal.has_sum_geometric hr⟩

lemma tsum_geometric_nnreal {r : nnreal} (hr : r < 1) : (∑'n:ℕ, r ^ n) = (1 - r)⁻¹ :=
tsum_eq_has_sum (nnreal.has_sum_geometric hr)

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
lemma ennreal.tsum_geometric (r : ennreal) : (∑'n:ℕ, r ^ n) = (1 - r)⁻¹ :=
begin
  cases lt_or_le r 1 with hr hr,
  { rcases ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩,
    norm_cast at *,
    convert ennreal.tsum_coe_eq (nnreal.has_sum_geometric hr),
    rw [ennreal.coe_inv $ ne_of_gt $ nnreal.sub_pos.2 hr] },
  { rw [ennreal.sub_eq_zero_of_le hr, ennreal.inv_zero, ennreal.tsum_eq_supr_nat, supr_eq_top],
    refine λ a ha, (ennreal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp
      (λ n hn, lt_of_lt_of_le hn _),
    have : ∀ k:ℕ, 1 ≤ r^k, by simpa using canonically_ordered_semiring.pow_le_pow_of_le_left hr,
    calc (n:ennreal) = (∑ i in range n, 1) : by rw [sum_const, nsmul_one, card_range]
    ... ≤ ∑ i in range n, r ^ i : sum_le_sum (λ k _, this k) }
end

variables {K : Type*} [normed_field K] {ξ : K}

lemma has_sum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : has_sum (λn:ℕ, ξ ^ n) (1 - ξ)⁻¹ :=
begin
  have xi_ne_one : ξ ≠ 1, by { contrapose! h, simp [h] },
  have A : tendsto (λn, (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)),
    from ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds,
  have B : (λ n, (∑ i in range n, ξ ^ i)) = (λ n, geom_series ξ n) := rfl,
  rw [has_sum_iff_tendsto_nat_of_summable_norm, B],
  { simpa [geom_sum, xi_ne_one, neg_inv] using A },
  { simp [normed_field.norm_pow, summable_geometric_of_lt_1 (norm_nonneg _) h] }
end

lemma summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : summable (λn:ℕ, ξ ^ n) :=
⟨_, has_sum_geometric_of_norm_lt_1 h⟩

lemma tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : (∑'n:ℕ, ξ ^ n) = (1 - ξ)⁻¹ :=
tsum_eq_has_sum (has_sum_geometric_of_norm_lt_1 h)

lemma has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : has_sum (λn:ℕ, r ^ n) (1 - r)⁻¹ :=
has_sum_geometric_of_norm_lt_1 h

lemma summable_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : summable (λn:ℕ, r ^ n) :=
summable_geometric_of_norm_lt_1 h

lemma tsum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : (∑'n:ℕ, r ^ n) = (1 - r)⁻¹ :=
tsum_geometric_of_norm_lt_1 h

end geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/
section edist_le_geometric

variables [emetric_space α] (r C : ennreal) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C * r^n)

include hr hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
lemma cauchy_seq_of_edist_le_geometric : cauchy_seq f :=
begin
  refine cauchy_seq_of_edist_le_of_tsum_ne_top _ hu _,
  rw [ennreal.tsum_mul_left, ennreal.tsum_geometric],
  refine ennreal.mul_ne_top hC (ennreal.inv_ne_top.2 _),
  exact ne_of_gt (ennreal.zero_lt_sub_iff_lt.2 hr)
end

omit hr hC

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
lemma edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  edist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _,
  simp only [pow_add, ennreal.tsum_mul_left, ennreal.tsum_geometric, ennreal.div_def, mul_assoc]
end

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
lemma edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ C / (1 - r) :=
by simpa only [pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end edist_le_geometric

section edist_le_geometric_two

variables [emetric_space α] (C : ennreal) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀n, edist (f n) (f (n+1)) ≤ C / 2^n) {a : α} (ha : tendsto f at_top (𝓝 a))

include hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
lemma cauchy_seq_of_edist_le_geometric_two : cauchy_seq f :=
begin
  simp only [ennreal.div_def, ennreal.inv_pow] at hu,
  refine cauchy_seq_of_edist_le_geometric 2⁻¹ C _ hC hu,
  simp [ennreal.one_lt_two]
end

omit hC
include ha

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
lemma edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) :
  edist (f n) a ≤ 2 * C / 2^n :=
begin
  simp only [ennreal.div_def, ennreal.inv_pow] at hu,
  rw [ennreal.div_def, mul_assoc, mul_comm, ennreal.inv_pow],
  convert edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n,
  rw [ennreal.one_sub_inv_two, ennreal.inv_inv]
end

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
lemma edist_le_of_edist_le_geometric_two_of_tendsto₀: edist (f 0) a ≤ 2 * C :=
by simpa only [pow_zero, ennreal.div_def, ennreal.inv_one, mul_one]
  using edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end edist_le_geometric_two

section le_geometric

variables [metric_space α] {r C : ℝ} (hr : r < 1) {f : ℕ → α}
  (hu : ∀n, dist (f n) (f (n+1)) ≤ C * r^n)

include hr hu

lemma aux_has_sum_of_le_geometric : has_sum (λ n : ℕ, C * r^n) (C / (1 - r)) :=
begin
  have h0 : 0 ≤ C,
    by simpa using le_trans dist_nonneg (hu 0),
  rcases eq_or_lt_of_le h0 with rfl | Cpos,
  { simp [has_sum_zero] },
  { have rnonneg: r ≥ 0, from nonneg_of_mul_nonneg_left
      (by simpa only [pow_one] using le_trans dist_nonneg (hu 1)) Cpos,
    refine has_sum.mul_left C _,
    by simpa using has_sum_geometric_of_lt_1 rnonneg hr }
end

variables (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
lemma cauchy_seq_of_le_geometric : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
lemma dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C / (1 - r) :=
(tsum_eq_has_sum $ aux_has_sum_of_le_geometric hr hu) ▸
  dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
lemma dist_le_of_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ (C * r^n) / (1 - r) :=
begin
  have := aux_has_sum_of_le_geometric hr hu,
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n,
  simp only [pow_add, mul_left_comm C, mul_div_right_comm],
  rw [mul_comm],
  exact (eq.symm $ tsum_eq_has_sum $ this.mul_left _)
end

omit hr hu

variable (hu₂ : ∀ n, dist (f n) (f (n+1)) ≤ (C / 2) / 2^n)

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
lemma cauchy_seq_of_le_geometric_two : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ hu₂ $ ⟨_, has_sum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
lemma dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ C :=
(tsum_geometric_two' C) ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
lemma dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ C / 2^n :=
begin
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n,
  simp only [add_comm n, pow_add, (div_div_eq_div_mul _ _ _).symm],
  symmetry,
  exact tsum_eq_has_sum (has_sum.mul_right _ $ has_sum_geometric_two' C)
end

end le_geometric

section summable_le_geometric

variables [normed_group α] {r C : ℝ} {f : ℕ → α}

lemma dist_partial_sum_le_of_le_geometric (hf : ∀n, ∥f n∥ ≤ C * r^n) (n : ℕ) :
  dist (∑ i in range n, f i) (∑ i in range (n+1), f i) ≤ C * r ^ n :=
begin
  rw [sum_range_succ, dist_eq_norm, ← norm_neg],
  convert hf n,
  rw [neg_sub, add_sub_cancel]
end

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
lemma cauchy_seq_finset_of_geometric_bound (hr : r < 1) (hf : ∀n, ∥f n∥ ≤ C * r^n) :
  cauchy_seq (λ s : finset (ℕ), ∑ x in s, f x) :=
cauchy_seq_finset_of_norm_bounded _
  (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
lemma norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀n, ∥f n∥ ≤ C * r^n)
  {a : α} (ha : has_sum f a) (n : ℕ) :
  ∥(∑ x in finset.range n, f x) - a∥ ≤ (C * r ^ n) / (1 - r) :=
begin
  rw ← dist_eq_norm,
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf),
  exact ha.tendsto_sum_nat
end

end summable_le_geometric

/-! ### Positive sequences with small sums on encodable types -/

/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def pos_sum_of_encodable {ε : ℝ} (hε : 0 < ε)
  (ι) [encodable ι] : {ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, has_sum ε' c ∧ c ≤ ε} :=
begin
  let f := λ n, (ε / 2) / 2 ^ n,
  have hf : has_sum f ε := has_sum_geometric_two' _,
  have f0 : ∀ n, 0 < f n := λ n, div_pos (half_pos hε) (pow_pos two_pos _),
  refine ⟨f ∘ encodable.encode, λ i, f0 _, _⟩,
  rcases hf.summable.summable_comp_of_injective (@encodable.encode_injective ι _)
    with ⟨c, hg⟩,
  refine ⟨c, hg, has_sum_le_inj _ (@encodable.encode_injective ι _) _ _ hg hf⟩,
  { assume i _, exact le_of_lt (f0 _) },
  { assume n, exact le_refl _ }
end

namespace nnreal

theorem exists_pos_sum_of_encodable {ε : nnreal} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → nnreal, (∀ i, 0 < ε' i) ∧ ∃c, has_sum ε' c ∧ c < ε :=
let ⟨a, a0, aε⟩ := dense hε in
let ⟨ε', hε', c, hc, hcε⟩ := pos_sum_of_encodable a0 ι in
⟨ λi, ⟨ε' i, le_of_lt $ hε' i⟩, assume i, nnreal.coe_lt_coe.2 $ hε' i,
  ⟨c, has_sum_le (assume i, le_of_lt $ hε' i) has_sum_zero hc ⟩, nnreal.has_sum_coe.1 hc,
   lt_of_le_of_lt (nnreal.coe_le_coe.1 hcε) aε ⟩

end nnreal

namespace ennreal

theorem exists_pos_sum_of_encodable {ε : ennreal} (hε : 0 < ε) (ι) [encodable ι] :
  ∃ ε' : ι → nnreal, (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ennreal)) < ε :=
begin
  rcases dense hε with ⟨r, h0r, hrε⟩,
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩,
  rcases nnreal.exists_pos_sum_of_encodable (coe_lt_coe.1 h0r) ι with ⟨ε', hp, c, hc, hcr⟩,
  exact ⟨ε', hp, (ennreal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩
end

end ennreal

/-!
### Harmonic series

Here we define the harmonic series and prove some basic lemmas about it,
leading to a proof of its divergence to +∞ -/

/-- The harmonic series `1 + 1/2 + 1/3 + ... + 1/n`-/
def harmonic_series (n : ℕ) : ℝ :=
∑ i in range n, 1/(i+1 : ℝ)

lemma mono_harmonic : monotone harmonic_series :=
begin
  intros p q hpq,
  apply sum_le_sum_of_subset_of_nonneg,
  rwa range_subset,
  intros x h _,
  exact le_of_lt nat.one_div_pos_of_nat,
end

lemma half_le_harmonic_double_sub_harmonic (n : ℕ) (hn : 0 < n) :
  1/2 ≤ harmonic_series (2*n) - harmonic_series n :=
begin
  suffices : harmonic_series n + 1 / 2 ≤ harmonic_series (n + n),
  { rw two_mul,
    linarith },
  have : harmonic_series n + ∑ k in Ico n (n + n), 1/(k + 1 : ℝ) = harmonic_series (n + n) :=
    sum_range_add_sum_Ico _ (show n ≤ n+n, by linarith),
  rw [← this,  add_le_add_iff_left],
  have : ∑ k in Ico n (n + n), 1/(n+n : ℝ) = 1/2,
  { have : (n : ℝ) + n ≠ 0,
    { norm_cast, linarith },
    rw [sum_const, Ico.card],
    field_simp [this],
    ring },
  rw ← this,
  apply sum_le_sum,
  intros x hx,
  rw one_div_le_one_div,
  { exact_mod_cast nat.succ_le_of_lt (Ico.mem.mp hx).2 },
  { norm_cast, linarith },
  { exact_mod_cast nat.zero_lt_succ x }
end

lemma self_div_two_le_harmonic_two_pow (n : ℕ) : (n / 2 : ℝ) ≤ harmonic_series (2^n) :=
begin
  induction n with n hn,
  unfold harmonic_series,
  simp only [one_div_eq_inv, nat.cast_zero, euclidean_domain.zero_div, nat.cast_succ, sum_singleton,
    inv_one, zero_add, nat.pow_zero, range_one, zero_le_one],
  have : harmonic_series (2^n) + 1 / 2 ≤ harmonic_series (2^(n+1)),
  { have := half_le_harmonic_double_sub_harmonic (2^n) (by {apply nat.pow_pos, linarith}),
    rw [nat.mul_comm, ← nat.pow_succ] at this,
    linarith },
  apply le_trans _ this,
  rw (show (n.succ / 2 : ℝ) = (n/2 : ℝ) + (1/2), by field_simp),
  linarith,
end

/-- The harmonic series diverges to +∞ -/
theorem harmonic_tendsto_at_top : tendsto harmonic_series at_top at_top :=
begin
  suffices : tendsto (λ n : ℕ, harmonic_series (2^n)) at_top at_top, by
  { exact tendsto_at_top_of_monotone_of_subseq mono_harmonic at_top_ne_bot this },
  apply tendsto_at_top_mono self_div_two_le_harmonic_two_pow,
  apply tendsto_at_top_div,
  norm_num,
  exact tendsto_coe_nat_real_at_top_at_top
end
