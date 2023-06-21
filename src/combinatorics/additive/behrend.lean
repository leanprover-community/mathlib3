/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.inner_product_space.pi_L2
import combinatorics.additive.salem_spencer
import combinatorics.pigeonhole
import data.complex.exponential_bounds

/-!
# Behrend's bound on Roth numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (sqrt (log n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n` dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`behrend.map`).

## Main declarations

* `behrend.sphere`: The intersection of the Euclidean sphere with the positive integer quadrant.
  This is the set that we will map on `ℕ`.
* `behrend.map`: Given a natural number `d`, `behrend.map d : ℕⁿ → ℕ` reads off the coordinates as
  digits in base `d`.
* `behrend.card_sphere_le_roth_number_nat`: Implicit lower bound on Roth numbers in terms of
  `behrend.sphere`.
* `behrend.roth_lower_bound`: Behrend's explicit lower bound on Roth numbers.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/

open finset nat (hiding log) real
open_locale big_operators pointwise

namespace behrend
variables {α β : Type*} {n d k N : ℕ} {x : fin n → ℕ}

/-!
### Turning the sphere into a Salem-Spencer set

We define `behrend.sphere`, the intersection of the $$L^2$$ sphere with the positive quadrant of
integer points. Because the $$L^2$$ closed ball is strictly convex, the $$L^2$$ sphere and
`behrend.sphere` are Salem-Spencer (`add_salem_spencer_sphere`). Then we can turn this set in
`fin n → ℕ` into a set in `ℕ` using `behrend.map`, which preserves `add_salem_spencer` because it is
an additive monoid homomorphism.
-/

/-- The box `{0, ..., d - 1}^n` as a finset. -/
def box (n d : ℕ) : finset (fin n → ℕ) := fintype.pi_finset $ λ _, range d

lemma mem_box : x ∈ box n d ↔ ∀ i, x i < d := by simp only [box, fintype.mem_pi_finset, mem_range]

@[simp] lemma card_box : (box n d).card = d ^ n := by simp [box]
@[simp] lemma box_zero : box (n + 1) 0 = ∅ := by simp [box]

/-- The intersection of the sphere of radius `sqrt k` with the integer points in the positive
quadrant. -/
def sphere (n d k : ℕ) : finset (fin n → ℕ) := (box n d).filter $ λ x, ∑ i, x i^2 = k

lemma sphere_zero_subset : sphere n d 0 ⊆ 0 :=
λ x, by simp [sphere, function.funext_iff] {contextual := tt}

@[simp] lemma sphere_zero_right (n k : ℕ) : sphere (n + 1) 0 k = ∅ := by simp [sphere]

lemma sphere_subset_box : sphere n d k ⊆ box n d := filter_subset _ _

lemma norm_of_mem_sphere {x : fin n → ℕ} (hx : x ∈ sphere n d k) :
  ‖(pi_Lp.equiv 2 _).symm (coe ∘ x : fin n → ℝ)‖ = sqrt k :=
begin
  rw euclidean_space.norm_eq,
  dsimp,
  simp_rw [abs_cast, ←cast_pow, ←cast_sum, (mem_filter.1 hx).2],
end

lemma sphere_subset_preimage_metric_sphere :
  (sphere n d k : set (fin n → ℕ)) ⊆
    (λ x : fin n → ℕ, (pi_Lp.equiv 2 _).symm (coe ∘ x : fin n → ℝ)) ⁻¹'
      metric.sphere (0 : pi_Lp 2 (λ _ : fin n, ℝ)) (sqrt k) :=
λ x hx, by rw [set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]

/-- The map that appears in Behrend's bound on Roth numbers. -/
@[simps] def map (d : ℕ) : (fin n → ℕ) →+ ℕ :=
{ to_fun := λ a, ∑ i, a i * d ^ (i : ℕ),
  map_zero' := by simp_rw [pi.zero_apply, zero_mul, sum_const_zero],
  map_add' := λ a b, by simp_rw [pi.add_apply, add_mul, sum_add_distrib] }

@[simp] lemma map_zero (d : ℕ) (a : fin 0 → ℕ) : map d a = 0 := by simp [map]

lemma map_succ (a : fin (n + 1) → ℕ) : map d a = a 0 + (∑ x : fin n, a x.succ * d ^ (x : ℕ)) * d :=
by simp [map, fin.sum_univ_succ, pow_succ', ←mul_assoc, ←sum_mul]

lemma map_succ' (a : fin (n + 1) → ℕ) : map d a = a 0 + map d (a ∘ fin.succ) * d := map_succ _

lemma map_monotone (d : ℕ) : monotone (map d : (fin n → ℕ) → ℕ) :=
λ x y h, by { dsimp, exact sum_le_sum (λ i _, nat.mul_le_mul_right _ $ h i) }

lemma map_mod (a : fin n.succ → ℕ) : map d a % d = a 0 % d :=
by rw [map_succ, nat.add_mul_mod_self_right]

lemma map_eq_iff {x₁ x₂ : fin n.succ → ℕ} (hx₁ : ∀ i, x₁ i < d) (hx₂ : ∀ i, x₂ i < d) :
  map d x₁ = map d x₂ ↔ x₁ 0 = x₂ 0 ∧ map d (x₁ ∘ fin.succ) = map d (x₂ ∘ fin.succ) :=
begin
  refine ⟨λ h, _, λ h, by rw [map_succ', map_succ', h.1, h.2]⟩,
  have : x₁ 0 = x₂ 0,
  { rw [←mod_eq_of_lt (hx₁ _), ←map_mod, ←mod_eq_of_lt (hx₂ _), ←map_mod, h] },
  rw [map_succ, map_succ, this, add_right_inj, mul_eq_mul_right_iff] at h,
  exact ⟨this, h.resolve_right (pos_of_gt (hx₁ 0)).ne'⟩,
end

lemma map_inj_on : {x : fin n → ℕ | ∀ i, x i < d}.inj_on (map d) :=
begin
  intros x₁ hx₁ x₂ hx₂ h,
  induction n with n ih,
  { simp },
  ext i,
  have x := (map_eq_iff hx₁ hx₂).1 h,
  refine fin.cases x.1 (congr_fun $ ih (λ _, _) (λ _, _) x.2) i,
  { exact hx₁ _ },
  { exact hx₂ _ }
end

lemma map_le_of_mem_box (hx : x ∈ box n d) :
  map (2 * d - 1) x ≤ ∑ i : fin n, (d - 1) * (2 * d - 1) ^ (i : ℕ) :=
map_monotone (2 * d - 1) $ λ _, nat.le_pred_of_lt $ mem_box.1 hx _

lemma add_salem_spencer_sphere : add_salem_spencer (sphere n d k : set (fin n → ℕ)) :=
begin
  set f : (fin n → ℕ) →+ euclidean_space ℝ (fin n) :=
  { to_fun := λ f, (coe : ℕ → ℝ) ∘ f,
    map_zero' := funext $ λ _, cast_zero,
    map_add' := λ _ _, funext $ λ _, cast_add _ _ },
  refine add_salem_spencer.of_image (f.to_add_freiman_hom (sphere n d k) 2) _ _,
  { exact cast_injective.comp_left.inj_on _ },
  refine (add_salem_spencer_sphere 0 $ sqrt k).mono (set.image_subset_iff.2 $ λ x, _),
  rw [set.mem_preimage, mem_sphere_zero_iff_norm],
  exact norm_of_mem_sphere,
end

lemma add_salem_spencer_image_sphere :
  add_salem_spencer ((sphere n d k).image (map (2 * d - 1)) : set ℕ) :=
begin
  rw coe_image,
  refine @add_salem_spencer.image _ (fin n → ℕ) ℕ _ _ (sphere n d k) _ (map (2 * d - 1))
   (map_inj_on.mono _) add_salem_spencer_sphere,
  rw set.add_subset_iff,
  rintro a ha b hb i,
  have hai := mem_box.1 (sphere_subset_box ha) i,
  have hbi := mem_box.1 (sphere_subset_box hb) i,
  rw [lt_tsub_iff_right, ←succ_le_iff, two_mul],
  exact (add_add_add_comm _ _ 1 1).trans_le (add_le_add hai hbi),
end

lemma sum_sq_le_of_mem_box (hx : x ∈ box n d) : ∑ i : fin n, (x i)^2 ≤ n * (d - 1)^2 :=
begin
  rw mem_box at hx,
  have : ∀ i, x i ^ 2 ≤ (d - 1) ^ 2 := λ i, nat.pow_le_pow_of_le_left (nat.le_pred_of_lt (hx i)) _,
  exact (sum_le_card_nsmul univ _ _ $ λ i _, this i).trans (by rw [card_fin, smul_eq_mul]),
end

lemma sum_eq : ∑ i : fin n, d * (2 * d + 1) ^ (i : ℕ) = ((2 * d + 1) ^ n - 1) / 2 :=
begin
  refine (nat.div_eq_of_eq_mul_left zero_lt_two _).symm,
  rw [←sum_range (λ i, d * (2 * d + 1) ^ (i : ℕ)), ←mul_sum, mul_right_comm,  mul_comm d,
    ←geom_sum_mul_add, add_tsub_cancel_right, mul_comm],
end

lemma sum_lt : ∑ i : fin n, d * (2 * d + 1) ^ (i : ℕ) < (2 * d + 1) ^ n :=
sum_eq.trans_lt $ (nat.div_le_self _ 2).trans_lt $ pred_lt (pow_pos (succ_pos _) _).ne'

lemma card_sphere_le_roth_number_nat (n d k : ℕ) :
  (sphere n d k).card ≤ roth_number_nat ((2 * d - 1) ^ n) :=
begin
  cases n,
  { refine (card_le_univ _).trans_eq _,
    rw pow_zero,
    exact fintype.card_unique },
  cases d,
  { simp },
  refine add_salem_spencer_image_sphere.le_roth_number_nat _ _ (card_image_of_inj_on _),
  { simp only [subset_iff, mem_image, and_imp, forall_exists_index, mem_range,
      forall_apply_eq_imp_iff₂, sphere, mem_filter],
    rintro _ x hx _ rfl,
    exact (map_le_of_mem_box hx).trans_lt sum_lt },
  refine map_inj_on.mono (λ x, _),
  simp only [mem_coe, sphere, mem_filter, mem_box, and_imp, two_mul],
  exact λ h _ i, (h i).trans_le le_self_add,
end

/-!
### Optimization

Now that we know how to turn the integer points of any sphere into a Salem-Spencer set, we find a
sphere containing many integer points by the pigeonhole principle. This gives us an implicit bound
that we then optimize by tweaking the parameters. The (almost) optimal parameters are
`behrend.n_value` and `behrend.d_value`.
-/

lemma exists_large_sphere_aux (n d : ℕ) :
  ∃ k ∈ range (n * (d - 1)^2 + 1), (↑(d ^ n) / (↑(n * (d - 1)^2) + 1) : ℝ) ≤ (sphere n d k).card :=
begin
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to (λ x hx, _) nonempty_range_succ _,
  { rw [mem_range, lt_succ_iff],
    exact sum_sq_le_of_mem_box hx },
  { rw [card_range, _root_.nsmul_eq_mul, mul_div_assoc', cast_add_one, mul_div_cancel_left,
      card_box],
    exact (cast_add_one_pos _).ne' }
end

lemma exists_large_sphere (n d : ℕ) : ∃ k, (d ^ n / ↑(n * d^2) : ℝ) ≤ (sphere n d k).card :=
begin
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d,
  refine ⟨k, _⟩,
  obtain rfl | hn := n.eq_zero_or_pos,
  { simp },
  obtain rfl | hd := d.eq_zero_or_pos,
  { simp },
  rw ←cast_pow,
  refine (div_le_div_of_le_left _ _ _).trans hk,
  { exact cast_nonneg _ },
  { exact cast_add_one_pos _ },
  simp only [←le_sub_iff_add_le', cast_mul, ←mul_sub, cast_pow, cast_sub hd, sub_sq,
    one_pow, cast_one, mul_one, sub_add, sub_sub_self],
  apply one_le_mul_of_one_le_of_one_le,
  { rwa one_le_cast },
  rw le_sub_iff_add_le,
  norm_num,
  exact one_le_cast.2 hd,
end

lemma bound_aux' (n d : ℕ) : (d ^ n / ↑(n * d^2) : ℝ) ≤ roth_number_nat ((2 * d - 1)^n) :=
let ⟨k, h⟩ := exists_large_sphere n d in h.trans $ cast_le.2 $ card_sphere_le_roth_number_nat _ _ _

lemma bound_aux (hd : d  ≠ 0) (hn : 2 ≤ n) :
  (d ^ (n - 2) / n : ℝ) ≤ roth_number_nat ((2 * d - 1)^n) :=
begin
  convert bound_aux' n d using 1,
  rw [cast_mul, cast_pow, mul_comm, ←div_div, pow_sub₀ _ _ hn, ←div_eq_mul_inv],
  rwa cast_ne_zero,
end

open_locale filter topology
open real

section numerical_bounds

lemma log_two_mul_two_le_sqrt_log_eight : log 2 * 2 ≤ sqrt (log 8) :=
begin
  rw [show (8 : ℝ) = 2 ^ ((3 : ℕ) : ℝ), by norm_num1, log_rpow zero_lt_two (3:ℕ)],
  apply le_sqrt_of_sq_le,
  rw [mul_pow, sq (log 2), mul_assoc, mul_comm],
  refine mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff,
  apply log_two_lt_d9.le.trans,
  all_goals { norm_num1 }
end

lemma two_div_one_sub_two_div_e_le_eight : 2 / (1 - 2 / exp 1) ≤ 8 :=
begin
  rw [div_le_iff, mul_sub, mul_one, mul_div_assoc', le_sub_comm, div_le_iff (exp_pos _)],
  { linarith [exp_one_gt_d9] },
  rw [sub_pos, div_lt_one];
  exact exp_one_gt_d9.trans' (by norm_num),
end

lemma le_sqrt_log (hN : 4096 ≤ N) : log (2 / (1 - 2 / exp 1)) * (69 / 50) ≤ sqrt (log ↑N) :=
begin
  have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
  { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
    { norm_num1,
      exact_mod_cast hN },
    { exact rpow_pos_of_pos zero_lt_two _ },
    rw cast_pos,
    exact hN.trans_lt' (by norm_num1) },
  refine (mul_le_mul_of_nonneg_right ((log_le_log _ $ by norm_num1).2
    two_div_one_sub_two_div_e_le_eight) $ by norm_num1).trans (_),
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact exp_one_gt_d9.trans_le' (by norm_num1) },
  have l8 : log 8 = (3 : ℕ) * log 2,
  { rw [←log_rpow zero_lt_two, rpow_nat_cast],
    norm_num },
  rw [l8, cast_bit1, cast_one],
  apply le_sqrt_of_sq_le (le_trans _ this),
  simp only [cast_bit0, cast_bit1, cast_one],
  rw [mul_right_comm, mul_pow, sq (log 2), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff' ,
  { exact log_two_lt_d9.le.trans (by norm_num1) },
  exact sq_pos_of_ne_zero _ (by norm_num1),
end

lemma exp_neg_two_mul_le {x : ℝ} (hx : 0 < x) : exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ :=
begin
  have h₁ := ceil_lt_add_one hx.le,
  have h₂ : 1 - x ≤ 2 - ⌈x⌉₊,
  { rw le_sub_iff_add_le,
    apply (add_le_add_left h₁.le _).trans_eq,
    rw [←add_assoc, sub_add_cancel],
    refl },
  have h₃ : exp (-(x+1)) ≤ 1 / (x + 1),
  { rw [exp_neg, inv_eq_one_div],
    refine one_div_le_one_div_of_le (add_pos hx zero_lt_one) _,
    apply le_trans _ (add_one_le_exp_of_nonneg $ add_nonneg hx.le zero_le_one),
    exact le_add_of_nonneg_right zero_le_one },
  refine lt_of_le_of_lt _ (div_lt_div_of_lt_left (exp_pos _) (cast_pos.2 $ ceil_pos.2 hx) h₁),
  refine le_trans _ (div_le_div_of_le_of_nonneg (exp_le_exp.2 h₂) $ add_nonneg hx.le zero_le_one),
  rw [le_div_iff (add_pos hx zero_lt_one), ←le_div_iff' (exp_pos _), ←exp_sub, neg_mul,
    sub_neg_eq_add, two_mul, sub_add_add_cancel, add_comm _ x],
  refine le_trans _ (add_one_le_exp_of_nonneg $ add_nonneg hx.le zero_le_one),
  exact le_add_of_nonneg_right zero_le_one,
end

lemma div_lt_floor {x : ℝ} (hx : 2 / (1 - 2 / exp 1) ≤ x) : x / exp 1 < (⌊x/2⌋₊ : ℝ) :=
begin
  apply lt_of_le_of_lt _ (sub_one_lt_floor _),
  have : 0 < 1 - 2 / exp 1,
  { rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num) exp_one_gt_d9 },
  rwa [le_sub_comm, div_eq_mul_one_div x, div_eq_mul_one_div x, ←mul_sub, div_sub',
    ←div_eq_mul_one_div, mul_div_assoc', one_le_div, ←div_le_iff this],
  { exact zero_lt_two },
  { exact two_ne_zero }
end

lemma ceil_lt_mul {x : ℝ} (hx : 50/19 ≤ x) : (⌈x⌉₊ : ℝ) < 1.38 * x :=
begin
  refine (ceil_lt_add_one $ hx.trans' $ by norm_num).trans_le _,
  rwa [←le_sub_iff_add_le', ←sub_one_mul, show (69/50 - 1 : ℝ) = (50/19)⁻¹, by norm_num1,
    ←div_eq_inv_mul, one_le_div],
  norm_num1,
end

end numerical_bounds

/-- The (almost) optimal value of `n` in `behrend.bound_aux`. -/
noncomputable def n_value (N : ℕ) : ℕ := ⌈sqrt (log N)⌉₊

/-- The (almost) optimal value of `d` in `behrend.bound_aux`. -/
noncomputable def d_value (N : ℕ) : ℕ := ⌊(N : ℝ)^(1 / n_value N : ℝ)/2⌋₊

lemma n_value_pos (hN : 2 ≤ N) : 0 < n_value N :=
ceil_pos.2 $ real.sqrt_pos.2 $ log_pos $ one_lt_cast.2 $ hN

lemma two_le_n_value (hN : 3 ≤ N) : 2 ≤ n_value N :=
begin
  refine succ_le_of_lt (lt_ceil.2 $ lt_sqrt_of_sq_lt _),
  rw [cast_one, one_pow, lt_log_iff_exp_lt],
  refine lt_of_lt_of_le _ (cast_le.2 hN),
  { exact exp_one_lt_d9.trans_le (by norm_num) },
  rw cast_pos,
  exact (zero_lt_succ _).trans_le hN,
end

lemma three_le_n_value (hN : 64 ≤ N) : 3 ≤ n_value N :=
begin
  rw [n_value, ←lt_iff_add_one_le, lt_ceil, cast_two],
  apply lt_sqrt_of_sq_lt,
  have : (2 : ℝ)^((6 : ℕ) : ℝ) ≤ N,
  { rw rpow_nat_cast,
    exact (cast_le.2 hN).trans' (by norm_num1) },
  apply lt_of_lt_of_le _ ((log_le_log (rpow_pos_of_pos zero_lt_two _) _).2 this),
  rw [log_rpow zero_lt_two, cast_bit0, cast_bit1, cast_one, ←div_lt_iff'],
  { exact log_two_gt_d9.trans_le' (by norm_num1) },
  { norm_num1 },
  rw cast_pos,
  exact hN.trans_lt' (by norm_num1),
end

lemma d_value_pos (hN₃ : 8 ≤ N) : 0 < d_value N :=
begin
  have hN₀ : 0 < (N : ℝ) := cast_pos.2 (succ_pos'.trans_le hN₃),
  rw [d_value, floor_pos, ←log_le_log zero_lt_one, log_one, log_div _ two_ne_zero, log_rpow hN₀,
    div_mul_eq_mul_div, one_mul, sub_nonneg, le_div_iff],
  { have : (n_value N : ℝ) ≤ 2 * sqrt (log N),
    { apply (ceil_lt_add_one $ sqrt_nonneg _).le.trans,
      rw [two_mul, add_le_add_iff_left],
      apply le_sqrt_of_sq_le,
      rw [one_pow, le_log_iff_exp_le hN₀],
      exact (exp_one_lt_d9.le.trans $ by norm_num).trans (cast_le.2 hN₃) },
    apply (mul_le_mul_of_nonneg_left this $ log_nonneg one_le_two).trans _,
    rw [←mul_assoc, ←le_div_iff (real.sqrt_pos.2 $ log_pos $ one_lt_cast.2 _), div_sqrt],
    { apply log_two_mul_two_le_sqrt_log_eight.trans,
      apply real.sqrt_le_sqrt,
      rw log_le_log _ hN₀,
      { exact_mod_cast hN₃ },
      { norm_num } },
    exact hN₃.trans_lt' (by norm_num) },
  { exact cast_pos.2 (n_value_pos $ hN₃.trans' $ by norm_num) },
  { exact (rpow_pos_of_pos hN₀ _).ne' },
  { exact div_pos (rpow_pos_of_pos hN₀ _) zero_lt_two },
end

lemma le_N (hN : 2 ≤ N) : (2 * (d_value N) - 1)^(n_value N) ≤ N :=
begin
  have : (2 * d_value N - 1)^(n_value N) ≤ (2 * d_value N)^(n_value N) :=
    nat.pow_le_pow_of_le_left (nat.sub_le _ _) _,
  apply this.trans,
  suffices : ((2 * d_value N)^n_value N : ℝ) ≤ N, by exact_mod_cast this,
  rw ←rpow_nat_cast,
  suffices i : (2 * d_value N : ℝ) ≤ (N : ℝ)^(1/n_value N : ℝ),
  { apply (rpow_le_rpow (mul_nonneg zero_le_two (cast_nonneg _)) i (cast_nonneg _)).trans,
    rw [←rpow_mul (cast_nonneg _), one_div_mul_cancel, rpow_one],
    rw cast_ne_zero,
    apply (n_value_pos hN).ne', },
  rw ←le_div_iff',
  { exact floor_le (div_nonneg (rpow_nonneg_of_nonneg (cast_nonneg _) _) zero_le_two) },
  apply zero_lt_two
end

lemma bound (hN : 4096 ≤ N) : (N : ℝ)^(1/n_value N : ℝ) / exp 1 < d_value N :=
begin
  apply div_lt_floor _,
  rw [←log_le_log, log_rpow, mul_comm, ←div_eq_mul_one_div],
  { apply le_trans _ (div_le_div_of_le_left _ _ (ceil_lt_mul _).le),
    rw [mul_comm, ←div_div, div_sqrt, le_div_iff],
    { exact le_sqrt_log hN },
    { norm_num1 },
    { apply log_nonneg,
      rw one_le_cast,
      exact hN.trans' (by norm_num1) },
    { rw [cast_pos, lt_ceil, cast_zero, real.sqrt_pos],
      refine log_pos _,
      rw one_lt_cast,
      exact hN.trans_lt' (by norm_num1) },
    apply le_sqrt_of_sq_le,
    have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
    { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
      { norm_num1,
        exact_mod_cast hN },
      { exact rpow_pos_of_pos zero_lt_two _ },
      rw cast_pos,
      exact hN.trans_lt' (by norm_num1) },
    refine le_trans _ this,
    simp only [cast_bit0, cast_bit1, cast_one],
    rw ←div_le_iff',
    { exact log_two_gt_d9.le.trans' (by norm_num1) },
    { norm_num1 } },
  { rw cast_pos,
    exact hN.trans_lt' (by norm_num1) },
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9 },
  apply rpow_pos_of_pos,
  rw cast_pos,
  exact hN.trans_lt' (by norm_num1),
end

lemma roth_lower_bound_explicit (hN : 4096 ≤ N) :
  (N : ℝ) * exp (-4 * sqrt (log N)) < roth_number_nat N :=
begin
  let n := n_value N,
  have hn : 0 < (n : ℝ) := cast_pos.2 (n_value_pos $ hN.trans' $ by norm_num1),
  have hd : 0 < d_value N := d_value_pos (hN.trans' $ by norm_num1),
  have hN₀ : 0 < (N : ℝ) := cast_pos.2 (hN.trans' $ by norm_num1),
  have hn₂ : 2 ≤ n := two_le_n_value (hN.trans' $ by norm_num1),
  have : (2 * d_value N - 1)^n ≤ N := le_N (hN.trans' $ by norm_num1),
  refine ((bound_aux hd.ne' hn₂).trans $ cast_le.2 $ roth_number_nat.mono this).trans_lt' _,
  refine (div_lt_div_of_lt hn $ pow_lt_pow_of_lt_left (bound hN) _ _).trans_le' _,
  { exact div_nonneg (rpow_nonneg_of_nonneg (cast_nonneg _) _) (exp_pos _).le },
  { exact tsub_pos_of_lt (three_le_n_value $ hN.trans' $ by norm_num1) },
  rw [←rpow_nat_cast, div_rpow (rpow_nonneg_of_nonneg hN₀.le _) (exp_pos _).le, ←rpow_mul hN₀.le,
    mul_comm (_ / _), mul_one_div, cast_sub hn₂, cast_two, same_sub_div hn.ne', exp_one_rpow,
    div_div, rpow_sub hN₀, rpow_one, div_div, div_eq_mul_inv],
  refine mul_le_mul_of_nonneg_left _ (cast_nonneg _),
  rw [mul_inv, mul_inv, ←exp_neg, ←rpow_neg (cast_nonneg _), neg_sub, ←div_eq_mul_inv],
  have : exp ((-4) * sqrt (log N)) = exp (-2 * sqrt (log N)) * exp (-2 * sqrt (log N)),
  { rw [←exp_add, ←add_mul],
    norm_num },
  rw this,
  refine (mul_le_mul _ (exp_neg_two_mul_le $ real.sqrt_pos.2 $ log_pos _).le (exp_pos _).le $
    rpow_nonneg_of_nonneg (cast_nonneg _) _),
  { rw [←le_log_iff_exp_le (rpow_pos_of_pos hN₀ _), log_rpow hN₀, ←le_div_iff, mul_div_assoc,
      div_sqrt, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff hn],
    { exact mul_le_mul_of_nonneg_left (le_ceil _) zero_le_two },
    refine real.sqrt_pos.2 (log_pos _),
    rw one_lt_cast,
    exact hN.trans_lt' (by norm_num1) },
  { rw one_lt_cast,
    exact hN.trans_lt' (by norm_num1) }
end

lemma exp_four_lt : exp 4 < 64 :=
begin
  rw [show (64 : ℝ) = 2 ^ ((6 : ℕ) : ℝ), by norm_num1,
    ←lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two, ←div_lt_iff'],
  exact log_two_gt_d9.trans_le' (by norm_num1),
  norm_num
end

lemma four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 :=
begin
  rw [←log_lt_iff_lt_exp (show (0 : ℝ) < 4096, by norm_num), show (4096 : ℝ) = 2 ^ 12, by norm_num,
    ←rpow_nat_cast, log_rpow zero_lt_two, cast_bit0, cast_bit0, cast_bit1, cast_one],
  linarith [log_two_lt_d9],
end

lemma lower_bound_le_one' (hN : 2 ≤ N) (hN' : N ≤ 4096) : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  rw [←log_le_log (mul_pos (cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one,
    log_one, log_mul (cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne', log_exp,
    neg_mul, ←sub_eq_add_neg, sub_nonpos, ←div_le_iff (real.sqrt_pos.2 $ log_pos $
    one_lt_cast.2 $ one_lt_two.trans_le hN), div_sqrt, sqrt_le_left
    (zero_le_bit0.2 zero_le_two), log_le_iff_le_exp (cast_pos.2 (zero_lt_two.trans_le hN))],
  norm_num1,
  apply le_trans _ four_zero_nine_six_lt_exp_sixteen.le,
  exact_mod_cast hN',
end

lemma lower_bound_le_one (hN : 1 ≤ N) (hN' : N ≤ 4096) : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  obtain rfl | hN := hN.eq_or_lt,
  { norm_num },
  { exact lower_bound_le_one' hN hN' }
end

lemma roth_lower_bound : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ roth_number_nat N :=
begin
  obtain rfl | hN := nat.eq_zero_or_pos N,
  { norm_num },
  obtain h₁ | h₁ := le_or_lt 4096 N,
  { exact (roth_lower_bound_explicit h₁).le },
  { apply (lower_bound_le_one hN h₁.le).trans,
    simpa using roth_number_nat.monotone hN }
end

end behrend
