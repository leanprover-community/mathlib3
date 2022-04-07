/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import analysis.inner_product_space.pi_L2
import combinatorics.additive.salem_spencer
import data.complex.exponential_bounds

/-!
# Behrend bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers.
-/

open finset nat
open_locale big_operators

variables {α β : Type*}

namespace behrend

def sphere (n d : ℕ) : finset (fin n → ℕ) := fintype.pi_finset (λ _, range d)

lemma mem_sphere {n d : ℕ} (x : fin n → ℕ) : x ∈ sphere n d ↔ ∀ i, x i < d := by simp [sphere]

lemma bound_of_mem_sphere {n d : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere n d) : ∀ i, x i < d :=
(mem_sphere _).1 hx

def sphere_slice (n d k : ℕ) : finset (fin n → ℕ) := (sphere n d).filter (λ x, ∑ i, x i^2 = k)

lemma sphere_slice_zero {n d : ℕ} : sphere_slice n d 0 ⊆ {λ _, 0} :=
begin
  intros x hx,
  simp only [sphere_slice, nat.succ_pos', sum_eq_zero_iff, mem_filter, mem_univ, forall_true_left,
    pow_eq_zero_iff] at hx,
  simp only [mem_singleton, function.funext_iff],
  apply hx.2
end

lemma sphere_to_nat_mod {n d : ℕ} (a : fin n.succ → ℕ) : from_digits d a % d = a 0 % d :=
by rw [from_digits_succ, nat.add_mul_mod_self_right]

lemma sphere_to_nat_eq_iff {n d : ℕ} {x₁ x₂ : fin n.succ → ℕ} (hx₁ : ∀ i, x₁ i < d)
  (hx₂ : ∀ i, x₂ i < d) :
  from_digits d x₁ = from_digits d x₂ ↔
    x₁ 0 = x₂ 0 ∧ from_digits d (x₁ ∘ fin.succ) = from_digits d (x₂ ∘ fin.succ) :=
begin
  split,
  { intro h,
    have : from_digits d x₁ % d = from_digits d x₂ % d,
    { rw h },
    simp only [sphere_to_nat_mod, nat.mod_eq_of_lt (hx₁ _), nat.mod_eq_of_lt (hx₂ _)] at this,
    refine ⟨this, _⟩,
    rw [from_digits_succ, from_digits_succ, this, add_right_inj, mul_eq_mul_right_iff] at h,
    apply or.resolve_right h,
    apply (lt_of_le_of_lt (nat.zero_le _) (hx₁ 0)).ne' },
  rintro ⟨h₁, h₂⟩,
  rw [from_digits_succ', from_digits_succ', h₁, h₂],
end

lemma sphere_to_nat_inj_on {n d : ℕ} : set.inj_on (from_digits d) {x : fin n → ℕ | ∀ i, x i < d} :=
begin
  simp only [set.inj_on, set.mem_set_of_eq],
  intros x₁ hx₁ x₂ hx₂ h,
  induction n with n ih,
  { simp },
  ext i,
  have x := (sphere_to_nat_eq_iff hx₁ hx₂).1 h,
  refine fin.cases x.1 (function.funext_iff.1 (ih (λ _, _) (λ _, _) x.2)) i,
  { exact hx₁ _ },
  { exact hx₂ _ }
end

-- lemma sum_mul_sq_le_sq_mul_sq' {α : Type*} (s : finset α) (f g : α → ℝ)  :
--   (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
-- begin
--   simp only [←finset.sum_finset_coe _ s, pow_two],
--   exact real_inner_mul_inner_self_le (show euclidean_space ℝ s, from f ∘ coe)
--     (show euclidean_space ℝ s, from g ∘ coe),
-- end

-- theorem inner_eq_norm_mul_iff_real {F : Type u_3} [inner_product_space ℝ F] {x y : F} :
-- inner x y = ∥x∥ * ∥y∥ ↔ ∥y∥ • x = ∥x∥ • y

lemma sphere_strictly_convex {F : Type*} [inner_product_space ℝ F] {x y : F} (h : ∥x∥ = ∥y∥)
  (hx : x ≠ 0) (hxy : x ≠ y) : ∥(1/2 : ℝ) • (x + y)∥ < ∥x∥ :=
begin
  have := @inner_eq_norm_mul_iff_real _ _ x y,
  apply lt_of_pow_lt_pow 2 (norm_nonneg _) _,
  rw [norm_smul, mul_pow, norm_add_sq_real, h, add_right_comm, ←two_mul, ←mul_add, ←mul_assoc],
  suffices : inner x y < ∥y∥^2,
  { norm_num,
    linarith },
  apply lt_of_le_of_ne,
  { simpa [h, sq] using real_inner_le_norm x y },
  rw h at this,
  simp only [←sq] at this,
  rw [ne.def, this],
  refine (smul_right_injective _ _).ne hxy,
  rw ←h,
  simpa [←h] using hx,
end

lemma slice_norm {n d k : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere_slice n d k) :
  @has_norm.norm (euclidean_space ℝ (fin n)) _ (coe ∘ x : fin n → ℝ) = real.sqrt k :=
begin
  sorry --time out
  -- rw pi_Lp.norm_eq_of_L2,
  -- simp only [real.norm_coe_nat, function.comp_app, ←nat.cast_pow, ←nat.cast_sum],
  -- congr' 2,
  -- simp only [sphere_slice, mem_filter] at hx,
  -- apply hx.2
end

lemma add_salem_spencer_sphere_slice (n d : ℕ) {k : ℕ} :
  add_salem_spencer (sphere_slice n d k : set (fin n → ℕ)) :=
begin
  intros x z y hx hz hy hxyz,
  rcases nat.eq_zero_or_pos k with rfl | hk,
  { rw [mem_singleton.1 (sphere_slice_zero hx), mem_singleton.1 (sphere_slice_zero hz)] },
  let x' : euclidean_space ℝ (fin n) := (coe ∘ x : fin n → ℝ),
  let y' : euclidean_space ℝ (fin n) := (coe ∘ y : fin n → ℝ),
  let z' : euclidean_space ℝ (fin n) := (coe ∘ z : fin n → ℝ),
  have : x' + z' = y' + y',
  { simpa [function.funext_iff, ←nat.cast_add] using hxyz },
  by_contra hxz,
  have nxz : x' ≠ z',
  { simpa [function.funext_iff] using hxz },
  have nxy : x' ≠ y',
  { intro t,
    apply nxz,
    rw ←t at this,
    exact add_right_injective _ this.symm },
  have yeq : (1 / 2 : ℝ) • (x' + z') = y',
  { rw [one_div, inv_smul_eq_iff₀ (show (2 : ℝ) ≠ 0, by norm_num)],
    simp only [function.funext_iff, pi.add_apply] at hxyz,
    ext j,
    simp only [algebra.id.smul_eq_mul, pi.add_apply, pi.smul_apply, ←nat.cast_add, two_mul,
      nat.cast_inj, hxyz] },
  have xz : ∥x'∥ = ∥z'∥,
  { simp only [slice_norm hx, slice_norm hz] },
  have i₂ := @sphere_strictly_convex (euclidean_space ℝ (fin n)) _ x' z' xz _ nxz,
  { rw [yeq, slice_norm hx, slice_norm hy] at i₂,
    simpa using i₂ },
  suffices : ∥x'∥ ≠ 0,
  { simpa using this },
  rw slice_norm hx,
  simp [hk.ne'],
end

lemma add_salem_spencer_image_slice {n d k : ℕ} :
  add_salem_spencer ((finset.image (from_digits (2 * d - 1)) (sphere_slice n d k)) : set ℕ) :=
begin
  -- rw add_salem_spencer_iff_eq_right,
  rintro a b c ha hb hc,
  rw [mem_coe, mem_image] at ha hb hc,
  obtain ⟨x, hx, rfl⟩ := ha,
  obtain ⟨y, hy, rfl⟩ := hc,
  obtain ⟨z, hz, rfl⟩ := hb,
  have hx' : ∀ i, x i < d := bound_of_mem_sphere (mem_filter.1 hx).1,
  have hy' : ∀ i, y i < d := bound_of_mem_sphere (mem_filter.1 hy).1,
  have hz' : ∀ i, z i < d := bound_of_mem_sphere (mem_filter.1 hz).1,
  rw [←from_digits_two_add hx' hz', ←from_digits_two_add hy' hy'],
  rintro (t : from_digits (2 * d - 1) (x + z) = from_digits (2 * d - 1) (y + y)),
  rw sphere_to_nat_inj_on.eq_iff (λ i, (hx' i).trans_le $ le_succ_mul_neg _ _)
    (λ i, (hz' i).trans_le $ le_succ_mul_neg _ _),
  rw sphere_to_nat_inj_on.eq_iff (sum_bound hx' hz') (sum_bound hy' hy') at t,
  exact add_salem_spencer_sphere_slice n d hx hz hy t,
end

@[simp] lemma sphere_size {n d : ℕ} : (sphere n d).card = d ^ n := by simp [sphere]

lemma sum_squares_bound_of_le {n d : ℕ} (x : fin n → ℕ) (hx : x ∈ sphere n d) :
  ∑ (i : fin n), (x i)^2 ≤ n * (d - 1)^2 :=
begin
  simp only [mem_sphere] at hx,
  have : ∀ i, x i^2 ≤ (d - 1)^2,
  { intro i,
    apply nat.pow_le_pow_of_le_left,
    apply nat.le_pred_of_lt (hx i) },
  refine (finset.sum_le_card_nsmul univ _ _ $ λ i _, this i).trans _,
  simp,
end

lemma le_of_mem_sphere {n d : ℕ} : ∀ x ∈ sphere n d, x ≤ (λ i, d - 1) :=
λ x hx i, nat.le_pred_of_lt (bound_of_mem_sphere hx i)

lemma from_digits_le_of_mem_sphere {n d : ℕ} :
  ∀ x ∈ sphere n d, from_digits (2 * d - 1) x ≤ ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) :=
λ x hx, from_digits_monotone (2 * d - 1) (le_of_mem_sphere x hx)

lemma behrend_bound_aux1 {n d k N : ℕ} (hd : 0 < d) (hN : (2 * d - 1)^n ≤ N):
  (sphere_slice n d k).card ≤ roth_number_nat N :=
begin
  refine add_salem_spencer_image_slice.le_roth_number_nat _ _ (card_image_of_inj_on _),
  { simp only [subset_iff, mem_image, and_imp, forall_exists_index, mem_range,
      forall_apply_eq_imp_iff₂, sphere_slice, mem_filter],
    rintro _ x hx _ rfl,
    apply ((from_digits_le_of_mem_sphere x hx).trans_lt (digits_sum_le hd)).trans_le hN },
  refine set.inj_on.mono (λ x, _) sphere_to_nat_inj_on,
  simp only [mem_coe, sphere_slice, mem_filter, mem_sphere, and_imp, set.mem_set_of_eq],
  exact λ h₁ h₂ i, (h₁ i).trans_le (le_succ_mul_neg _ _),
end

lemma large_slice_aux (n d : ℕ) :
  ∃ k ∈ range (n * (d - 1)^2 + 1),
    (↑(d ^ n) / (↑(n * (d - 1)^2) + 1) : ℝ) ≤ (sphere_slice n d k).card :=
begin
  apply exists_le_card_fiber_of_mul_le_card_of_maps_to',
  { intros x hx,
    rw [mem_range, nat.lt_succ_iff],
    apply sum_squares_bound_of_le _ hx },
  { simp },
  { rw [card_range, _root_.nsmul_eq_mul, mul_div_assoc', nat.cast_add_one, mul_div_cancel_left],
    { simp },
    exact (nat.cast_add_one_pos _).ne' }
end

lemma large_slice {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
  ∃ k, (d ^ n / ↑(n * d^2) : ℝ) ≤ (sphere_slice n d k).card :=
begin
  obtain ⟨k, -, hk⟩ := large_slice_aux n d,
  refine ⟨k, _⟩,
  rw ←nat.cast_pow,
  refine (div_le_div_of_le_left _ _ _).trans hk,
  { exact nat.cast_nonneg _ },
  { exact nat.cast_add_one_pos _ },
  simp only [←le_sub_iff_add_le', nat.cast_mul, ←mul_sub, nat.cast_pow, nat.cast_sub hd, sub_sq,
    one_pow, nat.cast_one, mul_one, sub_add, sub_sub_self],
  apply one_le_mul_of_one_le_of_one_le,
  { rwa nat.one_le_cast },
  rw le_sub_iff_add_le,
  norm_num,
  exact le_mul_of_one_le_right zero_le_two (nat.one_le_cast.2 hd),
end

lemma behrend_bound_aux2 {n d N : ℕ} (hd : 0 < d) (hn : 0 < n) (hN : (2 * d - 1)^n ≤ N):
  (d ^ n / ↑(n * d^2) : ℝ) ≤ roth_number_nat N :=
begin
  obtain ⟨k, _⟩ := large_slice hn hd,
  apply h.trans,
  rw nat.cast_le,
  apply behrend_bound_aux1 hd hN,
end

lemma behrend_bound_aux3 {n d N : ℕ} (hd : 0 < d) (hn : 2 ≤ n) (hN : (2 * d - 1)^n ≤ N):
  (d ^ (n - 2) / n : ℝ) ≤ roth_number_nat N :=
begin
  convert behrend_bound_aux2 hd (zero_lt_two.trans_le hn) hN using 1,
  rw [nat.cast_mul, nat.cast_pow, mul_comm, ←div_div_eq_div_mul, pow_sub₀ _ _ hn, ←div_eq_mul_inv],
  rw nat.cast_ne_zero,
  apply hd.ne',
end

open_locale filter topological_space
open real

variables {N : ℕ}

lemma two_pow_log_two_lt : (2 : ℝ) ^ log 2 < 2 :=
begin
  have : real.log 2 < 1 := log_two_lt_d9.trans_le (by norm_num),
  simpa using rpow_lt_rpow_of_exponent_lt one_lt_two this,
end

noncomputable def n_value (N : ℕ) : ℕ := ⌈sqrt (real.log N)⌉₊
noncomputable def d_value (N : ℕ) : ℕ := ⌊(N:ℝ)^(1/n_value N:ℝ)/2⌋₊

lemma n_value_pos {N : ℕ} (hN : 2 ≤ N) : 0 < n_value N :=
begin
  rw [pos_iff_ne_zero, n_value, ne.def, nat.ceil_eq_zero, not_le, real.sqrt_pos],
  refine log_pos _,
  rw nat.one_lt_cast,
  apply hN
end

lemma two_le_n_value {N : ℕ} (hN : 3 ≤ N) : 2 ≤ n_value N :=
begin
  rw [n_value],
  apply nat.succ_le_of_lt,
  rw [nat.lt_ceil, nat.cast_one],
  apply lt_sqrt_of_sq_lt,
  rw [one_pow, lt_log_iff_exp_lt],
  refine lt_of_lt_of_le _ (nat.cast_le.2 hN),
  { exact exp_one_lt_d9.trans_le (by norm_num) },
  rw nat.cast_pos,
  exact lt_of_lt_of_le (by norm_num) hN,
end

lemma three_le_n_value {N : ℕ} (hN : 64 ≤ N) : 3 ≤ n_value N :=
begin
  rw [n_value, ←nat.lt_iff_add_one_le, nat.lt_ceil, nat.cast_two],
  apply lt_sqrt_of_sq_lt,
  have : (2 : ℝ)^((6 : ℕ) : ℝ) ≤ N,
  { rw rpow_nat_cast,
    refine le_trans _ (nat.cast_le.2 hN),
    norm_num1 },
  apply lt_of_lt_of_le _ ((log_le_log (rpow_pos_of_pos zero_lt_two _) _).2 this),
  rw [log_rpow zero_lt_two, nat.cast_bit0, nat.cast_bit1, nat.cast_one, ←div_lt_iff'],
  { exact lt_of_le_of_lt (by norm_num1) log_two_gt_d9 },
  { norm_num1 },
  rw nat.cast_pos,
  exact lt_of_lt_of_le (by norm_num1) hN,
end

lemma log_two_mul_two_le_sqrt_log_eight : real.log 2 * 2 ≤ sqrt (log 8) :=
begin
  suffices : real.log 2 * 2 ≤ sqrt ((3:ℕ) * log 2),
  { rw [←log_rpow zero_lt_two (3:ℕ), rpow_nat_cast] at this,
    norm_num at this,
    apply this },
  apply le_sqrt_of_sq_le,
  rw [mul_pow, sq (real.log 2), mul_assoc, mul_comm],
  refine mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff,
  apply log_two_lt_d9.le.trans,
  all_goals { norm_num }
end

lemma d_value_pos {N : ℕ} (hN₃ : 8 ≤ N) : 0 < d_value N :=
begin
  have hN₀ : 0 < (N:ℝ) := nat.cast_pos.2 (nat.succ_pos'.trans_le hN₃),
  rw [d_value, nat.floor_pos, ←log_le_log zero_lt_one, log_one, log_div _ two_ne_zero, log_rpow hN₀,
    div_mul_eq_mul_div, one_mul, sub_nonneg, le_div_iff],
  { have : (n_value N : ℝ) ≤ 2 * sqrt (log N),
    { apply (nat.ceil_lt_add_one (sqrt_nonneg _)).le.trans,
      rw [two_mul, add_le_add_iff_left],
      apply le_sqrt_of_sq_le,
      rw [one_pow, le_log_iff_exp_le hN₀],
      exact (exp_one_lt_d9.le.trans (by norm_num)).trans (nat.cast_le.2 hN₃) },
    apply (mul_le_mul_of_nonneg_left this (log_nonneg one_le_two)).trans _,
    rw [←mul_assoc, ←le_div_iff (real.sqrt_pos.2 (log_pos (nat.one_lt_cast.2 _))), div_sqrt],
    { apply log_two_mul_two_le_sqrt_log_eight.trans,
      apply real.sqrt_le_sqrt,
      rw log_le_log _ hN₀,
      { exact_mod_cast hN₃ },
      { norm_num } },
    exact lt_of_lt_of_le (by norm_num) hN₃ },
  { exact nat.cast_pos.2 (n_value_pos ((show 2 ≤ 8, by norm_num).trans hN₃)) },
  { apply (rpow_pos_of_pos hN₀ _).ne' },
  { exact div_pos (rpow_pos_of_pos hN₀ _) zero_lt_two },
end

lemma le_N (hN : 2 ≤ N) : (2 * (d_value N) - 1)^(n_value N) ≤ N :=
begin
  have : (2 * d_value N - 1)^(n_value N) ≤ (2 * d_value N)^(n_value N) :=
    nat.pow_le_pow_of_le_left (nat.sub_le _ _) _,
  apply this.trans,
  suffices : ((2 * d_value N)^n_value N : ℝ) ≤ N, by exact_mod_cast this,
  rw ←rpow_nat_cast,
  suffices i : (2 * d_value N : ℝ) ≤ (N:ℝ)^(1/n_value N:ℝ),
  { apply (rpow_le_rpow (mul_nonneg zero_le_two (nat.cast_nonneg _)) i (nat.cast_nonneg _)).trans,
    rw [←rpow_mul (nat.cast_nonneg _), one_div_mul_cancel, rpow_one],
    rw nat.cast_ne_zero,
    apply (n_value_pos hN).ne', },
  rw ←le_div_iff',
  { exact nat.floor_le (div_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) zero_le_two) },
  apply zero_lt_two
end

lemma floor_lt_mul {x : ℝ} (hx : 2 / (1 - 2 / exp 1) ≤ x) :
  x / exp 1 < (⌊x/2⌋₊ : ℝ) :=
begin
  apply lt_of_le_of_lt _ (nat.sub_one_lt_floor _),
  have : 0 < 1 - 2 / exp 1,
  { rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num) exp_one_gt_d9 },
  rwa [le_sub, div_eq_mul_one_div x, div_eq_mul_one_div x, ←mul_sub, div_sub', ←div_eq_mul_one_div,
    mul_div_assoc', one_le_div, ←div_le_iff this],
  { exact zero_lt_two },
  { exact two_ne_zero }
end

lemma ceil_lt_mul {x : ℝ} (hx : 50/19 ≤ x) :
  (⌈x⌉₊ : ℝ) < 1.38 * x :=
begin
  refine (nat.ceil_lt_add_one (le_trans (by norm_num) hx)).trans_le _,
  rw [←le_sub_iff_add_le', div_mul_eq_mul_div, div_sub', one_le_div, ←sub_mul],
  linarith,
  norm_num,
  norm_num,
end

lemma weird_bound :
  2 / (1 - 2 / exp 1) ≤ 8 :=
begin
  rw [div_le_iff, mul_sub, mul_one, mul_div_assoc', le_sub, div_le_iff (exp_pos _)],
  { linarith [exp_one_gt_d9] },
  rw [sub_pos, div_lt_one];
  exact lt_trans (by norm_num) exp_one_gt_d9,
end

lemma annoying_bound (hN : 4096 ≤ N) :
  log (2 / (1 - 2 / exp 1)) * (69 / 50) ≤ sqrt (log ↑N) :=
begin
  have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
  { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
    { norm_num1,
      exact_mod_cast hN },
    { apply rpow_pos_of_pos zero_lt_two },
    rw nat.cast_pos,
    apply lt_of_lt_of_le _ hN,
    norm_num1 },
  refine (mul_le_mul_of_nonneg_right ((log_le_log _ (by norm_num1)).2 weird_bound) _).trans _,
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9 },
  { norm_num1 },
  have l8 : real.log 8 = (3 : ℕ) * log 2,
  { rw [←log_rpow zero_lt_two, rpow_nat_cast],
    norm_num },
  rw [l8, nat.cast_bit1, nat.cast_one],
  apply le_sqrt_of_sq_le (le_trans _ this),
  simp only [nat.cast_bit0, nat.cast_bit1, nat.cast_one],
  rw [mul_right_comm, mul_pow, sq (real.log 2), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff',
  { apply log_two_lt_d9.le.trans,
    norm_num1 },
  apply sq_pos_of_ne_zero,
  norm_num1,
end

lemma bound (hN : 4096 ≤ N) : (N:ℝ)^(1/n_value N:ℝ) / exp 1 < d_value N :=
begin
  apply floor_lt_mul _,
  rw [←log_le_log, log_rpow, mul_comm, ←div_eq_mul_one_div],
  { apply le_trans _ (div_le_div_of_le_left _ _ (ceil_lt_mul _).le),
    rw [mul_comm, ←div_div_eq_div_mul, div_sqrt, le_div_iff],
    { apply annoying_bound hN },
    { apply div_pos;
      norm_num1 },
    { apply log_nonneg,
      rw nat.one_le_cast,
      exact le_trans (by norm_num1) hN },
    { rw [nat.cast_pos, nat.lt_ceil, nat.cast_zero, real.sqrt_pos],
      apply real.log_pos,
      rw nat.one_lt_cast,
      exact lt_of_lt_of_le (by norm_num1) hN },
    apply le_sqrt_of_sq_le,
    have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
    { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
      { norm_num1,
        exact_mod_cast hN },
      { apply rpow_pos_of_pos zero_lt_two },
      rw nat.cast_pos,
      apply lt_of_lt_of_le _ hN,
      norm_num1 },
    refine le_trans _ this,
    simp only [nat.cast_bit0, nat.cast_bit1, nat.cast_one],
    rw ←div_le_iff',
    { refine le_trans (by norm_num1) log_two_gt_d9.le },
    { norm_num1 } },
  { rw nat.cast_pos,
    exact lt_of_lt_of_le (by norm_num1) hN },
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9 },
  apply rpow_pos_of_pos,
  rw nat.cast_pos,
  exact lt_of_lt_of_le (by norm_num1) hN,
end

lemma lower_bound_increasing_comp {c : ℝ} : monotone_on (λ x, x * (x - c)) (set.Ici (c/2)) :=
begin
  apply (convex_Ici _).monotone_on_of_deriv_nonneg,
  { exact continuous_on_id.mul (continuous_on_id.sub continuous_on_const) },
  { exact differentiable_on_id.mul (differentiable_on_id.sub (differentiable_on_const _)) },
  intros x hx,
  simp only [interior_Ici, set.mem_Ioi, div_lt_iff', zero_lt_two] at hx,
  simp_rw [mul_sub, ←sq],
  simpa using hx.le,
end

lemma lower_bound_increasing (c : ℝ) :
  monotone_on (λ N, N * exp (-c * sqrt (log N))) (set.Ici $ exp $ (c/2)^2) :=
begin
  have pos : set.Ici (exp ((c/2)^2)) ⊆ set.Ioi 0 := λ x hx, (exp_pos _).trans_le hx,
  have : set.eq_on (λ N, N * exp (-c * sqrt (log N))) (λ N, exp (sqrt (log N) * (sqrt (log N) - c)))
    (set.Ici (exp ((c/2)^2))),
  { intros x hx,
    dsimp,
    rw set.mem_Ici at hx,
    rw [mul_sub, mul_self_sqrt, sub_eq_add_neg, exp_add, neg_mul, exp_log, mul_comm c],
    { exact pos hx },
    refine log_nonneg _,
    apply le_trans _ hx,
    apply one_le_exp_iff.2 (sq_nonneg _) },
  apply monotone_on.congr _ this.symm,
  apply monotone.comp_monotone_on,
  { apply exp_monotone },
  intros x hx y hy xy,
  apply lower_bound_increasing_comp _ _ (sqrt_le_sqrt ((log_le_log (pos hx) (pos hy)).2 xy));
  { rw [set.mem_Ici],
    apply le_sqrt_of_sq_le,
    rw le_log_iff_exp_le (pos _);
    assumption },
end

lemma lower_bound_increasing' : monotone_on (λ N, N * exp (-4 * sqrt (log N))) (set.Ici (exp 4)) :=
begin
  convert lower_bound_increasing 4,
  norm_num1
end

lemma exp_thing {x : ℝ} (hx : 0 < x) : exp (- 2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ :=
begin
  have i := nat.ceil_lt_add_one hx.le,
  have h₁ : 0 < ⌈x⌉₊, by rwa [nat.lt_ceil, nat.cast_zero],
  have h₂ : 1 - x ≤ 2 - ⌈x⌉₊,
  { rw le_sub_iff_add_le,
    apply (add_le_add_left i.le _).trans,
    rw [←add_assoc, sub_add_cancel],
    apply le_refl },
  have h₃ : exp (-(x+1)) ≤ 1 / (x + 1),
  { rw [exp_neg, inv_eq_one_div],
    refine one_div_le_one_div_of_le (add_pos hx zero_lt_one) _,
    apply le_trans _ (add_one_le_exp_of_nonneg (add_nonneg hx.le zero_le_one)),
    exact le_add_of_nonneg_right zero_le_one },
  refine lt_of_le_of_lt _ (div_lt_div_of_lt_left (exp_pos _) (nat.cast_pos.2 h₁) i),
  refine le_trans _ (div_le_div_of_le_of_nonneg (exp_le_exp.2 h₂) (add_nonneg hx.le zero_le_one)),
  rw [le_div_iff (add_pos hx zero_lt_one), ←le_div_iff' (exp_pos _), ←exp_sub, neg_mul,
    sub_neg_eq_add, two_mul, sub_add_add_cancel, add_comm _ x],
  refine le_trans _ (add_one_le_exp_of_nonneg (add_nonneg hx.le zero_le_one)),
  exact le_add_of_nonneg_right zero_le_one
end

lemma exp_one_rpow {r : ℝ} : exp 1^r = exp r := by rw [←exp_mul, one_mul]

lemma roth_lower_bound_explicit (hN : 4096 ≤ N) :
  (N : ℝ) * exp (-4 * sqrt (log N)) < roth_number_nat N :=
begin
  let n := n_value N,
  have hn : 0 < n := n_value_pos ((show _ ≤ _, by norm_num1).trans hN),
  have hd : 0 < d_value N := d_value_pos ((show _ ≤ _, by norm_num1).trans hN),
  have hN₀ : 0 < (N:ℝ) := nat.cast_pos.2 ((show 0 < 4096, by norm_num1).trans_le hN),
  have hn₂ : 2 ≤ n := two_le_n_value ((show _ ≤ _, by norm_num1).trans hN),
  have : (2 * d_value N - 1)^n ≤ N := le_N (ge_trans hN (by norm_num1)),
  have := behrend_bound_aux3 hd hn₂ this,
  apply lt_of_lt_of_le _ this,
  apply lt_of_le_of_lt _ (div_lt_div_of_lt _ (pow_lt_pow_of_lt_left (bound hN) _ _)),
  { rw [←rpow_nat_cast, div_rpow (rpow_nonneg_of_nonneg hN₀.le _) (exp_pos _).le, ←rpow_mul hN₀.le,
      mul_comm (_ / _), mul_one_div, nat.cast_sub hn₂, nat.cast_two, same_sub_div, exp_one_rpow,
      div_div_eq_div_mul, rpow_sub, rpow_one, div_div_eq_div_mul, div_eq_mul_inv],
    { apply mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
      rw [mul_inv₀, mul_inv₀, ←exp_neg, ←rpow_neg (nat.cast_nonneg _), neg_sub, ←div_eq_mul_inv],
      have : exp ((-4) * sqrt (log N)) = exp (-2 * sqrt (log N)) * exp (-2 * sqrt (log N)),
      { rw [←exp_add, ←add_mul],
        norm_num },
      rw this,
      apply (mul_le_mul _ (exp_thing (real.sqrt_pos.2 _)).le _ _),
      { rw [←le_log_iff_exp_le (rpow_pos_of_pos hN₀ _), log_rpow hN₀, ←le_div_iff, mul_div_assoc,
          div_sqrt, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff],
        { exact mul_le_mul_of_nonneg_left (nat.le_ceil _) zero_le_two },
        { rwa nat.cast_pos },
        rw real.sqrt_pos,
        refine real.log_pos _,
        rw nat.one_lt_cast,
        exact lt_of_lt_of_le (by norm_num1) hN },
      { refine real.log_pos _,
        rw nat.one_lt_cast,
        exact lt_of_lt_of_le (by norm_num1) hN },
      { apply (exp_pos _).le },
      apply rpow_nonneg_of_nonneg (nat.cast_nonneg _) },
    { apply hN₀ },
    apply ne_of_gt,
    rwa nat.cast_pos },
  { rwa nat.cast_pos },
  { exact div_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (exp_pos _).le },
  apply nat.sub_pos_of_lt,
  apply three_le_n_value,
  apply le_trans _ hN,
  norm_num1
end

lemma exp_four_lt : exp 4 < 64 :=
begin
  have : (2:ℝ) ^ ((6:ℕ):ℝ) = 64,
  { rw rpow_nat_cast,
    norm_num1 },
  rw [←this, ←lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two,
    ←div_lt_iff'],
  refine lt_of_le_of_lt (by norm_num1) log_two_gt_d9,
  norm_num
end


lemma four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 :=
begin
  rw [←log_lt_iff_lt_exp (show (0:ℝ) < 4096, by norm_num)],
  have : (4096:ℝ) = 2 ^ 12,
  { norm_num },
  rw [this, ←rpow_nat_cast, log_rpow zero_lt_two, nat.cast_bit0, nat.cast_bit0, nat.cast_bit1,
    nat.cast_one],
  linarith [log_two_lt_d9]
end

lemma lower_bound_le_one' (hN : 2 ≤ N) (hN' : N ≤ 4096) : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  rw [←log_le_log (mul_pos (nat.cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one,
    log_one, log_mul (nat.cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne', log_exp,
    neg_mul, ←sub_eq_add_neg, sub_nonpos, ←div_le_iff (real.sqrt_pos.2 $ log_pos $
    nat.one_lt_cast.2 $ one_lt_two.trans_le hN), div_sqrt,
    sqrt_le_left (zero_le_bit0.2 zero_le_two),
    log_le_iff_le_exp (nat.cast_pos.2 (zero_lt_two.trans_le hN))],
  norm_num1,
  apply le_trans _ four_zero_nine_six_lt_exp_sixteen.le,
  exact_mod_cast hN'
end

lemma lower_bound_le_one (hN : 1 ≤ N) (hN' : N ≤ 4096) : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  rcases nat.eq_or_lt_of_le hN with rfl | hN,
  { simp },
  apply lower_bound_le_one' hN hN',
end

lemma roth_lower_bound : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ roth_number_nat N :=
begin
  rcases nat.eq_zero_or_pos N with rfl | hN,
  { simp },
  { cases le_or_lt 4096 N with h₁ h₁,
    { apply (roth_lower_bound_explicit h₁).le },
    apply (lower_bound_le_one hN h₁.le).trans,
    simpa using roth_number_nat.monotone hN }
end

-- lemma roth_lower_asymptotic {δ : ℝ} (hδ : 0 < δ) :
--   is_o (λ (x:ℝ), x^(1 - δ)) (λ x, (mul_roth_number ⌊x⌋₊ : ℝ)) at_top :=
-- begin
--   suffices : is_o (λ (x:ℝ), (x^(1 - δ))) (λ x, x * exp (-4 * sqrt (log x))) at_top,
--   { apply is_o.trans_is_O this,
--     simp only [is_O_iff, eventually_le, eventually_at_top],
--     refine ⟨1, exp 4, λ N hN, _⟩,
--     rw [norm_coe_nat, real.norm_eq_abs, one_mul],
--     -- have := is_o.trans_le,
--     -- apply this.trans_le,
--     -- intros x,
--     -- rw [normed_field.norm_mul, norm_coe_nat, norm_coe_nat, real.norm_eq_abs, abs_exp],
--     -- apply roth_lower_bound
--     },
-- end

-- lemma roth_lower_asymptotic {δ : ℝ} (hδ : 0 < δ) :
--   is_o (λ (N:ℕ), (N:ℝ)^(1 - δ)) (λ N, (mul_roth_number N : ℝ)) at_top :=
-- begin
--   suffices : is_o (λ (N:ℕ), ((N:ℝ)^(1 - δ))) (λ (N:ℕ), (N : ℝ) * exp (-4 * sqrt (log N))) at_top,
--   { apply this.trans_le,
--     intros x,
--     rw [normed_field.norm_mul, norm_coe_nat, norm_coe_nat, real.norm_eq_abs, abs_exp],
--     apply roth_lower_bound },
--   suffices : is_o (λ (N:ℕ), ((N:ℝ) * N^(-δ)))
    -- (λ (N:ℕ), (N : ℝ) * exp (-4 * sqrt (log N))) at_top,
--   { apply is_o.congr' _ (eventually_eq.refl _ _) this,
--     rw [eventually_eq, eventually_at_top],
--     refine ⟨1, λ N hN, _⟩,
--     rw [rpow_sub (nat.cast_pos.2 hN), rpow_neg (nat.cast_nonneg _), rpow_one, div_eq_mul_inv] },
--    refine is_O.mul_is_o (is_O_refl _ _) _,
--   rw is_o_iff,
--   intros c hc,
--   rw eventually_at_top,
--   refine ⟨1, λ N hN, _⟩,
--   have hN' : 0 < (N : ℝ) ^ -δ := rpow_pos_of_pos (nat.cast_pos.2 hN) _,
--   rw [real.norm_rpow_of_nonneg (nat.cast_nonneg _), norm_coe_nat, real.norm_eq_abs, abs_exp,
--     ←div_le_iff' hc, ←log_le_iff_le_exp (div_pos hN' hc), log_div hN'.ne' hc.ne'],
--   -- simp only [neg_mul, ge_iff_le, eventually_at_top, real.norm_eq_abs],

--   -- have : is_O (λ (N:ℕ), (N : ℝ) * exp (-4 * sqrt (log N)))
      -- (λ N, (mul_roth_number N : ℝ)) at_top,
--   -- { apply is_O_of_le,
--   --   simp only [normed_field.norm_mul, norm_coe_nat],
--   --   intro x,
--   --   simp only [real.norm_eq_abs, abs_exp],
--   --   apply roth_lower_bound },

-- end

end behrend
