/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.hom.freiman
import analysis.inner_product_space.pi_L2
import combinatorics.additive.salem_spencer
import combinatorics.pigeonhole
import data.complex.exponential_bounds

/-!
# Behrend's bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (log (sqrt n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n` dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`behrend.map`).

## Main declarations

* `behrend.sphere`: The intersection of the Euclidean with the positive integer quadrant. This is
  the set that we will map on `ℕ`.
* `behrend.map`: The map from the Euclidean space to `n`. It reads off the coordinates as digits in
  base `d`.
* `behrend.card_sphere_le_roth_number_nat`: Implicit lower bound on Roth numbers in terms of
  `behrend.sphere`.
* `behrend.roth_lower_bound`: Behrend's explicit lower bound on Roth numbers.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/

section smul
variables {α β : Type*} [group_with_zero α] [mul_action α β] {g : α} {x y : β}

lemma smul_left_cancel₀ (hg : g ≠ 0) (h : g • x = g • y) : x = y :=
smul_left_cancel (units.mk0 _ hg) h

@[simp] lemma smul_left_cancel_iff₀ (hg : g ≠ 0) : g • x = g • y ↔ x = y :=
smul_left_cancel_iff $ units.mk0 _ hg

end smul

namespace nat

lemma le_succ_mul_neg (n : ℕ) : ∀ d, d ≤ (n + 1) * d - n
| 0       := zero_le _
| (d + 1) := begin
    rw [mul_add, mul_one, add_tsub_assoc_of_le (n.le_add_right _), add_tsub_cancel_left],
    exact add_le_add_right (le_mul_of_one_le_left d.zero_le $ nat.le_add_left _ _) 1,
  end

variables {α : Type*} [linear_ordered_semiring α] [floor_semiring α] {a : α}

@[simp] lemma ceil_pos  : 0 < ⌈a⌉₊ ↔ 0 < a := lt_ceil

end nat

namespace set
variables {α : Type*} [has_mul α] {s t u : set α}

open_locale pointwise

@[to_additive]
lemma mul_subset_iff : s * t ⊆ u ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ t → a * b ∈ u := image2_subset_iff
-- TODO: `div` too

end set

namespace real

@[simp] lemma exp_one_rpow {r : ℝ} : exp 1^r = exp r := by rw [←exp_mul, one_mul]

end real

namespace finset
open_locale big_operators

variables {α : Type*} [add_comm_monoid α]

lemma sum_fin (n : ℕ) (f : ℕ → α) : ∑ i : fin n, f i = ∑ i in range n, f i :=
(sum_subtype (range n) (λ _, mem_range) f).symm

end finset

open finset nat real
open_locale big_operators pointwise

-- Should *replace* the existing lemma with a similar name.
lemma exists_le_card_fiber_of_mul_le_card_of_maps_to' {α β M : Type*} [linear_ordered_comm_ring M]
  [decidable_eq β] {s : finset α} {t : finset β} {f : α → β} {b : M} (hf : ∀ a ∈ s, f a ∈ t)
  (ht : t.nonempty) (hn : t.card • b ≤ s.card) :
  ∃ y ∈ t, b ≤ (s.filter (λ x, f x = y)).card :=
begin
  simp only [card_eq_sum_ones, nat.cast_sum],
  refine exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht _,
  simpa using hn,
end

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

/-- The intersection of the sphere of radius `sqrt k` with the integer points in the positive
quadrant. -/
def sphere (n d k : ℕ) : finset (fin n → ℕ) := (box n d).filter $ λ x, ∑ i, x i^2 = k

lemma sphere_zero : sphere n d 0 ⊆ 0 :=
begin
  intros x hx,
  simp only [sphere, nat.succ_pos', sum_eq_zero_iff, mem_filter, mem_univ, forall_true_left,
    pow_eq_zero_iff] at hx,
  simp only [mem_zero, function.funext_iff],
  apply hx.2
end

lemma sphere_subset_box : sphere n d k ⊆ box n d := filter_subset _ _

lemma norm_of_mem_sphere {n d k : ℕ} {x : fin n → ℕ} (hx : x ∈ sphere n d k) :
  ∥@id (euclidean_space ℝ (fin n)) (coe ∘ x : fin n → ℝ)∥ = sqrt k :=
begin
  rw euclidean_space.norm_eq,
  congr',
  change ∑ (i : fin n), ∥(x i : ℝ)∥ ^ 2 = k,
  simp_rw [norm_coe_nat, ←nat.cast_pow, ←nat.cast_sum, (mem_filter.1 hx).2],
end

/-- The map that appears in Behrend's bound on Roth numbers. -/
@[simps] def map (d : ℕ) : (fin n → ℕ) →+ ℕ :=
{ to_fun := λ a, ∑ i, a i * d^(i : ℕ),
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
  refine ⟨λ h, _, _⟩,
  { have : map d x₁ % d = map d x₂ % d,
    { rw h },
    simp only [map_mod, nat.mod_eq_of_lt (hx₁ _), nat.mod_eq_of_lt (hx₂ _)] at this,
    refine ⟨this, _⟩,
    rw [map_succ, map_succ, this, add_right_inj, mul_eq_mul_right_iff] at h,
    exact h.resolve_right ((nat.zero_le _).trans_lt $ hx₁ 0).ne' },
  rintro ⟨h₁, h₂⟩,
  rw [map_succ', map_succ', h₁, h₂],
end

lemma map_inj_on : {x : fin n → ℕ | ∀ i, x i < d}.inj_on (map d) :=
begin
  intros x₁ hx₁ x₂ hx₂ h,
  induction n with n ih,
  { simp },
  ext i,
  have x := (map_eq_iff hx₁ hx₂).1 h,
  refine fin.cases x.1 (congr_fun $ ih (λ _, _) (λ _, _) ((map_eq_iff hx₁ hx₂).1 h).2) i,
  { exact hx₁ _ },
  { exact hx₂ _ }
end

lemma map_le_of_mem_box (hx : x ∈ box n d) :
  map (2 * d - 1) x ≤ ∑ i : fin n, (d - 1) * (2 * d - 1)^(i : ℕ) :=
map_monotone (2 * d - 1) $ λ _, nat.le_pred_of_lt $ mem_box.1 hx _

lemma add_salem_spencer_sphere : add_salem_spencer (sphere n d k : set (fin n → ℕ)) :=
begin
  set f : (fin n → ℕ) →+ euclidean_space ℝ (fin n) :=
  { to_fun := λ f, (coe : ℕ → ℝ) ∘ f,
    map_zero' := rfl,
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
  refine @add_salem_spencer.image _ (fin n → ℕ) ℕ _ _ (sphere n d k) _ (map (2 * d - 1)) _
    add_salem_spencer_sphere,
  refine map_inj_on.mono _,
  rw set.add_subset_iff,
  rintro a ha b hb i,
  have hai := succ_le_of_lt (mem_box.1 (sphere_subset_box ha) i),
  have hbi := succ_le_of_lt (mem_box.1 (sphere_subset_box hb) i),
  rw [lt_tsub_iff_right, ←succ_le_iff, two_mul],
  exact (add_add_add_comm _ _ 1 1).trans_le (add_le_add hai hbi),
end

lemma sum_sq_le_of_mem_box (hx : x ∈ box n d) : ∑ i : fin n, (x i)^2 ≤ n * (d - 1)^2 :=
begin
  rw mem_box at hx,
  have : ∀ i, x i^2 ≤ (d - 1)^2 := λ i, nat.pow_le_pow_of_le_left (nat.le_pred_of_lt (hx i)) _,
  refine (sum_le_card_nsmul univ _ _ $ λ i _, this i).trans _,
  rw [card_fin, smul_eq_mul],
end

lemma digits_sum_eq : ∑ i : fin n, (d - 1) * (2 * d - 1)^(i : ℕ) = ((2 * d - 1)^n - 1) / 2 :=
begin
  apply (nat.div_eq_of_eq_mul_left zero_lt_two _).symm,
  rcases nat.eq_zero_or_pos d with rfl | hd,
  { simp only [mul_zero, nat.zero_sub, zero_mul, sum_const_zero, tsub_eq_zero_iff_le, zero_pow_eq],
    split_ifs; simp },
  have : ((2 * d - 2) + 1) = 2 * d - 1,
  { rw ←tsub_tsub_assoc (nat.le_mul_of_pos_right hd) one_le_two },
  rw [sum_fin n (λ i, (d - 1) * (2 * d - 1)^(i : ℕ)), ←mul_sum, mul_right_comm, tsub_mul,
    mul_comm d, one_mul, ←this, ←geom_sum_def, ←geom_sum_mul_add, add_tsub_cancel_right, mul_comm],
end

lemma digits_sum_le (hd : 0 < d) : ∑ i : fin n, (d - 1) * (2 * d - 1)^(i : ℕ) < (2 * d - 1)^n :=
begin
  rw digits_sum_eq,
  exact (nat.div_le_self _ _).trans_lt
    (nat.pred_lt (pow_pos (hd.trans_le $ le_succ_mul_neg _ _) _).ne'),
end

lemma card_sphere_le_roth_number_nat (hd : 0 < d) (hN : (2 * d - 1)^n ≤ N) :
  (sphere n d k).card ≤ roth_number_nat N :=
begin
  refine add_salem_spencer_image_sphere.le_roth_number_nat _ _ (card_image_of_inj_on _),
  { simp only [subset_iff, mem_image, and_imp, forall_exists_index, mem_range,
      forall_apply_eq_imp_iff₂, sphere, mem_filter],
    rintro _ x hx _ rfl,
    exact ((map_le_of_mem_box hx).trans_lt (digits_sum_le hd)).trans_le hN },
  refine map_inj_on.mono (λ x, _),
  simp only [mem_coe, sphere, mem_filter, mem_box, and_imp],
  exact λ h _ i, (h i).trans_le (le_succ_mul_neg _ _),
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
  refine exists_le_card_fiber_of_mul_le_card_of_maps_to' (λ x hx, _) nonempty_range_succ _,
  { rw [mem_range, nat.lt_succ_iff],
    exact sum_sq_le_of_mem_box hx },
  { rw [card_range, _root_.nsmul_eq_mul, mul_div_assoc', nat.cast_add_one, mul_div_cancel_left,
      card_box],
    exact (nat.cast_add_one_pos _).ne' }
end

lemma exists_large_sphere (hn : 0 < n) (hd : 0 < d) :
  ∃ k, (d ^ n / ↑(n * d^2) : ℝ) ≤ (sphere n d k).card :=
begin
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d,
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

lemma bound_aux' (hd : 0 < d) (hn : 0 < n) (hN : (2 * d - 1)^n ≤ N) :
  (d ^ n / ↑(n * d^2) : ℝ) ≤ roth_number_nat N :=
begin
  obtain ⟨k, _⟩ := exists_large_sphere hn hd,
  apply h.trans,
  rw nat.cast_le,
  apply card_sphere_le_roth_number_nat hd hN,
end

lemma bound_aux (hd : 0 < d) (hn : 2 ≤ n) (hN : (2 * d - 1)^n ≤ N) :
  (d ^ (n - 2) / n : ℝ) ≤ roth_number_nat N :=
begin
  convert bound_aux' hd (zero_lt_two.trans_le hn) hN using 1,
  rw [nat.cast_mul, nat.cast_pow, mul_comm, ←div_div_eq_div_mul, pow_sub₀ _ _ hn, ←div_eq_mul_inv],
  rw nat.cast_ne_zero,
  apply hd.ne',
end

open_locale filter topological_space
open real

section numerical_bounds

lemma log_two_mul_two_le_sqrt_log_eight : log 2 * 2 ≤ sqrt (log 8) :=
begin
  suffices : log 2 * 2 ≤ sqrt ((3:ℕ) * log 2),
  { rw [←log_rpow zero_lt_two (3:ℕ), rpow_nat_cast] at this,
    norm_num at this,
    apply this },
  apply le_sqrt_of_sq_le,
  rw [mul_pow, sq (log 2), mul_assoc, mul_comm],
  refine mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff,
  apply log_two_lt_d9.le.trans,
  all_goals { norm_num }
end

lemma two_div_one_sub_two_div_e_le_eight : 2 / (1 - 2 / exp 1) ≤ 8 :=
begin
  rw [div_le_iff, mul_sub, mul_one, mul_div_assoc', le_sub, div_le_iff (exp_pos _)],
  { linarith [exp_one_gt_d9] },
  rw [sub_pos, div_lt_one];
  exact lt_trans (by norm_num) exp_one_gt_d9,
end

lemma annoying_bound (hN : 4096 ≤ N) : log (2 / (1 - 2 / exp 1)) * (69 / 50) ≤ sqrt (log ↑N) :=
begin
  have : ((12 : ℕ) : ℝ) * log 2 ≤ log N,
  { rw [←log_rpow zero_lt_two, log_le_log, rpow_nat_cast],
    { norm_num1,
      exact_mod_cast hN },
    { apply rpow_pos_of_pos zero_lt_two },
    rw nat.cast_pos,
    apply lt_of_lt_of_le _ hN,
    norm_num1 },
  refine (mul_le_mul_of_nonneg_right ((log_le_log _ $ by norm_num1).2
    two_div_one_sub_two_div_e_le_eight) _).trans _,
  { refine div_pos zero_lt_two _,
    rw [sub_pos, div_lt_one (exp_pos _)],
    exact lt_of_le_of_lt (by norm_num1) exp_one_gt_d9 },
  { norm_num1 },
  have l8 : log 8 = (3 : ℕ) * log 2,
  { rw [←log_rpow zero_lt_two, rpow_nat_cast],
    norm_num },
  rw [l8, nat.cast_bit1, nat.cast_one],
  apply le_sqrt_of_sq_le (le_trans _ this),
  simp only [nat.cast_bit0, nat.cast_bit1, nat.cast_one],
  rw [mul_right_comm, mul_pow, sq (log 2), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right _ (log_nonneg one_le_two),
  rw ←le_div_iff',
  { apply log_two_lt_d9.le.trans,
    norm_num1 },
  apply sq_pos_of_ne_zero,
  norm_num1,
end

lemma exp_thing {x : ℝ} (hx : 0 < x) : exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ :=
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

lemma floor_lt_mul {x : ℝ} (hx : 2 / (1 - 2 / exp 1) ≤ x) : x / exp 1 < (⌊x/2⌋₊ : ℝ) :=
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

lemma ceil_lt_mul {x : ℝ} (hx : 50/19 ≤ x) : (⌈x⌉₊ : ℝ) < 1.38 * x :=
begin
  refine (nat.ceil_lt_add_one (le_trans (by norm_num) hx)).trans_le _,
  have : (0 : ℝ) < 50 := by norm_num,
  rw [←le_sub_iff_add_le', div_mul_eq_mul_div, div_sub' _ _ _ this.ne', one_le_div this, ←sub_mul],
  linarith,
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
  rw [nat.cast_one, one_pow, lt_log_iff_exp_lt],
  refine lt_of_lt_of_le _ (nat.cast_le.2 hN),
  { exact exp_one_lt_d9.trans_le (by norm_num) },
  rw nat.cast_pos,
  exact (zero_lt_succ _).trans_le hN,
end

lemma three_le_n_value (hN : 64 ≤ N) : 3 ≤ n_value N :=
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

lemma d_value_pos (hN₃ : 8 ≤ N) : 0 < d_value N :=
begin
  have hN₀ : 0 < (N : ℝ) := nat.cast_pos.2 (nat.succ_pos'.trans_le hN₃),
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
  suffices i : (2 * d_value N : ℝ) ≤ (N : ℝ)^(1/n_value N : ℝ),
  { apply (rpow_le_rpow (mul_nonneg zero_le_two (nat.cast_nonneg _)) i (nat.cast_nonneg _)).trans,
    rw [←rpow_mul (nat.cast_nonneg _), one_div_mul_cancel, rpow_one],
    rw nat.cast_ne_zero,
    apply (n_value_pos hN).ne', },
  rw ←le_div_iff',
  { exact nat.floor_le (div_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) zero_le_two) },
  apply zero_lt_two
end

lemma bound (hN : 4096 ≤ N) : (N : ℝ)^(1/n_value N : ℝ) / exp 1 < d_value N :=
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
      apply log_pos,
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

lemma roth_lower_bound_explicit (hN : 4096 ≤ N) :
  (N : ℝ) * exp (-4 * sqrt (log N)) < roth_number_nat N :=
begin
  let n := n_value N,
  have hn : 0 < n := n_value_pos ((show _ ≤ _, by norm_num1).trans hN),
  have hd : 0 < d_value N := d_value_pos ((show _ ≤ _, by norm_num1).trans hN),
  have hN₀ : 0 < (N : ℝ) := nat.cast_pos.2 ((show 0 < 4096, by norm_num1).trans_le hN),
  have hn₂ : 2 ≤ n := two_le_n_value ((show _ ≤ _, by norm_num1).trans hN),
  have : (2 * d_value N - 1)^n ≤ N := le_N (ge_trans hN $ by norm_num1),
  apply lt_of_lt_of_le _ (bound_aux hd hn₂ this),
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
        { exact mul_le_mul_of_nonneg_left (le_ceil _) zero_le_two },
        { rwa cast_pos },
        rw real.sqrt_pos,
        refine log_pos _,
        rw one_lt_cast,
        exact lt_of_lt_of_le (by norm_num1) hN },
      { refine log_pos _,
        rw one_lt_cast,
        exact lt_of_lt_of_le (by norm_num1) hN },
      { apply (exp_pos _).le },
      apply rpow_nonneg_of_nonneg (cast_nonneg _) },
    { apply hN₀ },
    apply ne_of_gt,
    rwa cast_pos },
  { rwa cast_pos },
  { exact div_nonneg (rpow_nonneg_of_nonneg (cast_nonneg _) _) (exp_pos _).le },
  apply tsub_pos_of_lt,
  apply three_le_n_value,
  apply le_trans _ hN,
  norm_num1
end

lemma exp_four_lt : exp 4 < 64 :=
begin
  have : (2 : ℝ) ^ ((6 : ℕ) : ℝ) = 64,
  { rw rpow_nat_cast,
    norm_num1 },
  rw [←this, ←lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two,
    ←div_lt_iff'],
  refine lt_of_le_of_lt (by norm_num1) log_two_gt_d9,
  norm_num
end

lemma four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 :=
begin
  rw [←log_lt_iff_lt_exp (show (0 : ℝ) < 4096, by norm_num)],
  have : (4096 : ℝ) = 2 ^ 12,
  { norm_num },
  rw [this, ←rpow_nat_cast, log_rpow zero_lt_two, cast_bit0, cast_bit0, cast_bit1, cast_one],
  linarith [log_two_lt_d9]
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
  exact_mod_cast hN'
end

lemma lower_bound_le_one (hN : 1 ≤ N) (hN' : N ≤ 4096) : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ 1 :=
begin
  obtain rfl | hN := hN.eq_or_lt,
  { norm_num },
  { exact lower_bound_le_one' hN hN' }
end

lemma roth_lower_bound : (N : ℝ) * exp (-4 * sqrt (log N)) ≤ roth_number_nat N :=
begin
  rcases nat.eq_zero_or_pos N with rfl | hN,
  { norm_num },
  cases le_or_lt 4096 N with h₁ h₁,
  { exact (roth_lower_bound_explicit h₁).le },
  { apply (lower_bound_le_one hN h₁.le).trans,
    simpa using roth_number_nat.monotone hN }
end

end behrend
