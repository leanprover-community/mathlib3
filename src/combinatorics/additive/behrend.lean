/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.inner_product_space.pi_L2
import combinatorics.additive.salem_spencer

/-!
# Behrend's bound on Roth numbers

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

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/

open finset nat real
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
  ∥(pi_Lp.equiv 2 _).symm (coe ∘ x : fin n → ℝ)∥ = sqrt k :=
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

end behrend
