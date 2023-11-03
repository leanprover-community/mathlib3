/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies, Jiale Miao, Alistair Bill,
Michał Mrugała, Jan Ot Piña
-/
import data.real.basic
import analysis.normed.field.basic
import analysis.special_functions.pow

/-!
# Seminorms and norms on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `ring_seminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `ring_norm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `mul_ring_seminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `mul_ring_norm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.

## Notes

The corresponding hom classes are defined in `analysis.order.hom.basic` to be used by absolute
values.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

set_option old_structure_cmd true

open_locale nnreal big_operators

variables {F R S : Type*} (x y : R) (r : ℝ)

/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure ring_seminorm (R : Type*) [non_unital_non_assoc_ring R]
  extends add_group_seminorm R :=
(mul_le' : ∀ x y : R, to_fun (x * y) ≤ to_fun x * to_fun y)

/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
structure ring_norm (R : Type*) [non_unital_non_assoc_ring R]
  extends ring_seminorm R, add_group_norm R

/-- A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
-/
structure mul_ring_seminorm (R : Type*) [non_assoc_ring R]
  extends add_group_seminorm R, monoid_with_zero_hom R ℝ

/-- A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that `f x = 0`
implies `x = 0`. -/
structure mul_ring_norm (R : Type*) [non_assoc_ring R] extends mul_ring_seminorm R, add_group_norm R

attribute [nolint doc_blame] ring_seminorm.to_add_group_seminorm ring_norm.to_add_group_norm
  ring_norm.to_ring_seminorm mul_ring_seminorm.to_add_group_seminorm
  mul_ring_seminorm.to_monoid_with_zero_hom mul_ring_norm.to_add_group_norm
  mul_ring_norm.to_mul_ring_seminorm

namespace ring_seminorm

section non_unital_ring

variables [non_unital_ring R]

instance ring_seminorm_class : ring_seminorm_class (ring_seminorm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_mul_le_mul := λ f, f.mul_le',
  map_neg_eq_map := λ f, f.neg' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_seminorm R) (λ _, R → ℝ) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (p : ring_seminorm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : ring_seminorm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

instance : has_zero (ring_seminorm R) :=
⟨{ mul_le' := λ _ _, (zero_mul _).ge,
  ..add_group_seminorm.has_zero.zero }⟩

lemma eq_zero_iff {p : ring_seminorm R} : p = 0 ↔ ∀ x, p x = 0 := fun_like.ext_iff
lemma ne_zero_iff {p : ring_seminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]

instance : inhabited (ring_seminorm R) := ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance [decidable_eq R] : has_one (ring_seminorm R) :=
⟨{ mul_le' := λ x y, begin
    by_cases h : x * y = 0,
    { refine (if_pos h).trans_le (mul_nonneg _ _);
      { change _ ≤ ite _ _ _,
        split_ifs,
        exacts [le_rfl, zero_le_one] } },
    { change ite _ _ _ ≤ ite _ _ _ * ite _ _ _,
      simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one] }
  end,
  ..(1 : add_group_seminorm R) }⟩

@[simp] lemma apply_one [decidable_eq R] (x : R) :
  (1 : ring_seminorm R) x = if x = 0 then 0 else 1 := rfl

end non_unital_ring

section ring

variables [ring R] (p : ring_seminorm R)

lemma seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) :
  p 1 = 1 ↔ p ≠ 0 :=
begin
  refine ⟨λ h, ne_zero_iff.mpr ⟨1, by {rw h, exact one_ne_zero}⟩, λ h, _⟩,
  obtain hp0 | hp0 := (map_nonneg p (1 : R)).eq_or_gt,
  { cases h (ext $ λ x, (map_nonneg _ _).antisymm' _),
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1},
  { refine hp.antisymm ((le_mul_iff_one_le_left hp0).1 _),
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _ }
end

end ring

end ring_seminorm

/-- The norm of a `non_unital_semi_normed_ring` as a `ring_seminorm`. -/
def norm_ring_seminorm (R : Type*) [non_unital_semi_normed_ring R] :
  ring_seminorm R :=
{ to_fun    := norm,
  mul_le'   := norm_mul_le,
  ..(norm_add_group_seminorm R) }

namespace ring_norm

variable [non_unital_ring R]

instance ring_norm_class : ring_norm_class (ring_norm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_add_le_add := λ f, f.add_le',
  map_mul_le_mul := λ f, f.mul_le',
  map_neg_eq_map := λ f, f.neg',
  eq_zero_of_map_eq_zero := λ f, f.eq_zero_of_map_eq_zero' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (ring_norm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[simp] lemma to_fun_eq_coe (p : ring_norm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : ring_norm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

variable (R)

/-- The trivial norm on a ring `R` is the `ring_norm` taking value `0` at `0` and `1` at every
  other element. -/
instance [decidable_eq R] : has_one (ring_norm R) :=
⟨{ ..(1 : ring_seminorm R), ..(1 : add_group_norm R) }⟩

@[simp] lemma apply_one [decidable_eq R] (x : R) : (1 : ring_norm R) x = if x = 0 then 0 else 1 :=
rfl

instance [decidable_eq R] : inhabited (ring_norm R) := ⟨1⟩

end ring_norm

namespace mul_ring_seminorm
variables [non_assoc_ring R]

instance mul_ring_seminorm_class : mul_ring_seminorm_class (mul_ring_seminorm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_one := λ f, f.map_one',
  map_add_le_add := λ f, f.add_le',
  map_mul := λ f, f.map_mul',
  map_neg_eq_map := λ f, f.neg' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (mul_ring_seminorm R) (λ _, R → ℝ) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (p : mul_ring_seminorm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : mul_ring_seminorm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

variables [decidable_eq R] [no_zero_divisors R] [nontrivial R]

/-- The trivial seminorm on a ring `R` is the `mul_ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance : has_one (mul_ring_seminorm R) :=
⟨{ map_one' := if_neg one_ne_zero,
  map_mul' := λ x y, begin
    obtain rfl | hx := eq_or_ne x 0,
    { simp },
    obtain rfl | hy := eq_or_ne y 0,
    { simp },
    { simp [hx, hy] }
  end,
  ..(1 : add_group_seminorm R) }⟩

@[simp] lemma apply_one (x : R) : (1 : mul_ring_seminorm R) x = if x = 0 then 0 else 1 := rfl

instance : inhabited (mul_ring_seminorm R) := ⟨1⟩

end mul_ring_seminorm

namespace mul_ring_norm
variable [non_assoc_ring R]

instance mul_ring_norm_class : mul_ring_norm_class (mul_ring_norm R) R ℝ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_zero := λ f, f.map_zero',
  map_one := λ f, f.map_one',
  map_add_le_add := λ f, f.add_le',
  map_mul := λ f, f.map_mul',
  map_neg_eq_map := λ f, f.neg',
  eq_zero_of_map_eq_zero := λ f, f.eq_zero_of_map_eq_zero' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (mul_ring_norm R) (λ _, R → ℝ) := ⟨λ p, p.to_fun⟩

@[simp] lemma to_fun_eq_coe (p : mul_ring_norm R) : p.to_fun = p := rfl

@[ext] lemma ext {p q : mul_ring_norm R} : (∀ x, p x = q x) → p = q := fun_like.ext p q

variables (R) [decidable_eq R] [no_zero_divisors R] [nontrivial R]

/-- The trivial norm on a ring `R` is the `mul_ring_norm` taking value `0` at `0` and `1` at every
other element. -/
instance : has_one (mul_ring_norm R) :=
⟨{ ..(1 : mul_ring_seminorm R), ..(1 : add_group_norm R) }⟩

@[simp] lemma apply_one (x : R) : (1 : mul_ring_norm R) x = if x = 0 then 0 else 1 := rfl

instance : inhabited (mul_ring_norm R) := ⟨1⟩

lemma map_neg_one {R : Type*} [non_assoc_ring R] {f : mul_ring_norm R} :
  f (-1) = 1 :=
begin
  have H₁ : f (-1) * f (-1) = 1,
  calc
    f (-1) * f (-1) = f ((-1) * (-1)) : by simp only [map_neg_eq_map, map_one, mul_one, mul_neg]
    ...             = f 1 : by norm_num
    ...             = 1 : f.map_one',
  have H₂: f (-1) ≥ 0 := map_nonneg f (-1),
  rw mul_self_eq_one_iff at H₁,
  cases H₁,
  { exact H₁ },
  { rw H₁ at H₂,
    have h' : ¬(-1 ≥ (0 : ℝ)) := by norm_num,
    contradiction },
end

lemma map_sum_le {R : Type*} [ring R] (f : mul_ring_norm R) (n : ℕ) (ι : ℕ → R) :
  f (∑ i in finset.range n, ι i) ≤ ∑ i in finset.range n, f (ι i) :=
begin
  induction n with n hn,
  { simp only [finset.range_zero, finset.sum_empty, map_zero] },
  { rw finset.sum_range_succ,
    rw finset.sum_range_succ,
    calc f (∑ (x : ℕ) in finset.range n, ι x + ι n)
        ≤ f (∑ i in finset.range n, ι i) + f (ι n) : f.add_le' _ _
    ... ≤ (∑ i in finset.range n, f (ι i)) + f (ι n) : add_le_add_right hn _ }
end

/-- Two multiplicative ring norms `f, g` on `R` are equivalent if there exists a positive constant
  `c` such that for all `x ∈ R`, `(f x)^c = g x`. -/
def equiv {R : Type*} [ring R] (f g : mul_ring_norm R) :=
  ∃ c : ℝ, 0 < c ∧ (λ x : R, (f x) ^ c) = g

lemma equiv_refl {R : Type*} [ring R] (f : mul_ring_norm R) :
  equiv f f := by refine ⟨1, by linarith, by simp only [real.rpow_one]⟩

lemma equiv_symm {R : Type*} [ring R] (f g : mul_ring_norm R) (hfg : equiv f g) :
  equiv g f :=
begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  refine ⟨1 / c, by simp only [hfg1, one_div, inv_pos], _⟩,
  rw ← hfg2,
  ext,
  simp only [one_div],
  have h1 : c ≠ 0 := by linarith,
  rw ← real.rpow_mul (map_nonneg f x),
  simp only [h1, mul_inv_cancel, ne.def, not_false_iff, real.rpow_one],
end

lemma equiv_trans {R : Type*} [ring R] (f g k : mul_ring_norm R)
  (hfg : equiv f g) (hgk : equiv g k) : equiv f k :=
begin
  rcases hfg with ⟨c, hfg1, hfg2⟩,
  rcases hgk with ⟨d, hgk1, hgk2⟩,
  refine ⟨c * d, by simp only [hfg1, hgk1, zero_lt_mul_right], _⟩,
  rw [← hgk2, ← hfg2],
  ext,
  exact real.rpow_mul (map_nonneg f x) c d,
end

end mul_ring_norm

section nonarchimedean_mul_ring_norm

-- PR#17817
/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def is_nonarchimedean {α : Type*} [has_add α] {β : Type*} [linear_order β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

-- PR#17817
lemma is_nonarchimedean_def {α : Type*} [has_add α] {β : Type*} [linear_order β] (f : α → β) :
is_nonarchimedean f ↔ ∀ r s, f (r + s) ≤ max (f r) (f s) := iff.rfl

namespace mul_ring_norm

-- PR#17817
lemma is_nonarchimedean.map_nat_cast_le_one {R : Type*} [non_assoc_ring R] {f : mul_ring_norm R}
  (hf : is_nonarchimedean f) (n : ℕ) : f n ≤ 1 :=
begin
  induction n with c hc,
  { simp only [nat.cast_zero, map_zero, zero_le_one] },
  { rw nat.succ_eq_add_one,
    specialize hf c 1,
    rw map_one at hf,
    simp only [nat.cast_add, nat.cast_one],
    exact le_trans hf (max_le hc rfl.ge) }
end

-- PR#17817
lemma is_nonarchimedean.map_int_cast_le_one {R : Type*} [non_assoc_ring R] {f : mul_ring_norm R}
  (hf : is_nonarchimedean f) (z : ℤ) : f z ≤ 1 :=
begin
  suffices goal : (∀ n : ℕ, f n ≤ 1) ↔ (∀ z : ℤ, f z ≤ 1),
  { revert z,
    rw ← goal,
    exact is_nonarchimedean.map_nat_cast_le_one hf },
  split,
  { intros h z,
    obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
    { norm_cast,
      exact h n },
    { simp only [int.cast_neg, int.cast_coe_nat, map_neg_eq_map],
      exact h n } },
  { intros h n,
    exact_mod_cast (h n) },
end

open filter

/-- A `mul_ring_norm` f is nonarchimedean if and only if there exist some non-zero elements such
  that `f (n * x) ≤ 1` for all n ∈ ℕ. -/
lemma is_nonarchimedean_iff_exists_ne_zero_map_nat_mul_le_one {R : Type*} [comm_ring R]
  [nontrivial R] {f : mul_ring_norm R} :
    is_nonarchimedean f ↔ (∃ x : R, x ≠ 0 ∧ ∀ n : ℕ, f (n * x) ≤ 1) :=
begin
  split,
  { intros hf,
    refine ⟨1, one_ne_zero, _⟩,
    intro n,
    rw mul_one,
    exact is_nonarchimedean.map_nat_cast_le_one hf n },
  { intros H y z,
    obtain ⟨x, hx, hn⟩ := H,
    have hn1 : ∀ (n : ℕ), f n ≤ 1 / (f x),
    { intro n,
      specialize hn n,
      rw map_mul at hn,
      rwa le_div_iff (map_pos_of_ne_zero f hx) },
    have hyz : ∀ (k : ℕ), f (y + z) ^ k ≤ ((k + 1) / f x) * max (f y) (f z) ^ k,
    { intro k,
      rw [← map_pow _ _ _, add_pow y z k],
      apply le_trans (map_sum_le f (k + 1) _),
      have h : ∑ (i : ℕ) in finset.range (k + 1), f (y ^ i * z ^ (k - i) * (k.choose i))
        ≤ ∑ (i : ℕ) in finset.range (k + 1), (f y) ^ i * (f z) ^ (k - i) / (f x),
      { apply finset.sum_le_sum,
        intros i hi,
        rw [map_mul, map_mul, map_pow, map_pow],
        specialize hn1 (k.choose i),
        have hyz : 0 ≤ f y ^ i * f z ^ (k - i),
        { apply mul_nonneg,
          { apply pow_nonneg,
            simp only [map_nonneg] },
          { apply pow_nonneg,
            simp only [map_nonneg] } },
        rw ← mul_one_div,
        exact (mul_le_mul_of_nonneg_left hn1 hyz) },
      apply le_trans h,
      have h1 : ∑ (i : ℕ) in finset.range (k + 1), (f y) ^ i * (f z) ^ (k - i) / (f x)
        ≤ ∑ (i : ℕ) in finset.range (k + 1), (max (f y) (f z)) ^ k / (f x),
      { apply finset.sum_le_sum,
        intros i hi,
        apply div_le_div_of_le_of_nonneg,
        { by_cases hyz : (f y) ≤ (f z),
          { simp only [hyz, max_eq_right],
            calc f y ^ i * f z ^ (k - i) ≤ f z ^ i * f z ^ (k - i) :
              begin
                apply mul_le_mul_of_nonneg_right,
                { apply pow_le_pow_of_le_left,
                  { simp only [map_nonneg] },
                  { exact hyz } },
                { apply pow_nonneg,
                  simp only [map_nonneg] }
              end
            ...                          = f z ^ k :
              begin
                rw ← pow_add,
                congr,
                simp only [finset.mem_range] at hi,
                have hi₁ : i ≤ k := by linarith,
                zify,
                ring,
              end
          },
          { have h₁ : f z ≤ f y := by linarith,
            rw max_eq_left h₁,
            calc f y ^ i * f z ^ (k - i) ≤ f y ^ i * f y ^ (k - i) :
              begin
                apply mul_le_mul_of_nonneg_left,
                { apply pow_le_pow_of_le_left,
                  { simp only [map_nonneg] },
                  { exact h₁ } },
                { apply pow_nonneg,
                  simp only [map_nonneg]}
              end
            ...                          = f y ^ k :
              begin
                rw ← pow_add,
                congr,
                simp only [finset.mem_range] at hi,
                have hi₁ : i ≤ k := by linarith,
                zify,
                ring,
              end
          } },
        { simp only [map_nonneg] } },
      apply le_trans h1,
      rw finset.sum_const ((max (f y) (f z)) ^ k / (f x)),
      simp only [finset.card_range, nsmul_eq_mul, nat.cast_add, algebra_map.coe_one],
      field_simp },
    have hyz1 : ∀ (k : ℕ), k ≠ 0 →
      f (y + z) ≤ ((k + 1) / f x) ^ (1 / (k : ℝ)) * max (f y) (f z),
    { intros k hk,
      specialize hyz k,
      refine le_of_pow_le_pow k _ (nat.pos_of_ne_zero hk) _,
      { apply mul_nonneg,
        { apply real.rpow_nonneg_of_nonneg,
          apply div_nonneg,
          { norm_cast,
            exact zero_le (k + 1) },
          { simp only [map_nonneg] } },
        { by_cases h : (f y) ≤ (f z),
          { simp only [h, max_eq_right, map_nonneg] },
          { simp only [le_max_iff, map_nonneg, or_self] }} },
      { rw mul_pow,
        nth_rewrite 1 ← real.rpow_nat_cast,
        rw ← real.rpow_mul _ (1 / (k : ℝ)),
        { field_simp,
          rw div_self,
          { rw real.rpow_one,
            exact hyz },
          norm_cast,
          exact hk },
        apply div_nonneg,
        { norm_cast,
          exact zero_le (k + 1) },
        { simp only [map_nonneg] } } }, clear hyz,
    have limit : tendsto (λ n : ℕ, ((n + 1 : ℝ) / (f x)) ^ (1 / (n : ℝ))
      * max (f y) (f z)) at_top (nhds (max (f y) (f z))),
    { have triv : max (f y) (f z) = 1 * max (f y) (f z) := by rwa one_mul,
      nth_rewrite 0 triv,
      apply tendsto.mul_const (max (f y) (f z)),
      have hk : (λ (k : ℕ), (((k : ℝ) + 1) / (f x)) ^ (1 / (k : ℝ)))
         = (λ (k : ℕ), real.exp (real.log (((k : ℝ) + 1) / (f x)) / k)),
      { ext k,
        have h : 0 < (((k : ℝ) + 1) / f x),
        { apply div_pos,
          { norm_cast,
            rw ← nat.succ_eq_add_one,
            exact nat.succ_pos k },
          { exact map_pos_of_ne_zero f hx } },
        nth_rewrite 0 ← real.exp_log h,
        rw [← real.exp_mul, mul_one_div] },
      rw hk,
      refine real.tendsto_exp_nhds_0_nhds_1.comp _,
      have hk₁ : (λ (k : ℕ), real.log (((k : ℝ) + 1) / (f x)) / k)
       = (λ (k : ℕ), (real.log ((k : ℝ) + 1) / k - real.log (f x) / k)),
      { ext k,
        rw real.log_div,
        { rwa sub_div },
        { norm_cast,
          rw ← nat.succ_eq_add_one,
          exact nat.succ_ne_zero k },
        { rwa map_ne_zero_iff_ne_zero f } },
      rw hk₁,
      have goal1 : tendsto (λ k : ℕ, (real.log ((k : ℝ) + 1) / k)) at_top (nhds 0),
      { have h₁ : tendsto (λ (k : ℕ), real.log (↑k + 1) / (↑k + 1)) at_top (nhds 0),
        { have h₂ := real.tendsto_pow_log_div_mul_add_at_top 1 0 1 (by linarith),
          ring_nf at h₂,
          suffices : tendsto (λ (k : ℕ),
            real.log (↑(k + 1) : ℝ) / (↑(k + 1) : ℝ)) at_top (nhds 0),
          { simpa },
          rw @tendsto_add_at_top_iff_nat _ (λ k, (real.log (k : ℝ)) / (k : ℝ)) _ 1,
          suffices goal : tendsto (λ (k : ℝ), (real.log k) / k) at_top (nhds 0),
          { exact goal.comp tendsto_coe_nat_at_top_at_top },
          exact h₂ },
        have h₂ : tendsto (λ (k : ℕ), ((k : ℝ) + 1) / k) at_top (nhds 1),
        { have h₃ : (λ (k : ℕ), ((k : ℝ) + 1) / k) = (λ (k : ℕ),
            (k : ℝ) / k + (k : ℝ)⁻¹),
          { ext k,
            rw add_div,
            rw one_div },
          rw h₃, clear h₃,
          suffices goal : tendsto (λ (k : ℕ), (k : ℝ) / k) at_top (nhds 1) ∧
            tendsto (λ (k : ℕ), (k : ℝ)⁻¹) at_top (nhds 0),
          { have goal1 := tendsto.add goal.1 goal.2,
            rwa add_zero at goal1 },
          split,
          { have h : ∀ (k : ℕ), k ≥ 1 → (k : ℝ) / k = 1,
            { intros k hk,
              rw div_self,
              norm_cast,
              linarith },
            exact tendsto_at_top_of_eventually_const h },
          { exact tendsto_inverse_at_top_nhds_0_nat } },
        have goal := tendsto.mul h₁ h₂,
        simp only [zero_mul] at goal,
        convert goal,
        ext x,
        have hx₁ : (x : ℝ) + 1 ≠ 0,
        { norm_cast,
          exact nat.add_one_ne_zero x },
        rwa div_mul_div_cancel (real.log (↑x + 1)) hx₁ },
      have goal2 : tendsto (λ k : ℕ, (real.log (f x) / k)) at_top (nhds 0),
      { exact tendsto_const_div_at_top_nhds_0_nat (real.log (f x)) },
      have goal := tendsto.sub goal1 goal2,
      rwa zero_sub_zero at goal },
    apply ge_of_tendsto limit _,
    simp only [eventually_at_top, ge_iff_le],
    refine ⟨1, _⟩,
    intros b hb,
    have hb1 : b ≠ 0 := by linarith,
    specialize hyz1 b hb1,
    exact hyz1 }
end

end mul_ring_norm
end nonarchimedean_mul_ring_norm

/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def ring_seminorm.to_ring_norm {K : Type*} [field K] (f : ring_seminorm K) (hnt : f ≠ 0) :
  ring_norm K :=
{ eq_zero_of_map_eq_zero' := λ x hx,
  begin
    obtain ⟨c, hc⟩ := ring_seminorm.ne_zero_iff.mp hnt,
    by_contradiction hn0,
    have hc0 : f c = 0,
    { rw [← mul_one c, ← mul_inv_cancel hn0, ← mul_assoc, mul_comm c, mul_assoc],
      exact le_antisymm (le_trans (map_mul_le_mul f _ _)
        (by rw [← ring_seminorm.to_fun_eq_coe, hx, zero_mul])) (map_nonneg f _) },
    exact hc hc0,
  end,
  ..f }

/-- The norm of a normed_ring as a ring_norm. -/
@[simps] def norm_ring_norm (R : Type*) [non_unital_normed_ring R] : ring_norm R :=
{ ..norm_add_group_norm R, ..norm_ring_seminorm R }
