/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
import tactic.basic
import data.real.irrational
import combinatorics.pigeonhole

/-!
# Diophantine Approximation

This file gives proofs of various versions of **Dirichlet's approximation theorem**
and its important consequence that when `ξ` is an irrational real number, then there are
infinitely many rationals `x/y` (in lowest terms) such that `|ξ - x/y| < 1/y^2`.

We also show the converse, i.e., that for rational `ξ` there are only finitely many
such rational approximations.

The proof (of the interesting direction) is based on the pigeonhole principle.

## Main definitions

We define the set `dioph_approx.rat_approx ξ` for a real number `ξ` to be the set
of pairs `(x, y)` of coprime integers with `y` positive such that `|ξ - x/y| < 1/y^2`.
This set is in natural bijection with `{q : ℚ | |ξ - q| < 1/q.denom^2}`
(see `dioph_approx.rat_approx_equiv`).

## Main statements

The main results are
* `dioph_approx.dirichlet_approx`, which is a version of Dirichlet's approximation
  theorem and states that for all real `ξ` and natural `0 < n`, there are integers
  `j` and `k` with `0 < k ≤ n` and `|ξ*k - j| ≤ 1/(n+1)`,
* A variant `dioph_approx.dirichlet_approx'` of this in terms of rationals `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.denom)` and `q.denom ≤ n`,
* `dioph_approx.rat_approx_infinite`, which states that for irrational `ξ`,
  `{q : ℚ | |ξ - q| < 1/q.denom^2}` is infinite,
* `dioph_approx.rat_approx_finite`, which states that `{q : ℚ | |a/b - q| < 1/q.denom^2}`
  is finite for integers `a` and `b`,
* `dioph_approx.rat_approx_infinite_iff_irrational`, which combines the two previous
  statements to give an iff statement, and
* `dioph_approx.rat_approx_infinite_iff_irrational'`, which is a version
   in terms of `dioph_approx.rat_approx ξ`.

## Implementation notes

We use the namespace `dioph_approx`.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>

## Tags

Diophantine approximation, Dirichlet's approximation theorem
-/

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.denom ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.denom)`.
-/

namespace real

open finset int

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`,
with `0 < k ≤ n` and `|ξ*k - j| ≤ 1/(n+1)`. -/
lemma exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
  ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |ξ * k - j| ≤ 1 / (n + 1) :=
begin
  let f : ℤ → ℤ := λ m, ⌊fract (ξ * m) * (n + 1)⌋,
  have hn : 0 < (n : ℝ) + 1 := by exact_mod_cast nat.succ_pos _,
  have hfu := λ m : ℤ, mul_lt_of_lt_one_left hn $ fract_lt_one (ξ * ↑m),
  conv in (|_| ≤ _) { rw [le_div_iff hn, ← abs_of_pos hn, ← abs_mul], },
  let D := Icc (0 : ℤ) n,
  by_cases H : ∃ m ∈ D, f m = n,
  { obtain ⟨m, hm, hf⟩ := H,
    have hf' : (n : ℝ) ≤ fract (ξ * ↑m) * (↑n + 1),
    { have : (f m : ℝ) ≤ fract (ξ * ↑m) * (↑n + 1) := floor_le (fract (ξ * ↑m) * (↑n + 1)),
      rw hf at this,
      exact_mod_cast this, },
    have hm₀ : 0 < m,
    { have hf₀ : f 0 = 0,
      { simp only [floor_eq_zero_iff, algebra_map.coe_zero, mul_zero, fract_zero, zero_mul,
                   set.left_mem_Ico, zero_lt_one], },
      refine ne.lt_of_le (λ h, n_pos.ne _) (mem_Icc.mp hm).1,
      exact_mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n), },
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, _⟩,
    rw [cast_add, ← sub_sub, sub_mul, cast_one, one_mul, abs_le],
    refine ⟨le_sub_iff_add_le.mpr _, sub_le_iff_le_add.mpr $ le_of_lt $
             (hfu m).trans $ lt_one_add _⟩,
    simpa only [neg_add_cancel_comm_assoc] using hf', },
  { simp_rw [not_exists] at H,
    have hD : (Ico (0 : ℤ) n).card < D.card,
    { rw [card_Icc, card_Ico], exact lt_add_one n, },
    have hfu' : ∀ m, f m ≤ n := λ m, lt_add_one_iff.mp (floor_lt.mpr (by exact_mod_cast hfu m)),
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n :=
      λ x hx, mem_Ico.mpr ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le),
                           ne.lt_of_le (H x hx) (hfu' x)⟩,
    have : ∃ (x : ℤ) (hx : x ∈ D) (y : ℤ) (hy : y ∈ D), x < y ∧ f x = f y,
    { obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd,
      rcases lt_trichotomy x y with h | h | h,
      exacts [⟨x, hx, y, hy, h, hxy⟩, false.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩], },
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ := this,
    refine ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
            sub_le_iff_le_add.mpr $ le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, _⟩,
    convert_to |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1,
    { congr, push_cast, simp only [fract], ring, },
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le, }
end

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is an integer `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
lemma exists_int_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
  ∃ k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) :=
begin
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos,
  rw [mul_comm] at h,
  exact ⟨k, hk₀, hk₁, (round_le (↑k * ξ) j).trans h⟩,
end

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.denom ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.denom)`. -/
lemma exists_rat_abs_sub_le_and_denom_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
  ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.denom) ∧ q.denom ≤ n :=
begin
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos,
  have hk₀' : (0 : ℝ) < k := int.cast_pos.mpr hk₀,
  have hden : ((j / k : ℚ).denom : ℤ) ≤ k,
  { convert le_of_dvd hk₀ (rat.denom_dvd j k), exact rat.coe_int_div_eq_mk, },
  refine ⟨j / k, _, nat.cast_le.mp (hden.trans hk₁)⟩,
  rw [← div_div, le_div_iff (nat.cast_pos.mpr $ rat.pos _ : (0 : ℝ) < _)],
  refine (mul_le_mul_of_nonneg_left (int.cast_le.mpr hden : _ ≤ (k : ℝ)) (abs_nonneg _)).trans _,
  rwa [← abs_of_pos hk₀', rat.cast_div, rat.cast_coe_int, rat.cast_coe_int,
       ← abs_mul, sub_mul, div_mul_cancel _ hk₀'.ne'],
end

end real

namespace dioph_approx

section rat_approx

/-!
### Equivalence between `rat_approx ξ` and approximating fractions

We define `dioph_approx.rat_approx ξ` and show that it is bijective to the
set of fractions `q` such that `|ξ - q| < 1/q.denom^2`. We also prove some
more properties.
-/

open set

/-- We define the set `rat_approx ξ` of good rational approximations to `ξ`
as a set of pairs `(x, y)` of integers (corresponding to the fraction `x/y`). -/
def rat_approx (ξ : ℝ) : set (ℤ × ℤ) :=
  {xy : ℤ × ℤ | 0 < xy.2 ∧ int.gcd xy.1 xy.2 = 1 ∧ |ξ - xy.1 / xy.2| < 1 / xy.2 ^ 2}

/-- There is always at least one good rational approximation. -/
lemma rat_approx_nonempty' (ξ : ℝ) : (rat_approx ξ).nonempty :=
⟨(⌊ξ⌋, 1), by simp [rat_approx, abs_of_nonneg (int.fract_nonneg ξ), int.fract_lt_one]⟩

/-- If `x/y` is a good approximation to `ξ`, then `x` is bounded in terms of `y` (and `ξ`). -/
lemma rat_approx_num_bound {ξ : ℝ} {x y : ℤ} (h : (x, y) ∈ rat_approx ξ) :
  ⌈ξ * y⌉ - 1 ≤ x ∧ x ≤ ⌊ξ * y⌋ + 1 :=
begin
  obtain ⟨hpos, _, hbd⟩ := h,
  have hpos' : (0 : ℝ) < y := int.cast_pos.mpr hpos,
  rw [← mul_lt_mul_right hpos'] at hbd,
  nth_rewrite 1 ← abs_of_pos hpos' at hbd,
  rw [← abs_mul, sub_mul, sq, ← div_div, div_mul_cancel _ hpos'.ne', div_mul_cancel _ hpos'.ne']
    at hbd,
  have H : (1 : ℝ) / y ≤ 1,
  { refine (one_div_le zero_lt_one hpos').mp _,
    simp only [div_self one_ne_zero],
    exact_mod_cast hpos, },
  obtain ⟨hbd₁, hbd₂⟩ := abs_sub_lt_iff.mp (lt_of_lt_of_le hbd H),
  rw [sub_lt_iff_lt_add, add_comm] at hbd₁ hbd₂,
  rw [← sub_lt_iff_lt_add] at hbd₂,
  norm_cast at hbd₁ hbd₂,
  exact ⟨sub_le_iff_le_add.mpr (int.ceil_le.mpr hbd₁.le),
         sub_le_iff_le_add.mp (int.le_floor.mpr hbd₂.le)⟩,
end

/-- There are only finitely many good approximations to `ξ` with given denominator. -/
lemma rat_approx_to_denom_finite_fibers (ξ : ℝ) (y : ℤ) :
  (prod.snd ⁻¹' {y} ∩ rat_approx ξ).finite :=
begin
  cases le_or_gt y 0 with hy hy,
  { have : (prod.snd ⁻¹' {y} ∩ rat_approx ξ) = ∅,
    { ext xy,
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
                 iff_false, not_and],
      rintros h₁ ⟨ypos, _⟩,
      exact lt_irrefl (0 : ℤ) (lt_of_lt_of_le (h₁ ▸ ypos : 0 < y) hy), },
    exact this.symm ▸ finite_empty, },
  { refine finite.subset (finite.prod (finite_Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1))
             (finite_singleton y)) (λ xy hxy, _),
    simp only [prod_singleton, mem_image, mem_Icc],
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hxy,
    exact ⟨xy.1, rat_approx_num_bound $ hxy.1 ▸ hxy.2, hxy.1 ▸ prod.mk.eta⟩, }
end

/-- The set of good rational approximations is infinite if and only if the set of
denominators of good rational approximations is infinite. -/
lemma rat_approx_infinite_iff_to_denom_infinite (ξ : ℝ) :
  (rat_approx ξ).infinite ↔ (prod.snd '' rat_approx ξ).infinite :=
begin
  have H : rat_approx ξ ⊆ ⋃ y ∈ (prod.snd '' rat_approx ξ), prod.snd ⁻¹' {y} ∩ rat_approx ξ,
  { intros xy hxy,
    simp_rw [mem_Union, mem_inter_iff, mem_preimage],
    exact ⟨xy.2, mem_image_of_mem _ hxy, mem_singleton _, hxy⟩, },
  refine ⟨mt (λ h, finite.subset (finite.bUnion h _) H), infinite_of_infinite_image prod.snd⟩,
  exact λ y _, (rat_approx_to_denom_finite_fibers ξ y),
end

/-- The map sending `(x, y)` to `x/y` gives a bijection between `rat_approx ξ` and
the set `{q : ℚ | |ξ - q| < 1/q.denom^2}`. -/
lemma rat_approx_equiv (ξ : ℝ) :
  bij_on (λ xy : ℤ × ℤ, (xy.1 : ℚ) / xy.2) (rat_approx ξ) {q : ℚ | |ξ - q| < 1 / q.denom ^ 2} :=
begin
  have hcp : ∀ {a b : ℤ}, a.gcd b = 1 → a.nat_abs.coprime b.nat_abs :=
    λ a b h, @int.gcd_eq_nat_abs a b ▸ h,
  refine ⟨_, _, λ q hq, _⟩,
  { simp only [maps_to, mem_set_of_eq, rat.cast_div, rat.cast_coe_int, prod.forall],
    rintros x y ⟨h₁, h₂, h₃⟩,
    rwa [(by norm_cast : ((x / y : ℚ).denom : ℝ) = ((x / y : ℚ).denom : ℤ)),
         rat.denom_div_eq_of_coprime h₁ (hcp h₂)], },
  { simp only [inj_on, prod.forall, prod.mk.inj_iff],
    rintros x y ⟨hxy₁, hxy₂, hxy₃⟩ u v ⟨huv₁, huv₂, huv₃⟩ h,
    have hx := rat.num_div_eq_of_coprime hxy₁ (hcp hxy₂),
    have hy := rat.denom_div_eq_of_coprime hxy₁ (hcp hxy₂),
    rw h at hx hy,
    exact ⟨hx.symm.trans $ rat.num_div_eq_of_coprime huv₁ (hcp huv₂),
           hy.symm.trans $ rat.denom_div_eq_of_coprime huv₁ (hcp huv₂)⟩, },
  { simp only [mem_image, prod.exists],
    refine ⟨q.num, q.denom,
            ⟨by exact_mod_cast q.pos, by {rw [int.gcd_eq_nat_abs], exact q.cop}, _⟩,
            by simp only [int.cast_coe_nat, rat.num_div_denom]⟩,
    rwa [(by norm_cast : ((q.denom : ℤ) : ℝ) = q.denom),
         (by norm_cast : (q.num : ℝ) / q.denom = (q.num / q.denom : ℚ)),
         rat.num_div_denom q], },
end

/-- `rat_approx ξ` is infinite if and only if `{q : ℚ | |ξ - q| < 1/q.denom^2}` is infinite. -/
lemma rat_approx_infinite_iff {ξ : ℝ} :
  (rat_approx ξ).infinite ↔ {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.infinite :=
infinite_coe_iff.symm.trans $ (equiv.infinite_iff $ bij_on.equiv _ $ rat_approx_equiv ξ).trans
  infinite_coe_iff

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/

/-- Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`. -/
lemma ex_better_approx {ξ : ℝ} (hξ : irrational ξ) (q : ℚ) :
  ∃ q' : ℚ, |ξ - q'| < 1 / q'.denom ^ 2 ∧ |ξ - q'| < |ξ - q| :=
begin
  have h : 0 < |ξ - q|,
  { refine abs_pos.mpr (sub_ne_zero.mpr _),
    simp only [irrational, mem_range, not_exists, ← ne.def] at hξ,
    exact (hξ q).symm, },
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|),
  have m_pos : 0 < (m : ℝ) := (one_div_pos.mpr h).trans hm,
  obtain ⟨q', hbd, hden⟩ := real.exists_rat_abs_sub_le_and_denom_le ξ (nat.cast_pos.mp m_pos),
  have den_pos : (0 : ℝ) < q'.denom := nat.cast_pos.mpr q'.pos,
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos,
  refine ⟨q', lt_of_le_of_lt hbd _, lt_of_le_of_lt hbd _⟩,
  { rw [sq, one_div_lt_one_div md_pos (mul_pos den_pos den_pos), mul_lt_mul_right den_pos],
    exact lt_add_of_le_of_pos (nat.cast_le.mpr hden) zero_lt_one, },
  { rw [one_div_lt md_pos h],
    refine hm.trans (lt_of_lt_of_le (lt_add_one _) $
                      (le_mul_iff_one_le_right $ add_pos m_pos zero_lt_one).mpr _),
    exact_mod_cast (q'.pos : 1 ≤ q'.denom), }
end

/-- There is always at least one good rational approximation. -/
lemma rat_approx_nonempty (ξ : ℝ) : {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.nonempty :=
⟨⌊ξ⌋, by simp [abs_of_nonneg, int.fract_lt_one]⟩

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
lemma rat_approx_infinite {ξ : ℝ} (hξ : irrational ξ) :
  {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.infinite :=
begin
  refine or.resolve_left (set.finite_or_infinite _) (λ h, _),
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : ℚ | |ξ - q| < 1 / q.denom ^ 2} (λ q, |ξ - q|) h (rat_approx_nonempty ξ),
  obtain ⟨q', hmem, hbetter⟩ := ex_better_approx hξ q,
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter),
end

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
lemma rat_approx_infinite' {ξ : ℝ} (hξ : irrational ξ) : (rat_approx ξ).infinite :=
rat_approx_infinite_iff.mpr (rat_approx_infinite hξ)

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/

/-- If `x/y` is a good approximation to `a/b`, then `y ≤ b`. -/
lemma denom_bounded_of_rat_approx_rational (a b x y : ℤ) (hb : b ≠ 0)
  (hxy : (x, y) ∈ rat_approx (a / b)) :
  0 < y ∧ y ≤ |b| :=
begin
  obtain ⟨h₁, h₂, h₃⟩ := hxy,
  refine ⟨h₁, _⟩,
  have hy₀ : (y : ℝ) ≠ 0 := int.cast_ne_zero.mpr h₁.ne',
  have hy : 0 < (y ^ 2 : ℝ) := (sq_pos_iff _).mpr hy₀,
  have hb₀ : (b : ℝ) ≠ 0 := int.cast_ne_zero.mpr hb,
  rw [← mul_lt_mul_right (abs_pos.mpr hy.ne'), ← mul_lt_mul_right (abs_pos.mpr hb₀),
      ← abs_mul, ← abs_mul] at h₃,
  field_simp at h₃, -- why doesn't it cancel `↑b * ↑y`?
  rw [sq, ← mul_assoc, ← div_div, mul_div_cancel _ hb₀, mul_div_cancel _ hy₀, abs_mul,
      abs_of_pos (int.cast_pos.mpr h₁ : 0 < (y : ℝ)), mul_comm ↑b] at h₃,
  norm_cast at h₃,
  cases eq_or_ne (a * y - x * b) 0 with H H,
  { exact int.le_of_dvd (abs_pos.mpr hb) ((dvd_abs y b).mpr (int.dvd_of_dvd_mul_right_of_gcd_one
          (dvd_of_mul_left_eq a (eq_of_sub_eq_zero H)) (int.gcd_comm x y ▸ h₂))), },
  { exact ((le_mul_iff_one_le_left h₁).mpr (abs_pos.mpr H)).trans h₃.le, }
end

/-- If `ξ = a/b` is rational, then it has only finitely many good rational approximations. -/
lemma rat_approx_finite' (a b : ℤ) : (rat_approx (a / b)).finite :=
begin
  -- first prove it assuming `b ≠ 0`, then deal with `b = 0` by reducing to `0/1`.
  have H : ∀ a b : ℤ, b ≠ 0 → (rat_approx (a / b)).finite,
  { refine λ a b hb, not_infinite.mp $
             mt (rat_approx_infinite_iff_to_denom_infinite (a / b)).mp (not_infinite.mpr _),
    have h : ∀ y : ℤ, y ∈ prod.snd '' rat_approx (a / b) → 0 < y ∧ y ≤ |b|,
    { intros y hy,
      obtain ⟨xy, hxy⟩ := (mem_image prod.snd (rat_approx (a / b)) y).mp hy,
      exact hxy.2 ▸ denom_bounded_of_rat_approx_rational a b xy.1 xy.2 hb hxy.1, },
    refine finite.subset (finite_Ioc _ _) h, },
  refine or.elim (eq_or_ne b 0) (λ hb, _) (H a b),
  convert H 0 1 one_ne_zero using 2,
  rw [hb, algebra_map.coe_zero, zero_div, div_zero],
end

/-- If `ξ = a/b` is rational, then it has only finitely many good rational approximations. -/
lemma rat_approx_finite (a b : ℤ) : {q : ℚ | |(a / b : ℝ) - q| < 1 / q.denom ^ 2}.finite :=
not_infinite.mp $ (mt rat_approx_infinite_iff.mpr) $ not_infinite.mpr $ rat_approx_finite' a b

/-- The set of good rational approximations to a real number `ξ` is infinite if and only if
`ξ` is irrational. -/
lemma rat_approx_infinite_iff_irrational {ξ : ℝ} :
  {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.infinite ↔ irrational ξ :=
⟨λ h, (irrational_iff_ne_rational ξ).mpr
        (λ a b H, not_infinite.mpr (rat_approx_finite a b) (H ▸ h)),
 rat_approx_infinite⟩

/-- The set of good rational approximations to a real number `ξ` is infinite if and only if
`ξ` is irrational. -/
lemma rat_approx_infinite_iff_irrational' {ξ : ℝ} : (rat_approx ξ).infinite ↔ irrational ξ :=
rat_approx_infinite_iff.trans rat_approx_infinite_iff_irrational

end rat_approx

end dioph_approx
