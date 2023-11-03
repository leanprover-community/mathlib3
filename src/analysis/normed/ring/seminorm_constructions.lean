/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import analysis.special_functions.pow
import analysis.normed.ring.seminorm
import topology.metric_space.basic
import topology.algebra.order.monotone_convergence

/-!
# Smoothing procedures for seminorms

This file contains several ring seminorm constructions that will be used in the proof that a rank 1
nonarchimedean valuation on a complete field can be uniquely extended to any algebraic extension.

## Main declarations

* `seminorm_from_const`: Given a power-multiplicative ring seminorm `f` on a ring `R` and an
  element `c ∈ R` with `f c ≠ 0`, the real-valued function sending `x ∈ R` to the limit of
  `(f (x * c^n))/((f c)^n)` is a power-multiplicative ring seminorm on `R` satisfying some
  multiplicativity conditions [BGR84, Proposition 1.3.2/2].

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

noncomputable theory

open filter

open_locale topological_space

section defs

/-- A function `f : α → β` is power-multiplicative if for all `a ∈ α` and all positive `n ∈ ℕ`,
  `f (a ^ n) = (f a) ^ n`. -/
def is_pow_mul {α β : Type*} [has_pow α ℕ] [has_pow β ℕ]  (f : α → β) :=
∀ (a : α) {n : ℕ} (hn : n ≠ 0), f (a ^ n) = (f a) ^ n

/-- A function `f : α → β` is nonarchimedean if it satisfies the inequality
  `f (a + b) ≤ max (f a) (f b)` for all `a, b ∈ α`. -/
def is_nonarchimedean {α : Type*} [has_add α] {β : Type*} [linear_order β] (f : α → β) : Prop :=
∀ r s, f (r + s) ≤ max (f r) (f s)

end defs

section seminorm_from_const
/- In this section we prove Proposition 1.3.2/2 in
[S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]. -/

section ring

variables {R : Type*} [comm_ring R] (c : R) (f : ring_seminorm R) (hc : 0 ≠ f c)
  (hpm : is_pow_mul f)

/-- For a ring seminorm `f` on `R` and `c ∈ R`, the sequence given by `(f (x * c^n))/((f c)^n)`. -/
def seminorm_from_const_seq (x : R) : ℕ → ℝ :=
λ n, (f (x * c^n))/((f c)^n)

lemma seminorm_from_const_nonneg (x : R) (n : ℕ) : 0 ≤ seminorm_from_const_seq c f x n :=
div_nonneg (map_nonneg f (x * c ^ n)) (pow_nonneg (map_nonneg f c) n)

lemma seminorm_from_const_is_bdd_below (x : R) :
  bdd_below (set.range (seminorm_from_const_seq c f x)) :=
begin
  use 0,
  rw mem_lower_bounds,
  rintros r ⟨n, hn⟩,
  rw ← hn,
  exact seminorm_from_const_nonneg c f x n,
end

variable {f}

lemma seminorm_from_const_apply (x : R) (n : ℕ) :
  seminorm_from_const_seq c f x n = (f (x * c^n))/((f c)^n) :=
rfl

lemma seminorm_from_const_seq_zero (hf : f 0 = 0) :
  seminorm_from_const_seq c f 0 = 0 :=
begin
  ext n,
  rw [seminorm_from_const_apply, zero_mul, hf, zero_div],
  refl,
end

variable {c}

include hc hpm

lemma seminorm_from_const_seq_one {n : ℕ} (hn : n ≠ 0) :
  seminorm_from_const_seq c f 1 n = 1 :=
by rw [seminorm_from_const_apply, one_mul, hpm _ hn, div_self (pow_ne_zero n (ne.symm hc))]

lemma seminorm_from_const_seq_antitone (x : R) :
  antitone (seminorm_from_const_seq c f x) :=
begin
  apply antitone_nat_of_succ_le,
  have hc_pos : 0 < f c := lt_of_le_of_ne (map_nonneg f _) hc,
  intros n,
  simp only [seminorm_from_const_seq],
  rw [pow_add, ← mul_assoc],
  apply le_trans ((div_le_div_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _)),
  rw [hpm c one_ne_zero, mul_div_assoc, pow_add, div_eq_mul_inv, mul_inv_rev, pow_one,
    ← mul_assoc (f c), mul_inv_cancel (ne.symm hc), div_eq_mul_inv, one_mul],
end

omit hc hpm

variables (f c)

/-- The real-valued function sending `x ∈ R` to the limit of `(f (x * c^n))/((f c)^n)`. -/
def seminorm_from_const_def : R → ℝ := λ x, ⨅ n, seminorm_from_const_seq c f x n

include hc hpm

variables {f c}

lemma seminorm_from_const_def_is_limit (x : R) :
  at_top.tendsto ((seminorm_from_const_seq c f x)) (𝓝 (seminorm_from_const_def  c f x)) :=
tendsto_at_top_is_glb (seminorm_from_const_seq_antitone hc hpm x)
  (is_glb_cinfi (seminorm_from_const_is_bdd_below c f x))

lemma seminorm_from_const_zero : seminorm_from_const_def c f 0 = 0 :=
tendsto_nhds_unique (seminorm_from_const_def_is_limit hc hpm 0)
  (by simpa [seminorm_from_const_seq_zero c (map_zero _)] using tendsto_const_nhds)

lemma seminorm_from_const_is_norm_one_class : seminorm_from_const_def c f 1 = 1 :=
tendsto_nhds_unique_of_eventually_eq (seminorm_from_const_def_is_limit hc hpm 1)
  tendsto_const_nhds (eventually_at_top.mpr
    ⟨1, λ n hn, seminorm_from_const_seq_one hc hpm (nat.one_le_iff_ne_zero.mp hn)⟩)

lemma seminorm_from_const_mul (x y : R) :
  seminorm_from_const_def c f (x * y) ≤
    seminorm_from_const_def c f x * seminorm_from_const_def c f y :=
begin
  have hlim : at_top.tendsto (λ n, seminorm_from_const_seq c f (x * y) (2 *n))
    (𝓝 (seminorm_from_const_def  c f (x * y) )),
  { apply (seminorm_from_const_def_is_limit hc hpm (x * y)).comp,
    apply tendsto_at_top_at_top_of_monotone,
    { intros n m hnm, simp only [mul_le_mul_left, nat.succ_pos', hnm], },
    { rintro n, use n, linarith, }},
  apply le_of_tendsto_of_tendsto' hlim ((seminorm_from_const_def_is_limit hc hpm x).mul
    (seminorm_from_const_def_is_limit hc hpm y)),
  intro n,
  simp only [seminorm_from_const_seq],
  rw [div_mul_div_comm, ← pow_add, two_mul, div_le_div_right
    (pow_pos (lt_of_le_of_ne (map_nonneg f _) hc) _),
    pow_add, ← mul_assoc, mul_comm (x * y), ← mul_assoc, mul_assoc, mul_comm (c^n)],
  exact map_mul_le_mul f (x * c ^ n) (y * c ^ n),
end

lemma seminorm_from_const_neg (x : R)  :
  seminorm_from_const_def c f (-x) = seminorm_from_const_def c f x  :=
begin
  refine tendsto_nhds_unique (seminorm_from_const_def_is_limit  hc hpm (-x)) _,
  convert seminorm_from_const_def_is_limit hc hpm x using 1,
  simp only [seminorm_from_const_seq],
  ext n,
  rw [neg_mul, map_neg_eq_map],
end

lemma seminorm_from_const_add (x y : R)  :
  seminorm_from_const_def c f (x + y) ≤
    seminorm_from_const_def c f x +  seminorm_from_const_def c f y :=
begin
  apply le_of_tendsto_of_tendsto' (seminorm_from_const_def_is_limit hc hpm (x + y))
    ((seminorm_from_const_def_is_limit hc hpm x).add (seminorm_from_const_def_is_limit hc hpm y)),
  intro n,
  have h_add : f ((x + y) * c ^ n) ≤ (f (x * c ^ n)) + (f (y * c ^ n)),
  { rw add_mul, exact map_add_le_add f _ _ },
  simp only [seminorm_from_const_seq],
  rw div_add_div_same,
  exact (div_le_div_right (pow_pos (lt_of_le_of_ne (map_nonneg f _) hc) _)).mpr h_add,
end

/-- The function `seminorm_from_const` is a `ring_seminorm` on `R`. -/
def seminorm_from_const :
  ring_seminorm R  :=
{ to_fun    := seminorm_from_const_def c f,
  map_zero' := seminorm_from_const_zero hc hpm,
  add_le'   := seminorm_from_const_add hc hpm,
  neg'      := seminorm_from_const_neg hc hpm,
  mul_le'   := seminorm_from_const_mul hc hpm }

lemma seminorm_from_const_is_norm_le_one_class : seminorm_from_const hc hpm 1 ≤ 1 :=
(seminorm_from_const_is_norm_one_class hc hpm).le

lemma seminorm_from_const_is_nonarchimedean (hna : is_nonarchimedean f) :
  is_nonarchimedean (seminorm_from_const hc hpm)  :=
begin
  intros x y,
  apply le_of_tendsto_of_tendsto' (seminorm_from_const_def_is_limit hc hpm (x + y))
    ((seminorm_from_const_def_is_limit hc hpm x).max (seminorm_from_const_def_is_limit hc hpm y)),
  intro n,
  have hmax : f ((x + y) * c ^ n) ≤ max (f (x * c ^ n)) (f (y * c ^ n)),
  { rw add_mul, exact hna _ _ },
  rw le_max_iff at hmax ⊢,
  cases hmax; [left, right];
  exact (div_le_div_right (pow_pos (lt_of_le_of_ne (map_nonneg f c) hc) _)).mpr hmax,
end

lemma seminorm_from_const_is_pow_mult : is_pow_mul (seminorm_from_const hc hpm) :=
begin
  intros x m hm,
  simp only [seminorm_from_const],
  have hpow := (seminorm_from_const_def_is_limit hc hpm x).pow m,
  have hlim : at_top.tendsto (λ n, seminorm_from_const_seq c f (x^m) (m*n))
    (𝓝 (seminorm_from_const_def  c f (x^m) )),
  { apply (seminorm_from_const_def_is_limit hc hpm (x^m)).comp,
    apply tendsto_at_top_at_top_of_monotone,
    { intros n k hnk, exact mul_le_mul_left' hnk m, },
    { rintro n, use n, refine nat.le_mul_of_pos_left (nat.pos_of_ne_zero hm) }},
  apply tendsto_nhds_unique hlim,
  convert (seminorm_from_const_def_is_limit hc hpm x).pow  m,
  ext n,
  simp only [seminorm_from_const_seq],
  rw [div_pow, ← hpm _ hm, ← pow_mul, mul_pow, ← pow_mul, mul_comm m n],
end

lemma seminorm_from_const_le_seminorm (x : R) : seminorm_from_const hc hpm x ≤ f x :=
begin
  apply le_of_tendsto (seminorm_from_const_def_is_limit hc hpm x),
  simp only [eventually_at_top, ge_iff_le],
  use 1,
  rintros n hn,
  apply le_trans ((div_le_div_right (pow_pos (lt_of_le_of_ne (map_nonneg f c) hc) _)).mpr
    (map_mul_le_mul _ _ _)),
  rw [hpm c (nat.one_le_iff_ne_zero.mp hn), mul_div_assoc, div_self (pow_ne_zero n hc.symm),
    mul_one],
end

lemma seminorm_from_const_apply_of_is_mult {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
  seminorm_from_const hc hpm x = f x :=
begin
  have hlim : at_top.tendsto (seminorm_from_const_seq c f x) (𝓝 (f x)),
  { have hseq : seminorm_from_const_seq c f x = λ n, f x,
    { ext n,
      by_cases hn : n = 0,
      { simp only [seminorm_from_const_seq],
        rw [hn, pow_zero, pow_zero, mul_one, div_one], },
      { simp only [seminorm_from_const_seq],
        rw [hx (c ^n), hpm _ hn, mul_div_assoc,
          div_self (pow_ne_zero n hc.symm), mul_one], }},
    simpa [hseq] using tendsto_const_nhds, },
  exact tendsto_nhds_unique (seminorm_from_const_def_is_limit hc hpm x) hlim,
end

lemma seminorm_from_const_is_mul_of_is_mul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
  seminorm_from_const hc hpm (x * y) =
    seminorm_from_const hc hpm x * seminorm_from_const hc hpm y :=
begin
  have hlim : at_top.tendsto (seminorm_from_const_seq c f (x * y))
    (𝓝 (seminorm_from_const hc hpm x * seminorm_from_const hc hpm y)),
  { rw seminorm_from_const_apply_of_is_mult hc hpm hx,
    have hseq : seminorm_from_const_seq c f (x * y) = λ n, f x * seminorm_from_const_seq c f y n,
    { ext n,
      simp only [seminorm_from_const_seq],
      rw [mul_assoc, hx, mul_div_assoc], },
    simpa [hseq]
      using (seminorm_from_const_def_is_limit hc hpm y).const_mul _ },
  exact tendsto_nhds_unique (seminorm_from_const_def_is_limit hc hpm (x * y)) hlim,
end

lemma seminorm_from_const_apply_c : seminorm_from_const hc hpm c = f c :=
begin
  have hlim : at_top.tendsto (seminorm_from_const_seq c f c) (𝓝 (f c)),
  { have hseq : seminorm_from_const_seq c f c = λ n, f c,
    { ext n,
      simp only [seminorm_from_const_seq],
      rw [← pow_succ, hpm _ (nat.succ_ne_zero n), pow_succ, mul_div_assoc,
        div_self (pow_ne_zero n hc.symm), mul_one] },
    simpa [hseq] using tendsto_const_nhds },
    exact tendsto_nhds_unique (seminorm_from_const_def_is_limit hc hpm c) hlim,
end

lemma seminorm_from_const_c_is_mul (x : R) :
  seminorm_from_const hc hpm (c * x) =
    seminorm_from_const hc hpm c * seminorm_from_const hc hpm x :=
begin
  have hlim : at_top.tendsto (λ n, seminorm_from_const_seq c f x (n + 1))
    (𝓝 (seminorm_from_const_def  c f x)),
  { apply (seminorm_from_const_def_is_limit hc hpm x).comp,
    apply tendsto_at_top_at_top_of_monotone,
    { intros n m hnm,
      exact add_le_add_right hnm 1, },
    { rintro n, use n, linarith, }},
  rw seminorm_from_const_apply_c hc hpm,
  apply tendsto_nhds_unique (seminorm_from_const_def_is_limit hc hpm (c * x)),
  have hterm : seminorm_from_const_seq c f (c * x) =
    (λ n, f c * (seminorm_from_const_seq c f x (n + 1))),
  { simp only [seminorm_from_const_seq],
    ext n,
    rw [mul_comm c, pow_succ, pow_succ, mul_div, div_eq_mul_inv _ (f c * f c ^ n), mul_inv,
      ← mul_assoc, mul_comm (f c), mul_assoc _ (f c), mul_inv_cancel hc.symm,
      mul_one, mul_assoc, div_eq_mul_inv] },
  simpa [hterm] using tendsto_const_nhds.mul hlim,
end

end ring

section field

variables {K : Type*} [field K] (k : K) {g : ring_seminorm K} (hg_k : g k ≠ 0)
  (hg_pm : is_pow_mul g)

/-- If `K` is a field, the function `seminorm_from_const` is a `ring_norm` on `K`. -/
def seminorm_from_const_ring_norm_of_field : ring_norm K :=
g.to_ring_norm (ring_seminorm.ne_zero_iff.mpr ⟨k, hg_k⟩)

end field

end seminorm_from_const
