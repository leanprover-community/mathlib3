/-
Copyright (c) 2022 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import data.polynomial.eval
import data.polynomial.ring_division
import algebra.polynomial.big_operators

/-!
# Lagrange Polynomials

## Main definitions

* `lagrange_basis x i` - The `i`-th Lagrange basis polynomial of `x`
* `lagrange_poly f x` - The Lagrange polynomial interpolating `f` at the points `x`.

## Main statements

* `lagrange_poly_eval_eq` - The Lagrange polynomial interpolating `f` at the points `x` is equal to
  `f` at each `x i`.
* `eq_lagrange_poly_of_eval_eq` - If `p` is a polynomial of degree less than or equal to `n`, and
  interpolates `f` at the points `x`, then `p` is equal to the Lagrange polynomial.
-/


noncomputable theory

variables {R : Type*} [field R] {n : ℕ} {f : R → R} {x : fin (n + 1) → R}

open_locale big_operators

open polynomial

/--
The `i`-th Lagrange basis polynomial of `x`.
-/
def lagrange_basis (x : fin (n + 1) → R) (i : fin (n + 1)) : polynomial R :=
∏ (j : fin (n + 1)), if i = j then 1 else (x i - x j)⁻¹ • (X - C (x j))

lemma lagrange_basis_eval {i : fin (n + 1)} (y : R) :
  (lagrange_basis x i).eval y =
    ∏ (j : fin (n + 1)), if i = j then 1 else (x i - x j)⁻¹ * (y - x j) :=
begin
  unfold lagrange_basis,
  rw [←coe_eval_ring_hom, ring_hom.map_prod],
  apply finset.prod_congr rfl,
  intros j hj,
  split_ifs;
  simp
end

lemma lagrange_basis_eq_one (hx : function.injective x) (i : fin (n + 1)) :
  (lagrange_basis x i).eval (x i) = 1 :=
begin
  rw lagrange_basis_eval,
  apply finset.prod_eq_one,
  intros j hj,
  split_ifs,
  { simp },
  { have : (x i - x j)⁻¹ * (x i - x j) = 1,
    { rw inv_mul_cancel,
      rw sub_ne_zero,
      exact hx.ne h },
    simp [this] }
end

lemma degree_smul {a : R} (h : a ≠ 0) (f : polynomial R):
  degree (a • f) = degree f :=
begin
  apply le_antisymm,
  { exact degree_smul_le _ _ },
  convert degree_smul_le (a⁻¹) (a • f),
  simp [h]
end

lemma degree_lagrange_basis (hx : function.injective x) (i : fin (n + 1)) :
  (lagrange_basis x i).degree = n :=
begin
  unfold lagrange_basis,
  rw degree_prod,
  have : ∀ j, (ite (i = j) 1 ((x i - x j)⁻¹ • (X - C (x j)))).degree = (ite (i = j) 0 1 : ℕ),
  { intros j,
    split_ifs,
    { simp },
    { rw degree_smul,
      { simp },
      apply inv_ne_zero,
      rw sub_ne_zero,
      exact hx.ne h, } },
  rw finset.sum_congr (refl finset.univ) (λ j hj, this j),
  simp_rw ←with_top.coe_coe_add_hom,
  rw ←add_monoid_hom.map_sum,
  apply congr_arg,
  apply @nat.add_left_cancel (∑ j, ite (i = j) 1 0),
  rw [←finset.sum_add_distrib],
  rw finset.sum_congr (refl finset.univ) (λ j hj, apply_ite2 (+) (i = j) 1 0 0 1),
  simp only [finset.card_fin, if_t_t, mul_one, algebra.id.smul_eq_mul, finset.sum_boole,
    nat.cast_id, finset.sum_const],
  rw [finset.filter_eq, if_pos (finset.mem_univ i), finset.card_singleton, add_comm],
end

lemma lagrange_basis_eq_zero {i j : fin (n + 1)} (h : i ≠ j) :
  (lagrange_basis x i).eval (x j) = 0 :=
begin
  rw lagrange_basis_eval,
  apply finset.prod_eq_zero (finset.mem_univ j),
  rw if_neg h,
  simp
end

/--
The Lagrange polynomial interpolating `f` at the points `x`.
-/
def lagrange_poly (f : R → R) (x : fin (n + 1) → R) : polynomial R :=
∑ i, f (x i) • lagrange_basis x i

lemma lagrange_poly_eval (y : R) :
  (lagrange_poly f x).eval y = ∑ i, f (x i) • (lagrange_basis x i).eval y :=
begin
  unfold lagrange_poly,
  rw [←coe_eval_ring_hom, ring_hom.map_sum],
  simp,
end

lemma lagrange_poly_eval_eq (hx : function.injective x) (i : fin (n + 1)) :
  (lagrange_poly f x).eval (x i) = f (x i) :=
begin
  rw [lagrange_poly_eval, finset.sum_eq_single i],
  { simp [lagrange_basis_eq_one hx] },
  { intros j hj h,
    simp [lagrange_basis_eq_zero h] },
  { intro h,
    exact (h (finset.mem_univ i)).elim }
end

lemma lagrange_poly_degree (hx : function.injective x) :
  (lagrange_poly f x).degree ≤ n :=
le_trans (degree_sum_le _ _) (finset.sup_le (λ i hi,
  le_trans (degree_smul_le _ _) (le_of_eq (degree_lagrange_basis hx i))))

theorem eq_lagrange_poly_of_eval_eq (hx : function.injective x) {p : polynomial R}
  (hpn : degree p ≤ n) (hp : ∀ i, p.eval (x i) = f (x i)) :
  p = lagrange_poly f x :=
begin
  set r := p - lagrange_poly f x with hr,
  classical,
  by_contra h,
  have hr0 : r ≠ 0,
  { rwa [hr, sub_ne_zero] },
  have hrdeg : degree r ≤ n := le_trans (degree_sub_le _ _) (max_le hpn (lagrange_poly_degree hx)),
  have hrx : ∀ i, x i ∈ r.roots,
  { intro i,
    rw mem_roots,
    { rw [is_root.def, hr, eval_sub, hp i, lagrange_poly_eval_eq hx, sub_self] },
    { exact hr0 } },
  have : (n + 1) ≤ r.roots.card,
  { have h0 : multiset.map x finset.univ.val ≤ r.roots,
    { rw multiset.le_iff_subset,
      { intros y hy,
        rw multiset.mem_map at hy,
        obtain ⟨i, -, rfl⟩ := hy,
        exact hrx i },
      { exact multiset.nodup_map hx finset.univ.nodup} },
    have h1 : (multiset.map x finset.univ.val).card = n + 1,
    { simp [←finset.card_def] },
    rw ←h1,
    exact multiset.card_le_of_le h0 },
  rw ←with_bot.coe_le_coe at this,
  have hcontra := (this.trans (card_roots hr0)).trans hrdeg,
  rw with_bot.coe_le_coe at hcontra,
  norm_num at hcontra,
end
