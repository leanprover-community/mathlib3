/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import data.polynomial.ring_division
import linear_algebra.dimension
import algebra.polynomial.big_operators

open finset

open_locale big_operators

noncomputable theory

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
structure linear_recurrence (α : Type*) [comm_semiring α] := (order : ℕ) (coeffs : fin order → α)

namespace linear_recurrence

section comm_semiring

variables {α : Type*} [comm_semiring α] (E : linear_recurrence α)

/-- We say that a sequence `u` is solution of `linear_recurrence order coeffs` when we have
  `u (n + order) = ∑ i : fin order, coeffs i * u (n + i)` for any `n`. -/
def is_solution (u : ℕ → α) :=
  ∀ n, u (n + E.order) = (∑ i, E.coeffs i * u (n + i))

/-- A solution of a `linear_recurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
def mk_sol (init : fin E.order → α) : ℕ → α
| n := if h : n < E.order then init ⟨n, h⟩ else
  ∑ k : fin E.order, have n - E.order + k.1 < n, by have := k.2; omega,
    E.coeffs k * mk_sol (n - E.order + k)

/-- `E.mk_sol` indeed gives solutions to `E`. -/
lemma is_sol_mk_sol (init : fin E.order → α) :
  E.is_solution (E.mk_sol init) :=
  λ n, by rw mk_sol; simp

/-- `E.mk_sol init`'s first `E.order` terms are `init`. -/
lemma mk_sol_eq_init (init : fin E.order → α) :
  ∀ n : fin E.order, E.mk_sol init n = init n :=
  λ n, by rw mk_sol; simp [fin.coe_eq_val, n.2]

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mk_sol init n`. -/
lemma eq_mk_of_is_sol_of_eq_init {u : ℕ → α} {init : fin E.order → α}
  (h : E.is_solution u) (heq : ∀ n : fin E.order, u n = init n) :
  ∀ n, u n = E.mk_sol init n
| n := if h' : n < E.order
  then by rw mk_sol; simp only [h', dif_pos]; exact_mod_cast heq ⟨n, h'⟩
  else begin
    rw mk_sol,
    rw ← nat.sub_add_cancel (le_of_not_lt h'),
    rw h (n-E.order),
    simp [h'],
    congr',
    ext k,
    exact have wf : n - E.order + k.1 < n, by have := k.2; omega,
      by rw eq_mk_of_is_sol_of_eq_init
  end

/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mk_sol init`. This proves that `E.mk_sol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
lemma eq_mk_of_is_sol_of_eq_init' {u : ℕ → α} {init : fin E.order → α}
  (h : E.is_solution u) (heq : ∀ n : fin E.order, u n = init n) :
  u = E.mk_sol init := funext (E.eq_mk_of_is_sol_of_eq_init h heq)

example : semimodule α (ℕ → α) := by apply_instance

/-- The space of solutions of `E`, as a `submodule` over `α` of the semimodule `ℕ → α`. -/
def sol_space : submodule α (ℕ → α) :=
{ carrier := {u | E.is_solution u},
  zero_mem' := λ n, by simp,
  add_mem' := λ u v hu hv n, by simp [mul_add, sum_add_distrib, hu n, hv n],
  smul_mem' := λ a u hu n, by simp [hu n, mul_sum]; congr'; ext; ac_refl }

/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
lemma is_sol_iff_mem_sol_space (u : ℕ → α) :
  E.is_solution u ↔ u ∈ E.sol_space := by refl

/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `linear_equiv`. -/
def sol_space_linear_equiv_init_space :
  E.sol_space ≃ₗ[α] (fin E.order → α) :=
{ to_fun := λ u x, (u : ℕ → α) x,
  map_add' := λ u v, by ext; simp; norm_cast,
  map_smul' := λ a u, by ext; simp,
  inv_fun := λ u, ⟨E.mk_sol u, E.is_sol_mk_sol u⟩,
  left_inv := λ u, by ext n; symmetry; apply E.eq_mk_of_is_sol_of_eq_init u.2; intros k; refl,
  right_inv := λ u, function.funext_iff.mpr (λ n, E.mk_sol_eq_init u n) }

/-! `E.tuple_succ` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. This operation is quite useful for determining closed-form
  solutions of `E`. -/

/-- `E.tuple_succ` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. -/
def tuple_succ : (fin E.order → α) →ₗ[α] (fin E.order → α) :=
{ to_fun := λ X i, if h : i.1 + 1 < E.order then X ⟨i+1, h⟩ else (∑ i, E.coeffs i * X i),
  map_add' := λ x y,
    begin
      ext i,
      by_cases h : i.1 + 1 < E.order,
      { simp [h] },
      { simp [h, mul_add, sum_add_distrib] }
    end,
  map_smul' := λ x y,
    begin
      ext i,
      by_cases h : i.1 + 1 < E.order,
      { simp [h] },
      { simp [h, mul_sum], congr, ext, ac_refl }
    end }

end comm_semiring

section field

variables {α : Type*} [field α] (E : linear_recurrence α)

/-- The dimension of `E.sol_space` is `E.order`. -/
lemma sol_space_dim :
  vector_space.dim α E.sol_space = E.order :=
@dim_fin_fun α _ E.order ▸ E.sol_space_linear_equiv_init_space.dim_eq

end field

section comm_ring

variables {α : Type*} [comm_ring α] (E : linear_recurrence α)

/-- The auxiliary polynomial of `E` is `X ^ E.order - ∑ i : fin E.order, (E.coeffs i) * X ^ i`. -/
def aux_poly : polynomial α :=
  polynomial.monomial E.order 1 - (∑ i : fin E.order, polynomial.monomial i (E.coeffs i))

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s auxiliary polynomial. -/
lemma geom_sol_iff_root_aux_poly (q : α) :
  E.is_solution (λ n, q^n) ↔ E.aux_poly.is_root q :=
begin
  rw [aux_poly, polynomial.is_root.def, polynomial.eval],
  simp only [polynomial.eval₂_finset_sum, one_mul,
              ring_hom.id_apply, polynomial.eval₂_monomial, polynomial.eval₂_sub],
  split,
  { intro h,
    specialize h 0,
    simp only [zero_add] at h,
    rwa ← sub_eq_zero_iff_eq at h },
  { intros h n,
    rw sub_eq_zero_iff_eq at h,
    simp only [pow_add],
    rw [h, mul_sum],
    congr,
    ext,
    ring }
end

end comm_ring

end linear_recurrence
