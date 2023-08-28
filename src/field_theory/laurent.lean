/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.polynomial.taylor
import field_theory.ratfunc

/-!
# Laurent expansions of rational functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main declarations

* `ratfunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `alg_hom`.
* `ratfunc.laurent_injective`: the Laurent expansion at `r` is unique

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `alg_hom` easier,
  which works on `comm_ring` which are not necessarily domains.
-/

universe u
namespace ratfunc
noncomputable theory
open polynomial
open_locale classical non_zero_divisors polynomial

variables {R : Type u} [comm_ring R] [hdomain : is_domain R]
  (r s : R) (p q : R[X]) (f : ratfunc R)

lemma taylor_mem_non_zero_divisors (hp : p ∈ R[X]⁰) : taylor r p ∈ R[X]⁰ :=
begin
  rw mem_non_zero_divisors_iff,
  intros x hx,
  have : x = taylor (r - r) x,
  { simp },
  rwa [this, sub_eq_add_neg, ←taylor_taylor, ←taylor_mul,
       linear_map.map_eq_zero_iff _ (taylor_injective _),
       mul_right_mem_non_zero_divisors_eq_zero_iff hp,
       linear_map.map_eq_zero_iff _ (taylor_injective _)] at hx,
end

/-- The Laurent expansion of rational functions about a value.
Auxiliary definition, usage when over integral domains should prefer `ratfunc.laurent`. -/
def laurent_aux : ratfunc R →+* ratfunc R :=
ratfunc.map_ring_hom (ring_hom.mk (taylor r) (taylor_one _) (taylor_mul _)
  (linear_map.map_zero _) (linear_map.map_add _)) (taylor_mem_non_zero_divisors _)

lemma laurent_aux_of_fraction_ring_mk (q : R[X]⁰) :
  laurent_aux r (of_fraction_ring (localization.mk p q)) =
    of_fraction_ring (localization.mk (taylor r p)
      ⟨taylor r q, taylor_mem_non_zero_divisors r q q.prop⟩) :=
map_apply_of_fraction_ring_mk _ _ _ _

include hdomain

lemma laurent_aux_div :
  laurent_aux r (algebra_map _ _ p / (algebra_map _ _ q)) =
    algebra_map _ _ (taylor r p) / (algebra_map _ _ (taylor r q)) :=
map_apply_div _ _ _ _

@[simp] lemma laurent_aux_algebra_map :
  laurent_aux r (algebra_map _ _ p) = algebra_map _ _ (taylor r p) :=
by rw [←mk_one, ←mk_one, mk_eq_div, laurent_aux_div, mk_eq_div, taylor_one, _root_.map_one]

/-- The Laurent expansion of rational functions about a value. -/
def laurent : ratfunc R →ₐ[R] ratfunc R :=
ratfunc.map_alg_hom (alg_hom.mk (taylor r) (taylor_one _) (taylor_mul _)
  (linear_map.map_zero _) (linear_map.map_add _) (by simp [polynomial.algebra_map_apply]))
  (taylor_mem_non_zero_divisors _)

lemma laurent_div :
  laurent r (algebra_map _ _ p / (algebra_map _ _ q)) =
    algebra_map _ _ (taylor r p) / (algebra_map _ _ (taylor r q)) :=
laurent_aux_div r p q

@[simp] lemma laurent_algebra_map :
  laurent r (algebra_map _ _ p) = algebra_map _ _ (taylor r p) :=
laurent_aux_algebra_map _ _

@[simp] lemma laurent_X : laurent r X = X + C r :=
by rw [←algebra_map_X, laurent_algebra_map, taylor_X, _root_.map_add, algebra_map_C]

@[simp] lemma laurent_C (x : R) : laurent r (C x) = C x :=
by rw [←algebra_map_C, laurent_algebra_map, taylor_C]

@[simp] lemma laurent_at_zero : laurent 0 f = f :=
by { induction f using ratfunc.induction_on, simp }

lemma laurent_laurent :
  laurent r (laurent s f) = laurent (r + s) f :=
begin
  induction f using ratfunc.induction_on,
  simp_rw [laurent_div, taylor_taylor]
end

lemma laurent_injective : function.injective (laurent r) :=
λ _ _ h, by simpa [laurent_laurent] using congr_arg (laurent (-r)) h

end ratfunc
