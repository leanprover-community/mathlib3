/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.polynomial.taylor
import field_theory.ratfunc
import ring_theory.laurent_series

/-!
# Laurent expansions of rational functions

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
open_locale classical

variables {R : Type u} [comm_ring R] [hdomain : is_domain R]
  (r s : R) (p q : polynomial R) (f : ratfunc R)

lemma taylor_non_zero_divisors (hp : p ∈ non_zero_divisors (polynomial R)) :
  taylor r p ∈ non_zero_divisors (polynomial R) :=
begin
  rw mem_non_zero_divisors_iff,
  intros x hx,
  have : x = taylor (r - r) x,
  { simp },
  have ht := polynomial.taylor_injective r,
  rwa [this, sub_eq_add_neg, ←taylor_taylor, ←taylor_mul,
       linear_map.map_eq_zero_iff _ (taylor_injective _),
       mul_right_mem_non_zero_divisors_eq_zero_iff hp,
       linear_map.map_eq_zero_iff _ (taylor_injective _)] at hx,
end

/-- The Laurent expansion of rational functions about a value.
Auxiliary definition, usage should prefer `ratfunc.laurent`. -/
def laurent_aux : ratfunc R → ratfunc R :=
λ f, ratfunc.lift_on f
  (λ p q, if hq : q ∈ non_zero_divisors (polynomial R) then
    of_fraction_ring (localization.mk (taylor r p)
      ⟨(taylor r q), taylor_non_zero_divisors _ _ hq⟩) else 0)
  begin
    intros p q p' q' hq hq' h,
    simp only [hq, hq', dif_pos, localization.mk_eq_mk', is_localization.mk'_eq_iff_eq,
               subtype.coe_mk, h, ←taylor_mul]
  end

lemma laurent_aux_of_fraction_ring_mk (q : non_zero_divisors (polynomial R)) :
  laurent_aux r (of_fraction_ring (localization.mk p q)) =
    of_fraction_ring (localization.mk (taylor r p)
      ⟨taylor r q, taylor_non_zero_divisors r q q.prop⟩) :=
begin
  dsimp [laurent_aux],
  rw [lift_on_of_fraction_ring_mk, dif_pos]
end

include hdomain

lemma laurent_aux_div :
  laurent_aux r (algebra_map _ _ p / (algebra_map _ _ q)) =
    algebra_map _ _ (taylor r p) / (algebra_map _ _ (taylor r q)) :=
begin
  dsimp [laurent_aux],
  rw [lift_on_div],
  { split_ifs with hq hq,
    { rw [localization.mk_eq_mk', ←mk_coe_def, mk_eq_div, subtype.coe_mk] },
    { rw [mem_non_zero_divisors_iff_ne_zero, not_not] at hq,
      simp only [hq, div_zero, _root_.map_zero] } },
  { simp only [div_zero, if_t_t, dite_eq_ite, is_localization.alg_equiv_apply, _root_.map_zero,
               is_localization.ring_equiv_of_ring_equiv_apply, set_like.coe_mk, forall_const,
               ring_equiv.to_fun_eq_coe, zero_div, of_fraction_ring_eq, fraction_ring.mk_eq_div] },
  { intros p q p' q' hq hq' h,
    rw ←mem_non_zero_divisors_iff_ne_zero at hq hq',
    rw [dif_pos hq, dif_pos hq', of_fraction_ring_injective.eq_iff, localization.mk_eq_mk_iff],
    refine localization.r_of_eq _,
    simp only [subtype.coe_mk, ←taylor_mul, h] }
end

@[simp] lemma laurent_aux_algebra_map :
  laurent_aux r (algebra_map _ _ p) = algebra_map _ _ (taylor r p) :=
by rw [←mk_one, ←mk_one, mk_eq_div, laurent_aux_div, mk_eq_div, taylor_one, _root_.map_one]

/-- The Laurent expansion of rational functions about a value. -/
def laurent : ratfunc R →ₐ[R] ratfunc R :=
{ to_fun := laurent_aux r,
  map_add' := begin
    intros x y,
    induction x using ratfunc.induction_on with xn xd hx,
    induction y using ratfunc.induction_on with yn yd hy,
    rw [laurent_aux_div, laurent_aux_div, div_add_div, ←_root_.map_mul, ←_root_.map_mul,
        ←_root_.map_mul, ←_root_.map_add, laurent_aux_div, taylor_mul, _root_.map_mul,
        _root_.map_add, _root_.map_add, _root_.add_div, taylor_mul, _root_.map_mul,
        mul_div_mul_right, taylor_mul, _root_.map_mul, mul_div_mul_left],
    { simpa [linear_map.map_eq_zero_iff _ (taylor_injective r)] using hx },
    { simpa [linear_map.map_eq_zero_iff _ (taylor_injective r)] using hy },
    { simpa using hx },
    { simpa using hx }
  end,
  map_mul' := begin
    intros f g,
    induction f using ratfunc.induction_on,
    induction g using ratfunc.induction_on,
    simp only [div_mul_div, ←_root_.map_mul, laurent_aux_div, taylor_mul]
  end,
  map_one' := begin
    have : algebra_map (polynomial R) (ratfunc R) 1 = 1 := _root_.map_one _,
    rw [←this, laurent_aux_algebra_map, taylor_one, _root_.map_one]
  end,
  map_zero' := begin
    have : algebra_map (polynomial R) (ratfunc R) 0 = 0 := _root_.map_zero _,
    rw [←this, laurent_aux_algebra_map, linear_map.map_zero, _root_.map_zero]
  end,
  commutes' := λ _, by rw [algebra_map_eq_C, ←algebra_map_C,
                           laurent_aux_algebra_map, taylor_C] }

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
