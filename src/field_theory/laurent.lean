/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.polynomial.taylor
import field_theory.ratfunc

/-!
# Laurent expansions of rational functions

## Main declarations

* `ratfunc.laurent`: the Laurent expansion of the rational function `f` at `r`, as an `alg_hom`.

## Implementation details

Implemented as the quotient of two Taylor expansions, over domains.
An auxiliary definition is provided first to make the construction of the `alg_hom` easier.
-/

namespace ratfunc
noncomputable theory

variables {K : Type*} [comm_ring K] [is_domain K]
  (r : K) (p q : polynomial K) (f g : ratfunc K)

/-- The Laurent expansion of rational functions about a root.
Auxiliary definition, usage should prefer `ratfunc.laurent`. -/
def laurent_aux : ratfunc K → ratfunc K :=
λ f, ratfunc.lift_on f
    (λ p q, algebra_map _ _ (polynomial.taylor r p) / (algebra_map _ _ (polynomial.taylor r q)))
    begin
      intros p q p' q' hq hq' h,
      rw [←mk_eq_div, ←mk_eq_div, mk_eq_mk],
      { simp [←polynomial.taylor_mul, h] },
      { rwa [ne.def, linear_map.map_eq_zero_iff _ (polynomial.taylor_injective r)] },
      { rwa [ne.def, linear_map.map_eq_zero_iff _ (polynomial.taylor_injective r)] }
    end

lemma laurent_aux_div :
  laurent_aux r (algebra_map _ _ p / (algebra_map _ _ q)) =
    algebra_map _ _ (polynomial.taylor r p) / (algebra_map _ _ (polynomial.taylor r q)) :=
lift_on_div _ _ _ (by simp) _

@[simp] lemma laurent_aux_algebra_map :
  laurent_aux r (algebra_map _ _ p) = algebra_map _ _ (polynomial.taylor r p) :=
by rw [←mk_one, ←mk_one, mk_eq_div, laurent_aux_div, mk_eq_div, polynomial.taylor_one, map_one]

/-- The Laurent expansion of rational functions about a root. -/
def laurent : ratfunc K →ₐ[K] ratfunc K :=
{ to_fun := laurent_aux r,
  map_add' := begin
    intros x y,
    induction x using ratfunc.induction_on with xn xd hx,
    induction y using ratfunc.induction_on with yn yd hy,
    rw [laurent_aux_div, laurent_aux_div, div_add_div, ←map_mul, ←map_mul, ←map_mul, ←map_add,
        laurent_aux_div, polynomial.taylor_mul, map_mul,
        map_add, map_add, add_div, polynomial.taylor_mul, map_mul, mul_div_mul_right,
        polynomial.taylor_mul, map_mul, mul_div_mul_left],
    { simpa [linear_map.map_eq_zero_iff _ (polynomial.taylor_injective r)] using hx },
    { simpa [linear_map.map_eq_zero_iff _ (polynomial.taylor_injective r)] using hy },
    { simpa using hx },
    { simpa using hx }
  end,
  map_mul' := begin
    intros f g,
    induction f using ratfunc.induction_on with fn fd hf,
    induction g using ratfunc.induction_on with gn gd hg,
    simp only [div_mul_div, ←map_mul, laurent_aux_div, polynomial.taylor_mul]
  end,
  map_one' := begin
    have : algebra_map (polynomial K) (ratfunc K) 1 = 1 := by simp only [map_one],
    rw [←this, laurent_aux_algebra_map, polynomial.taylor_one, map_one]
  end,
  map_zero' := begin
    have : algebra_map (polynomial K) (ratfunc K) 0 = 0 := by simp only [map_zero],
    rw [←this, laurent_aux_algebra_map, linear_map.map_zero, map_zero]
  end,
  commutes' := λ _, by rw [algebra_map_eq_C, ←algebra_map_C,
                           laurent_aux_algebra_map, polynomial.taylor_C] }

lemma laurent_div :
  laurent r (algebra_map _ _ p / (algebra_map _ _ q)) =
    algebra_map _ _ (polynomial.taylor r p) / (algebra_map _ _ (polynomial.taylor r q)) :=
laurent_aux_div r p q

@[simp] lemma laurent_algebra_map :
  laurent r (algebra_map _ _ p) = algebra_map _ _ (polynomial.taylor r p) :=
laurent_aux_algebra_map _ _

@[simp] lemma laurent_X : laurent r X = X + C r :=
by rw [←algebra_map_X, laurent_algebra_map, polynomial.taylor_X, map_add, algebra_map_C]

@[simp] lemma laurent_C (x : K) : laurent r (C x) = C x :=
by rw [←algebra_map_C, laurent_algebra_map, polynomial.taylor_C]

end ratfunc
