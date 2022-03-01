/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import ring_theory.subring.basic

/-!
# FOOBAR TODO

-- should this go near the `submonoid` centralizer?
-/


namespace subring

variables {R : Type*} [ring R]

def centralizer (r : R) : subring R :=
{ carrier := {x | r * x = x * r},
  zero_mem' := by simp only [mul_zero, zero_mul, set.mem_set_of_eq],
  one_mem' := by simp only [mul_one, one_mul, set.mem_set_of_eq],
  add_mem' := λ x y hx hy, by { simp only [set.mem_set_of_eq, mul_add, add_mul, *] at *, },
  neg_mem' := λ x hx, by { simp only [set.mem_set_of_eq,
    ← neg_mul_eq_mul_neg, ← neg_mul_eq_neg_mul, *] at *, },
  mul_mem' := λ x y hx hy,
  by { simp only [set.mem_set_of_eq] at *,
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc], } }

@[simp] lemma mem_centralizer (r x : R) : x ∈ centralizer r ↔ r * x = x * r := iff.rfl

lemma center_le_centralizer (r : R) : center R ≤ centralizer r := λ x hx, hx r

lemma mem_center_of_centralizer_eq_top {r : R} (h : centralizer r = ⊤) :
  r ∈ center R :=
λ x, eq.symm $ show x ∈ centralizer r, by { rw h, exact mem_top x }

end subring
