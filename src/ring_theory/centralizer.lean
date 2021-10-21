import ring_theory.subring

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

end subring
