import algebra.ordered_field
import tactic.linarith tactic.ring

section

variables {α : Type*} [linear_ordered_field α] {a b c : α}

lemma exists_le_mul : ∀ a : α, ∃ x : α, a ≤ x * x :=
begin
  assume a, cases le_total 1 a with ha ha,
  { use a, exact le_mul_of_ge_one_left (by linarith) ha },
  { use 1, linarith }
end

lemma exists_lt_mul : ∀ a : α, ∃ x : α, a < x * x :=
begin
  assume a, rcases (exists_le_mul a) with ⟨x, hx⟩,
  cases le_total 0 x with hx' hx',
  { use (x + 1),
    have : (x+1)*(x+1) = x*x + 2*x + 1, ring,
    exact lt_of_le_of_lt hx (by rw this; linarith)},
  { use (x - 1),
    have : (x-1)*(x-1) = x*x - 2*x + 1, ring,
    exact lt_of_le_of_lt hx (by rw this; linarith)}
end

end

section

variables {α : Type*} [discrete_linear_ordered_field α] {a b c : α}

/-- If a polynomial of degree 2 is always nonnegative, then its dicriminant is nonpositive -/
lemma discriminant_le_zero {a b c : α} (h : ∀ x : α,  0 ≤ a*x*x + b*x + c) : b*b - 4*a*c ≤ 0 :=
have hc : 0 ≤ c, by { have := h 0, linarith },
begin
  by_cases ha : a = 0, by_cases hb : b = 0,
  { rw [ha, hb], ring }, -- `a = b = 0`
  { have := h ((-c-1)/b), rw [ha, mul_div_cancel' _ hb] at this, linarith }, --`a = 0 but b ≠ 0`
  by_cases hb : b = 0,
  -- the case where `a ≠ 0` but `b = 0`
  { rw hb at *,
    cases le_total 0 a with ha' ha',
    { simp only [neg_nonpos, zero_add, sub_eq_add_neg, mul_zero],
      exact mul_nonneg (mul_nonneg (by linarith) ha') hc },
    { rcases exists_lt_mul (-c/a) with ⟨x, hx⟩,
      have := mul_lt_mul_of_neg_left hx (lt_of_le_of_ne ha' ha),
      rw [mul_div_cancel' _ ha, ← mul_assoc] at this,
      have h₂ := h x, linarith } },
  -- the case where `a ≠ 0` and `b ≠ 0`
  { cases le_total 0 a with ha' ha',
    { have : 4*a* (a*(-(b/a)*(1/2))*(-(b/a)*(1/2)) + b*(-(b/a)*(1/2)) + c) = -(b*b - 4*a*c), from
      calc
        4*a* (a*(-(b/a)*(1/2))*(-(b/a)*(1/2)) + b*(-(b/a)*(1/2)) + c) =
          4*a*a*(-(b/a)*(1/2))*(-(b/a)*(1/2)) + 4*a*b*(-(b/a)*(1/2)) + 4*a*c : by ring
        ... = (a*(b/a)) * (a*(b/a)) - 2*(a*(b/a))*b + 4*a*c : by ring
        ... = -(b*b - 4*a*c) : by { simp only [mul_div_cancel' b ha], ring },
      have ha' : 0 ≤ 4*a, linarith,
      have h := (mul_nonneg ha' (h (-(b/a) * (1/2)))),
      rw this at h, rwa ← neg_nonneg },
    { by_cases hc' : c = 0,
      { rw hc' at *,
        have : -(a*-b*-b + b*-b + 0) = (1-a)*(b*b), ring,
        have h := h (-b), rw [← neg_nonpos, this] at h,
        have : b * b ≤ 0, from nonpos_of_mul_nonpos_left h (by linarith),
        linarith },
      { have h := h (-c/b),
        have : a*(-c/b)*(-c/b) + b*(-c/b) + c = a*((c/b)*(c/b)),
          rw mul_div_cancel' _ hb, ring,
        rw this at h,
        have : 0 ≤ a := nonneg_of_mul_nonneg_right h (mul_self_pos $ div_ne_zero hc' hb),
        linarith [lt_of_le_of_ne ha' ha] } } }
end

end
