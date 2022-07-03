import tactic.move_add
import data.list.of_fn
import algebra.group.pi

variables {R : Type*} [add_comm_semigroup R] {a b c d e f g h : R}

example (e f g : R) (h : a + b + c = d) : b + (a + c) = d :=
begin
  success_if_fail_with_msg {move_add [d] at *} "'d' is an unused variable",
  move_add at *,
  success_if_fail_with_msg {move_add at *} "nothing changed",
  success_if_fail_with_msg {move_add [a, e, f, g] at h a b c ⊢}
    "'[a, b, c]' did not change\n'[e, f, g]' are unused variables",
  success_if_fail_with_msg {move_add [a, e, f, g] at h ⊢} "'[e, f, g]' are unused variables",
  success_if_fail_with_msg {move_add at ⊢ h} "Goal did not change\n'[h]' did not change",
  move_add ← a at *,  -- `move_add` closes the goal, since, after rearranging, it tries `assumption`
end

example {R : Type*} [comm_semigroup R] (a b c d e f g : R) (h : a * b * c = d) : b * (a * c) = d :=
begin
  success_if_fail_with_msg {move_mul [d] at *} "'d' is an unused variable",
  move_mul at *,
  success_if_fail_with_msg {move_mul at *} "nothing changed",
  success_if_fail_with_msg {move_mul [a, e, f, g] at h a b c ⊢}
    "'[a, b, c]' did not change\n'[e, f, g]' are unused variables",
  success_if_fail_with_msg {move_mul [a, e, f, g] at h ⊢} "'[e, f, g]' are unused variables",
  success_if_fail_with_msg {move_mul at ⊢ h} "Goal did not change\n'[h]' did not change",
  success_if_fail_with_msg {move_mul at ⊢} "Goal did not change",
  move_mul ← a at *,  -- `move_mul` closes the goal, since, after rearranging, it tries `assumption`
end

example : let k := c + (a + b) in k = a + b + c :=
begin
  move_add [← a, c],
  simp only,
end

example (n : ℕ) : list.of_fn (λ i : fin (n + 3), (i : ℕ)) = list.of_fn (λ i : fin (3 + n), i) :=
begin
  move_add [←n],
end

example (a b : ℕ) : a + max a b = max b a + a :=
begin
  move_oper [max] ← a at *,
  move_oper [(+)] a at *,
end

example (h : b + a = b + c + a) : a + b = a + b + c :=
by move_add [a]

example {R : Type*} [comm_semigroup R] {a b : R} :
  ∀ x : R, ∃ y : R, a * x * b * y = x * y * b * a :=
by { move_mul [a, b], exact λ x, ⟨x, rfl⟩ }

example {R : Type*} [has_add R] [comm_semigroup R] {a b c d e f g : R} :
  a * (b * c * a) * ((d * e) * e) * f * g = (c * b * a) * (e * (e * d)) * g * f * a :=
by move_mul [a, a, b, c, d, e, f]

example [has_mul R] [has_neg R] : a + (b + c + a) * (- (d + e) + e) + f + g =
  (c + b + a) * (e + - (e + d)) + g + f + a :=
by move_add [b, d, g, f, a, e]

example (h : d + b + a = b + a → d + c + a = c + a) : a + d + b = b + a → d + c + a = a + c :=
by move_add [a]

example [decidable_eq R] : if b + a = c + a then a + b = c + a else a + b ≠ c + a :=
begin
  move_add [← a],
  split_ifs; exact h,
end

example (r : R → R → Prop) (h : r (a + b) (c + b + a)) : r (a + b) (a + b + c) :=
by move_add [a, b, c] at h

example (h : a + c + b = a + d + b) : c + b + a = b + a + d :=
by move_add [← a, b]  -- Goal before `exact h`: `a + c + b = a + d + b`

example [has_mul R] (h : a * c + c + b * c = a * d + d + b * d) :
  c + b * c + a * c = a * d + d + b * d :=
begin
  -- the first input `_ * c` unifies with `b * c` and moves to the right
  -- the second input `_ * c` unifies with `a * c` and moves to the left
  move_add [_ * c, ← _ * c], -- Goal before `exact h`: `a * c + c + b * c = a * d + d + b * d`
end

variables [has_mul R] [has_one R] {X r s t u : R} (C D E : R → R)

example (he : E (C r * D X + D X * h + 7 + 42 + f) = C r * D X + h * D X + 7 + 42 + g) :
  E (7 + f + (C r * D X + 42) + D X * h) = C r * D X + h * D X + g + 7 + 42 :=
begin
  -- move `7, 42, f, g` to the right of their respective sides
  move_add [(7 : R), (42 : R), f, g],
end

example : true :=
begin
  letI iacs : ∀ i, add_comm_semigroup (fin i → ℕ) := λ i, by apply_instance,
  letI ia : ∀ i, has_add (fin i → ℕ) := λ i,
    @add_semigroup.to_has_add _
    (@add_comm_semigroup.to_add_semigroup _ (iacs i)),
  -- move_add should work if there are unified metavariables
  have : ∀ (a b : fin _ → ℕ), @has_add.add _ (ia _) a b = @has_add.add _ (ia _) b a,
  { intros a b,
    move_add [a] },
  trivial, -- close the outer goal
  exact 37 -- resolve the metavariable
end
