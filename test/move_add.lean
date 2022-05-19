import tactic.move_add

open tactic interactive
variables {R : Type*} [add_comm_semigroup R] {a b c d e f g h : R}

example (e f g : R) (h : a + b + c = d) : b + (a + c) = d :=
begin
--  move_add [d] at *, -- d is an unused variable
  move_add at *,
--  move_add at *,  -- 'move_add at *' changes nothing
--  move_add [a, e, f, g] at h a b c ⊢, -- '[a, b, c]' did not change,
                                        -- '[e, f, g]' are unused variables
--  move_add at ⊢ h,  -- '[h]' did not change
                      -- Goal did not change
  move_add ← a at *,  -- `move_add` closes the goal, since it tries assumption
end

example (r : R → R → Prop) (h : r (a + b) (c + b + a)) : r (a + b) (a + b + c) :=
begin
  move_add [a, b, c] at h,
end

example (h : a + c + b = a + d + b) : c + b + a = b + a + d :=
begin
  move_add [← a, b],  -- Goal before `exact h`: `a + c + b = a + d + b`
end

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
