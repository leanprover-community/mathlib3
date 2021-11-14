/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/
import tactic.converter.interactive
import tactic.ring

example : 0 + 0 = 0 :=
begin
  conv_lhs {erw [add_zero]}
end

example : 0 + 0 = 0 :=
begin
  conv_lhs {simp}
end

example : 0 = 0 + 0 :=
begin
  conv_rhs {simp}
end

-- Example with ring discharging the goal
example : 22 + 7 * 4 + 3 * 8 = 0 + 7 * 4 + 46 :=
begin
  conv { ring, },
end

-- Example with ring failing to discharge, to normalizing the goal
example : (22 + 7 * 4 + 3 * 8 = 0 + 7 * 4 + 47) = (74 = 75) :=
begin
  conv { ring_nf, },
end

-- Example with ring discharging the goal
example (x : ℕ) : 22 + 7 * x + 3 * 8 = 0 + 7 * x + 46 :=
begin
  conv { ring, },
end

-- Example with ring failing to discharge, to normalizing the goal
example (x : ℕ) : (22 + 7 * x + 3 * 8 = 0 + 7 * x + 46 + 1)
                    = (7 * x + 46 = 7 * x + 47) :=
begin
  conv { ring_nf, },
end

-- norm_num examples:
example : 22 + 7 * 4 + 3 * 8 = 74 :=
begin
  conv { norm_num, },
end

example (x : ℕ) : 22 + 7 * x + 3 * 8 = 7 * x + 46 :=
begin
  simp [add_comm, add_left_comm],
  conv { norm_num, },
end
