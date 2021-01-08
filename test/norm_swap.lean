import data.equiv.basic
import tactic.norm_swap

open equiv tactic

local attribute [-simp] swap_apply_left
local attribute [-simp] swap_apply_right

/--
We can check all possibilities of swapping of `0, 1, bit0 _, bit1 _` using the
64 combinations of `[0, 1, 2, 3]`. This example should execute and complete without error,
if `norm_swap.eval` is behaving properly.
-/
example : true := by do
  let l : list ℕ := [0, 1, 2, 3],
  let l' : list ((ℕ × ℕ) × ℕ) := (do a ← l, b ← l, c ← l, pure ((a, b), c)),
  (lhs : list expr) ← mmap (λ (tup : (ℕ × ℕ) × ℕ),
    to_expr ``(equiv.swap %%tup.fst.fst %%tup.fst.snd %%tup.snd)) l',
  (rhs : list expr) ← mmap (λ (tup : (ℕ × ℕ) × ℕ),
    if tup.snd = tup.fst.fst then to_expr ``(%%tup.fst.snd)
    else if tup.snd = tup.fst.snd then to_expr ``(%%tup.fst.fst)
    else to_expr ``(%%tup.snd)) l',
  let eqs : list expr := list.zip_with (λ L R, `(@eq.{1} ℕ %%L %%R)) lhs rhs,
  g ← get_goals,
  gls ← mmap mk_meta_var eqs,
  set_goals $ g ++ gls,
  triv, -- to discharge the starting `true` goal
  repeat $ tactic.norm_num norm_swap.eval [] (interactive.loc.ns [none]),
  done

-- norm_swap does not yet handle non-ℕ types
example : swap (3 : fin 7) 5 0 = 0 :=
begin
  success_if_fail {norm_num},
  rw swap_apply_of_ne_of_ne;
  dec_trivial
end

example : swap (-3 : ℤ) 5 0 = 0 :=
begin
  success_if_fail {norm_num},
  rw swap_apply_of_ne_of_ne;
  dec_trivial
end

-- norm_swap doesn't generate trace output on non-swap expressions
example : (1 : ℤ) = (1 : ℕ) := by norm_num
