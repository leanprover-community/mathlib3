import data.equiv.basic
import tactic.norm_swap


open equiv tactic

/--
To properly test that norm_swap works without the help of the simplifier,
we turn off the simp lemmas that simplify swaps of the form
`swap x y x = y` and `swap x y y = x`.
-/
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

example : true := by do
  let l : list ℤ := [0, 2, -1, 3, -4],
  let l' := (do a ← l, b ← l, c ← l, pure ((a, b), c)),
  ic ← mk_instance_cache `(ℤ),
  -- we have to convert the provided `int`s into numeral form for the goals
  -- to look like what they would usually: `⇑(swap -1 3) -4 = -4`, instead of
-- `⇑(swap (int.neg_succ_of_nat 0) (int.of_nat 3)) (int.neg_succ_of_nat 3) = int.neg_succ_of_nat 3`
  el ← mmap (λ (tup : (ℤ × ℤ) × ℤ), do
    (_, a) ← ic.of_int tup.fst.fst,
    (_, b) ← ic.of_int tup.fst.snd,
    (_, c) ← ic.of_int tup.snd,
    pure ((a, b), c)) l',
  (lhs : list expr) ← mmap (λ (tup : (expr × expr) × expr),
    to_expr ``((equiv.swap %%tup.fst.fst %%tup.fst.snd) %%tup.snd)) el,
  let rhs : list expr := el.map (λ (tup : (expr × expr) × expr),
    if tup.snd = tup.fst.fst then tup.fst.snd
    else if tup.snd = tup.fst.snd then tup.fst.fst
    else tup.snd),
  let eqs : list expr := list.zip_with (λ L R, `(@eq.{1} ℤ %%L %%R)) lhs rhs,
  g ← get_goals,
  gls ← mmap mk_meta_var eqs,
  set_goals $ g ++ gls,
  triv, -- to discharge the starting `true` goal
  repeat $ tactic.norm_num norm_swap.eval [] (interactive.loc.ns [none]),
  done

example : true := by do
  let l : list ℚ := [0, (2 : ℚ) / -2, -1, 3 / 5, 4],
  let l' := (do a ← l, b ← l, c ← l, pure ((a, b), c)),
  ic ← mk_instance_cache `(ℚ),
  -- we have to convert the provided `rat`s into numeral form for the goals
  -- to look like what they would usually: `⇑(swap -1 3) -4 = -4`, like with ℤ above
  el ← mmap (λ (tup : (ℚ × ℚ) × ℚ), do
    (_, a) ← ic.of_rat tup.fst.fst,
    (_, b) ← ic.of_rat tup.fst.snd,
    (_, c) ← ic.of_rat tup.snd,
    pure ((a, b), c)) l',
  (lhs : list expr) ← mmap (λ (tup : (expr × expr) × expr),
    to_expr ``((equiv.swap %%tup.fst.fst %%tup.fst.snd) %%tup.snd)) el,
  let rhs : list expr := el.map (λ (tup : (expr × expr) × expr),
    if tup.snd = tup.fst.fst then tup.fst.snd
    else if tup.snd = tup.fst.snd then tup.fst.fst
    else tup.snd),
  let eqs : list expr := list.zip_with (λ L R, `(@eq.{1} ℚ %%L %%R)) lhs rhs,
  g ← get_goals,
  gls ← mmap mk_meta_var eqs,
  set_goals $ g ++ gls,
  triv, -- to discharge the starting `true` goal
  repeat $ tactic.norm_num norm_swap.eval [] (interactive.loc.ns [none]),
  done

example : swap (3 : fin 7) 5 0 = 0 := by norm_num
example : swap (fin.succ 2 : fin 7) 5 0 = 0 := by norm_num
example : swap (3 : fin 7) 5 3 = 5 := by norm_num
example : swap (3 : fin 1) 5 0 = 0 := by norm_num
example : swap (3 : fin 7) 5 10 = 12 := by norm_fin
example : swap (2 : fin 7) 4 9 = 11 := by norm_fin
example : swap (3 : fin 7) 5 0 = 0 := by norm_num
example : swap (3 : fin 7) 12 9 = 2 := by norm_num
example : swap (0 : fin (1 + 2)) (1 : fin (nat.succ (1 + 1))) ((fin.succ 1) : fin 3) = 2 :=
by norm_num

-- norm_swap doesn't generate trace output on non-swap expressions
example : (1 : ℤ) = (1 : ℕ) := by norm_num
