import tactic.norm_fin

example : (5 : fin 7) = fin.succ (fin.succ 8) := by norm_num
example : (12 : fin 7) = 5 := by norm_num
example : (11 : fin 7) = 4 := by norm_num
example : (12 : fin 6) = 0 := by norm_num
example : (11 : fin 6) = 5 := by norm_num
example : (1 : fin 1) = 0 := by norm_num
example : fin.succ (4 : fin 6) = 12 := by norm_num
example : fin.succ (1 : fin (1 + 2)) = 2 := by norm_num
example : fin.succ (1 : fin (nat.succ (1 + 1))) = 2 := by norm_num
example : (1 : fin (nat.succ (1 + 1))) = 1 := by norm_num
example : (1 : fin (nat.succ (1 + 2))) = 1 := by norm_num
example : (3 : fin (nat.succ (1 + 1 + 1))) = 3 := by norm_num
example : (2 : fin (nat.succ (2 + 1 + 1))) = 7 := by norm_num
example : (2 : fin (nat.succ (nat.succ (2 + 1 + 1)))) = 8 := by norm_num
example : fin.cast_succ (1 : fin (nat.succ (1 + 1))) = 1 := by norm_num
example : (1 : fin (nat.succ (1 + 1))) = 1 := by norm_num
example : fin.succ (3 : fin 6) = 11 := by norm_num
example : fin.cast_succ (4 : fin 6) = 4 := by norm_num
example : fin.cast_succ (fin.cast_succ (4 : fin 5)) = 4 := by norm_num
example : fin.cast_succ (4 : fin 6) = 11 := by norm_num
example : fin.cast_succ (3 : fin 6) = 10 := by norm_num
example : fin.cast_succ (fin.cast_succ (3 : fin 5)) = 10 := by norm_num
example : ¬ fin.cast_succ (fin.cast_succ (3 : fin 5)) ≠ 10 := by norm_num

example : equiv.swap (0 : fin 3) 1 (fin.succ 1) = 2 :=
begin
  success_if_fail {guard_target ((equiv.swap (0 : fin 3) 1) 2 = 2)},
  norm_fin,
  guard_target (equiv.swap (0 : fin 3) 1 2 = 2),
  exact equiv.swap_apply_of_ne_of_ne dec_trivial dec_trivial
end
example : equiv.swap (0 : fin (1 + 2)) (1 : fin (nat.succ (1 + 1))) (fin.succ 1) = 2 :=
begin
  success_if_fail {guard_target ((equiv.swap (0 : fin 3) 1) 2 = 2)},
  norm_fin,
  guard_target' (equiv.swap (0 : fin 3) 1 2 = 2),
  exact equiv.swap_apply_of_ne_of_ne dec_trivial dec_trivial
end
example : equiv.swap (0 : fin 3) 1 (fin.cast_succ 1) = 0 := by norm_fin

example : (5 : fin 7) < fin.succ (fin.succ 9) := by norm_num
example : (12 : fin 7) < 6 := by norm_num
example : (11 : fin 7) > 3 := by norm_num
example : (12 : fin 6) ≤ 0 := by norm_num
example : (11 : fin 6) ≥ 5 := by norm_num
example : fin.succ (4 : fin 6) < 13 := by norm_num
example : fin.succ (1 : fin (1 + 2)) < 3 := by norm_num
example : fin.succ (1 : fin (nat.succ (1 + 1))) < 3 := by norm_num
example : (1 : fin (nat.succ (1 + 1))) < 2 := by norm_num
example : (1 : fin (nat.succ (1 + 2))) < 7 := by norm_num
example : (3 : fin (nat.succ (1 + 1 + 1))) > 4 := by norm_num
example : (2 : fin (nat.succ (2 + 1 + 1))) < 8 := by norm_num
example : (2 : fin (nat.succ (nat.succ (2 + 1 + 1)))) < 9 := by norm_num
example : fin.cast_succ (1 : fin (nat.succ (1 + 1))) < 7 := by norm_num
example : (1 : fin (nat.succ (1 + 1))) < fin.succ 3 := by norm_num
example : fin.succ (3 : fin 6) < fin.cast_succ 11 := by norm_num
example : fin.cast_succ (4 : fin 6) < fin.succ 4 := by norm_num
example : fin.cast_succ (fin.cast_succ (4 : fin 5)) < fin.cast_succ (fin.succ 4) := by norm_num
example : fin.cast_succ (4 : fin 6) < fin.succ 11 := by norm_num
example : fin.cast_succ (3 : fin 6) < fin.cast_succ 10 := by norm_num
example : fin.cast_succ (fin.cast_succ (3 : fin 5)) < fin.succ (fin.cast_succ 9) := by norm_num

example : (5 : fin 7) ≠ fin.succ (fin.succ 9) := by norm_num
example : (12 : fin 7) ≠ 6 := by norm_num
example : (11 : fin 7) ≠ 3 := by norm_num
example : fin.succ (4 : fin 6) ≠ 13 := by norm_num
example : fin.succ (1 : fin (1 + 2)) ≠ 3 := by norm_num
example : fin.succ (1 : fin (nat.succ (1 + 1))) ≠ 3 := by norm_num
example : (1 : fin (nat.succ (1 + 1))) ≠ 2 := by norm_num
example : (1 : fin (nat.succ (1 + 2))) ≠ 7 := by norm_num
example : (3 : fin (nat.succ (1 + 1 + 1))) ≠ 4 := by norm_num
example : (2 : fin (nat.succ (2 + 1 + 1))) ≠ 8 := by norm_num
example : (2 : fin (nat.succ (nat.succ (2 + 1 + 1)))) ≠ 9 := by norm_num
example : fin.cast_succ (1 : fin (nat.succ (1 + 1))) ≠ 7 := by norm_num
example : (1 : fin (nat.succ (1 + 1))) ≠ fin.succ 3 := by norm_num
example : fin.succ (3 : fin 6) ≠ fin.cast_succ 11 := by norm_num
example : fin.cast_succ (4 : fin 6) ≠ fin.succ 4 := by norm_num
example : fin.cast_succ (fin.cast_succ (4 : fin 5)) ≠ fin.cast_succ (fin.succ 4) := by norm_num
example : fin.cast_succ (4 : fin 6) ≠ fin.succ 11 := by norm_num
example : fin.cast_succ (3 : fin 6) ≠ fin.cast_succ 10 := by norm_num
example : fin.cast_succ (fin.cast_succ (3 : fin 5)) ≠ fin.succ (fin.cast_succ 9) := by norm_num

example : (5 : fin 7) ≠ fin.succ (fin.succ 9) :=
begin
  intro H,
  norm_num at H,
end
