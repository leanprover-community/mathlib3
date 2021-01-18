import tactic.norm_fin

example : (5 : fin 7) = fin.succ (fin.succ 8) := by norm_num
example : (12 : fin 7) = 5 := by norm_num
example : (11 : fin 7) = 4 := by norm_num
example : (12 : fin 6) = 0 := by norm_num
example : (11 : fin 6) = 5 := by norm_num
example : (1 : fin 1) = 0 := by norm_num
example : fin.succ (4 : fin 6) = 12 := by norm_num
example : fin.succ (3 : fin 6) = 11 := by norm_num
example : fin.cast_succ (4 : fin 6) = 4 := by norm_num
example : fin.cast_succ (fin.cast_succ (4 : fin 5)) = 4 := by norm_num
example : fin.cast_succ (4 : fin 6) = 11 := by norm_num
example : fin.cast_succ (3 : fin 6) = 10 := by norm_num
example : fin.cast_succ (fin.cast_succ (3 : fin 5)) = 10 := by norm_num
