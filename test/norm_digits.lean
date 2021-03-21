import data.nat.digits

example : nat.digits 0 0 = [] := by norm_num
example : nat.digits 1 0 = [] := by norm_num
example : nat.digits 2 0 = [] := by norm_num
example : nat.digits 10 0 = [] := by norm_num
example : nat.digits 0 1 = [1] := by norm_num
example : nat.digits 0 1000 = [1000] := by norm_num
example : nat.digits 1 10 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by norm_num
example : nat.digits 2 65536 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by norm_num
example : nat.digits 3 30000000 = [0, 1, 0, 1, 2, 0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 2] := by norm_num
example : nat.digits 10 1234567 = [7, 6, 5, 4, 3, 2, 1] := by norm_num
