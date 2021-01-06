import data.equiv.basic

open equiv

example : swap 2 4 5 = 5 := by simp
example : swap 0 4 5 = 5 := by simp
example : swap 4 0 5 = 5 := by simp
example : swap 2 4 1 = 1 := by simp
example : swap 3 5 2 = 2 := by simp
example : swap 1 5 2 = 2 := by simp
example : swap 5 1 2 = 2 := by simp
example : swap 3 5 0 = 0 := by simp
