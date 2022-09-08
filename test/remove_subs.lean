import tactic.remove_subs

example {i l : ℕ} (i1 : 1 ≤ i) (il : i + 1 ≤ l) :
  i - 1 + (l - i - 1 + 1) + 1 = l :=
by remove_subs!

example (n m : ℕ) : nat.pred n - m = nat.pred (n - m) :=
show n - 1 - m = n - m - 1, by remove_subs!

example (n m : ℕ) : nat.pred n - m = nat.pred (n - m) :=
by remove_subs!

example {a b c d e f g : ℕ} : a - b - c - d - e - f - g = a - f - g - e - c - d - b :=
by remove_subs!

example {a b c : ℕ} : a + b + c = a + b + c :=
begin
  success_if_fail_with_msg {remove_subs} "no ℕ-subtraction found",
  refl
end

example {a b c : ℕ} : (a : ℤ) - b = a - b :=
begin
  success_if_fail_with_msg {remove_subs} "no ℕ-subtraction found",
  refl
end

example {R} [ring R] {a b c d : ℕ} : (a : R) - b = a - b ∨ a - b = c - d ∨ (a : ℤ) - b = c - d :=
by remove_subs; exact or.inl rfl

example {R} [ring R] {a b c d : ℕ} : ite (a - b = a - b) ((a : R) - b = a - b) (a - b = c - d) :=
by remove_subs; rw if_pos rfl

example (a b : ℕ) : min a b + (a - b) = a :=
by remove_subs; simp; assumption
