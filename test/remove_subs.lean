import tactic.remove_subs
import data.real.nnreal
open_locale nnreal

example {i l : ℕ} (i1 : 1 ≤ i) (il : i + 1 ≤ l) :
  i - 1 + (l - i - 1 + 1) + 1 = l :=
by remove_subs!

example (n m : ℕ) : nat.pred n - m = nat.pred (n - m) :=
show n - 1 - m = n - m - 1, by remove_subs!

example (n m : ℕ) : nat.pred n - m = nat.pred (n - m) :=
by remove_subs!

example {a b c d e f g : ℕ} : a - b - c - d - e - f - g = a - f - g - e - c - d - b :=
by remove_subs!

example {a b c d e f g : ℕ} (h : a - b - c - d - e - f - g = a - f - g - e - c - d - b) : true :=
by remove_subs at h; trivial

example {a b c : ℕ} : a + b + c = a + b + c :=
begin
  success_if_fail_with_msg {remove_subs} "'remove_subs' made no progress",
  refl
end

example {a b c : ℕ} : (a : ℤ) - b = a - b :=
begin
  success_if_fail_with_msg {remove_subs} "'remove_subs' made no progress",
  refl
end

example {R} [ring R] {a b c d : ℕ} : (a : R) - b = a - b ∨ a - b = c - d ∨ (a : ℤ) - b = c - d :=
by remove_subs; exact or.inl rfl

example {R} [ring R] {a b c d : ℕ} : ite (a - b = a - b) ((a : R) - b = a - b) (a - b = c - d) :=
by remove_subs; rw if_pos rfl

example (a b : ℕ) : min a b + (a - b) = a :=
by remove_subs; simp; assumption

example {a b c : ℕ} (bc : b - c = a) (ca : c - a = b) : a = 0 :=
by remove_subs! at bc ca

example {a b c : ℕ} (bc : b - c = a) (ca : c - a = b) (h : a + b = b + a) : a = 0 :=
begin
  success_if_fail_with_msg {remove_subs at bc ca h h ⊢ bc} "Try this: remove_subs at bc ca",
  success_if_fail_with_msg {remove_subs! at bc ca h h ⊢ bc} "Try this: remove_subs! at bc ca",
  remove_subs! at bc ca
end

example {a b c : ℕ} (bc : b - c = a) (ca : c - a = b) (h : a + b = b + a) : a = 0 :=
begin
  success_if_fail_with_msg {remove_subs at bc ca h h ⊢ bc} "Try this: remove_subs at bc ca",
  success_if_fail_with_msg {remove_subs! at bc ca h h ⊢ bc} "Try this: remove_subs! at bc ca",
  remove_subs! at bc ca
end

example : true :=
begin
  success_if_fail_with_msg {remove_subs at bc ca h h ⊢ bc} "'remove_subs' made no progress",
  success_if_fail_with_msg {remove_subs! at bc ca h h ⊢ bc} "'remove_subs!' made no progress",
  trivial
end

example {a b : ℕ} : a - b  = a - b :=
begin
  success_if_fail_with_msg {remove_subs at ⊢ a} "Try this: remove_subs",
  success_if_fail_with_msg {remove_subs! at a ⊢ a} "Try this: remove_subs!",
  remove_subs!,
end

example {a b : ℕ} (h : a - b = b): a - b = b :=
begin
  success_if_fail_with_msg {remove_subs! at h ⊢ ⊢ h ⊢} "Try this: remove_subs! at h ⊢ ⊢",
  remove_subs! at h ⊢ ⊢,
end

example {a b : ℝ≥0} (h : a - b = b): a - b = b :=
begin
  success_if_fail_with_msg {remove_subs at h ⊢ ⊢ h ⊢} "Try this: remove_subs at h ⊢",
  remove_subs at h ⊢,
  { assumption },
  { subst h,
    simpa only [zero_add, le_zero_iff] using h_1 },
  { simpa only [add_tsub_cancel_left] },
end

example {a b : ℕ} (h : a - b = b): a - b = b :=
begin
  remove_subs! at *,
  success_if_fail_with_msg {remove_subs! at *} "Try this: remove_subs! at h",
  remove_subs! at h,
end

/-
https://leanprover.zulipchat.com/#narrow/stream/ --merge the next line with this!
217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20converse.20of.20.60nat.2Esub_le_sub_left.60
-/
example {n m k : ℕ} (hm : m ≤ k) (hn : n ≤ k) (h : k - m ≤ k - n) : n ≤ m := by remove_subs! at h

example {n m : ℕ} (k) (h : n ≤ m) : k - m ≤ k - n := by remove_subs!
