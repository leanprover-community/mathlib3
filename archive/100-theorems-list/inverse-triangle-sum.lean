import tactic
import algebra.big_operators
import data.real.basic

-- lemma range_insert (n : ℕ) :
-- insert n (finset.range n) = finset.range (n + 1) :=
-- begin
-- ext, rw finset.mem_range,
-- simp only [finset.mem_insert, finset.mem_range],
-- split; omega,
-- end
#print notation ≤

#check finset.range_succ

lemma discrete_FTC
{α : Type*}
[comm_ring α]
(f F : ℕ → α)
(hF : F 0 = 0)
:
(∀ n,(finset.range n).sum f = F n) ↔
∀ n, F (n + 1) - F n = f n :=
begin
split; intro h,

{intro n, rw [← h n, ← h (n+1)],
rw sub_eq_iff_eq_add, rw finset.range_succ, apply finset.sum_insert,
simp only [finset.not_mem_range_self, not_false_iff]},

intro d, induction d with k hk,
    rw hF, simp only [finset.sum_empty, finset.range_zero],
rw ← nat.add_one,
have calc1 := h k,
rw sub_eq_iff_eq_add at calc1,
rw calc1, clear calc1,
rw ← hk,
rw  finset.range_succ,
simp only [finset.not_mem_range_self, finset.sum_insert, not_false_iff],
end
-- #print notation ∑
lemma sum_range_induction {M : Type*} [add_comm_monoid M]
  (f s : ℕ → M) (h0 : s 0 = 0) (h : ∀ n, s (n + 1) = s n + f n) (n : ℕ) :
   (finset.range n).sum f = s n :=
begin
induction n with k hk,
    {rw h0, simp only [finset.sum_empty, finset.range_zero]},
rw [← nat.add_one, h k, ←hk,finset.range_succ],
simp only [finset.not_mem_range_self, finset.sum_insert, not_false_iff],
rw add_comm,
end

-- making this a named function helped me avoid the evils of nat subtraction. It's possible to avoid nat subtraction inline, but it looks kind of arcane / fragile?
def solution (x : ℚ) : ℚ := if x ≤ 1 then 0 else 1 - 1 / x

lemma inverse_triangle_sum
(n : ℕ) :
(finset.range n).sum (λ x, (1 : ℚ) / (x * (x + 1))) = solution (n : ℚ ) :=
begin
unfold solution,
revert n, rw discrete_FTC,
  swap, rw if_pos, norm_num,
intro n,

by_cases h0 : n = 0,
  {rw [h, if_pos, if_pos], ring,
    norm_num, norm_num},


by_cases h1 : n = 1,
  {rw [h, if_neg, if_pos], ring,
    norm_num, norm_num,},


-- we're going to do arithmetic where n-1, n, and n+1 all appear in denominators, so let's show that's okay
have n0 : ( n : ℚ) ≠ 0 := by {norm_cast, exact h0}, clear h0,
have n1 : ( (n + 1) : ℚ) ≠ 0 := by {norm_cast, omega},
have nn1 : ( n - 1: ℚ) ≠ 0,
  {intro h, revert h1, rw [imp_false, not_not],
  apply_fun (λ x, x + 1) at h,
  simp only [sub_add_cancel, zero_add] at h,
  norm_cast at h, exact h},

-- let's clear our if-then-else
rw [if_neg, if_neg],
  swap, revert h1 n0, norm_cast, omega,
  swap, revert n0, norm_cast, omega,
clear h1,

-- let's leave ℕ now
have coe_elim : ∃ x : ℚ, (n : ℚ) = x, simp only [exists_eq'],
cases coe_elim with x coe_elim,
simp only [one_div_eq_inv, add_sub_cancel, nat.cast_add, nat.cast_one],
rw coe_elim at *,
clear coe_elim n,

-- now that we're morally in (units ℚ), our tactics can do the arithmetic
field_simp [nn1, n0, n1], ring,
end
