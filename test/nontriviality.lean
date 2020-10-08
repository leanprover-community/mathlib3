import logic.nontrivial
import algebra.ordered_ring
import data.nat.basic

example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality,
  guard_hyp _inst : nontrivial R,
  assumption,
end

example {R : Type} [comm_ring R] {r s : R} : r * s = s * r :=
begin
  nontriviality,
  guard_hyp _inst : nontrivial R,
  apply mul_comm,
end

example {R : Type} [ordered_ring R] : 0 ≤ (1 : R) :=
begin
  nontriviality R,
  guard_hyp _inst : nontrivial R,
  exact zero_le_one,
end

example {R : Type} [ordered_ring R] : 0 ≤ (1 : R) :=
begin
  nontriviality ℕ,
  guard_hyp _inst : nontrivial ℕ,
  exact zero_le_one,
end

example {R : Type} [ordered_ring R] : 0 ≤ (1 : R) :=
begin
  success_if_fail { nontriviality punit },
  exact zero_le_one,
end

example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 2 ∣ 4 :=
begin
  nontriviality R,
  guard_hyp _inst : nontrivial R,
  dec_trivial
end
