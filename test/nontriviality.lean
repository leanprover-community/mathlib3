import logic.nontrivial
import algebra.ordered_ring

example {R : Type} [ordered_ring R] {a : R} (h : 0 < a) : 0 < a :=
begin
  nontriviality,
  guard_hyp _inst : nontrivial R,
  assumption,
end

example {R : Type} [ordered_ring R] (h : false) : 0 ≤ (1 : R) :=
begin
  nontriviality,
  guard_hyp _inst : nontrivial R,
  exfalso,
  assumption,
end
