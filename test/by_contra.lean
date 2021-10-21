import tactic.by_contra
import tactic.interactive

example : 1 < 2 :=
begin
  by_contra' h,
  guard_hyp' h : 2 ≤ 1,
  revert h,
  exact dec_trivial
end

example : 1 < 2 :=
begin
  by_contra' h : 2 ≤ 1,
  guard_hyp' h : 2 ≤ 1, -- this is not defeq to `¬ 1 < 2`
  revert h,
  exact dec_trivial
end

example : 1 < 2 :=
begin
  by_contra' h : ¬ 1 < 2,
  guard_hyp' h : ¬ 1 < 2, -- this is not defeq to `2 ≤ 1`
  revert h,
  exact dec_trivial
end

example : 1 < 2 :=
begin
  by_contra' : 2 ≤ 1,
  guard_hyp' this : 2 ≤ 1, -- this is not defeq to `¬ 1 < 2`
  revert this,
  exact dec_trivial
end
