import tactic.lift

example (n m k x z u : ℤ) (hn : 0 < n) (hk : 0 ≤ k + n) (hu : 0 ≤ u) (h : k + n = 2 + x) :
  k + n = m + x :=
begin
  lift n to ℕ using le_of_lt hn,
    guard_target (k + ↑n = m + x), guard_hyp hn := (0 : ℤ) < ↑n,
  lift m to ℕ,
    guard_target (k + ↑n = ↑m + x), tactic.swap, guard_target (0 ≤ m), tactic.swap,
    tactic.num_goals >>= λ n, guard (n = 2),
  lift (k + n) to ℕ using hk with l hl,
    guard_hyp l := ℕ, guard_hyp hl := ↑l = k + ↑n, guard_target (↑l = ↑m + x),
    tactic.success_if_fail (tactic.get_local `hk),
  lift x to ℕ with y hy,
    guard_hyp y := ℕ, guard_hyp hy := ↑y = x, guard_target (↑l = ↑m + x),
  lift z to ℕ with w,
    guard_hyp w := ℕ, tactic.success_if_fail (tactic.get_local `z),
  lift u to ℕ using hu with u rfl hu,
    guard_hyp hu := (0 : ℤ) ≤ ↑u,
  all_goals { admit }
end
