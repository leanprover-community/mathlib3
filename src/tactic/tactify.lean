import tactic
import data.nat.factorial

open tactic expr

namespace tactic

namespace tactify

meta inductive proof_step
| apply (e : expr) : proof_step
| exact (e : expr) : proof_step
| intro (n : name) : proof_step
| rewrite (r : expr) : proof_step
| «sorry» : proof_step

meta inductive proof_script
| done : proof_script
| step (state : tactic_state) (step : proof_step) (rest : proof_script) : proof_script

namespace proof_step

meta def to_format : proof_step → tactic format
| (apply e) := do p ← pp e, return format!"apply {p}"
| (exact e) := do p ← pp e, return format!"exact {p}"
| (intro n) := return format!"intro {n}"
| (rewrite r) := do p ← pp r, return format!"rw {p}"
| («sorry») := return format!"sorry"

meta instance : has_to_tactic_format proof_step :=
⟨to_format⟩

meta def subgoals' (solutions : list expr) {α} (t : tactic α) :
  tactic (list expr) :=
do
  -- Keep a copy of the initial goals (which should unify with the solutions)
  initial_goals ← get_goals,
  -- Run the tactic
  -- trace_state,
  -- trace_result,
  t,
  -- trace_state,
  -- trace_result,
  -- Collect the subgoals
  get_goals >>= set_goals,
  new_goals ← get_goals,
  lock_tactic_state $ (do
    -- By unifying the initial goals with the given solutions,
    -- find the corresponding solutions for the new goals.
    (initial_goals.zip solutions).mmap' (λ ⟨g, s⟩, unify g s),
    new_goals.mmap instantiate_mvars)

meta def as_tactic : proof_step → tactic unit
| (apply e) := tactic.apply e >> skip
| (exact e) := tactic.exact e
| (intro n) := tactic.intro n >> skip
| (rewrite r) := tactic.rewrite_target r >> skip
| («sorry») := tactic.admit

meta def subgoals (solutions : list expr) (step : proof_step) :
  tactic (list expr) :=
subgoals' solutions step.as_tactic

end proof_step

namespace proof_script

-- TODO: produce scripts using correct braces?
meta def to_format : proof_script → tactic format
| (proof_script.done) := return $ format.of_string "done"
| (proof_script.step st s n) := do
  ps ← pp s,
  pn ← to_format n,
  return (ps ++ "," ++ format.line ++ pn)

meta instance : has_to_tactic_format proof_script :=
⟨to_format⟩

meta def prompts : proof_script → tactic (list (string × string))
| (proof_script.done) := return []
| (proof_script.step st s r) := do
  ppst ← pp st,
  pps ← pp s,
  rs ← r.prompts,
  return $ (to_string ppst, to_string pps) :: rs

end proof_script

meta def tactic_state_with_goal (goal : expr) : tactic tactic_state :=
lock_tactic_state $ do
  n ← mk_fresh_name,
  assert n goal,
  g :: _ ← get_goals,
  set_goals [g],
  get_state

meta def run_with_goal (goal : expr) {α} (t : tactic α) : tactic α :=
do
  state ← tactic_state_with_goal goal,
  run_with_state state t

/--
Hopefully `apply f` works against the `state`, in which case return `f`.
Otherwise, try using `apply f _`, `apply f _ _` and so on.
-/
meta def apply_with_underscores : expr → tactic expr
| f := do
  (lock_tactic_state (tactic.apply f) >> return f) <|>
  (do f' ← to_expr ``(%%f _),
      apply_with_underscores f')

/--
Attempt to deduce a single proof step from a list of `solutions` for the current goals,
along with the corresponding solutions for the new goals.
-/
meta def tactify_1 (solutions : list expr) :
  tactic (proof_step × list expr) :=
do
  let sol := solutions.head,
  s ← match sol with
  | (const n l) := return (proof_step.exact sol)
  | (local_const u p b t) := return (proof_step.exact sol)
  | (lam n bi ty bd) := return (proof_step.intro n) -- TODO use `intros`?
  | (app f x) := do
      let f' := f.get_app_fn,
      match f' with
      | `(@bit0) := return (proof_step.exact sol)
      | `(@bit1) := return (proof_step.exact sol)
      | `(@eq.mpr) := do
          let b := sol.app_fn.app_arg.app_arg.app_arg,
          let b := if b.get_app_fn.const_name = `propext then b.app_arg else b,
          return (proof_step.rewrite b)
      | _ := do
          let n := f'.const_name,
          if (`dcases_on).is_suffix_of n ∨ (`cases_on).is_suffix_of n then do
            return (proof_step.sorry)
          else do
            f'' ← apply_with_underscores f',
            return (proof_step.apply f'')
      end
  | _ := do
      trace_state,
      fail format!"don't know how to process {sol}"
  end,
  gs ← s.subgoals solutions,
  -- trace gs,
  return ⟨s, gs⟩

-- #exit
-- #print tactify_1
end tactify

open tactify

meta def tactify : list expr → tactic proof_script
| solutions :=
do
  goals ← get_goals,
  guard (goals.length = solutions.length) <|>
    fail "Number of solutions has diverged from the number of goals.",
  done >> return proof_script.done <|>
do
  state ← get_state,
  -- trace_state,
  -- trace solutions,
  (step, new_solutions) ← tactify_1 solutions,
  -- trace step,
  -- trace "---",
  next ← tactify new_solutions,
  return $ proof_script.step state step next

namespace interactive

meta def tactify (n : name) : tactic unit := do
  env ← get_env,
  d ← env.get n,
  run_with_goal d.type (do
    o ← tactic.tactify [d.value],
    trace o)

end interactive

end tactic

open tactic tactic.tactify

meta def tactic_prompts (n : name) : tactic unit := do
  env ← get_env,
  d ← env.get n,
    run_with_goal d.type (do
    o ← tactic.tactify [d.value],
    s ← o.prompts,
    s.mmap' (λ p, do trace p.1, trace p.2, trace ""))

-- Examples that work:
run_cmd tactic_prompts `nat.factorial_le
run_cmd tactic_prompts `nat.units_eq_one
run_cmd tactic_prompts `nat.add_factorial_succ_lt_factorial_add_succ
run_cmd tactic_prompts `nat.lt_factorial_self
run_cmd tactic_prompts `nat.zero_eq_mul

-- TODO try generating shorter `rw` proofs (i.e. leave off arguments when they aren't needed)
-- TODO combine `apply iff.mpr` and `apply F` into `apply F.mpr`.

-- PROJECT I don't know how to handle proofs that use `cases`, `induction`, or pattern matching.
run_cmd tactic_prompts `nat.add_factorial_le_factorial_add
run_cmd tactic_prompts `nat.self_le_factorial

example : false :=
begin
  tactify `nat.factorial_le,
  tactify `nat.add_factorial_succ_lt_factorial_add_succ,
end

-- Extracted from nat.add_factorial_succ_lt_factorial_add_succ.
example : ∀ {i : ℕ} (n : ℕ), 2 ≤ i → i + (n + 1).factorial < (i + n + 1).factorial :=
begin
  intro i,
  intro n,
  intro hi,
  rw (i + n).factorial_succ,
  rw (i + n).succ_eq_add_one,
  rw add_mul (i + n) 1 (i + n).factorial,
  rw one_mul (i + n).factorial,
  apply add_lt_add_of_lt_of_le,
  apply has_le.le.trans_lt,
  apply nat.le.intro,
  apply rfl,
  exact n,
  apply iff.mpr,
  apply lt_mul_iff_one_lt_right,
  apply has_lt.lt.trans_le,
  apply zero_lt_two,
  apply has_le.le.trans,
  exact hi,
  apply nat.le.intro,
  apply rfl,
  apply iff.mpr,
  apply lt_iff_le_and_ne,
  apply and.intro,
  apply nat.factorial_pos,
  intro g,
  apply nat.not_succ_le_self,
  apply has_le.le.trans,
  apply has_le.le.trans,
  exact hi,
  apply nat.le.intro,
  apply rfl,
  exact n,
  apply iff.mp,
  apply nat.factorial_eq_one,
  apply eq.symm,
  exact g,
  apply nat.factorial_le,
  apply has_le.le.trans,
  apply le_of_eq,
  apply add_comm,
  apply iff.mpr,
  apply add_le_add_iff_right,
  apply has_le.le.trans,
  apply one_le_two,
  exact hi,
  done,
end
