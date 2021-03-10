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

meta inductive proof_script
| step (goal : tactic_state) (step : proof_step) (rest : list proof_script) : proof_script

namespace proof_step

meta def to_format : proof_step → tactic format
| (apply e) := do p ← pp e, return format!"apply {p}"
| (exact e) := do p ← pp e, return format!"exact {p}"
| (intro n) := return format!"intro {n}"
| (rewrite r) := do p ← pp r, return format!"rw {p}"

meta instance : has_to_tactic_format proof_step :=
⟨to_format⟩

meta def subgoals' (state : tactic_state) (solution : expr) {α} (t : tactic α) :
  tactic (list (tactic_state × expr)) :=
run_with_state state $ do
  g ← get_goal,
  -- Run the tactic
  t,
  -- Collect the subgoals
  gs ← get_goals,
  -- Collect the tactic state for each of those goals
  states ← gs.mmap (λ g', do set_goals [g'], get_state),
  -- By unifying the goal with the given solution,
  -- find the corresponding solutions for the subgoals.
  unify g solution,
  gs ← gs.mmap instantiate_mvars,
  -- Return the new states and their corresponding solutions
  return (states.zip gs)

meta def as_tactic : proof_step → tactic unit
| (apply e) := tactic.apply e >> skip
| (exact e) := tactic.exact e
| (intro n) := tactic.intro n >> skip
| (rewrite r) := tactic.rewrite_target r >> skip

meta def subgoals (state : tactic_state) (solution : expr) (step : proof_step) :
  tactic (list (tactic_state × expr)) :=
subgoals' state solution (step.as_tactic)

end proof_step

namespace proof_script

meta def to_format : proof_script → tactic format
| (proof_script.step g s [n]) := do
  ps ← pp s,
  pn ← to_format n,
  return (ps ++ "," ++ format.line ++ pn)
| (proof_script.step g s r) := do
  ps ← pp s,
  pr ← r.mmap (λ n, do pn ← to_format n, return (format.of_string "{ " ++ (format.nest 2 pn) ++ " }")),
  return $ ps ++ "," ++ format.line ++ format.join (list.intersperse ("," ++ format.line) pr)

meta instance : has_to_tactic_format proof_script :=
⟨to_format⟩

meta def steps : proof_script → tactic (list (string × string))
| (proof_script.step g s r) := do
  ppg ← pp g,
  pps ← pp s,
  rs ← r.mmap steps,
  return $ (to_string ppg, to_string pps) :: rs.join

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
meta def apply_with_underscores (state : tactic_state) : expr → tactic expr
| f :=
do
  -- ppf ← pp f, trace format!"checking {ppf} against the goal",
  (run_with_state state (tactic.apply f) >> return f) <|>
  (do f' ← to_expr ``(%%f _),
      apply_with_underscores f')

/--
Attempt to extract from a `solution` to a `goal` a single proof step,
along with the resulting subgoals and their corresponding solutions
-/
meta def tactify_1 (state : tactic_state) (solution : expr) :
  tactic (proof_step × list (tactic_state × expr)) :=
do
  s ← match solution with
  -- | `(bit0 %%n) := return (proof_step.exact solution)
  -- | `(bit1 %%n) := return (proof_step.exact solution)
  -- | `(eq.mpr (@eq.rec _ _ _ _ _ %%b) _) :=
  --     return (proof_step.rewrite b)
  | (const n l) := return (proof_step.exact solution)
  | (local_const u p b t) := return (proof_step.exact solution)
  | (lam n bi ty bd) := return (proof_step.intro n) -- TODO use `intros`?
  | (app f x) := do
      let f' := f.get_app_fn,
      trace f',
      match f' with
      | `(bit0) := return (proof_step.exact solution)
      | `(bit1) := return (proof_step.exact solution)
      | `(@eq.mpr) := do
          let b := solution.app_fn.app_arg.app_arg.app_arg,
          trace b,
          return (proof_step.rewrite b)
      | _ := do
          f'' ← apply_with_underscores state f',
          return (proof_step.apply f'')
      end
  | _ := do
      trace state,
      fail format!"don't know how to process {solution}"
  end,
  gs ← s.subgoals state solution,
  return ⟨s, gs⟩

-- #exit
-- #print tactify_1
end tactify

open tactify

meta def tactify : tactic_state → expr → tactic proof_script
| goal solution :=
do
  trace goal,
  trace solution,
  (step, pairs) ← tactify_1 goal solution,
  trace step,
  trace "---",
  scripts' ← pairs.mmap (λ p, tactify p.1 p.2),
  return $ proof_script.step goal step scripts'

namespace interactive

meta def tactify (n : name) : tactic unit := do
  env ← get_env,
  d ← env.get n,
  state ← tactic_state_with_goal d.type,
  o ← tactic.tactify state d.value,
  trace o

end interactive

end tactic

open tactic tactic.tactify

meta def tactic_prompts (n : name) : tactic unit := do
  env ← get_env,
  d ← env.get n,
  state ← tactic_state_with_goal d.type,
  o ← tactic.tactify state d.value,
  s ← o.steps,
  s.mmap' (λ p, do trace p.1, trace p.2, trace "")

-- Examples that work:
run_cmd tactic_prompts `nat.factorial_le
run_cmd tactic_prompts `nat.units_eq_one

-- rewrites have spurious `propext`:
run_cmd tactic_prompts `nat.zero_eq_mul

-- Weird unification problems:
run_cmd tactic_prompts `nat.add_factorial_succ_lt_factorial_add_succ
#print nat.add_factorial_succ_lt_factorial_add_succ

-- dcases_on breaks things:
run_cmd tactic_prompts `nat.add_factorial_le_factorial_add

def quux : ℕ := nat.factorial (3 + (nat.factorial 7))

def quux' : ℕ :=
begin
apply nat.factorial,
apply has_add.add,
{ apply 3,
   },
{ apply nat.factorial,
  apply 7,
   }
end
#print quux'

def ff {α : Type*} (a : α) := [[a,a],[a,a,a]]

def ff' : Π {α : Type*} (a : α), list (list α) := begin
intro α,
intro a,
apply list.cons,
{ apply list.cons,
  { apply a,
     },
  { apply list.cons,
    { apply a,
       },
    { apply list.nil,
       } } },
{ apply list.cons,
  { apply list.cons,
    { apply a,
       },
    { apply list.cons,
      { apply a,
         },
      { apply list.cons,
        { apply a,
           },
        { apply list.nil,
           } } } },
  { apply list.nil,
     } }
end




run_cmd tactic.interactive.tactify `nat.factorial_le

example : false :=
begin
  tactify `quux,
  tactify `ff,
  tactify `nat.factorial_le,
  tactify `nat.add_factorial_succ_lt_factorial_add_succ,
  -- bar `bar,
end
