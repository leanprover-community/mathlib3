import tactic
import data.nat.factorial

open tactic expr

meta inductive proof_step
| apply (e : expr) : proof_step
| intro (n : name) : proof_step

meta inductive proof_script
| step (goal : tactic_state) (step : proof_step) (rest : list proof_script) : proof_script

namespace proof_step

meta def to_format : proof_step → tactic format
| (apply e) := do p ← pp e, return format!"apply {p}"
| (intro n) := return format!"intro {n}"

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

meta def subgoals (state : tactic_state) (solution : expr) :
  proof_step → tactic (list (tactic_state × expr))
| (apply e) := subgoals' state solution (tactic.apply e)
| (intro n) := subgoals' state solution (tactic.intro n)

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
Otherwise, try some variations...
-/
meta def discover_apply (state : tactic_state) : expr → tactic expr
| f :=
do
  ppf ← pp f, trace format!"checking {ppf} against the goal",
  (run_with_state state (tactic.apply f) >> trace "!" >> return f) <|>
  (do f' ← to_expr ``(%%f _),
      discover_apply f')

/--
Attempt to extract from a `solution` to a `goal` a single proof step,
along with the resulting subgoals and their corresponding solutions
-/
meta def tactify_1 (state : tactic_state) (solution : expr) :
  tactic (proof_step × list (tactic_state × expr)) :=
do
  s ← match solution with
  | `(bit0 %%n) := return (proof_step.apply solution)
  | `(bit1 %%n) := return (proof_step.apply solution)
  | (const n l) := return (proof_step.apply solution)
  | (local_const u p b t) := return (proof_step.apply solution)
  | (app f x) := do f' ← discover_apply state solution.get_app_fn, return (proof_step.apply f')
  | (lam n bi ty bd) := return (proof_step.intro n) -- TODO use `intros`?
  | _ := fail format!"don't know how to process {solution}"
  end,
  gs ← s.subgoals state solution,
  return ⟨s, gs⟩

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

meta def foo (d : declaration) : tactic unit :=
do
  state ← tactic_state_with_goal d.type,
  o ← tactify state d.value,
  trace o,
  skip

meta def bar (n : name) : tactic unit :=
do env ← get_env,
   d ← env.get n,
   foo d

meta def bar' (n : name) : tactic unit :=
begin
  apply id_rhs _,
end


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

example : false :=
begin
  bar `quux,
  bar `ff,
  -- bar `bar,
end
