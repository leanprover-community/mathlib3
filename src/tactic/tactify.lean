import tactic
import data.nat.factorial

open tactic

namespace expr

/-- Implementation of `get_app_fn_with_implicits`. -/
meta def app_implicits : expr → list expr → expr → expr
| f (x :: xs) (pi _ binder_info.default _ ty) := f
| f (x :: xs) (pi _ _ _ ty) := app_implicits (f x) xs ty
| f _ _ := f

/--
Extract the topmost function along with
all implicit arguments before the first explicit argument.
-/
meta def get_app_fn_with_implicits (e : expr) : tactic expr :=
let (f, args) := e.get_app_fn_args in
app_implicits f args <$> infer_type f

/-- Implementation of `app_implicits_mvars`. -/
meta def app_implicits_mvars_aux : expr → expr → tactic expr
| f (pi _ binder_info.default _ _) := return f
| f (pi _ _ v_ty b_ty) := do v ← mk_meta_var v_ty, app_implicits_mvars_aux (f v) b_ty
| f _ := return f

/-- Fill any implicit arguments in with fresh metavariables. -/
meta def app_implicits_mvars (e : expr) : tactic expr :=
infer_type e >>= app_implicits_mvars_aux e

-- /-- Implementation of `app_implicits_placeholders`. -/
-- meta def app_implicits_placeholders_aux : expr → expr → tactic expr
-- | f (pi _ binder_info.default _ _) := return f
-- | f (pi _ _ v_ty b_ty) :=
--   do app_implicits_placeholders_aux (f (unchecked_cast pexpr.mk_placeholder)) b_ty
-- | f _ := return f

-- /-- Fill any implicit arguments in with fresh metavariables. -/
-- meta def app_implicits_placeholders (e : expr) : tactic expr :=
-- infer_type e >>= app_implicits_placeholders_aux e

meta def lam_binding_names : expr → list name
| (lam n _ _ b) := n :: lam_binding_names b
| _ := []

meta def fill_args_with_mvars : expr → tactic expr
| e := do
  ty ← infer_type e,
  match ty with
  | (pi _ _ t _) := do
    m ← mk_meta_var t,
    fill_args_with_mvars $ e m
  | _ := return e
  end

meta def replace_args_with_mvars (e : expr) : tactic expr :=
e.get_app_fn.fill_args_with_mvars

end expr

open expr

namespace tactic

/--
Create a `tactic_state` with the given `goal` as its goal.
We don't try particularly hard to "start fresh".
-/
meta def tactic_state_with_goal (goal : expr) : tactic tactic_state :=
lock_tactic_state $ do
  n ← mk_fresh_name,
  assert n goal,
  g :: _ ← get_goals,
  set_goals [g],
  local_context >>= (λ ctx, ctx.mmap' (λ h, try (clear h))),
  get_state

meta def run_with_goal (goal : expr) {α} (t : tactic α) : tactic α :=
do
  state ← tactic_state_with_goal goal,
  run_with_state state t



namespace tactify

meta inductive proof_step
| apply (e : expr) : proof_step
| exact (e : expr) : proof_step
| intros (ns : list name) : proof_step
| rewrite (r : expr) : proof_step
| «sorry» (comment : format) : proof_step

meta inductive proof_script
| done : proof_script
| step (state : tactic_state) (step : proof_step) (rest : proof_script) : proof_script

namespace proof_step

meta def to_format : proof_step → tactic format
| (apply e) := do p ← pp e.replace_mvars, return format!"apply {p}"
| (exact e) := do p ← pp e, return format!"exact {p}"
| (intros ns) := do match ns with
  | [] := fail "unreachable code"
  | [n] := return format!"intro {n}"
  | _ := do let ns := string.intercalate " " (ns.map name.to_string), return format!"intros {ns}"
  end
| (rewrite r) := do p ← pp r, return format!"rw {p}"
| («sorry» c) := return $ format!"sorry" ++ " -- " ++ c

meta instance : has_to_tactic_format proof_step :=
⟨to_format⟩

/--
Given a list of solutions for the current goals, run a tactic `t`,
and compute the corresponding solutions for the new goals, if possible.
-/
meta def subgoals' (solutions : list expr) {α} (t : tactic α) :
  tactic (list expr) :=
do
  -- Keep a copy of the initial goals.
  initial_goals ← get_goals,
  -- Run the tactic
  -- trace_state,
  -- trace_result,
  t,
  -- trace_state,
  -- trace_result,
  -- then collect the new goals.
  new_goals ← get_goals,
  lock_tactic_state $ (do
    -- By unifying the initial goals with the given solutions,
    -- find the corresponding solutions for the new goals.
    (initial_goals.zip solutions).mmap' (λ ⟨g, s⟩, unify g s),
    new_goals.mmap instantiate_mvars)

meta def as_tactic : proof_step → tactic unit
| (apply e) := tactic.apply e >> skip
| (exact e) := tactic.exact e
| (intros ns) := tactic.intro_lst ns >> skip
| (rewrite r) := tactic.rewrite_target r >> try reflexivity
| («sorry» c) := tactic.admit

/-- Update a list of solutions for the current goals, as we progress through a proof_step. -/
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

/--
Return a list of pairs, consisting of a proof state, e.g.,
```
m n : ℕ,
h : m ≤ n
⊢ m.factorial ≤ n.factorial
```
and a tactic to run in that state, e.g. `apply nat.le_of_dvd`.

The intended purpose of this view is to generate training data.
-/
meta def prompts : proof_script → tactic (list (string × string))
| (proof_script.done) := return []
| (proof_script.step st s r) := do
  ppst ← pp st,
  pps ← pp s,
  rs ← r.prompts,
  return $ (to_string ppst, to_string pps) :: rs

end proof_script


meta def construct_apply_step (e : expr) : tactic proof_step :=
-- This part just doesn't work. :-(
-- (do
--   tgt ← target,
--   e' ← i_to_expr_strict ``(%%e : %%tgt),
--   lock_tactic_state (tactic.exact e'),
--   return (proof_step.exact e')) <|>
(do
  lock_tactic_state (tactic.apply e),
  return (proof_step.apply e)) <|>
(do
  pp_e ← pp e,
  pp_t ← infer_type e >>= pp,
  return (proof_step.sorry format!"tried to `apply {pp_e}` with type `{pp_t}` but couldn't make it work"))

/--
Attempt to deduce a single proof step from a list of `solutions` for the current goals,
along with the corresponding solutions for the new goals.
-/
meta def tactify_1 (solutions : list expr) :
  tactic (proof_step × list expr) :=
do
  let sol := solutions.head,
  s ← match sol with
  | (const _ _) := return (proof_step.exact sol)
  | (local_const _ _ _ _) := return (proof_step.exact sol)
  | (lam n _ _ _) := return (proof_step.intros sol.lam_binding_names)
  | (app f x) := do
      let f' := f.get_app_fn,
      match f' with
      | `(@bit0) := return (proof_step.exact sol)
      | `(@bit1) := return (proof_step.exact sol)
      | `(@eq.mpr) := do
          -- Assume the solution was built using `rw`, and hope we get it right:
          let b := sol.app_fn.app_arg.app_arg.app_arg,
          let b := if b.get_app_fn.const_name = `propext then b.app_arg else b,
          return (proof_step.rewrite b)
      -- | `(@iff.mpr) := do
      --     -- Rather than produce separate steps `apply iff.mpr` and then `apply F`,
      --     -- try to produce `refine (F _ _).mpr` in one step.
      --     match sol with
      --     | `(iff.mpr %%F %%x) := do
      --       -- Since we're playing with `_`s here, we need to discard extra goals that get created.
      --       -- gs ← get_goals,
      --       F' ← replace_args_with_mvars F,
      --       e ← lock_tactic_state $ to_expr ``(iff.mpr %%F'),
      --       -- set_goals gs,
      --       return (proof_step.apply e)
      --     | _ := fail "unreachable code"
      --     end
      | _ := do
          let n := f'.const_name,
          if (`dcases_on).is_suffix_of n ∨ (`cases_on).is_suffix_of n then
            return (proof_step.sorry "tactify can not cope with cases/induction/pattern mattching")
          else do
            construct_apply_step f'
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
    s.mmap' (λ p, do trace "---", trace p.1, trace p.2))

meta def all_tactic_prompts : tactic unit := do
  env ← get_env,
  env.mfold () (λ d _, do trace d.to_name, try (tactic_prompts d.to_name), trace "==="),
  skip

-- run_cmd all_tactic_prompts
-- set_option pp.all true

-- Examples that work:
run_cmd tactic_prompts `nat.factorial_le
run_cmd tactic_prompts `nat.units_eq_one
run_cmd tactic_prompts `nat.lt_factorial_self
run_cmd tactic_prompts `nat.zero_eq_mul

def foo (n m : ℕ) (h : m < n) : m.succ ≤ n :=
(nat.succ_le_iff).mpr h

run_cmd tactic_prompts `foo

-- TODO combine `apply iff.mpr` and `apply F` into `apply F.mpr`. (also `.mp`)
run_cmd tactic_prompts `nat.add_factorial_succ_lt_factorial_add_succ

example (i n : ℕ) (hi : 2 ≤ i) : i + n < (i + n) * (i + n).factorial :=
begin
  apply iff.mpr (lt_mul_iff_one_lt_right _),
end

-- TODO Use `exact` insteaf of `apply` where possible?
run_cmd tactic_prompts `multiset.coe_card -- verify that we generate `exact rfl`, not `apply rfl`.

-- TODO what's going on with
run_cmd tactic_prompts `add_cancel_comm_monoid.add_comm

-- TODO don't generate `apply id` steps
run_cmd tactic_prompts `list.decidable_chain._proof_2
#print list.decidable_chain
-- TODO avoid `apply id_rhs α`
-- TODO try generating shorter `rw` proofs (i.e. leave off arguments when they aren't needed)
-- TODO Also `eq.symm` (e.g. `functor.map_map`)?
-- TODO don't use `Exists.intro`?

-- PROJECT I don't know how to handle proofs that use `cases`, `induction`, or pattern matching.
run_cmd tactic_prompts `nat.add_factorial_le_factorial_add
run_cmd tactic_prompts `nat.self_le_factorial


#print add_lt_add_of_lt_of_le

#print rfl

example : false :=
begin
  tactify `nat.factorial_le,
  tactify `nat.add_factorial_succ_lt_factorial_add_succ,
end

example {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
  i + (n + 1).factorial < (i + n) * (i + n).factorial + (i + n).factorial :=
begin
  apply add_lt_add_of_lt_of_le,
  apply has_le.le.trans_lt,
  apply nat.le.intro,
  exact rfl,
  skip,
end

-- Extracted from nat.add_factorial_succ_lt_factorial_add_succ.
example : ∀ {i : ℕ} (n : ℕ), 2 ≤ i → i + (n + 1).factorial < (i + n + 1).factorial :=
begin
intros i n hi,
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
done
end

example : ∀ {i : ℕ} (n : ℕ), 2 ≤ i → i + (n + 1).factorial < (i + n + 1).factorial :=
begin
intros i n hi,
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
done
end
