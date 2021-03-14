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

/-- Implementation of `expr.mreplace`. -/
meta def mreplace_aux {m : Type* → Type*} [monad m] [alternative m] (R : expr → nat → m expr) :
  expr → ℕ → m expr
| (app f x) n := R (app f x) n <|>
  (do Rf ← mreplace_aux f n, Rx ← mreplace_aux x n, return $ app Rf Rx)
| (lam nm bi ty bd) n := R (lam nm bi ty bd) n <|>
  (do Rty ← mreplace_aux ty n, Rbd ← mreplace_aux bd (n+1), return $ lam nm bi Rty Rbd)
| (pi nm bi ty bd) n := R (pi nm bi ty bd) n <|>
  (do Rty ← mreplace_aux ty n, Rbd ← mreplace_aux bd (n+1), return $ pi nm bi Rty Rbd)
| (elet nm ty a b) n := R (elet nm ty a b) n <|>
  (do Rty ← mreplace_aux ty n,
    Ra ← mreplace_aux a n,
    Rb ← mreplace_aux b n,
    return $ elet nm Rty Ra Rb)
| e n := R e n <|> return e

/--
Monadic equivalent of `expr.replace`.

The function `R` visits each subexpression `e`, and is called with `R e n`, where
`n` is the number of binders above `e`.
If `R e n` returns some value, `e` is replaced with that value (and `mreplace` does not visit
its subexpressions).
If `R e n` fails, then `mreplace` continues visiting subexpressions of `e`.
-/
meta def mreplace {m : Type* → Type*} [monad m] [alternative m]
  (R : expr → nat → m expr) (e : expr) : m expr :=
mreplace_aux R e 0

/--
Replace each metavariable in an expression with a fresh metavariable of the same type.
-/
meta def refresh_mvars (e : expr) : tactic expr :=
e.mreplace (λ f n, if f.is_mvar then infer_type f >>= mk_meta_var else failed)

/--
Prepares a ``(n ___).mpr` expression that can be applied against the goal,
where `___` is however many `_`s are needed to obtain an `iff`.
-/
meta def iff_mpr_apply (n : name) : tactic expr :=
do t ← target,
   e ← prod.snd <$> (solve_aux t $ applyc `iff.mpr >> applyc n) >>= instantiate_mvars,
   e ← e.refresh_mvars,
   return e.app_fn

example (a b : ℕ) (h₁ : 1 < b) (h₂ : 0 < a) :
  a < a * b :=
begin
  apply (lt_mul_iff_one_lt_right _).mpr,
  exact h₁,
  exact h₂,
end

example (a b : ℕ) (h₁ : 1 < b) (h₂ : 0 < a) :
  a < a * b :=
begin
  iff_mpr_apply `lt_mul_iff_one_lt_right >>= trace, -- looks good: `(lt_mul_iff_one_lt_right ?m_1).mpr`
  iff_mpr_apply `lt_mul_iff_one_lt_right >>= apply,
  -- but we only get one goal :-(
  exact h₁,
end


end expr

open expr

namespace tactic

/--
Create a `tactic_state` with the given `goal` as its goal.
We don't try particularly hard to "start fresh".
-/
meta def tactic_state_with_goal (goal : expr) : tactic tactic_state :=
lock_tactic_state $ do
  g ← mk_meta_var goal,
  set_goals [g],
  get_state

meta def run_with_goal (goal : expr) {α} (t : tactic α) : tactic α :=
do
  state ← tactic_state_with_goal goal,
  run_with_state state t



namespace tactify

meta inductive proof_step
| apply (e : expr) : proof_step
-- | apply' (p : pexpr) (e : expr) : proof_step
| exact (e : expr) : proof_step
| intros (ns : list name) : proof_step
| rewrite (r : expr) (symm : bool) : proof_step
| «sorry» (comment : format) : proof_step

meta inductive proof_script
| done : proof_script
| step (state : tactic_state) (step : proof_step) (rest : proof_script) : proof_script

namespace proof_step

meta def to_format : proof_step → tactic format
| (apply e) := do p ← pp e.replace_mvars, return format!"apply {p}"
-- | (apply' p e) := do p ← pp e.replace_mvars, return format!"apply {p}"
| (exact e) := do p ← pp e, return format!"exact {p}"
| (intros ns) := do match ns with
  | [] := fail "unreachable code"
  | [n] := return format!"intro {n}"
  | _ := do let ns := string.intercalate " " (ns.map name.to_string), return format!"intros {ns}"
  end
| (rewrite r symm) := do p ← pp r, let a := if symm then "←" else "", return format!"rw {a}{p}"
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
  -- trace "before tactic:",
  -- trace_state,
  -- trace_result,
  -- trace "running tactic:",
  t,
  -- trace "after tactic:",
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
-- | (apply' p e) := tactic.interactive.apply p >> skip
| (exact e) := tactic.exact e
| (intros ns) := tactic.intro_lst ns >> skip
| (rewrite r symm) := tactic.rewrite_target r { symm := symm } >> try reflexivity
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
  -- trace "prompts:",
  ppst ← pp st,
  pps ← pp s,
  -- trace "prompts:",
  rs ← r.prompts,
  return $ (to_string ppst, to_string pps) :: rs

end proof_script



meta def construct_apply_step (e : expr) : tactic proof_step :=
(do
  lock_tactic_state (tactic.apply e),
  return (proof_step.apply e)) <|>
(do
  pp_e ← pp e,
  pp_t ← infer_type e >>= pp,
  return (proof_step.sorry format!"tried to `apply {pp_e}` with type `{pp_t}` but couldn't make it work"))

meta def shrink_rw_aux (symm : bool) (tgt : expr) (result : string) : expr → tactic expr
| r := do
  pp ← pp r,
  -- trace format!"shrink_rw_aux {pp}",
  if r.is_app then (do
    goal ← prod.snd <$> solve_aux tgt (tactic.rewrite_target r.app_fn { symm := symm }),
    result' ← to_string <$> tactic.pp goal,
    (guard (result = result') >> shrink_rw_aux (r.app_fn))) <|>
      return r
  else
    return r

meta def shrink_rw (symm : bool) (r : expr) : tactic expr :=
do
  t ← target,
  -- trace "target",
  -- trace t,
  -- trace symm,
  -- trace r,
  t' ← prod.snd <$> solve_aux t (tactic.rewrite_target r { symm := symm }),
  result ← to_string <$> tactic.pp t',
  shrink_rw_aux symm t result r

-- meta def shrink_rw (symm : bool) : expr → tactic expr
-- | e := do
--   -- trace e,
--   if e.is_app then do
--     s ← to_string <$> lock_tactic_state (do tactic.rewrite_target e { symm := symm }, get_state >>= pp),
--     let e' := e.app_fn,
--     s' ← to_string <$> lock_tactic_state (do tactic.rewrite_target e' { symm := symm }, get_state >>= pp),
--     if s = s' then
--       shrink_rw e'
--     else
--       return e
--   else
--     return e

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
          -- Now do some cleanup: first check for `eq.symm
          (symm, b) ← match b with
          | `(eq.symm %%b') := return (tt, b')
          | `(iff.symm %%b') := return (tt, b')
          | _ := return (ff, b)
          end,
          -- then try to discard arguments but still get the correct rewrite:
          -- trace format!"before shrink: {b}",
          b ← shrink_rw symm b,
          -- trace format!"after shrink: {b}",
          return (proof_step.rewrite b symm)
      -- | `(@iff.mpr) := do
      --     -- Rather than produce separate steps `apply iff.mpr` and then `apply F`,
      --     -- try to produce `refine (F _ _).mpr` in one step.
      --     match sol with
      --     | `(iff.mpr %%F %%x) := do
      --       -- Since we're playing with `_`s here, we need to discard extra goals that get created.
      --       -- trace_state,
      --       -- F' ← replace_args_with_mvars F,
      --       -- trace_state,
      --       -- let p := ``(iff.mpr %%F'),
      --       -- trace_state,
      --       -- e ← lock_tactic_state $ to_expr ``(iff.mpr %%F'),
      --       -- -- e ← mk_mapp ``iff.mpr [none,none,F'],
      --       -- -- e ← to_expr ``(iff.mpr %%F'),
      --       e ← iff_mpr_apply F.get_app_fn.const_name,
      --       trace e,
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
  -- trace "tactify:",
  goals ← get_goals,
  -- trace "tactify:",
  guard (goals.length = solutions.length) <|>
    fail "Number of solutions has diverged from the number of goals.",
  done >> return proof_script.done <|>
do
  -- trace "tactify:",
  state ← get_state,
  -- trace "before tactify_1:",
  -- trace_state,
  -- trace solutions,
  (step, new_solutions) ← tactify_1 solutions,
  -- trace "after tactify_1:",
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
run_cmd tactic_prompts `nat.lt_factorial_self -- minimising rewrites
run_cmd tactic_prompts `nat.zero_eq_mul

def foo (n m : ℕ) (h : m < n) : m.succ ≤ n :=
begin
  apply nat.succ_le_iff.mpr,
  exact h,
end

run_cmd tactic_prompts `foo

def bar (a b : ℕ) (h₁ : 1 < b) (h₂ : 0 < a) :
  a < a * b :=
begin
  -- show_term { applyc `iff.mpr, applyc `lt_mul_iff_one_lt_right, },
  apply (lt_mul_iff_one_lt_right _).mpr,
  exact h₁,
  exact h₂,
end

run_cmd tactic_prompts `bar


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
-- TODO Also `eq.symm` (e.g. `functor.map_map`)?
-- TODO don't use `Exists.intro`?

-- PROJECT I don't know how to handle proofs that use `cases`, `induction`, or pattern matching.
run_cmd tactic_prompts `nat.add_factorial_le_factorial_add
run_cmd tactic_prompts `nat.self_le_factorial


example : false :=
begin
  tactify `nat.factorial_le,
  tactify `nat.lt_factorial_self,
  tactify `nat.add_factorial_succ_lt_factorial_add_succ,
end

#print nat.lt_factorial_self

-- extract from nat.lt_factorial_self
example : ∀ {n : ℕ}, 3 ≤ n → n < n.factorial :=
begin
intros n hi,
rw ←nat.succ_pred_eq_of_pos ((zero_lt_two.trans (nat.lt.base 2)).trans_le hi),
rw nat.factorial_succ,
apply lt_mul_of_one_lt_right,
apply nat.succ_pos,
apply has_lt.lt.trans_le,
apply has_lt.lt.trans_le,
apply one_lt_two,
apply nat.le_pred_of_lt,
apply iff.mp,
apply nat.succ_le_iff,
exact hi,
apply nat.self_le_factorial,
done,
end

-- Extracted from nat.add_factorial_succ_lt_factorial_add_succ.
example : ∀ {i : ℕ} (n : ℕ), 2 ≤ i → i + (n + 1).factorial < (i + n + 1).factorial :=
begin
intros i n hi,
rw (i + n).factorial_succ,
rw nat.succ_eq_add_one,
rw add_mul,
rw one_mul,
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
