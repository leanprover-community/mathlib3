/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek
-/
import data.dlist.basic category.basic meta.expr meta.rb_map

namespace expr
open tactic

attribute [derive has_reflect] binder_info

protected meta def of_nat (α : expr) : ℕ → tactic expr :=
nat.binary_rec
  (tactic.mk_mapp ``has_zero.zero [some α, none])
  (λ b n tac, if n = 0 then mk_mapp ``has_one.one [some α, none] else
    do e ← tac, tactic.mk_app (cond b ``bit1 ``bit0) [e])

protected meta def of_int (α : expr) : ℤ → tactic expr
| (n : ℕ) := expr.of_nat α n
| -[1+ n] := do
  e ← expr.of_nat α (n+1),
  tactic.mk_app ``has_neg.neg [e]

/- only traverses the direct descendents -/
meta def {u} traverse {m : Type → Type u} [applicative m]
  {elab elab' : bool} (f : expr elab → m (expr elab')) :
  expr elab → m (expr elab')
 | (var v)  := pure $ var v
 | (sort l) := pure $ sort l
 | (const n ls) := pure $ const n ls
 | (mvar n n' e) := mvar n n' <$> f e
 | (local_const n n' bi e) := local_const n n' bi <$> f e
 | (app e₀ e₁) := app <$> f e₀ <*> f e₁
 | (lam n bi e₀ e₁) := lam n bi <$> f e₀ <*> f e₁
 | (pi n bi e₀ e₁) := pi n bi <$> f e₀ <*> f e₁
 | (elet n e₀ e₁ e₂) := elet n <$> f e₀ <*> f e₁ <*> f e₂
 | (macro mac es) := macro mac <$> list.traverse f es

meta def mfoldl {α : Type} {m} [monad m] (f : α → expr → m α) : α → expr → m α
| x e := prod.snd <$> (state_t.run (e.traverse $ λ e',
    (get >>= monad_lift ∘ flip f e' >>= put) $> e') x : m _)

end expr

namespace interaction_monad
open result

meta def get_result {σ α} (tac : interaction_monad σ α) :
  interaction_monad σ (interaction_monad.result σ α) | s :=
match tac s with
| r@(success _ s') := success r s'
| r@(exception _ _ s') := success r s'
end

end interaction_monad

namespace lean.parser
open lean interaction_monad.result

meta def of_tactic' {α} (tac : tactic α) : parser α :=
do r ← of_tactic (interaction_monad.get_result tac),
match r with
| (success a _) := return a
| (exception f pos _) := exception f pos
end

-- Override the builtin `lean.parser.of_tactic` coe, which is broken.
-- (See test/tactics.lean for a failure case.)
@[priority 2000]
meta instance has_coe' {α} : has_coe (tactic α) (parser α) :=
⟨of_tactic'⟩

meta def emit_command_here (str : string) : lean.parser string :=
do (_, left) ← with_input command_like str,
   return left

-- Emit a source code string at the location being parsed.
meta def emit_code_here : string → lean.parser unit
| str := do left ← emit_command_here str,
            if left.length = 0 then return ()
            else emit_code_here left

end lean.parser

namespace tactic

meta def eval_expr' (α : Type*) [_inst_1 : reflected α] (e : expr) : tactic α :=
mk_app ``id [e] >>= eval_expr α

-- `mk_fresh_name` returns identifiers starting with underscores,
-- which are not legal when emitted by tactic programs. Turn the
-- useful source of random names provided by `mk_fresh_name` into
-- names which are usable by tactic programs.
--
-- The returned name has four components.
meta def mk_user_fresh_name : tactic name :=
do nm ← mk_fresh_name,
   return $ `user__ ++ nm.pop_prefix.sanitize_name ++ `user__

meta def is_simp_lemma : name → tactic bool :=
succeeds ∘ tactic.has_attribute `simp

meta def local_decls : tactic (name_map declaration) :=
do e ← tactic.get_env,
   let xs := e.fold native.mk_rb_map
     (λ d s, if environment.in_current_file' e d.to_name
             then s.insert d.to_name d else s),
   pure xs

meta def simp_lemmas_from_file : tactic name_set :=
do s ← local_decls,
   let s := s.map (expr.list_constant ∘ declaration.value),
   xs ← s.to_list.mmap ((<$>) name_set.of_list ∘ mfilter tactic.is_simp_lemma ∘ name_set.to_list ∘ prod.snd),
   return $ name_set.filter (xs.foldl name_set.union mk_name_set) (λ x, ¬ s.contains x)

meta def file_simp_attribute_decl (attr : name) : tactic unit :=
do s ← simp_lemmas_from_file,
   trace format!"run_cmd mk_simp_attr `{attr}",
   let lmms := format.join $ list.intersperse " " $ s.to_list.map to_fmt,
   trace format!"local attribute [{attr}] {lmms}"

meta def mk_local (n : name) : expr :=
expr.local_const n n binder_info.default (expr.const n [])

meta def local_def_value (e : expr) : tactic expr := do
do (v,_) ← solve_aux `(true) (do
         (expr.elet n t v _) ← (revert e >> target)
           | fail format!"{e} is not a local definition",
         return v),
   return v

meta def check_defn (n : name) (e : pexpr) : tactic unit :=
do (declaration.defn _ _ _ d _ _) ← get_decl n,
   e' ← to_expr e,
   guard (d =ₐ e') <|> trace d >> failed

-- meta def compile_eqn (n : name) (univ : list name) (args : list expr) (val : expr) (num : ℕ) : tactic unit :=
-- do let lhs := (expr.const n $ univ.map level.param).mk_app args,
--    stmt ← mk_app `eq [lhs,val],
--    let vs := stmt.list_local_const,
--    let stmt := stmt.pis vs,
--    (_,pr) ← solve_aux stmt (tactic.intros >> reflexivity),
--    add_decl $ declaration.thm (n <.> "equations" <.> to_string (format!"_eqn_{num}")) univ stmt (pure pr)

meta def to_implicit : expr → expr
| (expr.local_const uniq n bi t) := expr.local_const uniq n binder_info.implicit t
| e := e

meta def pis : list expr → expr → tactic expr
| (e@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← pis es f,
  pure $ expr.pi pp info t (expr.abstract_local f' uniq)
| _ f := pure f

meta def lambdas : list expr → expr → tactic expr
| (e@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← lambdas es f,
  pure $ expr.lam pp info t (expr.abstract_local f' uniq)
| _ f := pure f

meta def extract_def (n : name) (trusted : bool) (elab_def : tactic unit) : tactic unit :=
do cxt ← list.map to_implicit <$> local_context,
   t ← target,
   (eqns,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   applyc n

meta def exact_dec_trivial : tactic unit := `[exact dec_trivial]

/-- Runs a tactic for a result, reverting the state after completion -/
meta def retrieve {α} (tac : tactic α) : tactic α :=
λ s, result.cases_on (tac s)
 (λ a s', result.success a s)
 result.exception

/-- Repeat a tactic at least once, calling it recursively on all subgoals,
  until it fails. This tactic fails if the first invocation fails. -/
meta def repeat1 (t : tactic unit) : tactic unit := t; repeat t

/-- `iterate_range m n t`: Repeat the given tactic at least `m` times and
  at most `n` times or until `t` fails. Fails if `t` does not run at least m times. -/
meta def iterate_range : ℕ → ℕ → tactic unit → tactic unit
| 0 0     t := skip
| 0 (n+1) t := try (t >> iterate_range 0 n t)
| (m+1) n t := t >> iterate_range m (n-1) t

meta def replace_at (tac : expr → tactic (expr × expr)) (hs : list expr) (tgt : bool) : tactic bool :=
do to_remove ← hs.mfilter $ λ h, do {
    h_type ← infer_type h,
    succeeds $ do
      (new_h_type, pr) ← tac h_type,
      assert h.local_pp_name new_h_type,
      mk_eq_mp pr h >>= tactic.exact },
  goal_simplified ← succeeds $ do {
    guard tgt,
    (new_t, pr) ← target >>= tac,
    replace_target new_t pr },
  to_remove.mmap' (λ h, try (clear h)),
  return (¬ to_remove.empty ∨ goal_simplified)

meta def simp_bottom_up' (post : expr → tactic (expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (expr × expr) :=
prod.snd <$> simplify_bottom_up () (λ _, (<$>) (prod.mk ()) ∘ post) e cfg

meta structure instance_cache :=
(α : expr)
(univ : level)
(inst : name_map expr)

meta def mk_instance_cache (α : expr) : tactic instance_cache :=
do u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   return ⟨α, u, mk_name_map⟩

namespace instance_cache

meta def get (c : instance_cache) (n : name) : tactic (instance_cache × expr) :=
match c.inst.find n with
| some i := return (c, i)
| none := do e ← mk_app n [c.α] >>= mk_instance,
  return (⟨c.α, c.univ, c.inst.insert n e⟩, e)
end

open expr
meta def append_typeclasses : expr → instance_cache → list expr →
  tactic (instance_cache × list expr)
| (pi _ binder_info.inst_implicit (app (const n _) (var _)) body) c l :=
  do (c, p) ← c.get n, return (c, p :: l)
| _ c l := return (c, l)

meta def mk_app (c : instance_cache) (n : name) (l : list expr) : tactic (instance_cache × expr) :=
do d ← get_decl n,
   (c, l) ← append_typeclasses d.type.binding_body c l,
   return (c, (expr.const n [c.univ]).mk_app (c.α :: l))

end instance_cache

/-- Reset the instance cache for the main goal. -/
meta def reset_instance_cache : tactic unit := unfreeze_local_instances

meta def match_head (e : expr) : expr → tactic unit
| e' :=
    unify e e'
<|> do `(_ → %%e') ← whnf e',
       v ← mk_mvar,
       match_head (e'.instantiate_var v)

meta def find_matching_head : expr → list expr → tactic (list expr)
| e []         := return []
| e (H :: Hs) :=
  do t ← infer_type H,
     ((::) H <$ match_head e t <|> pure id) <*> find_matching_head e Hs

meta def subst_locals (s : list (expr × expr)) (e : expr) : expr :=
(e.abstract_locals (s.map (expr.local_uniq_name ∘ prod.fst)).reverse).instantiate_vars (s.map prod.snd)

meta def set_binder : expr → list binder_info → expr
| e [] := e
| (expr.pi v _ d b) (bi :: bs) := expr.pi v bi d (set_binder b bs)
| e _ := e

meta def last_explicit_arg : expr → tactic expr
| (expr.app f e) :=
do t ← infer_type f >>= whnf,
   if t.binding_info = binder_info.default
     then pure e
     else last_explicit_arg f
| e := pure e

private meta def get_expl_pi_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     let l := expr.local_const m n bi d,
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_expl_pi_arity_aux new_b,
     if bi = binder_info.default then
       return (r + 1)
     else
       return r
| e := return 0

/-- Compute the arity of explicit arguments of the given (Pi-)type -/
meta def get_expl_pi_arity (type : expr) : tactic nat :=
whnf type >>= get_expl_pi_arity_aux

/-- Compute the arity of explicit arguments of the given function -/
meta def get_expl_arity (fn : expr) : tactic nat :=
infer_type fn >>= get_expl_pi_arity

/-- variation on `assert` where a (possibly incomplete)
    proof of the assertion is provided as a parameter.

    ``(h,gs) ← local_proof `h p tac`` creates a local `h : p` and
    use `tac` to (partially) construct a proof for it. `gs` is the
    list of remaining goals in the proof of `h`.

    The benefits over assert are:
    - unlike with ``h ← assert `h p, tac`` , `h` cannot be used by `tac`;
    - when `tac` does not complete the proof of `h`, returning the list
      of goals allows one to write a tactic using `h` and with the confidence
      that a proof will not boil over to goals left over from the proof of `h`,
      unlike what would be the case when using `tactic.swap`.
-/
meta def local_proof (h : name) (p : expr) (tac₀ : tactic unit) :
  tactic (expr × list expr) :=
focus1 $
do h' ← assert h p,
   [g₀,g₁] ← get_goals,
   set_goals [g₀], tac₀,
   gs ← get_goals,
   set_goals [g₁],
   return (h', gs)

meta def var_names : expr → list name
| (expr.pi n _ _ b) := n :: var_names b
| _ := []

meta def drop_binders : expr → tactic expr
| (expr.pi n bi t b) := b.instantiate_var <$> mk_local' n bi t >>= drop_binders
| e := pure e

meta def subobject_names (struct_n : name) : tactic (list name × list name) :=
do env ← get_env,
   [c] ← pure $ env.constructors_of struct_n | fail "too many constructors",
   vs  ← var_names <$> (mk_const c >>= infer_type),
   fields ← env.structure_fields struct_n,
   return $ fields.partition (λ fn, ↑("_" ++ fn.to_string) ∈ vs)

meta def expanded_field_list' : name → tactic (dlist $ name × name) | struct_n :=
do (so,fs) ← subobject_names struct_n,
   ts ← so.mmap (λ n, do
     e ← mk_const (n.update_prefix struct_n) >>= infer_type >>= drop_binders,
     expanded_field_list' $ e.get_app_fn.const_name),
   return $ dlist.join ts ++ dlist.of_list (fs.map $ prod.mk struct_n)
open functor function

meta def expanded_field_list (struct_n : name) : tactic (list $ name × name) :=
dlist.to_list <$> expanded_field_list' struct_n

meta def get_classes (e : expr) : tactic (list name) :=
attribute.get_instances `class >>= list.mfilter (λ n,
  succeeds $ mk_app n [e] >>= mk_instance)

open nat

meta def mk_mvar_list : ℕ → tactic (list expr)
| 0 := pure []
| (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

/--`iterate_at_most_on_all_goals n t`: repeat the given tactic at most `n` times on all goals,
or until it fails. Always succeeds. -/
meta def iterate_at_most_on_all_goals : nat → tactic unit → tactic unit
| 0        tac := trace "maximal iterations reached"
| (succ n) tac := tactic.all_goals $ (do tac, iterate_at_most_on_all_goals n tac) <|> skip

/--`iterate_at_most_on_subgoals n t`: repeat the tactic `t` at most `n` times on the first
goal and on all subgoals thus produced, or until it fails. Fails iff `t` fails on
current goal. -/
meta def iterate_at_most_on_subgoals : nat → tactic unit → tactic unit
| 0        tac := trace "maximal iterations reached"
| (succ n) tac := focus1 (do tac, iterate_at_most_on_all_goals n tac)

/--`apply_list l`: try to apply the tactics in the list `l` on the first goal, and
fail if none succeeds -/
meta def apply_list_expr : list expr → tactic unit
| []     := fail "no matching rule"
| (h::t) := do interactive.concat_tags (apply h) <|> apply_list_expr t

/-- constructs a list of expressions given a list of p-expressions, as follows:
- if the p-expression is the name of a theorem, use `i_to_expr_for_apply` on it
- if the p-expression is a user attribute, add all the theorems with this attribute
  to the list.-/
meta def build_list_expr_for_apply : list pexpr → tactic (list expr)
| [] := return []
| (h::t) := do
  tail ← build_list_expr_for_apply t,
  a ← i_to_expr_for_apply h,
  (do l ← attribute.get_instances (expr.const_name a),
      m ← list.mmap mk_const l,
      return (m.append tail))
  <|> return (a::tail)

/--`apply_rules hs n`: apply the list of rules `hs` (given as pexpr) and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times -/
meta def apply_rules (hs : list pexpr) (n : nat) : tactic unit :=
do l ← build_list_expr_for_apply hs,
   iterate_at_most_on_subgoals n (assumption <|> apply_list_expr l)

meta def replace (h : name) (p : pexpr) : tactic unit :=
do h' ← get_local h,
   p ← to_expr p,
   note h none p,
   clear h'

meta def symm_apply (e : expr) (cfg : apply_cfg := {}) : tactic (list (name × expr)) :=
tactic.apply e cfg <|> (symmetry >> tactic.apply e cfg)

meta def apply_assumption
  (asms : tactic (list expr) := local_context)
  (tac : tactic unit := skip) : tactic unit :=
do { ctx ← asms,
     ctx.any_of (λ H, symm_apply H >> tac) } <|>
do { exfalso,
     ctx ← asms,
     ctx.any_of (λ H, symm_apply H >> tac) }
<|> fail "assumption tactic failed"

meta def change_core (e : expr) : option expr → tactic unit
| none     := tactic.change e
| (some h) :=
  do num_reverted : ℕ ← revert h,
     expr.pi n bi d b ← target,
     tactic.change $ expr.pi n bi e b,
     intron num_reverted

/--
assuming olde and newe are defeq when elaborated, replaces occurences of olde with newe at hypothesis h.
-/
meta def change_with_at (olde newe : pexpr) (hyp : name) : tactic unit :=
do h ← get_local hyp,
   tp ← infer_type h,
   olde ← to_expr olde, newe ← to_expr newe,
   let repl_tp := tp.replace (λ a n, if a = olde then some newe else none),
   change_core repl_tp (some h)

open nat

meta def solve_by_elim_aux (discharger : tactic unit) (asms : tactic (list expr))  : ℕ → tactic unit
| 0 := done
| (succ n) := discharger <|> (apply_assumption asms $ solve_by_elim_aux n)

meta structure by_elim_opt :=
  (discharger : tactic unit := done)
  (assumptions : tactic (list expr) := local_context)
  (max_rep : ℕ := 3)

meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
do
  tactic.fail_if_no_goals,
  focus1 $
    solve_by_elim_aux opt.discharger opt.assumptions opt.max_rep

meta def metavariables : tactic (list expr) :=
do r ← result,
   pure (r.list_meta_vars)

/-- Succeeds only if the current goal is a proposition. -/
meta def propositional_goal : tactic unit :=
do goals ← get_goals,
   p ← is_proof goals.head,
   guard p

meta def triv' : tactic unit := do c ← mk_const `trivial, exact c reducible

variable {α : Type}

private meta def iterate_aux (t : tactic α) : list α → tactic (list α)
| L := (do r ← t, iterate_aux (r :: L)) <|> return L

/-- Apply a tactic as many times as possible, collecting the results in a list. -/
meta def iterate' (t : tactic α) : tactic (list α) :=
list.reverse <$> iterate_aux t []

/-- Like iterate', but fail if the tactic does not succeed at least once. -/
meta def iterate1 (t : tactic α) : tactic (α × list α) :=
do r ← decorate_ex "iterate1 failed: tactic did not succeed" t,
   L ← iterate' t,
   return (r, L)

meta def intros1 : tactic (list expr) :=
iterate1 intro1 >>= λ p, return (p.1 :: p.2)

/-- `successes` invokes each tactic in turn, returning the list of successful results. -/
meta def successes (tactics : list (tactic α)) : tactic (list α) :=
list.filter_map id <$> monad.sequence (tactics.map (λ t, try_core t))

/-- Return target after instantiating metavars and whnf -/
private meta def target' : tactic expr :=
target >>= instantiate_mvars >>= whnf

/--
Just like `split`, `fsplit` applies the constructor when the type of the target is an inductive data type with one constructor.
However it does not reorder goals or invoke `auto_param` tactics.
-/
-- FIXME check if we can remove `auto_param := ff`
meta def fsplit : tactic unit :=
do [c] ← target' >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= λ e, apply e {new_goals := new_goals.all, auto_param := ff} >> skip

run_cmd add_interactive [`fsplit]

/-- Calls `injection` on each hypothesis, and then, for each hypothesis on which `injection`
    succeeds, clears the old hypothesis. -/
meta def injections_and_clear : tactic unit :=
do l ← local_context,
   results ← successes $ l.map $ λ e, injection e >> clear e,
   when (results.empty) (fail "could not use `injection` then `clear` on any hypothesis")

run_cmd add_interactive [`injections_and_clear]

meta def note_anon (e : expr) : tactic unit :=
do n ← get_unused_name "lh",
   note n none e, skip

/-- `find_local t` returns a local constant with type t, or fails if none exists. -/
meta def find_local (t : pexpr) : tactic expr :=
do t' ← to_expr t,
   prod.snd <$> solve_aux t' assumption

/-- `dependent_pose_core l`: introduce dependent hypothesis, where the proofs depend on the values
of the previous local constants. `l` is a list of local constants and their values. -/
meta def dependent_pose_core (l : list (expr × expr)) : tactic unit := do
  let lc := l.map prod.fst,
  let lm := l.map (λ⟨l, v⟩, (l.local_uniq_name, v)),
  t ← target,
  new_goal ← mk_meta_var (t.pis lc),
  old::other_goals ← get_goals,
  set_goals (old :: new_goal :: other_goals),
  exact ((new_goal.mk_app lc).instantiate_locals lm),
  return ()

/-- like `mk_local_pis` but translating into weak head normal form before checking if it is a Π. -/
meta def mk_local_pis_whnf : expr → tactic (list expr × expr) | e := do
(expr.pi n bi d b) ← whnf e | return ([], e),
p ← mk_local' n bi d,
(ps, r) ← mk_local_pis (expr.instantiate_var b p),
return ((p :: ps), r)

/-- Changes `(h : ∀xs, ∃a:α, p a) ⊢ g` to `(d : ∀xs, a) (s : ∀xs, p (d xs) ⊢ g` -/
meta def choose1 (h : expr) (data : name) (spec : name) : tactic expr := do
  t ← infer_type h,
  (ctxt, t) ← mk_local_pis_whnf t,
  `(@Exists %%α %%p) ← whnf t transparency.all | fail "expected a term of the shape ∀xs, ∃a, p xs a",
  α_t ← infer_type α,
  expr.sort u ← whnf α_t transparency.all,
  value ← mk_local_def data (α.pis ctxt),
  t' ← head_beta (p.app (value.mk_app ctxt)),
  spec ← mk_local_def spec (t'.pis ctxt),
  dependent_pose_core [
    (value, ((((expr.const `classical.some [u]).app α).app p).app (h.mk_app ctxt)).lambdas ctxt),
    (spec, ((((expr.const `classical.some_spec [u]).app α).app p).app (h.mk_app ctxt)).lambdas ctxt)],
  try (tactic.clear h),
  intro1,
  intro1

/-- Changes `(h : ∀xs, ∃as, p as) ⊢ g` to a list of functions `as`, an a final hypothesis on `p as` -/
meta def choose : expr → list name → tactic unit
| h [] := fail "expect list of variables"
| h [n] := do
  cnt ← revert h,
  intro n,
  intron (cnt - 1),
  return ()
| h (n::ns) := do
  v ← get_unused_name >>= choose1 h n,
  choose v ns

/-- This makes sure that the execution of the tactic does not change the tactic state.
    This can be helpful while using rewrite, apply, or expr munging.
    Remember to instantiate your metavariables before you're done! -/
meta def lock_tactic_state {α} (t : tactic α) : tactic α
| s := match t s with
       | result.success a s' := result.success a s
       | result.exception msg pos s' := result.exception msg pos s
end

/--
Hole command used to fill in a structure's field when specifying an instance.

In the following:

```
instance : monad id :=
{! !}
```

invoking hole command `Instance Stub` produces:

```
instance : monad id :=
{ map := _,
  map_const := _,
  pure := _,
  seq := _,
  seq_left := _,
  seq_right := _,
  bind := _ }
```
-/
@[hole_command] meta def instance_stub : hole_command :=
{ name := "Instance Stub",
  descr := "Generate a skeleton for the structure under construction.",
  action := λ _,
  do tgt ← target >>= whnf,
     let cl := tgt.get_app_fn.const_name,
     env ← get_env,
     fs ← expanded_field_list cl,
     let fs := fs.map prod.snd,
     let fs := list.intersperse (",\n  " : format) $ fs.map (λ fn, format!"{fn} := _"),
     let out := format.to_string format!"{{ {format.join fs} }",
     return [(out,"")] }

meta def is_default_local : expr → bool
| (expr.local_const _ _ binder_info.default _) := tt
| _ := ff

meta def mk_patterns (t : expr) : tactic (list format) :=
do let cl := t.get_app_fn.const_name,
   env ← get_env,
   let fs := env.constructors_of cl,
   fs.mmap $ λ f,
     do { (vs,_) ← mk_const f >>= infer_type >>= mk_local_pis,
          let vs := vs.filter (λ v, is_default_local v),
          vs ← vs.mmap (λ v,
            do v' ← get_unused_name v.local_pp_name,
               pose v' none `(()),
               pure v' ),
          vs.mmap' $ λ v, get_local v >>= clear,
          let args := list.intersperse (" " : format) $ vs.map to_fmt,
          if args.empty
            then pure $ format!"| {f} := _\n"
            else pure format!"| ({f} {format.join args}) := _\n" }

/--
Hole command used to generate a `match` expression.

In the following:

```
meta def foo (e : expr) : tactic unit :=
{! e !}
```

invoking hole command `Match Stub` produces:

```
meta def foo (e : expr) : tactic unit :=
match e with
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
end
```
-/
@[hole_command] meta def match_stub : hole_command :=
{ name := "Match Stub",
  descr := "Generate a list of equations for a `match` expression.",
  action := λ es,
  do [e] ← pure es | fail "expecting one expression",
     e ← to_expr e,
     t ← infer_type e >>= whnf,
     fs ← mk_patterns t,
     e ← pp e,
     let out := format.to_string format!"match {e} with\n{format.join fs}end\n",
     return [(out,"")] }

/--
Hole command used to generate a `match` expression.

In the following:

```
meta def foo : {! expr → tactic unit !} -- `:=` is omitted
```

invoking hole command `Equations Stub` produces:

```
meta def foo : expr → tactic unit
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

A similar result can be obtained by invoking `Equations Stub` on the following:

```
meta def foo : expr → tactic unit := -- do not forget to write `:=`!!
{! !}
```

```
meta def foo : expr → tactic unit := -- don't forget to erase `:=`!!
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

-/
@[hole_command] meta def eqn_stub : hole_command :=
{ name := "Equations Stub",
  descr := "Generate a list of equations for a recursive definition.",
  action := λ es,
  do t ← match es with
         | [t] := to_expr t
         | [] := target
         | _ := fail "expecting one type"
         end,
     e ← whnf t,
     (v :: _,_) ← mk_local_pis e | fail "expecting a Pi-type",
     t' ← infer_type v,
     fs ← mk_patterns t',
     t ← pp t,
     let out :=
         if es.empty then
           format.to_string format!"-- do not forget to erase `:=`!!\n{format.join fs}"
           else format.to_string format!"{t}\n{format.join fs}",
     return [(out,"")] }

/--
This command lists the constructors that can be used to satisfy the expected type.

When used in the following hole:

```
def foo : ℤ ⊕ ℕ :=
{! !}
```

the command will produce:

```
def foo : ℤ ⊕ ℕ :=
{! sum.inl, sum.inr !}
```

and will display:

```
sum.inl : ℤ → ℤ ⊕ ℕ

sum.inr : ℕ → ℤ ⊕ ℕ
```

-/
@[hole_command] meta def list_constructors_hole : hole_command :=
{ name := "List Constructors",
  descr := "Show the list of constructors of the expected type.",
  action := λ es,
  do t ← target >>= whnf,
     (_,t) ← mk_local_pis t,
     let cl := t.get_app_fn.const_name,
     let args := t.get_app_args,
     env ← get_env,
     let cs := env.constructors_of cl,
     ts ← cs.mmap $ λ c,
       do { e ← mk_const c,
            t ← infer_type (e.mk_app args) >>= pp,
            pure format!"\n{c} : {t}\n" },
     let fs := list.intersperse (", " : format) $ cs.map to_fmt,
     let out := format.to_string format!"{{! {format.join fs} !}",
     trace (format.join ts).to_string,
     return [(out,"")] }

meta def classical : tactic unit :=
do h ← get_unused_name `_inst,
   mk_const `classical.prop_decidable >>= note h none,
   reset_instance_cache

open expr

meta def add_prime : name → name
| (name.mk_string s p) := name.mk_string (s ++ "'") p
| n := (name.mk_string "x'" n)

meta def mk_comp (v : expr) : expr → tactic expr
| (app f e) :=
  if e = v then pure f
  else do
    guard (¬ v.occurs f) <|> fail "bad guard",
    e' ← mk_comp e >>= instantiate_mvars,
    f ← instantiate_mvars f,
    mk_mapp ``function.comp [none,none,none,f,e']
| e :=
  do guard (e = v),
     t ← infer_type e,
     mk_mapp ``id [t]

meta def mk_higher_order_type : expr → tactic expr
| (pi n bi d b@(pi _ _ _ _)) :=
  do v ← mk_local_def n d,
     let b' := (b.instantiate_var v),
     (pi n bi d ∘ flip abstract_local v.local_uniq_name) <$> mk_higher_order_type b'
| (pi n bi d b) :=
  do v ← mk_local_def n d,
     let b' := (b.instantiate_var v),
     (l,r) ← match_eq b' <|> fail format!"not an equality {b'}",
     l' ← mk_comp v l,
     r' ← mk_comp v r,
     mk_app ``eq [l',r']
 | e := failed

open lean.parser interactive.types

@[user_attribute]
meta def higher_order_attr : user_attribute unit (option name) :=
{ name := `higher_order,
  parser := optional ident,
  descr :=
"From a lemma of the shape `f (g x) = h x` derive an auxiliary lemma of the
form `f ∘ g = h` for reasoning about higher-order functions.",
  after_set := some $ λ lmm _ _,
    do env  ← get_env,
       decl ← env.get lmm,
       let num := decl.univ_params.length,
       let lvls := (list.iota num).map (`l).append_after,
       let l : expr := expr.const lmm $ lvls.map level.param,
       t ← infer_type l >>= instantiate_mvars,
       t' ← mk_higher_order_type t,
       (_,pr) ← solve_aux t' $ do {
         intros, applyc ``_root_.funext, intro1, applyc lmm; assumption },
       pr ← instantiate_mvars pr,
       lmm' ← higher_order_attr.get_param lmm,
       lmm' ← (flip name.update_prefix lmm.get_prefix <$> lmm') <|> pure (add_prime lmm),
       add_decl $ declaration.thm lmm' lvls t' (pure pr),
       copy_attribute `simp lmm tt lmm',
       copy_attribute `functor_norm lmm tt lmm' }

attribute [higher_order map_comp_pure] map_pure

private meta def tactic.use_aux (h : pexpr) : tactic unit :=
(focus1 (refine h >> done)) <|> (fconstructor >> tactic.use_aux)

meta def tactic.use (l : list pexpr) : tactic unit :=
focus1 $ l.mmap' $ λ h, tactic.use_aux h <|> fail format!"failed to instantiate goal with {h}"

meta def clear_aux_decl_aux : list expr → tactic unit
| []     := skip
| (e::l) := do cond e.is_aux_decl (tactic.clear e) skip, clear_aux_decl_aux l

meta def clear_aux_decl : tactic unit :=
local_context >>= clear_aux_decl_aux

end tactic
