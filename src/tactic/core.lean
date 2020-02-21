/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek
-/
import data.dlist.basic category.basic meta.expr meta.rb_map data.bool tactic.library_note
  tactic.derive_inhabited

namespace expr
open tactic

attribute [derive has_reflect] binder_info
attribute [derive decidable_eq] binder_info congr_arg_kind

/-- Given an expr `α` representing a type with numeral structure,
`of_nat α n` creates the `α`-valued numeral expression corresponding to `n`. -/
protected meta def of_nat (α : expr) : ℕ → tactic expr :=
nat.binary_rec
  (tactic.mk_mapp ``has_zero.zero [some α, none])
  (λ b n tac, if n = 0 then mk_mapp ``has_one.one [some α, none] else
    do e ← tac, tactic.mk_app (cond b ``bit1 ``bit0) [e])

/-- Given an expr `α` representing a type with numeral structure,
`of_int α n` creates the `α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
protected meta def of_int (α : expr) : ℤ → tactic expr
| (n : ℕ) := expr.of_nat α n
| -[1+ n] := do
  e ← expr.of_nat α (n+1),
  tactic.mk_app ``has_neg.neg [e]

/-- Generates an expression of the form `∃(args), inner`. `args` is assumed to be a list of local
  constants. When possible, `p ∧ q` is used instead of `∃(_ : p), q`. -/
meta def mk_exists_lst (args : list expr) (inner : expr) : tactic expr :=
args.mfoldr (λarg i:expr, do
    t ← infer_type arg,
    sort l ← infer_type t,
    return $ if arg.occurs i ∨ l ≠ level.zero
      then (const `Exists [l] : expr) t (i.lambdas [arg])
      else (const `and [] : expr) t i)
  inner

/-- `traverse f e` applies the monadic function `f` to the direct descendants of `e`. -/
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

/-- `mfoldl f a e` folds the monadic function `f` over the subterms of the expression `e`,
with initial value `a`. -/
meta def mfoldl {α : Type} {m} [monad m] (f : α → expr → m α) : α → expr → m α
| x e := prod.snd <$> (state_t.run (e.traverse $ λ e',
    (get >>= monad_lift ∘ flip f e' >>= put) $> e') x : m _)

end expr

namespace interaction_monad
open result

/-- `get_result tac` returns the result state of applying `tac` to the current state.
Note that it does not update the current state. -/
meta def get_result {σ α} (tac : interaction_monad σ α) :
  interaction_monad σ (interaction_monad.result σ α) | s :=
match tac s with
| r@(success _ s') := success r s'
| r@(exception _ _ s') := success r s'
end

end interaction_monad

namespace lean.parser
open lean interaction_monad.result

/-- `of_tactic' tac` lifts the tactic `tac` into the parser monad.
This replaces `of_tactic` in core, which has a buggy implementation. -/
meta def of_tactic' {α} (tac : tactic α) : parser α :=
do r ← of_tactic (interaction_monad.get_result tac),
match r with
| (success a _) := return a
| (exception f pos _) := exception f pos
end

/-- Override the builtin `lean.parser.of_tactic` coe, which is broken.
(See test/tactics.lean for a failure case.) -/
@[priority 2000]
meta instance has_coe' {α} : has_coe (tactic α) (parser α) :=
⟨of_tactic'⟩

/-- `emit_command_here str` behaves as if the string `str` were placed as a user command at the
current line. -/
meta def emit_command_here (str : string) : lean.parser string :=
do (_, left) ← with_input command_like str,
   return left

/-- `emit_code_here str` behaves as if the string `str` were placed at the current location in
source code. -/
meta def emit_code_here : string → lean.parser unit
| str := do left ← emit_command_here str,
            if left.length = 0 then return ()
            else emit_code_here left

end lean.parser

namespace format

/-- `intercalate x [a, b, c]` produces the format object `a.x.b.x.c`,
where `.` represents `format.join`. -/
meta def intercalate (x : format) : list format → format :=
format.join ∘ list.intersperse x

end format

namespace tactic
open function

/-- `mk_local_pisn e n` instantiates the first `n` variables of a pi expression `e`,
and returns the new local constants along with the instantiated expression. Fails if `e` does
not begin with at least `n` pi binders. -/
meta def mk_local_pisn : expr → nat → tactic (list expr × expr)
| (expr.pi n bi d b) (c + 1) := do
  p ← mk_local' n bi d,
  (ps, r) ← mk_local_pisn (b.instantiate_var p) c,
  return ((p :: ps), r)
| e 0 := return ([], e)
| _ _ := failed

-- TODO: move to `declaration` namespace in `meta/expr.lean`
/-- `mk_theorem n ls t e` creates a theorem declaration with name `n`, universe parameters named
`ls`, type `t`, and body `e`. -/
meta def mk_theorem (n : name) (ls : list name) (t : expr) (e : expr) : declaration :=
declaration.thm n ls t (task.pure e)

/-- `add_theorem_by n ls type tac` uses `tac` to synthesize a term with type `type`, and adds this
to the environment as a theorem with name `n` and universe parameters `ls`. -/
meta def add_theorem_by (n : name) (ls : list name) (type : expr) (tac : tactic unit) : tactic expr := do
  ((), body) ← solve_aux type tac,
  body ← instantiate_mvars body,
  add_decl $ mk_theorem n ls type body,
  return $ expr.const n $ ls.map level.param

/-- `eval_expr' α e` attempts to evaluate the expression `e` in the type `α`.
This is a variant of `eval_expr` in core. Due to unexplained behavior in the VM, in rare
situations the latter will fail but the former will succeed. -/
meta def eval_expr' (α : Type*) [_inst_1 : reflected α] (e : expr) : tactic α :=
mk_app ``id [e] >>= eval_expr α

/-- `mk_fresh_name` returns identifiers starting with underscores,
which are not legal when emitted by tactic programs. `mk_user_fresh_name`
turns the useful source of random names provided by `mk_fresh_name` into
names which are usable by tactic programs.

The returned name has four components which are all strings. -/
meta def mk_user_fresh_name : tactic name :=
do nm ← mk_fresh_name,
   return $ `user__ ++ nm.pop_prefix.sanitize_name ++ `user__


/-- `has_attribute n n'` checks whether n' has attribute n. -/
meta def has_attribute' : name → name → tactic bool | n n' :=
succeeds (has_attribute n n')

/-- Checks whether the name is a simp lemma -/
meta def is_simp_lemma : name → tactic bool :=
has_attribute' `simp

/-- Checks whether the name is an instance. -/
meta def is_instance : name → tactic bool :=
has_attribute' `instance

/-- `local_decls` returns a dictionary mapping names to their corresponding declarations.
Covers all declarations from the current file. -/
meta def local_decls : tactic (name_map declaration) :=
do e ← tactic.get_env,
   let xs := e.fold native.mk_rb_map
     (λ d s, if environment.in_current_file' e d.to_name
             then s.insert d.to_name d else s),
   pure xs

/-- If `{nm}_{n}` doesn't exist in the environment, returns that, otherwise tries `{nm}_{n+1}` -/
meta def get_unused_decl_name_aux (e : environment) (nm : name) : ℕ → tactic name | n :=
let nm' := nm.append_suffix ("_" ++ to_string n) in
if e.contains nm' then get_unused_decl_name_aux (n+1) else return nm'

/-- Return a name which doesn't already exist in the environment. If `nm` doesn't exist, it
  returns that, otherwise it tries nm_2, nm_3, ... -/
meta def get_unused_decl_name (nm : name) : tactic name :=
get_env >>= λ e, if e.contains nm then get_unused_decl_name_aux e nm 2 else return nm

/--
Returns a pair (e, t), where `e ← mk_const d.to_name`, and `t = d.type`
but with universe params updated to match the fresh universe metavariables in `e`.

This should have the same effect as just
```
do e ← mk_const d.to_name,
   t ← infer_type e,
   return (e, t)
```
but is hopefully faster.
-/
meta def decl_mk_const (d : declaration) : tactic (expr × expr) :=
do subst ← d.univ_params.mmap $ λ u, prod.mk u <$> mk_meta_univ,
   let e : expr := expr.const d.to_name (prod.snd <$> subst),
   return (e, d.type.instantiate_univ_params subst)

/-- `mk_local n` creates a dummy local variable with name `n`.
The type of this local constant is a constant with name `n`, so it is very unlikely to be
a meaningful expression. -/
meta def mk_local (n : name) : expr :=
expr.local_const n n binder_info.default (expr.const n [])

/-- `local_def_value e` returns the value of the expression `e`, assuming that `e` has been defined
locally using a `let` expression. Otherwise it fails. -/
meta def local_def_value (e : expr) : tactic expr :=
do (v,_) ← solve_aux `(true) (do
         (expr.elet n t v _) ← (revert e >> target)
           | fail format!"{e} is not a local definition",
         return v),
   return v

/-- `pis loc_consts f` is used to create a pi expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with pi binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``pis [a, b] `(f a b)`` will return the expression
`Π (a : Ta) (b : Tb), f a b` -/
meta def pis : list expr → expr → tactic expr
| (e@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← pis es f,
  pure $ expr.pi pp info t (expr.abstract_local f' uniq)
| _ f := pure f

/-- `lambdas loc_consts f` is used to create a lambda expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with lambda binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``lambdas [a, b] `(f a b)`` will return the expression
`λ (a : Ta) (b : Tb), f a b` -/
meta def lambdas : list expr → expr → tactic expr
| (e@(expr.local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← lambdas es f,
  pure $ expr.lam pp info t (expr.abstract_local f' uniq)
| _ f := pure f

/-- `mk_psigma [x,y,z]`, with `[x,y,z]` list of local constants of types `x : tx`,
`y : ty x` and `z : tz x y`, creates an expression of sigma type: `⟨x,y,z⟩ : Σ' (x : tx) (y : ty x), tz x y`.
 -/
meta def mk_psigma : list expr → tactic expr
| [] := mk_const ``punit
| [x@(expr.local_const _ _ _ _)] := pure x
| (x@(expr.local_const _ _ _ _) :: xs) :=
  do y ← mk_psigma xs,
     α ← infer_type x,
     β ← infer_type y,
     t ← lambdas [x] β >>= instantiate_mvars,
     r ← mk_mapp ``psigma.mk [α,t],
     pure $ r x y
| _ := fail "mk_psigma expects a list of local constants"

/-- `elim_gen_prod n e _ ns` with `e` an expression of type `psigma _`, applies `cases` on `e` `n` times
and uses `ns` to name the resulting variables. Returns a triple: list of new variables, remaining term
and unused variable names.
-/
meta def elim_gen_prod : nat → expr → list expr → list name → tactic (list expr × expr × list name)
| 0       e hs ns := return (hs.reverse, e, ns)
| (n + 1) e hs ns := do
  t ← infer_type e,
  if t.is_app_of `eq then return (hs.reverse, e, ns)
  else do
    [(_, [h, h'], _)] ← cases_core e (ns.take 1),
    elim_gen_prod n h' (h :: hs) (ns.drop 1)

private meta def elim_gen_sum_aux : nat → expr → list expr → tactic (list expr × expr)
| 0       e hs := return (hs, e)
| (n + 1) e hs := do
  [(_, [h], _), (_, [h'], _)] ← induction e [],
  swap,
  elim_gen_sum_aux n h' (h::hs)

/-- `elim_gen_sum n e` applies cases on `e` `n` times. `e` is assumed to be a local constant whose
type is a (nested) sum `⊕`. Returns the list of local constants representing the components of `e`. -/
meta def elim_gen_sum (n : nat) (e : expr) : tactic (list expr) := do
  (hs, h') ← elim_gen_sum_aux n e [],
  gs ← get_goals,
  set_goals $ (gs.take (n+1)).reverse ++ gs.drop (n+1),
  return $ hs.reverse ++ [h']

/-- Given `elab_def`, a tactic to solve the current goal,
`extract_def n trusted elab_def` will create an auxiliary definition named `n` and use it
to close the goal. If `trusted` is false, it will be a meta definition. -/
meta def extract_def (n : name) (trusted : bool) (elab_def : tactic unit) : tactic unit :=
do cxt ← list.map expr.to_implicit_local_const <$> local_context,
   t ← target,
   (eqns,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   applyc n

/-- Attempts to close the goal with `dec_trivial`. -/
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

/--
Given a tactic `tac` that takes an expression
and returns a new expression and a proof of equality,
use that tactic to change the type of the hypotheses listed in `hs`,
as well as the goal if `tgt = tt`.

Returns `tt` if any types were successfully changed.
-/
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

/-- A variant of `simplify_bottom_up`. Given a tactic `post` for rewriting subexpressions,
`simp_bottom_up post e` tries to rewrite `e` starting at the leaf nodes. Returns the resulting
expression and a proof of equality. -/
meta def simp_bottom_up' (post : expr → tactic (expr × expr)) (e : expr) (cfg : simp_config := {}) :
  tactic (expr × expr) :=
prod.snd <$> simplify_bottom_up () (λ _, (<$>) (prod.mk ()) ∘ post) e cfg

/-- Caches unary type classes on a type `α : Type.{univ}` -/
meta structure instance_cache :=
(α : expr)
(univ : level)
(inst : name_map expr)

/-- Creates an `instance_cache` for the type `α` -/
meta def mk_instance_cache (α : expr) : tactic instance_cache :=
do u ← mk_meta_univ,
   infer_type α >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   return ⟨α, u, mk_name_map⟩

namespace instance_cache

/-- If `n` is the name of a type class with one parameter, `get c n` tries to find an instance of
`n c.α` by checking the cache `c`. If there is no entry in the cache, it tries to find the instance
via type class resolution, and updates the cache. -/
meta def get (c : instance_cache) (n : name) : tactic (instance_cache × expr) :=
match c.inst.find n with
| some i := return (c, i)
| none := do e ← mk_app n [c.α] >>= mk_instance,
  return (⟨c.α, c.univ, c.inst.insert n e⟩, e)
end

open expr
/-- If `e` is a `pi` expression that binds an instance-implicit variable of type `n`,
`append_typeclasses e c l` searches `c` for an instance `p` of type `n` and returns `p :: l`. -/
meta def append_typeclasses : expr → instance_cache → list expr →
  tactic (instance_cache × list expr)
| (pi _ binder_info.inst_implicit (app (const n _) (var _)) body) c l :=
  do (c, p) ← c.get n, return (c, p :: l)
| _ c l := return (c, l)

/-- Creates the application `n c.α p l`, where `p` is a type class instance found in the cache `c`. -/
meta def mk_app (c : instance_cache) (n : name) (l : list expr) : tactic (instance_cache × expr) :=
do d ← get_decl n,
   (c, l) ← append_typeclasses d.type.binding_body c l,
   return (c, (expr.const n [c.univ]).mk_app (c.α :: l))

end instance_cache

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

/-- Auxilliary defintion for `get_pi_binders`. -/
meta def get_pi_binders_aux : list binder → expr → tactic (list binder × expr)
| es (expr.pi n bi d b) :=
  do m ← mk_fresh_name,
     let l := expr.local_const m n bi d,
     let new_b := expr.instantiate_var b l,
     get_pi_binders_aux (⟨n, bi, d⟩::es) new_b
| es e                  := return (es, e)

/-- Get the binders and target of a pi-type. Instantiates bound variables by
  local constants. Cf. `pi_binders` in `meta.expr` (which produces open terms).
  See also `mk_local_pis` in `init.core.tactic` which does almost the same. -/
meta def get_pi_binders : expr → tactic (list binder × expr) | e :=
do (es, e) ← get_pi_binders_aux [] e, return (es.reverse, e)

/-- Auxilliary definition for `get_pi_binders_dep`. -/
meta def get_pi_binders_dep_aux : ℕ → expr → tactic (list (ℕ × binder) × expr)
| n (expr.pi nm bi d b) :=
 do l ← mk_local' nm bi d,
    (ls, r) ← get_pi_binders_dep_aux (n+1) (expr.instantiate_var b l),
    return (if b.has_var then ls else (n, ⟨nm, bi, d⟩)::ls, r)
| n e                  := return ([], e)

/-- A variant of `get_pi_binders` that only returns the binders that do not occur in later
  arguments or in the target. Also returns the argument position of each returned binder. -/
meta def get_pi_binders_dep : expr → tactic (list (ℕ × binder) × expr) :=
get_pi_binders_dep_aux 0

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

/-- `var_names e` returns a list of the unique names of the initial pi bindings in `e`. -/
meta def var_names : expr → list name
| (expr.pi n _ _ b) := n :: var_names b
| _ := []

/-- When `struct_n` is the name of a structure type,
`subobject_names struct_n` returns two lists of names `(instances, fields)`.
The names in `instances` are the projections from `struct_n` to the structures that it extends
(assuming it was defined with `old_structure_cmd false`).
The names in `fields` are the standard fields of `struct_n`. -/
meta def subobject_names (struct_n : name) : tactic (list name × list name) :=
do env ← get_env,
   [c] ← pure $ env.constructors_of struct_n | fail "too many constructors",
   vs  ← var_names <$> (mk_const c >>= infer_type),
   fields ← env.structure_fields struct_n,
   return $ fields.partition (λ fn, ↑("_" ++ fn.to_string) ∈ vs)

private meta def expanded_field_list' : name → tactic (dlist $ name × name) | struct_n :=
do (so,fs) ← subobject_names struct_n,
   ts ← so.mmap (λ n, do
     (_, e) ← mk_const (n.update_prefix struct_n) >>= infer_type >>= mk_local_pis,
     expanded_field_list' $ e.get_app_fn.const_name),
   return $ dlist.join ts ++ dlist.of_list (fs.map $ prod.mk struct_n)
open functor function

/-- `expanded_field_list struct_n` produces a list of the names of the fields of the structure
named `struct_n`. These are returned as pairs of names `(prefix, name)`, where the full name
of the projection is `prefix.name`. -/
meta def expanded_field_list (struct_n : name) : tactic (list $ name × name) :=
dlist.to_list <$> expanded_field_list' struct_n

/--
Return a list of all type classes which can be instantiated
for the given expression.
-/
meta def get_classes (e : expr) : tactic (list name) :=
attribute.get_instances `class >>= list.mfilter (λ n,
  succeeds $ mk_app n [e] >>= mk_instance)

open nat

/-- Create a list of `n` fresh metavariables. -/
meta def mk_mvar_list : ℕ → tactic (list expr)
| 0 := pure []
| (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

/-- Returns the only goal, or fails if there isn't just one goal. -/
meta def get_goal : tactic expr :=
do gs ← get_goals,
   match gs with
   | [a] := return a
   | []  := fail "there are no goals"
   | _   := fail "there are too many goals"
   end

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

/-- `replace h p` elaborates the pexpr `p`, clears the existing hypothesis named `h` from the local
context, and adds a new hypothesis named `h`. The type of this hypothesis is the type of `p`.
Fails if there is nothing named `h` in the local context. -/
meta def replace (h : name) (p : pexpr) : tactic unit :=
do h' ← get_local h,
   p ← to_expr p,
   note h none p,
   clear h'

/-- Auxiliary function for `iff_mp` and `iff_mpr`. Takes a name, which should be either `` `iff.mp``
or `` `iff.mpr``. If the passed expression is an iterated function type eventually producing an
`iff`, returns an expression with the `iff` converted to either the forwards or backwards
implication, as requested. -/
meta def mk_iff_mp_app (iffmp : name) : expr → (nat → expr) → option expr
| (expr.pi n bi e t) f := expr.lam n bi e <$> mk_iff_mp_app t (λ n, f (n+1) (expr.var n))
| `(%%a ↔ %%b) f := some $ @expr.const tt iffmp [] a b (f 0)
| _ f := none

/-- `iff_mp_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., A → B` -/
meta def iff_mp_core (e ty: expr) : option expr :=
mk_iff_mp_app `iff.mp ty (λ_, e)

/-- `iff_mpr_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., B → A` -/
meta def iff_mpr_core (e ty: expr) : option expr :=
mk_iff_mp_app `iff.mpr ty (λ_, e)

/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the forward implication. -/
meta def iff_mp (e : expr) : tactic expr :=
do t ← infer_type e,
   iff_mp_core e t <|> fail "Target theorem must have the form `Π x y z, a ↔ b`"

/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the reverse implication. -/
meta def iff_mpr (e : expr) : tactic expr :=
do t ← infer_type e,
   iff_mpr_core e t <|> fail "Target theorem must have the form `Π x y z, a ↔ b`"

/--
Attempts to apply `e`, and if that fails, if `e` is an `iff`,
try applying both directions separately.
-/
meta def apply_iff (e : expr) : tactic (list (name × expr)) :=
let ap e := tactic.apply e {new_goals := new_goals.non_dep_only} in
ap e <|> (iff_mp e >>= ap) <|> (iff_mpr e >>= ap)

/-- `symm_apply e cfg` tries `apply e cfg`, and if this fails, calls `symmetry` and tries again. -/
meta def symm_apply (e : expr) (cfg : apply_cfg := {}) : tactic (list (name × expr)) :=
tactic.apply e cfg <|> (symmetry >> tactic.apply e cfg)

/-- `apply_assumption` searches for terms in the local context that can be applied to make progress
on the goal. If the goal is symmetric, it tries each goal in both directions. If this fails, it will
call `exfalso` and repeat. Optional arguments:

 * `asms` controls which expressions are applied. Defaults to `local_context`
 * `tac` is called after a successful application. Defaults to `skip` -/
meta def apply_assumption
  (asms : tactic (list expr) := local_context)
  (tac : tactic unit := skip) : tactic unit :=
do { ctx ← asms,
     ctx.any_of (λ H, symm_apply H >> tac) } <|>
do { exfalso,
     ctx ← asms,
     ctx.any_of (λ H, symm_apply H >> tac) }
<|> fail "assumption tactic failed"

/-- `change_core e none` is equivalent to `change e`. It tries to change the goal to `e` and fails
if this is not a definitional equality.

`change_core e (some h)` assumes `h` is a local constant, and tries to change the type of `h` to `e`
by reverting `h`, changing the goal, and reintroducing hypotheses. -/
meta def change_core (e : expr) : option expr → tactic unit
| none     := tactic.change e
| (some h) :=
  do num_reverted : ℕ ← revert h,
     expr.pi n bi d b ← target,
     tactic.change $ expr.pi n bi e b,
     intron num_reverted

/--
`change_with_at olde newe hyp` replaces occurences of `olde` with `newe` at hypothesis `hyp`,
assuming `olde` and `newe` are defeq when elaborated.
-/
meta def change_with_at (olde newe : pexpr) (hyp : name) : tactic unit :=
do h ← get_local hyp,
   tp ← infer_type h,
   olde ← to_expr olde, newe ← to_expr newe,
   let repl_tp := tp.replace (λ a n, if a = olde then some newe else none),
   change_core repl_tp (some h)

/-- Returns a list of all metavariables in the current partial proof. This can differ from
the list of goals, since the goals can be manually edited. -/
meta def metavariables : tactic (list expr) :=
expr.list_meta_vars <$> result

/-- Fail if the target contains a metavariable. -/
meta def no_mvars_in_target : tactic unit :=
expr.has_meta_var <$> target >>= guardb ∘ bnot

/-- Succeeds only if the current goal is a proposition. -/
meta def propositional_goal : tactic unit :=
do g :: _ ← get_goals,
   is_proof g >>= guardb

/-- Succeeds only if we can construct an instance showing the
    current goal is a subsingleton type. -/
meta def subsingleton_goal : tactic unit :=
do g :: _ ← get_goals,
   ty ← infer_type g >>= instantiate_mvars,
   to_expr ``(subsingleton %%ty) >>= mk_instance >> skip

/--
Succeeds only if the current goal is "terminal",
in the sense that no other goals depend on it
(except possibly through shared metavariables; see `independent_goal`).
-/
meta def terminal_goal : tactic unit :=
propositional_goal <|> subsingleton_goal <|>
do g₀ :: _ ← get_goals,
   mvars ← (λ L, list.erase L g₀) <$> metavariables,
   mvars.mmap' $ λ g, do
     t ← infer_type g >>= instantiate_mvars,
     d ← kdepends_on t g₀,
     monad.whenb d $
       pp t >>= λ s, fail ("The current goal is not terminal: " ++ s.to_string ++ " depends on it.")

/--
Succeeds only if the current goal is "independent", in the sense
that no other goals depend on it, even through shared meta-variables.
-/
meta def independent_goal : tactic unit :=
no_mvars_in_target >> terminal_goal

/-- `triv'` tries to close the first goal with the proof `trivial : true`. Unlike `triv`,
it only unfolds reducible definitions, so it sometimes fails faster. -/
meta def triv' : tactic unit := do c ← mk_const `trivial, exact c reducible

variable {α : Type}

private meta def iterate_aux (t : tactic α) : list α → tactic (list α)
| L := (do r ← t, iterate_aux (r :: L)) <|> return L

/-- Apply a tactic as many times as possible, collecting the results in a list. -/
meta def iterate' (t : tactic α) : tactic (list α) :=
list.reverse <$> iterate_aux t []

/-- Apply a tactic as many times as possible, collecting the results in a list.
Fail if the tactic does not succeed at least once. -/
meta def iterate1 (t : tactic α) : tactic (α × list α) :=
do r ← decorate_ex "iterate1 failed: tactic did not succeed" t,
   L ← iterate' t,
   return (r, L)

/-- Introduces one or more variables and returns the new local constants.
Fails if `intro` cannot be applied. -/
meta def intros1 : tactic (list expr) :=
iterate1 intro1 >>= λ p, return (p.1 :: p.2)

/-- `successes` invokes each tactic in turn, returning the list of successful results. -/
meta def successes (tactics : list (tactic α)) : tactic (list α) :=
list.filter_map id <$> monad.sequence (tactics.map (λ t, try_core t))

/--
Try all the tactics in a list, each time starting at the original tactic_state,
returning the list of successful results,
and reverting to the original tactic_state.
-/
-- Note this is not the same as `successes`, which keeps track of the evolving tactic_state.
meta def try_all {α : Type} (tactics : list (tactic α)) : tactic (list α) :=
λ s, result.success
(tactics.map $
λ t : tactic α,
  match t s with
  | result.success a s' := [a]
  | _ := []
  end).join s

/--
Try all the tactics in a list, each time starting at the original tactic_state,
returning the list of successful results sorted by
the value produced by a subsequent execution of the `sort_by` tactic,
and reverting to the original tactic_state.
-/
meta def try_all_sorted {α : Type} (tactics : list (tactic α)) (sort_by : tactic ℕ := num_goals) : tactic (list α) :=
λ s, result.success
(((tactics.map $
λ t : tactic α,
  match (do a ← t, n ← sort_by, return (a, n)) s with
  | result.success a s' := [a]
  | _ := []
  end).join.qsort (λ p q : α × ℕ, p.2 < q.2)).map (prod.fst)) s

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

/-- calls `cases` on every local hypothesis, succeeding if
    it succeeds on at least one hypothesis. -/
meta def case_bash : tactic unit :=
do l ← local_context,
   r ← successes (l.reverse.map (λ h, cases h >> skip)),
   when (r.empty) failed

/-- given a proof `pr : t`, adds `h : t` to the current context, where the name `h` is fresh.  -/
meta def note_anon (e : expr) : tactic expr :=
do n ← get_unused_name "lh",
   note n none e

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

/-- Changes `(h : ∀xs, ∃as, p as) ⊢ g` to a list of functions `as`, and a final hypothesis on `p as` -/
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

/--
Instantiates metavariables that appear in the current goal.
-/
meta def instantiate_mvars_in_target : tactic unit :=
target >>= instantiate_mvars >>= change

/--
Instantiates metavariables in all goals.
-/
meta def instantiate_mvars_in_goals : tactic unit :=
all_goals $ instantiate_mvars_in_target

/-- This makes sure that the execution of the tactic does not change the tactic state.
    This can be helpful while using rewrite, apply, or expr munging.
    Remember to instantiate your metavariables before you're done! -/
meta def lock_tactic_state {α} (t : tactic α) : tactic α
| s := match t s with
       | result.success a s' := result.success a s
       | result.exception msg pos s' := result.exception msg pos s
end

/-- similar to `mk_local_pis` but make meta variables instead of
    local constants -/
meta def mk_meta_pis : expr → tactic (list expr × expr)
| (expr.pi n bi d b) := do
  p ← mk_meta_var d,
  (ps, r) ← mk_meta_pis (expr.instantiate_var b p),
  return ((p :: ps), r)
| e := return ([], e)

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
     let fs := format.intercalate (",\n  " : format) $ fs.map (λ fn, format!"{fn} := _"),
     let out := format.to_string format!"{{ {fs} }",
     return [(out,"")] }

/-- Like `resolve_name` except when the list of goals is
    empty. In that situation `resolve_name` fails whereas
    `resolve_name'` simply proceeds on a dummy goal -/
meta def resolve_name' (n : name) : tactic pexpr :=
do [] ← get_goals | resolve_name n,
   g ← mk_mvar,
   set_goals [g],
   resolve_name n <* set_goals []

private meta def strip_prefix' (n : name) : list string → name → tactic name
| s name.anonymous := pure $ s.foldl (flip name.mk_string) name.anonymous
| s (name.mk_string a p) :=
  do let n' := s.foldl (flip name.mk_string) name.anonymous,
     do { n'' ← tactic.resolve_constant n',
          if n'' = n
            then pure n'
            else strip_prefix' (a :: s) p }
     <|> strip_prefix' (a :: s) p
| s n@(name.mk_numeral a p) := pure $ s.foldl (flip name.mk_string) n

/-- Strips unnecessary prefixes from a name, e.g. if a namespace is open. -/
meta def strip_prefix : name → tactic name
| n@(name.mk_string a a_1) :=
  if (`_private).is_prefix_of n
    then let n' := n.update_prefix name.anonymous in
            n' <$ resolve_name' n' <|> pure n
    else strip_prefix' n [a] a_1
| n := pure n

/-- Used to format return strings for the hole commands `match_stub` and `eqn_stub`. -/
meta def mk_patterns (t : expr) : tactic (list format) :=
do let cl := t.get_app_fn.const_name,
   env ← get_env,
   let fs := env.constructors_of cl,
   fs.mmap $ λ f,
     do { (vs,_) ← mk_const f >>= infer_type >>= mk_local_pis,
          let vs := vs.filter (λ v, v.is_default_local),
          vs ← vs.mmap (λ v,
            do v' ← get_unused_name v.local_pp_name,
               pose v' none `(()),
               pure v' ),
          vs.mmap' $ λ v, get_local v >>= clear,
          let args := list.intersperse (" " : format) $ vs.map to_fmt,
          f ← strip_prefix f,
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
            c ← strip_prefix c,
            pure format!"\n{c} : {t}\n" },
     fs ← format.intercalate ", " <$> cs.mmap (strip_prefix >=> pure ∘ to_fmt),
     let out := format.to_string format!"{{! {fs} !}",
     trace (format.join ts).to_string,
     return [(out,"")] }

/-- Makes the declaration `classical.prop_decidable` available to type class inference.
This asserts that all propositions are decidable, but does not have computational content. -/
meta def classical : tactic unit :=
do h ← get_unused_name `_inst,
   mk_const `classical.prop_decidable >>= note h none,
   reset_instance_cache

open expr

/-- `mk_comp v e` checks whether `e` is a sequence of nested applications `f (g (h v))`, and if so,
returns the expression `f ∘ g ∘ h`. -/
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

/--
From a lemma of the shape `∀ x, f (g x) = h x`
derive an auxiliary lemma of the form `f ∘ g = h`
for reasoning about higher-order functions.
-/
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

/-- A user attribute that applies to lemmas of the shape `∀ x, f (g x) = h x`.
It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.-/
@[user_attribute]
meta def higher_order_attr : user_attribute unit (option name) :=
{ name := `higher_order,
  parser := optional ident,
  descr :=
"From a lemma of the shape `∀ x, f (g x) = h x` derive an auxiliary lemma of the
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
       lmm' ← (flip name.update_prefix lmm.get_prefix <$> lmm') <|> pure lmm.add_prime,
       add_decl $ declaration.thm lmm' lvls t' (pure pr),
       copy_attribute `simp lmm tt lmm',
       copy_attribute `functor_norm lmm tt lmm' }

attribute [higher_order map_comp_pure] map_pure

/--
Use `refine` to partially discharge the goal,
or call `fconstructor` and try again.
-/
private meta def use_aux (h : pexpr) : tactic unit :=
(focus1 (refine h >> done)) <|> (fconstructor >> use_aux)

/-- Similar to `existsi`, `use l` will use entries in `l` to instantiate existential obligations
at the beginning of a target. Unlike `existsi`, the pexprs in `l` are elaborated with respect to
the expected type.

```
example : ∃ x : ℤ, x = x :=
by tactic.use ``(42)
```

See the doc string for `tactic.interactive.use` for more information.
 -/
protected meta def use (l : list pexpr) : tactic unit :=
focus1 $ seq (l.mmap' $ λ h, use_aux h <|> fail format!"failed to instantiate goal with {h}")
              instantiate_mvars_in_target

/-- `clear_aux_decl_aux l` clears all expressions in `l` that represent aux decls from the
local context. -/
meta def clear_aux_decl_aux : list expr → tactic unit
| []     := skip
| (e::l) := do cond e.is_aux_decl (tactic.clear e) skip, clear_aux_decl_aux l

/-- `clear_aux_decl` clears all expressions from the local context that represent aux decls. -/
meta def clear_aux_decl : tactic unit :=
local_context >>= clear_aux_decl_aux

/-- `apply_at_aux e et [] h ht` (with `et` the type of `e` and `ht` the type of `h`)
    finds a list of expressions `vs` and returns (e.mk_args (vs ++ [h]), vs) -/
meta def apply_at_aux (arg t : expr) : list expr → expr → expr → tactic (expr × list expr)
| vs e (pi n bi d b) :=
  do { v ← mk_meta_var d,
       apply_at_aux (v :: vs) (e v) (b.instantiate_var v) } <|>
  (e arg, vs) <$ unify d t
| vs e _ := failed

/-- `apply_at e h` applies implication `e` on hypothesis `h` and replaces `h` with the result -/
meta def apply_at (e h : expr) : tactic unit :=
do ht ← infer_type h,
   et ← infer_type e,
   (h', gs') ← apply_at_aux h ht [] e et,
   note h.local_pp_name none h',
   clear h,
   gs' ← gs'.mfilter is_assigned,
   (g :: gs) ← get_goals,
   set_goals (g :: gs' ++ gs)

/-- `symmetry_hyp h` applies symmetry on hypothesis `h` -/
meta def symmetry_hyp (h : expr) (md := semireducible) : tactic unit :=
do tgt   ← infer_type h,
   env   ← get_env,
   let r := get_app_fn tgt,
   match env.symm_for (const_name r) with
   | (some symm) := do s ← mk_const symm,
                       apply_at s h
   | none        := fail "symmetry tactic failed, target is not a relation application with the expected property."
   end

precedence `setup_tactic_parser`:0

/-- `setup_tactic_parser_cmd` is a user command that opens the namespaces used in writing
interactive tactics, and declares the local postfix notation `?` for `optional` and `*` for `many`.
It does *not* use the `namespace` command, so it will typically be used after
`namespace tactic.interactive`.
-/
@[user_command]
meta def setup_tactic_parser_cmd (_ : interactive.parse $ tk "setup_tactic_parser") : lean.parser unit :=
emit_code_here "
open lean
open lean.parser
open interactive interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many .
"

/-- `trace_error msg t` executes the tactic `t`. If `t` fails, traces `msg` and the failure message
of `t`. -/
meta def trace_error (msg : string) (t : tactic α) : tactic α
| s := match t s with
       | (result.success r s') := result.success r s'
       | (result.exception (some msg') p s') := (trace msg >> trace (msg' ()) >> result.exception (some msg') p) s'
       | (result.exception none p s') := result.exception none p s'
       end

/--
This combinator is for testing purposes. It succeeds if `t` fails with message `msg`,
and fails otherwise.
-/
meta def {u} success_if_fail_with_msg {α : Type u} (t : tactic α) (msg : string) : tactic unit :=
λ s, match t s with
| (interaction_monad.result.exception msg' _ s') :=
  let expected_msg := (msg'.iget ()).to_string in
  if msg = expected_msg then result.success () s
  else mk_exception format!"failure messages didn't match. Expected:\n{expected_msg}" none s
| (interaction_monad.result.success a s) :=
   mk_exception "success_if_fail_with_msg combinator failed, given tactic succeeded" none s
end

open lean interactive

/-- A type alias for `tactic format`, standing for "pretty print format". -/
meta def pformat := tactic format

/-- `mk` lifts `fmt : format` to the tactic monad (`pformat`). -/
meta def pformat.mk (fmt : format) : pformat := pure fmt

/-- an alias for `pp`. -/
meta def to_pfmt {α} [has_to_tactic_format α] (x : α) : pformat :=
pp x

meta instance pformat.has_to_tactic_format : has_to_tactic_format pformat :=
⟨ id ⟩

meta instance : has_append pformat :=
⟨ λ x y, (++) <$> x <*> y ⟩

meta instance tactic.has_to_tactic_format [has_to_tactic_format α] : has_to_tactic_format (tactic α) :=
⟨ λ x, x >>= to_pfmt ⟩

private meta def parse_pformat : string → list char → parser pexpr
| acc []            := pure ``(to_pfmt %%(reflect acc))
| acc ('\n'::s)     :=
do f ← parse_pformat "" s,
   pure ``(to_pfmt %%(reflect acc) ++ pformat.mk format.line ++ %%f)
| acc ('{'::'{'::s) := parse_pformat (acc ++ "{") s
| acc ('{'::s) :=
do (e, s) ← with_input (lean.parser.pexpr 0) s.as_string,
   '}'::s ← return s.to_list | fail "'}' expected",
   f ← parse_pformat "" s,
   pure ``(to_pfmt %%(reflect acc) ++ to_pfmt %%e ++ %%f)
| acc (c::s) := parse_pformat (acc.str c) s

reserve prefix `pformat! `:100

/-- See `format!` in `init/meta/interactive_base.lean`.

The main differences are that `pp` is called instead of `to_fmt` and that we can use
arguments of type `tactic α` in the quotations.

Now, consider the following:
```
e ← to_expr ``(3 + 7),
trace format!"{e}"  -- outputs `has_add.add.{0} nat nat.has_add (bit1.{0} nat nat.has_one nat.has_add (has_one.one.{0} nat nat.has_one)) ...`
trace pformat!"{e}" -- outputs `3 + 7`
```

The difference is significant. And now, the following is expressible:

```
e ← to_expr ``(3 + 7),
trace pformat!"{e} : {infer_type e}" -- outputs `3 + 7 : ℕ`
```

See also: `trace!` and `fail!`
-/
@[user_notation]
meta def pformat_macro (_ : parse $ tk "pformat!") (s : string) : parser pexpr :=
do e ← parse_pformat "" s.to_list,
   return ``(%%e : pformat)

reserve prefix `fail! `:100

/--
the combination of `pformat` and `fail`
-/
@[user_notation]
meta def fail_macro (_ : parse $ tk "fail!") (s : string) : parser pexpr :=
do e ← pformat_macro () s,
   pure ``((%%e : pformat) >>= fail)

reserve prefix `trace! `:100
/--
the combination of `pformat` and `fail`
-/
@[user_notation]
meta def trace_macro (_ : parse $ tk "trace!") (s : string) : parser pexpr :=
do e ← pformat_macro () s,
   pure ``((%%e : pformat) >>= trace)

/-- A hackish way to get the `src` directory of mathlib. -/
meta def get_mathlib_dir : tactic string :=
do e ← get_env,
  s ← e.decl_olean `tactic.reset_instance_cache,
  return $ s.popn_back 17

/-- Checks whether a declaration with the given name is declared in mathlib.
  If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
  since it is expensive to execute `get_mathlib_dir` many times. -/
meta def is_in_mathlib (n : name) : tactic bool :=
do ml ← get_mathlib_dir, e ← get_env, return $ e.is_prefix_of_file ml n

/-- auxiliary function for apply_under_pis -/
private meta def apply_under_pis_aux (func arg : pexpr) : ℕ → expr → pexpr
| n (expr.pi nm bi tp bd) := expr.pi nm bi (pexpr.of_expr tp) (apply_under_pis_aux (n+1) bd)
| n _ :=
  let vars := ((list.range n).reverse.map (@expr.var ff)),
      bd := vars.foldl expr.app arg.mk_explicit in
  func bd

/--
Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
meta def apply_under_pis (func arg : pexpr) (pi_expr : expr) : pexpr :=
apply_under_pis_aux func arg 0 pi_expr

/--
Tries to derive instances by unfolding the newly introduced type and applying type class resolution.

For example,
```
@[derive ring] def new_int : Type := ℤ
```
adds an instance `ring new_int`, defined to be the instance of `ring ℤ` found by `apply_instance`.

Multiple instances can be added with `@[derive [ring, module ℝ]]`.

This derive handler applies only to declarations made using `def`, and will fail on such a
declaration if it is unable to derive an instance. It is run with higher priority than the built-in
handlers, which will fail on `def`s.
-/
@[derive_handler, priority 2000] meta def delta_instance : derive_handler :=
λ cls new_decl_name,
do env ← get_env,
if env.is_inductive new_decl_name then return ff else
do new_decl_type ← declaration.type <$> get_decl new_decl_name,
   new_decl_pexpr ← resolve_name new_decl_name,
   tgt ← to_expr $ apply_under_pis cls new_decl_pexpr new_decl_type,
   (_, inst) ← solve_aux tgt
     (intros >> reset_instance_cache >> delta_target [new_decl_name]  >> apply_instance >> done),
   inst ← instantiate_mvars inst,
   tgt ← instantiate_mvars tgt,
   nm ← get_unused_decl_name $ new_decl_name ++
     match cls with
     -- the postfix is needed because we can't protect this name. using nm.last directly can
     -- conflict with open namespaces
     | (expr.const nm _) := (nm.last ++ "_1" : string)
     | _ := "inst"
     end,
   add_decl $ mk_definition nm inst.collect_univ_params tgt inst,
   set_basic_attribute `instance nm tt,
   return tt

/-- `find_private_decl n none` finds a private declaration named `n` in any of the imported files.

`find_private_decl n (some m)` finds a private declaration named `n` in the same file where a declaration named `m`
can be found.  -/
meta def find_private_decl (n : name) (fr : option name) : tactic name :=
do env ← get_env,
   fn ← option_t.run (do
         fr ← option_t.mk (return fr),
         d ← monad_lift $ get_decl fr,
         option_t.mk (return $ env.decl_olean d.to_name) ),
   let p : string → bool :=
     match fn with
     | (some fn) := λ x, fn = x
     | none := λ _, tt
     end,
   let xs := env.decl_filter_map (λ d,
     do fn ← env.decl_olean d.to_name,
        guard ((`_private).is_prefix_of d.to_name ∧ p fn ∧ d.to_name.update_prefix name.anonymous = n),
        pure d.to_name),
   match xs with
   | [n] := pure n
   | [] := fail "no such private found"
   | _ := fail "many matches found"
   end

open lean.parser interactive

/-- `import_private foo from bar` finds a private declaration `foo` in the same file as `bar`
    and creates a local notation to refer to it.

    `import_private foo` looks for `foo` in all imported files. -/
@[user_command]
meta def import_private_cmd (_ : parse $ tk "import_private") : lean.parser unit :=
do n  ← ident,
   fr ← optional (tk "from" *> ident),
   n ← find_private_decl n fr,
   c ← resolve_constant n,
   d ← get_decl n,
   let c := @expr.const tt c d.univ_levels,
   new_n ← new_aux_decl_name,
   add_decl $ declaration.defn new_n d.univ_params d.type c reducibility_hints.abbrev d.is_trusted,
   let new_not := sformat!"local notation `{n.update_prefix name.anonymous}` := {new_n}",
   emit_command_here $ new_not,
   skip .

/--
The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.
-/
@[user_command]
meta def mk_simp_attribute_cmd (_ : parse $ tk "mk_simp_attribute") : lean.parser unit :=
do n ← ident,
   d ← parser.pexpr,
   d ← to_expr ``(%%d : option string),
   descr ← eval_expr (option string) d,
   with_list ← types.with_ident_list <|> return [],
   mk_simp_attr n with_list,
   add_doc_string (name.append `simp_attr n) $ descr.get_or_else $ "simp set for " ++ to_string n

end tactic
