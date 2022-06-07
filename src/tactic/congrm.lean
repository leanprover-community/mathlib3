/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Damiano Testa
-/
import tactic.interactive

/-!  `congrm`: `congr` with pattern-matching -/

namespace tactic

def congrm_fun0 {α} {a : α} : α := a
notation `_₀` := congrm_fun0

def congrm_fun1 {α β} {b : β} : α → β := λ a, b
notation `_₁` := congrm_fun1

def congrm_fun2 {α β γ} {c : γ} : α → β → γ := λ a b, c
notation `_₂` := congrm_fun2

def congrm_fun3 {α β γ δ} {d : δ} : α → β → γ → δ := λ a b c, d
notation `_₃` := congrm_fun3

def congrm_fun4 {α β γ δ ε} {e : ε} : α → β → γ → δ → ε := λ a b c d, e
notation `_₄` := congrm_fun4

meta def test_under_nat (e : expr) : bool × ℕ :=
if e.get_app_fn.const_name = ``tactic.congrm_fun4 then (true, 4) else
if e.get_app_fn.const_name = ``tactic.congrm_fun3 then (true, 3) else
if e.get_app_fn.const_name = ``tactic.congrm_fun2 then (true, 2) else
if e.get_app_fn.const_name = ``tactic.congrm_fun1 then (true, 1) else
if e.get_app_fn.const_name = ``tactic.congrm_fun0 then (true, 0) else
  (false, 0)

meta def test_under (e : expr) : bool :=
  e.get_app_fn.const_name = ``tactic.congrm_fun4 ∨
  e.get_app_fn.const_name = ``tactic.congrm_fun3 ∨
  e.get_app_fn.const_name = ``tactic.congrm_fun2 ∨
  e.get_app_fn.const_name = ``tactic.congrm_fun1 ∨
  e.get_app_fn.const_name = ``tactic.congrm_fun0

/--
For each element of `list congr_arg_kind` that is `eq`, add a pair `(g, pat)` to the
final list.  Otherwise, discard an appropriate number of initial terms from each list
(possibly none from the first) and repeat.

`pat` is the given pattern-piece at the appropriate location, extracted from the last `list expr`.
It appears to be the list of arguments of a function application.

`g` is possibly the proof of an equality?  It is extracted from the first `list expr`.
-/
private meta def extract_subgoals : list expr → list congr_arg_kind → list expr →
  tactic (list (expr × expr))
| (_ :: _ :: g :: prf_args) (congr_arg_kind.eq :: kinds)             (pat :: pat_args) :=
  do --let cond := test_under pat,
     --trace $ cond,
     --trace sformat!"pat\n  {pat}",
     ----    trace sformat!"g is \n  {g}",
     --if cond then extract_subgoals prf_args kinds pat_args else
  (λ rest, (g, pat) :: rest) <$> extract_subgoals prf_args kinds pat_args
| (_ :: prf_args)           (congr_arg_kind.fixed :: kinds)          (_ :: pat_args) :=
  extract_subgoals prf_args kinds pat_args
| prf_args                  (congr_arg_kind.fixed_no_param :: kinds) (_ :: pat_args) :=
  extract_subgoals prf_args kinds pat_args
| (_ :: _ :: prf_args)      (congr_arg_kind.cast :: kinds)           (_ :: pat_args) :=
  extract_subgoals prf_args kinds pat_args
| _ _ [] := pure []
| cl ck pat := trace cl >> trace ck >> trace pat >> fail "unsupported congr lemma"

/-
meta def replace_explicit_args : expr → list expr → tactic expr
| e@(expr.app f e1)                       ll := do
  trace sformat!"app f\n {f}\napp e1\n {e1}",
  replace_explicit_args f ll
| (expr.lam f bi e1 e2)            ll := do
  trace sformat!"siamo passati {f}",
  return e1
| e _ := do trace "here we are", trace e, fail "not an app"

meta def replace_explicit_args_1 : expr → list expr → tactic expr
| e [] := trace "nothing" >> return e
| e (a::as) := do --trace e,
  match e with
  | `(expr.app %%f %%e1)                       := trace sformat!"siamo passati {f}" >> return e
  | `(expr.lam %%f %%bi %%e1 %%e2)             := trace sformat!"siamo passati {f}" >> return e
  | `(expr.pi %%f %%bi %%e1 %%e2)              := trace sformat!"siamo passati {f}" >> return e
  | `(expr.local_const %%f %%g %%bi %%e1 %%e2) := trace sformat!"siamo passati {f}" >> return e
  | `(expr.const %%f %%e1)                     := trace sformat!"siamo passati {f}" >> return e
  | `(expr.elet %%f %%e1 %%e2 %%e3)            := trace sformat!"siamo passati {f}" >> return e
  | _ := do trace "here we are", trace e, fail "not a function or an app"
  end
-/
#check expr.get_app_fn
meta def reinterpret_underscore_aux_new : expr → expr → tactic expr
| e1@(expr.app pat e) f1@(expr.app lhs f) := do
  trace "  * all",trace sformat!"{e1} ++ and ++ {f1}",trace "  * part",trace pat,trace lhs,
  npat ← reinterpret_underscore_aux_new pat lhs,
  com ← to_expr ``((λ x, %%npat %%f)),
  return com
| _ lhs := return lhs

meta def myconv4 (pat : expr) : expr → tactic expr
| (expr.app (expr.app (expr.app (expr.app mr ma) mb) mc) md) := do
  ta ← infer_type ma,
  tb ← infer_type mb,
  tc ← infer_type mc,
  td ← infer_type md,
  att ← to_expr ``((λ (x : %%ta) (y : %%tb) (z : %%tc) (w : %%td), %%mr x y z w)) tt ff,
  return $ att.app_of_list (pat.get_app_args.drop 6)
| _ := fail "not a trible application"

meta def myconv3 (pat : expr) : expr → tactic expr
| (expr.app (expr.app (expr.app mr ma) mb) mc) := do
  ta ← infer_type ma,
  tb ← infer_type mb,
  tc ← infer_type mc,
  att ← to_expr ``((λ (x : %%ta) (y : %%tb) (z : %%tc), %%mr x y z)) tt ff,
  return $ att.app_of_list (pat.get_app_args.drop 5)
| _ := fail "not a trible application"

meta def myconv2 (pat : expr) : expr → tactic expr
| (expr.app (expr.app mr ma) mb) := do
  ta ← infer_type ma,
  tb ← infer_type mb,
  att ← to_expr ``((λ (x : %%ta) (y : %%tb), %%mr x y)) tt ff,
  return $ att.app_of_list (pat.get_app_args.drop 4)
| _ := fail "not a double application"

meta def myconv1 (pat : expr) : expr → tactic expr
| (expr.app mr ma) := do
  ta ← infer_type ma,
  att ← to_expr ``((λ (x : %%ta), %%mr x)) tt ff,
  return $ att.app_of_list (pat.get_app_args.drop 3)
| _ := fail "not a double application"

meta def reinterpret_underscore_aux_aux : ℕ → expr → expr → tactic (expr × expr)
| 0 pat lhs := do typ ← infer_type lhs,return (typ, lhs)
| (n+1) pat lhs := do
  (typ,prev) ← reinterpret_underscore_aux_aux (n - 1) pat lhs,
  --typ ← infer_type prev,trace typ,
  att ← to_expr ``((λ x : %%typ, %%prev.get_app_fn x)),
  ntyp ← infer_type att,
  return $ (ntyp, att.app_of_list $ pat.get_app_args.drop 1)

def nov : ℕ → ℕ
| 0 := 2
| 1 := 2
| 2 := 3
| 3 := 3
| 4 := 4
| 5 := 4
| _ := 5

meta def as_lambda : expr → tactic expr
| (expr.app f e) := do exv ← as_lambda f, typ ← infer_type e,
  att ← to_expr ``((λ x : %%typ, %%exv)), return att
| e := return e

meta def list_explicit : expr → tactic (list expr)
| (expr.app f e) := do exv ← list_explicit f, return $ exv ++ [e]
| _ := fail "not a app"


meta def reinterpret_underscore_aux : ℕ → expr → expr → tactic expr
| 0 pat lhs := return lhs
--| 1 pat lhs := return lhs
--| 1 pat lhs := return lhs
| (n+1) pat lhs := do --trace "sono n",trace n,trace "per", trace lhs,
--  list_explicit lhs >>= trace,
  prev ← reinterpret_underscore_aux (n-2) pat lhs,
  trace "aslambda",trace $ as_lambda lhs,
  trace "  ** lhs app args **",trace lhs.get_app_args,
--  match lhs with
--  | (λ x, ff) := do trace "is lambda",failed
  let lhs1 := lhs.get_app_args.head, trace "head", trace lhs1,
  typ ← infer_type lhs1,trace typ,
--  typ ← infer_type $ lhs.ith_arg 0,trace typ,
--  let drarg := pat.get_app_args.drop (n / 2 + 2),

--  trace "dropped args",trace drarg,
--  (_::tys :: _ ) ← drarg.mmap infer_type,
--  match lhs with
--  | (expr.app fl al) := do
    att ← to_expr ``((λ x : %%typ, %%prev.get_app_fn x)),
    --trace "nov",trace $nov n,
    trace att,
    --trace "n again", trace n,
    return $ att.app_of_list $ pat.get_app_args.drop (n / 2 + 2)
--  | _ := fail "sorry"
--  end

meta def reinterpret_underscore_aux_one_typ (type : expr) : ℕ → expr → expr → tactic expr
| 0 pat lhs := return lhs
--| 1 pat lhs := return lhs
| (n+1) pat lhs := do
  prev ← reinterpret_underscore_aux_one_typ (n - 2) pat lhs,
  att ← to_expr ``((λ x : %%type, %%prev.get_app_fn x)) tt ff,
  return $ att.app_of_list $ pat.get_app_args.drop 3

/-
meta def reinterpret_underscore (pat lhs type : expr) : tactic expr :=
match pat.get_app_num_args with
| 2 := do att ← to_expr ``((λ x : %%type, %%lhs.get_app_fn x)),
  return $ att.app_of_list $ pat.get_app_args.drop 1
| 3 := do att ← to_expr ``((λ x y : %%type, %%lhs.get_app_fn x y)),
  return $ att.app_of_list $ pat.get_app_args.drop 1
| _ := fail "number of arguments not implemented.\nSee the comments to
  `tactic.reinterpret_underscore` for instructions on how to implement this."
end
-/

/--
`equate_with_pattern_core pat` solves a single goal of the form `lhs = rhs`
(assuming that `lhs` and `rhs` are unifiable with `pat`)
by applying congruence lemmas until `pat` is a metavariable.
Returns the list of metavariables for the new subgoals at the leafs.
Calls `set_goals []` at the end.
-/
meta def equate_with_pattern_core : expr → tactic (list expr) | pat :=
(applyc ``subsingleton.elim >> pure []) <|>
(applyc ``rfl >> pure []) <|>
if pat.is_mvar || pat.get_delayed_abstraction_locals.is_some then do
  try $ applyc ``_root_.propext,
  get_goals <* set_goals []
else if pat.is_app then do
  `(%%lhs = %%rhs) ← target,
  let (cond, na) := test_under_nat pat,
  --typ ← infer_type lhs,
  --trace pat,trace pat.get_app_num_args,trace pat.get_app_args,trace $ pat.get_app_args.drop 3,
  --pat.get_app_args.mmap infer_type >>= trace,
--  trace "aux",
--  trace $ reinterpret_underscore_aux typ pat.get_app_num_args pat lhs,
--  trace "current",
--  trace $ infer_type lhs >>= reinterpret_underscore pat lhs,
  pat ← if cond then
    if na = 1 then myconv1 pat lhs else
    if na = 2 then myconv2 pat lhs else
    if na = 3 then myconv3 pat lhs else
    if na = 4 then myconv4 pat lhs else
    fail "not yet"
    -- myc ← myconv lhs,trace "myc",trace myc,(pat.get_app_args).mmap infer_type >>= trace,
    --  return $ myc.app_of_list (pat.get_app_args.drop 4)
--    do res ← reinterpret_underscore_aux pat.get_app_num_args pat lhs,trace res,
    --do res ← reinterpret_underscore_aux pat.get_app_num_args pat lhs,trace res,
--    do res ← reinterpret_underscore_aux_new pat lhs,trace res,
--    unify res lhs <|> fail "no unification",
--    return res
    --trace $ reinterpret_underscore_aux typ pat.get_app_num_args pat lhs,
--    infer_type lhs >>= reinterpret_underscore pat lhs
  else return pat,
  cl ← mk_specialized_congr_lemma pat,
  H_congr_lemma ← assertv `H_congr_lemma cl.type cl.proof,
  [prf] ← get_goals,
  apply H_congr_lemma <|> fail "could not apply congr_lemma",
  all_goals' $ try $ clear H_congr_lemma,  -- given the `set_goals []` that follows, is this needed?
  prf ← instantiate_mvars prf,
  subgoals ← extract_subgoals prf.get_app_args cl.arg_kinds pat.get_app_args,
  subgoals ← subgoals.mmap (λ ⟨subgoal, subpat⟩, do
    set_goals [subgoal],
    equate_with_pattern_core subpat),
  pure subgoals.join
else if pat.is_lambda then do
  applyc ``_root_.funext,
  x ← intro pat.binding_name,
  equate_with_pattern_core $ pat.lambda_body.instantiate_var x
else if pat.is_pi then do
  applyc ``_root_.pi_congr,
  x ← intro pat.binding_name,
  equate_with_pattern_core $ pat.pi_codomain.instantiate_var x
else do
  infer_type pat >>= trace,
  pat ← pp pat,
  fail $ to_fmt "unsupported pattern:\n" ++ pat

/-  maybe works!!
meta def equate_with_pattern_core : expr → tactic (list expr) | pat :=
(applyc ``subsingleton.elim >> pure []) <|>
(applyc ``rfl >> pure []) <|>
if pat.is_mvar || pat.get_delayed_abstraction_locals.is_some then do
  try $ applyc ``_root_.propext,
  get_goals <* set_goals []
else if pat.is_app then do
  `(%%lhs = %%rhs) ← target,
--  body
  let bol := lhs.is_app,
--  `(expr.app %%fl %%_) ← lhs,
  let fl := lhs.app_fn,
  let fgetl := lhs.get_app_fn,
  let pargs := pat.get_app_args,
  let mfun := fgetl.const_name,
--  trace bol,
--  trace sformat!"lhs {lhs}\npat {pat}",
--  trace sformat!"fl = {fl}",
--  trace sformat!"fgetl = {fgetl}",
--  trace sformat!"pat.get_app_args = {pargs}",
--  trace sformat!"lhs.get_app_args = {lhs.get_app_args}",
--  trace sformat!"{mfun}",
--  trace sformat!"fgetl {fgetl} and its arguments {fgetl.get_app_args}",
--  --r ← get_local mfun,trace r,
--  trace sformat!"infer type lhs : ",
--  infer_type lhs >>= trace,
--  trace lhs.is_app,
--  infer_type fl >>= trace,
--  trace fl.is_app,
--  let fll := fl.get_app_fn,
--  trace sformat!"lhs: {lhs}\nfl: {fl}\nfll: {fll}\nfgetl: {fgetl}",
--  trace sformat!"lhs args: {lhs.get_app_args}\nfl args: {fl.get_app_args}\nfll args: {fll.get_app_args}\nfgetl args: {fgetl.get_app_args}",
--  trace pat.is_app,
--  trace pat.get_app_fn,
--  trace pargs,

--  let rname := fll.local_uniq_name,trace rname,
--  let rlhs := expr.mk_app fgetl pat.get_app_args,
--  trace sformat!"lhs rifatta:\n{rlhs}",
--  trace sformat!"fl:\n{fl}",
--  trace sformat!"lhs:\n{lhs}",
--  exarg ← replace_explicit_args lhs pargs,
--  trace sformat!"explicit args: {exarg}",
--  pats ← mk_app mfun pargs,
--  trace "passato",
  let cond := test_under pat,
  --trace pat.to_string,
--  trace "pat.is_app",trace pat.is_app,
--  trace "lhs.is_app",trace lhs.is_app,
--  trace $ replace_explicit_args pat [],
--  trace $ replace_explicit_args lhs.app_fn.app_fn lhs.get_app_args,
  trace "pattern, condizione e lhs:", trace pat,trace cond,trace lhs,
  trace "pat args", trace pat.get_app_args,
  trace "lhs args", trace lhs.get_app_args,
  let pa1 := pat.get_app_args.nth 1,
  let pas := pat.get_app_args,
  let mex := apply_list fgetl pas,
  et ← infer_type lhs,
--  trace "   `vecchio` pat", trace pat,
  reit ← reinterpret_underscore pat et lhs,
  let pat := if cond then reit else pat,
--  match pat.get_app_args with
--  | (p1:: p2) := do
--    trace "***proviamo***",
--    mex ← to_expr ``(%%fgetl %%p1 %%p2),
--    trace "mex", trace mex,
--    fail "ci siamo"
----  | [] := failed
--  | _ := fail "oy" --fail "not two arguments"
--  end,
--  trace $ ``(%%fgetl %%pa1),
--  let pat := if test_under pat then expr.mk_app fgetl (pat.get_app_args.drop 1) else pat,
--  let pat := if cond then expr.mk_app fgetl (pat.get_app_args.remove_nth 1) else pat,
  trace "   `nuovo` pat", trace pat,
  trace "   `lhs`", trace lhs,
--  trace "lhs" >> trace lhs,
  cl ← mk_specialized_congr_lemma pat,trace cl.type,
  H_congr_lemma ← assertv `H_congr_lemma cl.type cl.proof,
  [prf] ← get_goals,
  apply H_congr_lemma <|> fail "could not apply congr_lemma",
  all_goals' $ try $ clear H_congr_lemma,  -- given the `set_goals []` that follows, is this needed?
  prf ← instantiate_mvars prf,
  --trace "new proof:" >> trace prf,trace "new proof args:" >> trace prf.get_app_args,
  --trace "new pat args:" >> trace pat.get_app_args,
  --let parg := if cond then pat.get_app_args.drop 1 else pat.get_app_args,trace "parg" >> trace parg,
/-
  trace sformat!"this match?\n {prf}",
  trace sformat!"this match succeeds\n {prf}",
  trace "this match succeeds",
--    trace $ cond,
--    trace sformat!"pat\n  {pat}",
     --    trace sformat!"g is \n  {g}",
    if cond then do
    trace "here?",
      lili ← pat.get_app_args.mmap equate_with_pattern_core,
    trace "there?",
      let jo := lili.join,

      return jo
    else do
-/
--  set_goals [],
  --subgoals ← extract_subgoals prf.get_app_args cl.arg_kinds parg,
  --trace subgoals,
  subgoals ← extract_subgoals prf.get_app_args cl.arg_kinds pat.get_app_args,trace subgoals,
  subgoals ← subgoals.mmap (λ ⟨subgoal, subpat⟩, do
    set_goals [subgoal],
    equate_with_pattern_core subpat),
  pure subgoals.join
else if pat.is_lambda then do
  applyc ``_root_.funext,
  x ← intro pat.binding_name,
  equate_with_pattern_core $ pat.lambda_body.instantiate_var x
else if pat.is_pi then do
  applyc ``_root_.pi_congr,
  x ← intro pat.binding_name,
  equate_with_pattern_core $ pat.pi_codomain.instantiate_var x
else do --return []
  infer_type pat >>= trace,
  pat ← pp pat,
  fail $ to_fmt "unsupported pattern:\n" ++ pat
-/

/--
`equate_with_pattern pat` solves a single goal of the form `lhs = rhs`
(assuming that `lhs` and `rhs` are unifiable with `pat`)
by applying congruence lemmas until `pat` is a metavariable.
The subgoals for the leafs are prepended to the goals.
--/
meta def equate_with_pattern (pat : expr) : tactic unit := do
congr_subgoals ← solve1 (equate_with_pattern_core pat),
gs ← get_goals,
set_goals $ congr_subgoals ++ gs

end tactic

namespace tactic.interactive
open tactic interactive
setup_tactic_parser

/--
`congrm e` assumes that the goal is of the form `lhs = rhs` or `lhs ↔ rhs`.
`congrm e` scans `e, lhs, rhs` in parallel.
Assuming that the three expressions are successions of function applications, `congrm e`
uses `e` as a pattern to decide what to do in corresponding places of `lhs` and `rhs`.

If `e` has a meta-variable in a location, then the tactic produces a side-goal with
the equality of the corresponding locations in `lhs, rhs`.

If `e` is a function application, it applies the automatically generateed congruence lemma
(like `tactic.congr`).

If `e` is a lambda abstraction, it applies `funext`.  If `e` is a pi, it applies `pi_congr`.

Subexpressions that are defeq or whose type is a subsingleton are skipped.

```
example {a b : ℕ} (h : a = b) : (λ y : ℕ, ∀ z, a + a = z) = (λ x, ∀ z, b + a = z) :=
begin
  congrm λ x, ∀ w, _ + a = w,
  -- produces one goal for the underscore: ⊢ a = b
  exact h,
end
```
-/
meta def congrm (arg : parse texpr) : tactic unit := do
try $ applyc ``_root_.eq.to_iff,
`(@eq %%ty _ _) ← target | fail "congrm: goal must be an equality or iff",
ta ← to_expr ``((%%arg : %%ty)) tt ff,
pp_ta ← pp ta,
--trace "is this the unification?",
--trace sformat!"after unification\n{pp_ta}",
equate_with_pattern ta

/--  Scans three `expr`s `e, lhs, rhs` in parallel.
Currently, `equate_with_pattern_1` has three behaviours at each location:
produce a goal, recurse, or skip.

See the doc-string for `tactic.interactive.congrm_1` for more details.
-/
meta def equate_with_pattern_1 : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  match e with
  | (expr.mvar _ _ _) := do
    el ← mk_app `eq [e0, e1],
    n ← get_unused_name "h",
    assert n el,
    rotate,
    get_local n >>= rewrite_target,
    equate_with_pattern_1 f f0 f1
  | _ := do equate_with_pattern_1 e e0 e1 *> equate_with_pattern_1 f f0 f1
  end
| _ _ _ := skip

/--  `congrm_1 e` assumes that the goal is of the form `lhs = rhs`.
`congrm_1 e` scans `e, lhs, rhs` in parallel.
Assuming that the three expressions are successions of function applications, `congrm_1 e`
uses `e` as a pattern to decide what to do in corresponding places of `lhs` and `rhs`.

If `e` has a meta-variable in a location, then the tactic produces a side-goal with
the equality of the corresponding locations in `lhs, rhs`.

Otherwise, `congrm_1` keeps scanning deeper into the expressions, until either the expressions
finish or there is a mismatch between their shapes.

*Note:* `congrm_1` does no check to make sure that the functions that it is matching are equal,
or even defeq.  For instance,
```lean
example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  congrm_1 (id _) + nat.succ _,
end
```
produces the three goals
```
⊢ 5 = 8
⊢ 7 = 12
⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
```
In fact, not even the types need to match:
```
example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  let i₁ : ℤ → ℤ := sorry,
  let i₁' : ℤ → ℤ := sorry,
  let i₂ : ℤ → ℤ → ℤ := sorry,
  congrm_1 i₂ (i₁ _) (i₁' _),
end
```
produces the same three goals as above
```
⊢ 5 = 8
⊢ 7 = 12
⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
```
-/
meta def congrm_1 (arg : parse texpr) : tactic unit :=
do ta ← to_expr arg tt ff,
  tgt ← target,
  let nargs := tgt.get_app_num_args,
  equate_with_pattern_1 ta (tgt.ith_arg $ nargs - 2) (tgt.ith_arg $ nargs - 1),
  try refl,
  get_goals >>= (λ g, set_goals g.reverse)  -- reverse the order of the goals

end tactic.interactive
