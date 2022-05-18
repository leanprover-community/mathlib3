/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis
-/
import tactic.converter.interactive
import tactic.hint

/-!
# A tactic for normalizing casts inside expressions

This tactic normalizes casts inside expressions.
It can be thought of as a call to the simplifier with a specific set of lemmas to
move casts upwards in the expression.
It has special handling of numerals and a simple heuristic to help moving
casts "past" binary operators.
Contrary to simp, it should be safe to use as a non-terminating tactic.

The algorithm implemented here is described in the paper
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.

## Important definitions
* `tactic.interactive.norm_cast`
* `tactic.interactive.push_cast`
* `tactic.interactive.exact_mod_cast`
* `tactic.interactive.apply_mod_cast`
* `tactic.interactive.rw_mod_cast`
* `tactic.interactive.assumption_mod_cast`
-/

setup_tactic_parser

namespace tactic

/--
Runs `mk_instance` with a time limit.

This is a work around to the fact that in some cases
mk_instance times out instead of failing,
for example: `has_lift_t ℤ ℕ`

`mk_instance_fast` is used when we assume the type class search
should end instantly.
-/
meta def mk_instance_fast (e : expr) (timeout := 1000) : tactic expr :=
try_for timeout (mk_instance e)

end tactic

namespace norm_cast

open tactic expr

declare_trace norm_cast

/--
Output a trace message if `trace.norm_cast` is enabled.
-/
meta def trace_norm_cast {α} [has_to_tactic_format α] (msg : string) (a : α) : tactic unit :=
when_tracing `norm_cast $ do
a ← pp a,
trace ("[norm_cast] " ++ msg ++ a : format)

mk_simp_attribute push_cast "The `push_cast` simp attribute uses `norm_cast` lemmas
to move casts toward the leaf nodes of the expression."

/--
`label` is a type used to classify `norm_cast` lemmas.
* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
@[derive [decidable_eq, has_reflect, inhabited]]
inductive label
| elim   : label
| move   : label
| squash : label

namespace label

/-- Convert `label` into `string`. -/
protected def to_string : label → string
| elim   := "elim"
| move   := "move"
| squash := "squash"

instance : has_to_string label := ⟨label.to_string⟩
instance : has_repr label := ⟨label.to_string⟩
meta instance : has_to_format label := ⟨λ l, l.to_string⟩

/-- Convert `string` into `label`. -/
def of_string : string -> option label
| "elim" := some elim
| "move" := some move
| "squash" := some squash
| _ := none

end label

open label

/-- Count how many coercions are at the top of the expression. -/
meta def count_head_coes : expr → ℕ
| `(coe %%e) := count_head_coes e + 1
| `(coe_sort %%e) := count_head_coes e + 1
| `(coe_fn %%e) := count_head_coes e + 1
| _ := 0

/-- Count how many coercions are inside the expression, including the top ones. -/
meta def count_coes : expr → tactic ℕ
| `(coe %%e) := (+1) <$> count_coes e
| `(coe_sort %%e) := (+1) <$> count_coes e
| `(coe_fn %%e) := (+1) <$> count_coes e
| (app `(coe_fn %%e) x) := (+) <$> count_coes x <*> (+1) <$> count_coes e
| (expr.lam n bi t e) := do
  l ← mk_local' n bi t,
  count_coes $ e.instantiate_var l
| e := do
  as ← e.get_simp_args,
  list.sum <$> as.mmap count_coes

/-- Count how many coercions are inside the expression, excluding the top ones. -/
private meta def count_internal_coes (e : expr) : tactic ℕ := do
ncoes ← count_coes e,
pure $ ncoes - count_head_coes e

/--
Classifies a declaration of type `ty` as a `norm_cast` rule.
-/
meta def classify_type (ty : expr) : tactic label := do
(_, ty) ← open_pis ty,
(lhs, rhs) ← match ty with
  | `(%%lhs = %%rhs) := pure (lhs, rhs)
  | `(%%lhs ↔ %%rhs) := pure (lhs, rhs)
  | _ := fail "norm_cast: lemma must be = or ↔"
  end,
lhs_coes ← count_coes lhs,
when (lhs_coes = 0) $ fail "norm_cast: badly shaped lemma, lhs must contain at least one coe",
let lhs_head_coes := count_head_coes lhs,
lhs_internal_coes ← count_internal_coes lhs,
let rhs_head_coes := count_head_coes rhs,
rhs_internal_coes ← count_internal_coes rhs,
if lhs_head_coes = 0 then
  return elim
else if lhs_head_coes = 1 then do
  when (rhs_head_coes ≠ 0) $ fail "norm_cast: badly shaped lemma, rhs can't start with coe",
  if rhs_internal_coes = 0 then
    return squash
  else
    return move
else if rhs_head_coes < lhs_head_coes then do
  return squash
else do
  fail "norm_cast: badly shaped shaped squash lemma, rhs must have fewer head coes than lhs"

/-- The cache for `norm_cast` attribute stores three `simp_lemma` objects. -/
meta structure norm_cast_cache :=
(up : simp_lemmas)
(down : simp_lemmas)
(squash : simp_lemmas)

/-- Empty `norm_cast_cache`. -/
meta def empty_cache : norm_cast_cache :=
{ up     := simp_lemmas.mk,
  down   := simp_lemmas.mk,
  squash := simp_lemmas.mk, }

meta instance : inhabited norm_cast_cache := ⟨empty_cache⟩

/-- `add_elim cache e` adds `e` as an `elim` lemma to `cache`. -/
meta def add_elim (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_up ← cache.up.add e,
  return
  { up     := new_up,
    down   := cache.down,
    squash := cache.squash, }

/-- `add_move cache e` adds `e` as a `move` lemma to `cache`. -/
meta def add_move (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_up ← cache.up.add e tt,
  new_down ← cache.down.add e,
  return
  { up     := new_up,
    down   := new_down,
    squash := cache.squash, }

/-- `add_squash cache e` adds `e` as an `squash` lemma to `cache`. -/
meta def add_squash (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_squash ← cache.squash.add e,
  new_down ← cache.down.add e,
  return
  { up     := cache.up,
    down   := new_down,
    squash := new_squash, }

/--
The type of the `norm_cast` attribute.
The optional label is used to overwrite the classifier.
-/
meta def norm_cast_attr_ty : Type := user_attribute norm_cast_cache (option label)

/--
Efficient getter for the `@[norm_cast]` attribute parameter that does not call `eval_expr`.

See Note [user attribute parameters].
-/
meta def get_label_param (attr : norm_cast_attr_ty) (decl : name) : tactic (option label) := do
p ← attr.get_param_untyped decl,
match p with
| `(none) := pure none
| `(some label.elim) := pure label.elim
| `(some label.move) := pure label.move
| `(some label.squash) := pure label.squash
| _ := fail p
end

/--
`add_lemma cache decl` infers the proper `norm_cast` attribute for `decl` and adds it to `cache`.
-/
meta def add_lemma (attr : norm_cast_attr_ty) (cache : norm_cast_cache) (decl : name) :
  tactic norm_cast_cache :=
do
  e ← mk_const decl,
  param ← get_label_param attr decl,
  l ← param <|> (infer_type e >>= classify_type),
  match l with
  | elim   := add_elim cache e
  | move   := add_move cache e
  | squash := add_squash cache e
  end

-- special lemmas to handle the ≥, > and ≠ operators
private lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x := λ _ _, iff.rfl
private lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x := λ _ _, iff.rfl
private lemma ne_from_not_eq {α} : ∀ (x y : α), x ≠ y ↔ ¬(x = y) := λ _ _, iff.rfl

/--
`mk_cache names` creates a `norm_cast_cache`. It infers the proper `norm_cast` attributes
for names in `names`, and collects the lemmas attributed with specific `norm_cast` attributes.
-/
meta def mk_cache (attr : thunk norm_cast_attr_ty) (names : list name) :
  tactic norm_cast_cache := do
-- names has the declarations in reverse order
cache ← names.mfoldr (λ name cache, add_lemma (attr ()) cache name) empty_cache,

--some special lemmas to handle binary relations
let up := cache.up,
up ← up.add_simp ``ge_from_le,
up ← up.add_simp ``gt_from_lt,
up ← up.add_simp ``ne_from_not_eq,

let down := cache.down,
down ← down.add_simp ``coe_coe,

pure { up := up, down := down, squash := cache.squash }

/--
The `norm_cast` attribute.
-/
@[user_attribute] meta def norm_cast_attr : user_attribute norm_cast_cache (option label) :=
{ name      := `norm_cast,
  descr     := "attribute for norm_cast",
  parser    :=
    (do some l ← (label.of_string ∘ to_string) <$> ident, return l)
      <|> return none,
  after_set := some (λ decl prio persistent, do
    param ← get_label_param norm_cast_attr decl,
    match param with
    | some l :=
      when (l ≠ elim) $ simp_attr.push_cast.set decl () tt
    | none := do
      e ← mk_const decl,
      ty ← infer_type e,
      l ← classify_type ty,
      norm_cast_attr.set decl l persistent prio
    end),
  before_unset := some $ λ _ _, tactic.skip,
  cache_cfg := { mk_cache := mk_cache norm_cast_attr, dependencies := [] } }

/-- Classify a declaration as a `norm_cast` rule. -/
meta def make_guess (decl : name) : tactic label :=
do
  e ← mk_const decl,
  ty ← infer_type e,
  classify_type ty

/--
Gets the `norm_cast` classification label for a declaration. Applies the
override specified on the attribute, if necessary.
-/
meta def get_label (decl : name) : tactic label :=
do
  param ← get_label_param norm_cast_attr decl,
  param <|> make_guess decl

end norm_cast

namespace tactic.interactive
open norm_cast

/--
`push_cast` rewrites the expression to move casts toward the leaf nodes.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
Equivalent to `simp only with push_cast`.
Can also be used at hypotheses.

`push_cast` can also be used at hypotheses and with extra simp rules.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```
-/
meta def push_cast (hs : parse tactic.simp_arg_list) (l : parse location) : tactic unit :=
tactic.interactive.simp none none tt hs [`push_cast] l {discharger := tactic.assumption}


end tactic.interactive

namespace norm_cast
open tactic expr

/-- Prove `a = b` using the given simp set. -/
meta def prove_eq_using (s : simp_lemmas) (a b : expr) : tactic expr := do
(a', a_a', _) ← simplify s [] a {fail_if_unchanged := ff},
(b', b_b', _) ← simplify s [] b {fail_if_unchanged := ff},
on_exception (trace_norm_cast "failed: " (to_expr ``(%%a' = %%b') >>= pp)) $
  is_def_eq a' b' reducible,
b'_b ← mk_eq_symm b_b',
mk_eq_trans a_a' b'_b

/-- Prove `a = b` by simplifying using move and squash lemmas. -/
meta def prove_eq_using_down (a b : expr) : tactic expr := do
cache ← norm_cast_attr.get_cache,
trace_norm_cast "proving: " (to_expr ``(%%a = %%b) >>= pp),
prove_eq_using cache.down a b

/--
This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash lemma
-/
meta def splitting_procedure : expr → tactic (expr × expr)
| (app (app op x) y) :=
(do
  `(@coe %%α %%δ %%coe1 %%xx) ← return x,
  `(@coe %%β %%γ %%coe2 %%yy) ← return y,
  success_if_fail $ is_def_eq α β,
  is_def_eq δ γ,

  (do
    coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance_fast,
    new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
    let new_e := app (app op new_x) y,
    eq_x ← prove_eq_using_down x new_x,
    pr ← mk_congr_arg op eq_x,
    pr ← mk_congr_fun pr y,
    return (new_e, pr)
  ) <|> (do
    coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance_fast,
    new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
    let new_e := app (app op x) new_y,
    eq_y ← prove_eq_using_down y new_y,
    pr ← mk_congr_arg (app op x) eq_y,
    return (new_e, pr)
  )
) <|> (do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_one.one %%β %%h1) ← return y,
  h2 ← to_expr ``(has_one %%α) >>= mk_instance_fast,
  new_y ← to_expr ``(@coe %%α %%β %%coe1 (@has_one.one %%α %%h2)),
  eq_y ← prove_eq_using_down y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return (new_e, pr)
 ) <|> (do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_zero.zero %%β %%h1) ← return y,
  h2 ← to_expr ``(has_zero %%α) >>= mk_instance_fast,
  new_y ← to_expr ``(@coe %%α %%β %%coe1 (@has_zero.zero %%α %%h2)),
  eq_y ← prove_eq_using_down y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return (new_e, pr)
) <|> (do
  `(@has_one.one %%β %%h1) ← return x,
  `(@coe %%α %%β %%coe1 %%xx) ← return y,
  h1 ← to_expr ``(has_one %%α) >>= mk_instance_fast,
  new_x ← to_expr ``(@coe %%α %%β %%coe1 (@has_one.one %%α %%h1)),
  eq_x ← prove_eq_using_down x new_x,
  let new_e := app (app op new_x) y,
  pr ← mk_congr_arg (lam `x binder_info.default β (app (app op (var 0)) y)) eq_x,
  return (new_e, pr)
) <|> (do
  `(@has_zero.zero %%β %%h1) ← return x,
  `(@coe %%α %%β %%coe1 %%xx) ← return y,
  h1 ← to_expr ``(has_zero %%α) >>= mk_instance_fast,
  new_x ← to_expr ``(@coe %%α %%β %%coe1 (@has_zero.zero %%α %%h1)),
  eq_x ← prove_eq_using_down x new_x,
  let new_e := app (app op new_x) y,
  pr ← mk_congr_arg (lam `x binder_info.default β (app (app op (var 0)) y)) eq_x,
  return (new_e, pr)
)
| _ := failed

/--
Discharging function used during simplification in the "squash" step.

TODO: norm_cast takes a list of expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
private meta def prove : tactic unit :=
assumption

/--
Core rewriting function used in the "squash" step, which moves casts upwards
and eliminates them.

It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
meta def upward_and_elim (s : simp_lemmas) (e : expr) : tactic (expr × expr) :=
(do
  r ← mcond (is_prop e) (return `iff) (return `eq),
  (new_e, pr) ← s.rewrite e prove r,
  pr ← match r with
  | `iff := mk_app `propext [pr]
  | _    := return pr
  end,
  return (new_e, pr)
) <|> splitting_procedure e

/-!
The following auxiliary functions are used to handle numerals.
-/

/--
If possible, rewrite `(n : α)` to `((n : ℕ) : α)` where `n` is a numeral and `α ≠ ℕ`.
Returns a pair of the new expression and proof that they are equal.
-/
meta def numeral_to_coe (e : expr) : tactic (expr × expr) :=
do
  α ← infer_type e,
  success_if_fail $ is_def_eq α `(ℕ),
  n ← e.to_nat,
  h1 ← mk_app `has_lift_t [`(ℕ), α] >>= mk_instance_fast,
  let new_e : expr := reflect n,
  new_e ← to_expr ``(@coe ℕ %%α %%h1 %%new_e),
  pr ← prove_eq_using_down e new_e,
  return (new_e, pr)

/--
If possible, rewrite `((n : ℕ) : α)` to `(n : α)` where `n` is a numeral.
Returns a pair of the new expression and proof that they are equal.
-/
meta def coe_to_numeral (e : expr) : tactic (expr × expr) :=
do
  `(@coe ℕ %%α %%h1 %%e') ← return e,
  n ← e'.to_nat,
  -- replace e' by normalized numeral
  is_def_eq (reflect n) e' reducible,
  let e := e.app_fn (reflect n),
  new_e ← expr.of_nat α n,
  pr ← prove_eq_using_down e new_e,
  return (new_e, pr)

/-- A local variant on `simplify_top_down`. -/
private meta def simplify_top_down' {α} (a : α) (pre : α → expr → tactic (α × expr × expr))
  (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ a _ _ _ e, do
    (new_a, new_e, pr) ← pre a e,
    guard (¬ new_e =ₐ e),
    return (new_a, new_e, some pr, ff))
  (λ _ _ _ _ _, failed)
  `eq e

/--
The core simplification routine of `norm_cast`.
-/
meta def derive (e : expr) : tactic (expr × expr) :=
do
  cache ← norm_cast_attr.get_cache,
  e ← instantiate_mvars e,
  let cfg : simp_config :=
  { zeta := ff,
    beta := ff,
    eta  := ff,
    proj := ff,
    iota := ff,
    iota_eqn := ff,
    fail_if_unchanged := ff },
  let e0 := e,

  -- step 1: pre-processing of numerals
  ((), e1, pr1) ← simplify_top_down' () (λ _ e, prod.mk () <$> numeral_to_coe e) e0 cfg,
  trace_norm_cast "after numeral_to_coe: " e1,

  -- step 2: casts are moved upwards and eliminated
  ((), e2, pr2) ← simplify_bottom_up () (λ _ e, prod.mk () <$> upward_and_elim cache.up e) e1 cfg,
  trace_norm_cast "after upward_and_elim: " e2,

  -- step 3: casts are squashed
  (e3, pr3, _) ← simplify cache.squash [] e2 cfg,
  trace_norm_cast "after squashing: " e3,

  -- step 4: post-processing of numerals
  ((), e4, pr4) ← simplify_top_down' () (λ _ e, prod.mk () <$> coe_to_numeral e) e3 cfg,
  trace_norm_cast "after coe_to_numeral: " e4,

  let new_e := e4,
  guard (¬ new_e =ₐ e),
  pr ← mk_eq_trans pr1 pr2,
  pr ← mk_eq_trans pr pr3,
  pr ← mk_eq_trans pr pr4,
  return (new_e, pr)

/--
A small variant of `push_cast` suited for non-interactive use.

`derive_push_cast extra_lems e` returns an expression `e'` and a proof that `e = e'`.
-/
meta def derive_push_cast (extra_lems : list simp_arg_type) (e : expr) : tactic (expr × expr) :=
do (s, _) ← mk_simp_set tt [`push_cast] extra_lems,
   (e, prf, _) ← simplify (s.erase [`int.coe_nat_succ]) [] e
                  {fail_if_unchanged := ff} `eq tactic.assumption,
   return (e, prf)

end norm_cast

namespace tactic
open expr norm_cast

/-- `aux_mod_cast e` runs `norm_cast` on `e` and returns the result. If `include_goal` is true, it
also normalizes the goal. -/
meta def aux_mod_cast (e : expr) (include_goal : bool := tt) : tactic expr :=
match e with
| local_const _ lc _ _ := do
  e ← get_local lc,
  replace_at derive [e] include_goal,
  get_local lc
| e := do
  t ← infer_type e,
  e ← assertv `this t e,
  replace_at derive [e] include_goal,
  get_local `this
end

/-- `exact_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to use `e` to close the
goal. -/
meta def exact_mod_cast (e : expr) : tactic unit :=
decorate_error "exact_mod_cast failed:" $ do
  new_e ← aux_mod_cast e,
  exact new_e

/-- `apply_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to apply `e`. -/
meta def apply_mod_cast (e : expr) : tactic (list (name × expr)) :=
decorate_error "apply_mod_cast failed:" $ do
  new_e ← aux_mod_cast e,
  apply new_e

/-- `assumption_mod_cast` runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal. -/
meta def assumption_mod_cast : tactic unit :=
decorate_error "assumption_mod_cast failed:" $ do
  let cfg : simp_config :=
  { fail_if_unchanged := ff,
    canonize_instances := ff,
    canonize_proofs := ff,
    proj := ff },
  replace_at derive [] tt,
  ctx ← local_context,
  ctx.mfirst (λ h, aux_mod_cast h ff >>= tactic.exact)

end tactic

namespace tactic.interactive
open tactic norm_cast

/--
Normalize casts at the given locations by moving them "upwards".
As opposed to simp, norm_cast can be used without necessarily closing the goal.
-/
meta def norm_cast (loc : parse location) : tactic unit :=
do
  ns ← loc.get_locals,
  tt ← replace_at derive ns loc.include_goal | fail "norm_cast failed to simplify",
  when loc.include_goal $ try tactic.reflexivity,
  when loc.include_goal $ try tactic.triv,
  when (¬ ns.empty) $ try tactic.contradiction

/--
Rewrite with the given rules and normalize casts between steps.
-/
meta def rw_mod_cast (rs : parse rw_rules) (loc : parse location) : tactic unit :=
decorate_error "rw_mod_cast failed:" $ do
  let cfg_norm : simp_config := {},
  let cfg_rw : rewrite_cfg := {},
  ns ← loc.get_locals,
  monad.mapm' (λ r : rw_rule, do
    save_info r.pos,
    replace_at derive ns loc.include_goal,
    rw ⟨[r], none⟩ loc {}
  ) rs.rules,
  replace_at derive ns loc.include_goal,
  skip

/--
Normalize the goal and the given expression, then close the goal with exact.
-/
meta def exact_mod_cast (e : parse texpr) : tactic unit :=
do
  e ← i_to_expr e <|> do
  { ty ← target,
    e ← i_to_expr_strict ``(%%e : %%ty),
    pty ← pp ty, ptgt ← pp e,
    fail ("exact_mod_cast failed, expression type not directly " ++
    "inferrable. Try:\n\nexact_mod_cast ...\nshow " ++
    to_fmt pty ++ ",\nfrom " ++ ptgt : format) },
  tactic.exact_mod_cast e

/--
Normalize the goal and the given expression, then apply the expression to the goal.
-/
meta def apply_mod_cast (e : parse texpr) : tactic unit :=
do
  e ← i_to_expr_for_apply e,
  concat_tags $ tactic.apply_mod_cast e

/--
Normalize the goal and every expression in the local context, then close the goal with assumption.
-/
meta def assumption_mod_cast : tactic unit :=
tactic.assumption_mod_cast

end tactic.interactive

namespace conv.interactive
open conv
open norm_cast (derive)

/-- the converter version of `norm_cast' -/
meta def norm_cast : conv unit := replace_lhs derive

end conv.interactive

-- TODO: move this elsewhere?
@[norm_cast] lemma ite_cast {α β} [has_lift_t α β]
  {c : Prop} [decidable c] {a b : α} :
  ↑(ite c a b) = ite c (↑a : β) (↑b : β) :=
by by_cases h : c; simp [h]

@[norm_cast] lemma dite_cast {α β} [has_lift_t α β]
  {c : Prop} [decidable c] {a : c → α} {b : ¬ c → α} :
  ↑(dite c a b) = dite c (λ h, (↑(a h) : β)) (λ h, (↑(b h) : β)) :=
by by_cases h : c; simp [h]

add_hint_tactic "norm_cast at *"

/--
The `norm_cast` family of tactics is used to normalize casts inside expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and
`h` before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

`push_cast` rewrites the expression to move casts toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
It is equivalent to `simp only with push_cast`.
It can also be used at hypotheses with `push_cast at h`
and with extra simp lemmas with `push_cast [int.add_zero]`.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```

The implementation and behavior of the `norm_cast` family is described in detail at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
add_tactic_doc
{ name := "norm_cast",
  category   := doc_category.tactic,
  decl_names := [``tactic.interactive.norm_cast, ``tactic.interactive.rw_mod_cast,
                 ``tactic.interactive.apply_mod_cast, ``tactic.interactive.assumption_mod_cast,
                 ``tactic.interactive.exact_mod_cast, ``tactic.interactive.push_cast],
  tags       := ["coercions", "simplification"] }

/--
The `norm_cast` attribute should be given to lemmas that describe the
behaviour of a coercion in regard to an operator, a relation, or a particular
function.

It only concerns equality or iff lemmas involving `↑`, `⇑` and `↥`, describing the behavior of
the coercion functions.
It does not apply to the explicit functions that define the coercions.

Examples:
```lean
@[norm_cast] theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n

@[norm_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1

@[norm_cast] theorem cast_id : ∀ n : ℚ, ↑n = n

@[norm_cast] theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n

@[norm_cast] theorem cast_sub [add_group α] [has_one α] {m n} (h : m ≤ n) :
  ((n - m : ℕ) : α) = n - m

@[norm_cast] theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n

@[norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n

@[norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1
```

Lemmas tagged with `@[norm_cast]` are classified into three categories: `move`, `elim`, and
`squash`. They are classified roughly as follows:

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes

`norm_cast` uses `move` and `elim` lemmas to factor coercions toward the root of an expression
and to cancel them from both sides of an equation or relation. It uses `squash` lemmas to clean
up the result.

Occasionally you may want to override the automatic classification.
You can do this by giving an optional `elim`, `move`, or `squash` parameter to the attribute.

```lean
@[simp, norm_cast elim] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n :=
by rw [← of_real_nat_cast, of_real_re]
```

Don't do this unless you understand what you are doing.

A full description of the tactic, and the use of each lemma category, can be found at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
add_tactic_doc
{ name := "norm_cast attributes",
  category   := doc_category.attr,
  decl_names := [``norm_cast.norm_cast_attr],
  tags       := ["coercions", "simplification"] }

-- Lemmas defined in core.
attribute [norm_cast]
  int.nat_abs_of_nat
  int.coe_nat_sub
  int.coe_nat_mul
  int.coe_nat_zero
  int.coe_nat_one
  int.coe_nat_add

-- Lemmas about nat.succ need to get a low priority, so that they are tried last.
-- This is because `nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
attribute [norm_cast, priority 500] int.coe_nat_succ
