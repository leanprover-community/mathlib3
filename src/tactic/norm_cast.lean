/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis

Normalizing casts inside expressions.
-/

import tactic.basic tactic.interactive tactic.converter.interactive
import data.buffer.parser data.num.basic

/-!
# A tactic for normalizing casts inside expressions

This tactic normalizes casts inside expressions.
It can be thought of as a call to the simplifier with a specific set of lemmas to
move casts upwards in the expression.
It has special handling of numerals and a simple heuristic to help moving
casts "past" binary operators.
Contrary to simp, it should be safe to use as a non-terminating tactic.

## Important definitions
* `tactic.interactive.norm_cast`
* `tactic.interactive.push_cast`
* `tactic.interactive.exact_mod_cast`
* `tactic.interactive.apply_mod_cast`
* `tactic.interactive.rw_mod_cast`
* `tactic.interactive.assumption_mod_cast`
-/

namespace tactic

/--
This is a work around to the fact that in some cases
mk_instance times out instead of failing
example: has_lift_t ℤ ℕ

mk_instance' is used when we assume the type class search
should end instantly
-/
meta def mk_instance' (e : expr) : tactic expr :=
try_for 1000 (mk_instance e)

end tactic

@[reducible] meta def name.is_coe (n : name) : Prop :=
n = `has_coe.coe ∨ n = `coe ∨ n = `coe_fn

namespace expr

open tactic expr

meta def flip : expr → expr → option (pexpr × pexpr)
| `(%%a = %%b) e := some (``(%%b = %%a), ``(eq.symm %%e))
| `(%%a ↔ %%b) e := some (``(%%b ↔ %%a), ``(iff.symm %%e))
| (pi n bi d b) e := do
  (b', e') ← flip b (expr.lift_vars e 0 1 (var 0)),
  let d' := pexpr.of_expr d,
  let new_ty := pi n bi d' b',
  let new_e := lam n bi d' e',
  some (new_ty, new_e)
| _ _ := none

meta def reverse (ty e : expr) : tactic (expr × expr) :=
do
  (new_ty, new_e) ← flip ty e,
  new_ty ← to_expr new_ty,
  new_e ← to_expr new_e,
  return (new_ty, new_e)

meta def contains_coe' (e : expr) : bool :=
e.contains_constant name.is_coe

meta def is_coe : expr → bool
| (expr.const n _) := n.is_coe
| _ := ff

end expr

namespace norm_cast

open tactic expr

--meta def new_name (n : name) : name := name.mk_string "reversed" n

@[derive decidable_eq]
inductive label
| Elim : label
| Move : label
| Squash : label

open label

def label_to_string : label → string
| Elim := "elim_cast"
| Move := "move_cast"
| Squsah := "squash_cast"

instance : has_to_string label := ⟨label_to_string⟩

/-- rhs has the same number of or fewer casts at the beginning then lhs -/
meta def same_or_fewer_initial_casts : expr → expr → bool | lhs rhs :=
let lhs_head := lhs.get_app_fn, rhs_head := rhs.get_app_fn in
match lhs_head.is_coe, rhs_head.is_coe with
| tt, tt := same_or_fewer_initial_casts lhs.app_arg rhs.app_arg
| ff, tt := ff
| _, _ := tt
end

/- meta def same_or_fewer_initial_casts : expr → expr → bool
| `(↑%%lhs) `(↑%%rhs) := same_or_fewer_initial_casts lhs rhs
| `(↑%%_) _ := ff
| _ `(↑%%_) := ff
| _ _ := tt -/

private def squash_cast_fail :=
"norm_cast lemmas starting with ↑↑ on the LHS must be squash_cast lemmas, " ++
  "but squash_cast lemmas must remove at least one ↑."

meta def classify_type_aux (lhs rhs : expr) : tactic label :=
let lhs_head := lhs.get_app_fn in
if lhs_head.is_coe then
  let lhs_body := lhs.app_arg,
      lhs_body_head := lhs_body.get_app_fn in
  if lhs_body_head.is_coe then
    let rhs_head := rhs.get_app_fn in
    if same_or_fewer_initial_casts lhs_body.app_arg rhs.app_arg then
      return Squash
    else fail squash_cast_fail
  else /- !lhs_body_head.is_coe -/ if rhs.contains_coe' then return Move
  else return Squash
else if rhs.contains_coe' then -- !lhs_head.is_coe
  fail $ "norm_cast lemmas starting without ↑ on the LHS must be elim_cast lemmas," ++
                       " but elim_cast lemmas cannot contain ↑ on the RHS"
else if ! lhs.contains_coe' then
  fail "norm_cast lemmas must contain ↑"
else return Elim

meta def classify_type (ty : expr) : tactic label :=
do (args, tp) ← mk_local_pis ty,
match tp with
| `(%%lhs = %%rhs) := classify_type_aux lhs rhs
| `(%%lhs ↔ %%rhs) := classify_type_aux lhs rhs
| _ := fail "norm_cast lemmas must be = or ↔"
end

meta structure norm_cast_cache :=
( up : simp_lemmas )
( down : simp_lemmas )
( squash : simp_lemmas )

meta def empty_cache : norm_cast_cache :=
{ up := simp_lemmas.mk,
  down := simp_lemmas.mk,
  squash := simp_lemmas.mk,
}

meta def add_elim (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_up ← simp_lemmas.add cache.up e,
  return {
    up := new_up,
    down := cache.down,
    squash := cache.squash, }

meta def add_move (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  ty ← infer_type e,
  (rev_ty, rev_e) ← reverse ty e,
  new_up ← simp_lemmas.add cache.up rev_e,
  new_down ← simp_lemmas.add cache.down e,
  return {
    up := new_up,
    down := new_down,
    squash := cache.squash, }

meta def add_squash (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache :=
do
  new_squash ← simp_lemmas.add cache.squash e,
  new_down ← simp_lemmas.add cache.down e,
  return {
    up := cache.up,
    down := new_down,
    squash := new_squash, }

meta def add_lemma (cache : norm_cast_cache) (decl : name) : tactic norm_cast_cache :=
do
  --(declaration.thm n l ty task_e) ← get_decl decl | failed,
  --let e := task_e.get,
  e ← mk_const decl,
  ty ← infer_type e,
  guess ← classify_type ty,
  match guess with
  | Elim := add_elim cache e
  | Move := add_move cache e
  | Squash := add_squash cache e
  end

mk_simp_attribute push_cast "The `push_cast` simp attribute uses `norm_cast` lemmas
to move casts toward the leaf nodes of the expression."

meta def after_set (attr : option label) (decl : name) (n : ℕ) (b : bool) : tactic unit :=
do
  e ← mk_const decl,
  ty ← infer_type e,
  guess ← classify_type ty <|> fail "classifier failed",
  if guess ≠ Elim then simp_attr.push_cast.set decl () tt else skip,
  match attr with
  | none := skip
  | (some attr) :=
    if attr = guess then skip else trace $
    "#check " ++ to_string decl ++ " -- is labeled " ++ to_string attr ++ " but the classifier guessed " ++ to_string guess
  end


@[user_attribute] meta def elim_cast_attr : user_attribute unit :=
{
    name      := `elim_cast,
    descr     := "attribute for norm_cast",
    after_set := some $ after_set (some Elim),
    before_unset := some $ λ _ _, tactic.skip,
    cache_cfg := {
        mk_cache     := λ _, skip,
        dependencies := [],
    }
}

@[user_attribute] meta def move_cast_attr : user_attribute unit :=
{
    name      := `move_cast,
    descr     := "attribute for norm_cast",
    after_set := some $ after_set (some Move),
    before_unset := some $ λ _ _, tactic.skip,
    cache_cfg := {
        mk_cache     := λ _, skip,
        dependencies := [],
    }
}

@[user_attribute] meta def squash_cast_attr : user_attribute unit :=
{
    name      := `squash_cast,
    descr     := "attribute for norm_cast",
    after_set := some $ after_set (some Squash),
    before_unset := some $ λ _ _, tactic.skip,
    cache_cfg := {
        mk_cache     := λ _, skip,
        dependencies := [],
    }
}

-- lemmas to handle the ≥, > and ≠ operators
lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x := λ _ _, iff.rfl
lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x := λ _ _, iff.rfl
lemma ne_from_not_eq {α} : ∀ (x y : α), x ≠ y ↔ ¬(x = y) := λ _ _, iff.rfl

meta def mk_cache (names : list name) : tactic norm_cast_cache :=
do
  cache ← monad.foldl add_lemma empty_cache names,
  elim_lemmas ← attribute.get_instances `elim_cast >>= monad.mapm mk_const,
  move_lemmas ← attribute.get_instances `move_cast >>= monad.mapm mk_const,
  squash_lemmas ← attribute.get_instances `squash_cast >>= monad.mapm mk_const,
  cache ← monad.foldl add_elim cache elim_lemmas,
  cache ← monad.foldl add_move cache move_lemmas,
  cache ← monad.foldl add_squash cache squash_lemmas,

  new_up ← simp_lemmas.add_simp cache.up ``norm_cast.ge_from_le,
  new_up ← simp_lemmas.add_simp new_up ``gt_from_lt,
  new_up ← simp_lemmas.add_simp new_up ``ne_from_not_eq,
  let cache : norm_cast_cache := {
    up := new_up,
    down := cache.down,
    squash := cache.squash,
  },

  return cache

@[user_attribute] meta def norm_cast_attr : user_attribute norm_cast_cache :=
{
    name      := `norm_cast,
    descr     := "attribute for norm_cast",
    after_set := some $ after_set none,
    before_unset := some $ λ _ _, tactic.skip,
    cache_cfg := {
        mk_cache     := mk_cache,
        dependencies := [],
    }
}

end norm_cast

namespace tactic.interactive
open tactic interactive tactic.interactive interactive.types expr lean.parser
open norm_cast

/-- `push_cast` rewrites the expression to move casts toward the leaf nodes.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
Equivalent to `simp only with push_cast`.
Can also be used at hypotheses.
-/
meta def push_cast (l : parse location): tactic unit :=
tactic.interactive.simp none tt [] [`push_cast] l

end tactic.interactive

namespace norm_cast
open tactic expr

/-
This is an auxiliary function that proves e = new_e using only squash_cast lemmas.
-/
meta def aux_squash (e new_e : expr) : tactic expr :=
do
  cache ← norm_cast_attr.get_cache,
  let s := cache.squash,
  (e', pr) ← s.rewrite new_e,
  is_def_eq e e',
  mk_eq_symm pr

/-
This is the main heuristic used alongside the elim_cast and move_cast lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when the squash_cast lemmas can prove that (↑(x : α) : γ) = (↑(↑(x : α) : β) : γ)
-/
meta def heur (_ : unit) : expr → tactic (unit × expr × expr)
| (app (app op x) y) :=
( do
  `(@coe %%α %%δ %%coe1 %%xx) ← return x,
  `(@coe %%β %%γ %%coe2 %%yy) ← return y,
  success_if_fail $ is_def_eq α β,
  is_def_eq δ γ,

  (do
    coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance',
    new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
    let new_e := app (app op new_x) y,
    eq_x ← aux_squash x new_x,
    pr ← mk_congr_arg op eq_x,
    pr ← mk_congr_fun pr y,
    return ((), new_e, pr)
  ) <|> (do
    coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance',
    new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
    let new_e := app (app op x) new_y,
    eq_y ← aux_squash y new_y,
    pr ← mk_congr_arg (app op x) eq_y,
    return ((), new_e, pr)
  )
) <|> ( do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_one.one %%β %%h1) ← return y,
  h2 ← to_expr ``(has_one %%α) >>= mk_instance',
  new_y ← to_expr ``( @coe %%α %%β %%coe1 (@has_one.one %%α %%h2) ),
  eq_y ← aux_squash y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return ((), new_e, pr)
) <|> ( do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_one.one %%β %%h1) ← return y,
  h2 ← to_expr ``(has_one %%α) >>= mk_instance',
  new_y ← to_expr ``( @coe %%α %%β %%coe1 (@has_one.one %%α %%h2) ),
  eq_y ← aux_squash y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return ((), new_e, pr)
)
| _ := failed

/-
assumption is used to discharge proofs in step 2
-/
meta def prove : tactic unit := assumption

/-
TODO: norm_cast takes a list of expressions to use as lemmas for the discharger
-/

/-
This is an auxiliary function used in step 2.
It tries to rewrite an expression using the elim_cast and move_cast lemmas.
On failure, it calls the heuristic.
-/
meta def post (s : simp_lemmas) (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
( do
  r ← mcond (is_prop e) (return `iff) (return `eq),
  (new_e, pr) ← s.rewrite e prove r,
  pr ← match r with
  | `iff := mk_app `propext [pr]
  | _    := return pr
  end,
  return ((), new_e, pr)
) <|> heur () e

/-
The following auxiliary functions are used to handle numerals.
-/

-- prove ↑n = n where n is a numeral
meta def aux_num_prove_eq (a b : expr) : tactic expr :=
do
  h ← to_expr ``(%%a = %%b),
  s1 ← simp_lemmas.mk_default,
  cache ← norm_cast_attr.get_cache,
  let s := simp_lemmas.join s1 cache.down,
  (_, pr) ← simplify s [] h,
  some (_, tmp) ← expr.is_eq <$> infer_type pr,
  is_def_eq tmp `(true),
  to_expr ``(eq.mpr %%pr trivial)

-- if possible, rewrite (n : α) to ((n : ℕ) : α) where n is a numeral and α ≠ ℕ
meta def aux_num_1 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
  α ← infer_type e,
  success_if_fail $ is_def_eq α `(ℕ),
  n ← e.to_num,
  h1 ← mk_app `has_lift_t [`(ℕ), α] >>= mk_instance',
  new_e ← expr.of_num `(ℕ) n,
  new_e ← to_expr ``(@coe ℕ %%α %%h1 %%new_e),
  pr ← aux_num_prove_eq e new_e,
  return ((), new_e, pr)

-- if possible, rewrite (↑n : α) to (n : α) where n is a numeral
meta def aux_num_2 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
  `(@coe ℕ %%α %%h1 %%e') ← return e,
  n ← e'.to_num,
  new_e ← expr.of_num α n,
  h ← to_expr ``(%%e = %%new_e),
  pr ← aux_num_prove_eq e new_e,
  return ((), new_e, pr)

meta def simplify_top_down' {α} (a : α) (pre : α → expr → tactic (α × expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ a _ _ _ e, do (new_a, new_e, pr) ← pre a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, ff))
  (λ _ _ _ _ _, failed)
  `eq e

/-
Core function.
-/
meta def derive (e : expr) : tactic (expr × expr) :=
do
  cache ← norm_cast_attr.get_cache,
  e ← instantiate_mvars e,
  let cfg : simp_config := { fail_if_unchanged := ff },
  let e0 := e,

  -- step 1: pre-processing of numerals
  ((), e1, pr1) ← simplify_top_down' () aux_num_1 e0 cfg,

  -- step 2: casts are moved upwards and eliminated
  let s2 := cache.up,
  ((), e2, pr2) ← simplify_bottom_up () (post s2) e1 cfg,

  -- step 3: casts are squashed
  let s3 := cache.squash,
  (e3, pr3) ← simplify s3 [] e2 cfg,

  --step 4: post-processing of numerals
  ((), e4, pr4) ← simplify_top_down' () aux_num_2 e3 cfg,

  let new_e := e4,
  guard (¬ new_e =ₐ e),
  pr ← mk_eq_trans pr1 pr2,
  pr ← mk_eq_trans pr pr3,
  pr ← mk_eq_trans pr pr4,
  return (new_e, pr)

end norm_cast

namespace tactic
open tactic expr
open norm_cast

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

meta def exact_mod_cast (e : expr) : tactic unit :=
( do
  new_e ← aux_mod_cast e,
  exact new_e
) <|> fail "exact_mod_cast failed"

meta def apply_mod_cast (e : expr) : tactic (list (name × expr)) :=
( do
  new_e ← aux_mod_cast e,
  apply new_e
) <|> fail "apply_mod_cast failed"

meta def assumption_mod_cast : tactic unit :=
do {
  let cfg : simp_config := {
    fail_if_unchanged := ff,
    canonize_instances := ff,
    canonize_proofs := ff,
    proj := ff
  },
  replace_at derive [] tt,
  ctx ← local_context,
  try_lst $ ctx.map (λ h, aux_mod_cast h ff >>= tactic.exact)
} <|> fail "assumption_mod_cast failed"

end tactic

namespace tactic.interactive
open tactic interactive tactic.interactive interactive.types expr lean.parser
open norm_cast

local postfix `?`:9001 := optional

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
( do
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
) <|> fail "rw_mod_cast failed"

/--
Normalize the goal and the given expression, then close the goal with exact.
-/
meta def exact_mod_cast (e : parse texpr) : tactic unit :=
do
  e ← i_to_expr e <|> do {
    ty ← target,
    e ← i_to_expr_strict ``(%%e : %%ty),
    pty ← pp ty, ptgt ← pp e,
    fail ("exact_mod_cast failed, expression type not directly " ++
    "inferrable. Try:\n\nexact_mod_cast ...\nshow " ++
    to_fmt pty ++ ",\nfrom " ++ ptgt : format)
  },
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
open conv tactic tactic.interactive interactive interactive.types
open norm_cast (derive)

meta def norm_cast : conv unit := replace_lhs derive

end conv.interactive

-- lemmas defined in core
attribute [norm_cast] int.coe_nat_zero
attribute [norm_cast] int.coe_nat_one
attribute [norm_cast] int.nat_abs_of_nat
attribute [norm_cast] int.coe_nat_succ
attribute [norm_cast] int.coe_nat_add
attribute [norm_cast] int.coe_nat_sub
attribute [norm_cast] int.coe_nat_mul

-- TODO: move this elsewhere?
@[norm_cast] lemma ite_cast {α β : Type} [has_coe α β]
  {c : Prop} [decidable c] {a b : α} :
  ↑(ite c a b) = ite c (↑a : β) (↑b : β) :=
by by_cases h : c; simp [h]
