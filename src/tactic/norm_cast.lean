/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine

Normalizing casts inside expressions.
-/

import tactic.basic tactic.interactive tactic.converter.interactive
import data.buffer.parser

namespace tactic

/-
This is a work around to the fact that in some cases
mk_instance times out instead of failing
example: has_lift_t ℤ ℕ

mk_instance' is used when we assume the type class search
should end instantly
-/
meta def mk_instance' (e : expr) : tactic expr :=
try_for 1000 (mk_instance e)

end tactic

namespace expr
open tactic expr

meta def flip_eq (ty : expr) : tactic (expr × (expr → expr)) :=
do
    (a, b) ← is_eq ty,
    α ← infer_type a,
    new_ty ← to_expr ``(%%b = %%a),
    f ← to_expr ``(@eq.symm %%α %%a %%b),
    return (new_ty, ⇑f)

meta def flip_iff (ty : expr) : tactic (expr × (expr → expr)) :=
do
    (a, b) ← is_iff ty,
    new_ty ← to_expr ``(%%b ↔ %%a),
    f ← to_expr ``(@iff.symm %%a %%b),
    return (new_ty, ⇑f)

end expr

namespace norm_cast
open tactic expr

inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

namespace pos_num

instance : has_one pos_num := ⟨pos_num.one⟩

def succ : pos_num → pos_num
| 1        := bit0 one
| (bit1 n) := bit0 (succ n)
| (bit0 n) := bit1 n

protected def add : pos_num → pos_num → pos_num
| 1        b        := succ b
| a        1        := succ a
| (bit0 a) (bit0 b) := bit0 (add a b)
| (bit1 a) (bit1 b) := bit0 (succ (add a b))
| (bit0 a) (bit1 b) := bit1 (add a b)
| (bit1 a) (bit0 b) := bit1 (add a b)

instance : has_add pos_num := ⟨pos_num.add⟩

end pos_num

inductive num : Type
| zero  : num
| pos   : pos_num → num

namespace num
open pos_num

instance : has_zero num := ⟨num.zero⟩
instance : has_one num := ⟨num.pos 1⟩

def succ' : num → pos_num
| 0       := 1
| (pos p) := succ p

def succ (n : num) : num := pos (succ' n)

protected def add : num → num → num
| 0       a       := a
| b       0       := b
| (pos a) (pos b) := pos (a + b)

instance : has_add num := ⟨num.add⟩

end num

private meta def new_name (n : name) : name := name.mk_string "reversed" n

private meta def aux_after_set (tac : expr → tactic (expr × (expr → expr))) :
    expr → tactic (expr × (expr → expr))
| (pi n bi d b) := do
    uniq_n ← mk_fresh_name,
    let b' := b.instantiate_var (local_const uniq_n n bi d),
    (b', f) ← aux_after_set b',
    return $ (
        pi n bi d $ b'.abstract_local uniq_n,
        λ e, lam n bi d $ ( f $ e (local_const uniq_n n bi d) ).abstract_local uniq_n
    )
| ty := tac ty

private meta def after_set (decl : name) (prio : ℕ) (pers : bool) : tactic unit :=
do
    (declaration.thm n l ty e) ← get_decl decl | failed,
    let tac := λ ty, (flip_eq ty <|> flip_iff ty),
    (ty', f) ← aux_after_set tac ty,
    let e' := task.map f e,
    let n' := new_name n,
    add_decl (declaration.thm n' l ty' e')

private meta def mk_cache : list name → tactic simp_lemmas :=
monad.foldl simp_lemmas.add_simp simp_lemmas.mk

/--
This is an attribute for simplification rules that are
used to normalize casts.

Let r be = or ↔, then elimination lemmas of the shape
Π ..., P ↑a1 ... ↑an r P a1 ... an should be given the
attribute elim_cast.
-/
@[user_attribute]
meta def elim_cast_attr : user_attribute simp_lemmas :=
{
    name      := `elim_cast,
    descr     := "attribute for lemmas of the shape Π ..., P ↑a1 ... ↑an = P a1 ... an",
    cache_cfg :=
        { mk_cache     := mk_cache,
          dependencies := [], },
}

/--
This is an attribute for simplification rules that are
used to normalize casts.

Let r be = or ↔, then compositional lemmas of the shape
Π ..., ↑(P a1 ... an) r P ↑a1 ... ↑an should be given the
attribute move_cast.
-/
@[user_attribute]
meta def move_cast_attr : user_attribute simp_lemmas :=
{
    name      := `move_cast,
    descr     := "attribute for lemmas of the shape Π ..., ↑(P a1 ... an) = P ↑a1 ... ↑an",
    after_set := some after_set,
    cache_cfg :=
        { mk_cache     := mk_cache ∘ (list.map new_name),
          dependencies := [], },
}

private meta def get_cache : tactic simp_lemmas :=
do
    a ← elim_cast_attr.get_cache,
    b ← move_cast_attr.get_cache,
    return $ simp_lemmas.join a b

/--
This is an attribute for simplification rules of the shape
Π ..., ↑↑a = ↑a or  Π ..., ↑a = a.

They are used in a heuristic to infer intermediate casts.
-/
@[user_attribute]
meta def squash_cast_attr : user_attribute simp_lemmas :=
{
    name      := `squash_cast,
    descr     := "attribute for lemmas of the shape Π ..., ↑↑a = ↑a",
    after_set := none,
    cache_cfg := {
        mk_cache     := monad.foldl simp_lemmas.add_simp simp_lemmas.mk,
        dependencies := [],
    }
}

/-
This is an auxiliary function that proves e = new_e
using only squash_cast lemmas
-/
private meta def aux_squash (e new_e : expr) : tactic expr :=
do
    s ← squash_cast_attr.get_cache,
    (e', pr) ← s.rewrite new_e,
    is_def_eq e e',
    mk_eq_symm pr

private meta def num_of_expr : expr → option num
| `(@has_zero.zero %%α %%h) := some 0
| `(@has_one.one %%α %%h) := some 1
| `(@bit0 %%α %%h %%e) := do n ← num_of_expr e, some (bit0 n)
| `(@bit1 %%α %%h1 %%h2 %%e) := do n ← num_of_expr e, some (bit1 n)
| _ := none

private meta def aux_num (α h_one h_add : expr) : pos_num → pexpr
| pos_num.one := ``(@has_one.one %%α %%h_one)
| (pos_num.bit0 n) := ``(@bit0 %%α %%h_add (%%(aux_num n)))
| (pos_num.bit1 n) := ``(@bit1 %%α %%h_one %%h_add (%%(aux_num n)))

private meta def expr_of_num (α : expr) (n : num) : tactic expr :=
match n with
| num.zero := do
  h_zero ← mk_app `has_zero [α] >>= mk_instance',
  to_expr ``(@has_zero.zero %%α %%h_zero)
| (num.pos (pos_num.one)) := do
  h_one ← mk_app `has_one [α] >>= mk_instance',
  to_expr ``(@has_one.one %%α %%h_one)
| (num.pos m) := do
  h_one ← mk_app `has_one [α] >>= mk_instance',
  h_add ← mk_app `has_add [α] >>= mk_instance',
  to_expr (aux_num α h_one h_add m)
end

/-
This is the main heuristic used alongside the elim_cast and move_cast lemmas.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten as:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when the squash_cast lemmas can prove that (↑(x : α) : γ) = (↑(↑(x : α) : β) : γ)
-/
private meta def heur (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
match e with
| (app (expr.app op x) y) :=
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
    δ ← infer_type x,
    `(@coe %%β %%γ %%coe1 %%yy) ← return y,
    is_def_eq δ γ,
    n ← num_of_expr x,
    new_x ← expr_of_num β n >>= λ e, to_expr ``(@coe %%β %%δ %%coe1 %%e),
    let new_e := app (app op new_x) y,
    eq_x ← aux_squash x new_x,
    pr ← mk_congr_arg op eq_x,
    pr ← mk_congr_fun pr y,
    return ((), new_e, pr)
) <|> ( do
    `(@coe %%α %%δ %%coe1 %%xx) ← return x,
    γ ← infer_type y,
    is_def_eq δ γ,
    n ← num_of_expr y,
    new_y ← expr_of_num α n >>= λ e, to_expr ``(@coe %%α %%δ %%coe1 %%e),
    let new_e := app (app op x) new_y,
    eq_y ← aux_squash y new_y,
    pr ← mk_congr_arg (app op x) eq_y,
    return ((), new_e, pr)
)
| _ := failed
end

/-
assumption is used to discharge proofs
-/
private meta def prove : tactic unit :=
assumption

private meta def post (s : simp_lemmas) (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
( do
    r ← mcond (is_prop e) (return `iff) (return `eq),
    (new_e, pr) ← s.rewrite e prove r,
    pr ← match r with
    |`iff := mk_app `propext [pr]
    | _   := return pr
    end,
    return ((), new_e, pr)
) <|> ( do
  (a, new_e, pr) ← heur () e,
  return (a, new_e, pr)
)

/-
Core function
-/
meta def derive (e : expr) : tactic (expr × expr) :=
do
    s ← get_cache,
    e ← instantiate_mvars e,
    let cfg : simp_config := {fail_if_unchanged := ff},

    -- step 1: casts are moved upwards and eliminated
    ((), new_e, pr1) ← simplify_bottom_up ()
        (post s) e cfg,

    -- step 2: casts are squashed
    s ← squash_cast_attr.get_cache,
    (new_e, pr2) ← simplify s [] new_e cfg,

    guard (¬ new_e =ₐ e),
    pr ← mk_eq_trans pr1 pr2,
    return (new_e, pr)

end norm_cast

namespace tactic
open tactic expr
open norm_cast

private meta def aux_mod_cast (e : expr) (include_goal : bool := tt) : tactic expr :=
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
As opposed to simp, norm_cast can be used without necessarily
closing the goal.
-/
meta def norm_cast (loc : parse location) : tactic unit :=
do
    ns ← loc.get_locals,
    tt ← replace_at derive ns loc.include_goal
        | fail "norm_cast failed to simplify",
    when loc.include_goal $ try tactic.reflexivity,
    when loc.include_goal $ try tactic.triv,
    when (¬ ns.empty) $ try tactic.contradiction

/--
Rewrite with the given rule and normalize casts between steps.
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
Normalize the goal and the given expression,
then close the goal with exact.
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
Normalize the goal and the given expression,
then apply the expression to the goal.
-/
meta def apply_mod_cast (e : parse texpr) : tactic unit :=
do
    e ← i_to_expr_for_apply e,
    concat_tags $ tactic.apply_mod_cast e

/--
Normalize the goal and every expression in the local context,
then close the goal with assumption.
-/
meta def assumption_mod_cast : tactic unit :=
tactic.assumption_mod_cast

end tactic.interactive

namespace conv.interactive
open conv tactic tactic.interactive interactive interactive.types
open norm_cast (derive)

meta def norm_cast : conv unit := replace_lhs derive

end conv.interactive

@[elim_cast] lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x := λ _ _, iff.rfl
@[elim_cast] lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x := λ _ _, iff.rfl
@[elim_cast] lemma ne_from_not_eq {α} : ∀ (x y : α), x ≠ y ↔ ¬(x = y) := λ _ _, iff.rfl

attribute [squash_cast] int.coe_nat_zero
attribute [squash_cast] int.coe_nat_one

attribute [elim_cast] int.nat_abs_of_nat

attribute [move_cast] int.coe_nat_succ
attribute [move_cast] int.coe_nat_add
attribute [move_cast] int.coe_nat_sub
attribute [move_cast] int.coe_nat_mul

@[move_cast] lemma ite_cast {α β : Type} [has_coe α β]
    {c : Prop} [decidable c] {a b : α} :
    ↑(ite c a b) = ite c (↑a : β) (↑b : β) :=
by by_cases h : c; simp [h]
