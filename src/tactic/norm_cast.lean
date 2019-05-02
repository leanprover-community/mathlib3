/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine

Normalizing casts in arithmetic expressions.
-/

import tactic.basic tactic.interactive tactic.converter.interactive
import data.complex.basic data.nat.enat

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


namespace norm_cast
open tactic expr

private meta def new_name : name → name
| name.anonymous        := name.mk_string "norm_cast" name.anonymous
| (name.mk_string s n)  := name.mk_string s (new_name n)
| (name.mk_numeral i n) := name.mk_numeral i (new_name n)

/-
let ty an expression of the shape Π (x1 : t1) ... (x2 : tn), a = b
let e an expression of type ty
then flip_equation ty returns a couple (new_ty, f) such that
    new_ty = Π A1 .. An, b = a
    f e = λ (x1 : t1) ... (xn : tn), eq.symm (e x1 ... xn)
if ty is not of the correct shape, then the tactic fails
-/
private meta def flip_equation : expr → tactic (expr × (expr → expr))
| (pi n bi d b) := do
    (ty, f) ← flip_equation $ instantiate_var b (local_const n n bi d),
    return $ (
        pi n bi d $ abstract_local ty n,
        λ e, lam n bi d $ abstract_local ( f $ e (local_const n n bi d) ) n
    )
| ty := do
    `(%%a = %%b) ← return ty | failure,
    α ← infer_type a,
    symm ← to_expr ``(@eq.symm %%α %%a %%b),
    new_ty ← to_expr ``(%%b = %%a),
    return (new_ty, symm)

private meta def after_set (decl : name) (prio : ℕ) (pers : bool) : tactic unit :=
do
    (declaration.thm n l ty task_e) ← get_decl decl | failed,
    let new_n := new_name n,
    ( do
        /-
        equation lemmas have to be flipped before
        being added to the set of norm_cast lemmas
        -/
        (new_ty, f) ← flip_equation ty,
        let task_new_e := task.map f task_e,
        add_decl (declaration.thm new_n l new_ty task_new_e)
    ) <|> ( do
        add_decl (declaration.thm new_n l ty task_e)
    )

private meta def mk_cache : list name → tactic simp_lemmas :=
monad.foldl (λ s, s.add_simp ∘ new_name) simp_lemmas.mk

/--
This is an attribute for simplification rules that are going to be
used to normalize casts.

Equation lemmas are compositional lemmas of the shape
    Π ..., ↑(P a1 ... an) = P ↑a1 ... ↑an
Equivalence lemmas are of the shape
    Π ..., P ↑a ↑b ↔ P a b

Note that the goal of normalization is to move casts "upwards" in the
expression, but compositional rules are written in a "downwards"
fashion.
-/
@[user_attribute]
meta def norm_cast_attr : user_attribute simp_lemmas :=
{
    name      := `norm_cast,
    descr     := "attribute for cast normalization",
    after_set := some after_set,
    cache_cfg := {
        mk_cache     := mk_cache,
        dependencies := [],
    }
}

/--
This is an attribute given to the lemmas of the shape
Π ..., ↑↑a = ↑a or  Π ..., ↑a = a

They are used in a heuristic to infer intermediate casts.
-/
@[user_attribute]
meta def simp_cast_attr : user_attribute simp_lemmas :=
{
    name      := `simp_cast,
    descr     := "attribute for cast simplification",
    after_set := none,
    cache_cfg := {
        mk_cache     := monad.foldl simp_lemmas.add_simp simp_lemmas.mk,
        dependencies := [],
    }
}

/-
This is an auxiliary function that proves e = new_e
using only simp_cast lemmas
-/
private meta def aux_simp (e new_e : expr) : tactic expr :=
do
    s ← simp_cast_attr.get_cache,
    (e', pr) ← s.rewrite new_e,
    is_def_eq e e',
    mk_eq_symm pr

/-
This is the main heuristic used alongside the norm_cast lemmas.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten as:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when the simp_cast lemmas can prove that (↑(x : α) : γ) = (↑(↑(x : α) : β) : γ)
-/
private meta def heur (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
match e with
| (app (expr.app op x) y) :=
do
    `(@coe %%α %%δ %%coe1 %%xx) ← return x,
    `(@coe %%β %%γ %%coe2 %%yy) ← return y,
    success_if_fail $ is_def_eq α β,
    is_def_eq δ γ,

    (do
        coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance',
        new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
        let new_e := app (app op new_x) y,
        eq_x ← aux_simp x new_x,
        pr ← mk_congr_arg op eq_x,
        pr ← mk_congr_fun pr y,
        return ((), new_e, pr)
    ) <|> (do
        coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance',
        new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
        let new_e := app (app op x) new_y,
        eq_y ← aux_simp y new_y,
        pr ← mk_congr_arg (app op x) eq_y,
        return ((), new_e, pr)
    )
| _ := failed
end

-- simpa is used to discharge proofs
private meta def prove : tactic unit :=
tactic.interactive.simpa none ff [] [] none

private meta def post (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
    s ← norm_cast_attr.get_cache,
    r ← mcond (is_prop e) (return `iff) (return `eq),
    (new_e, pr) ← s.rewrite e prove r,
    pr ← match r with
    |`iff := mk_app `propext [pr]
    | _   := return pr
    end,
    return ((), new_e, pr)

/-
This is a function to pre-process numerals:
- (1 : α) is rewritten as ((1 : ℕ) : α)
- (0 : α) is rewritten as ((0 : ℕ) : α)
-/
private meta def aux_num (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
match e with
| `(0 : ℕ) := failed
| `(1 : ℕ) := failed
| `(@has_zero.zero %%α %%h) := do
    coe_nat ← to_expr ``(has_lift_t ℕ %%α) >>= mk_instance',
    new_e ← to_expr ``(@coe ℕ %%α %%coe_nat 0),
    pr ← aux_simp e new_e,
    return ((), new_e, pr)
| `(@has_one.one %%α %%h) := do
    coe_nat ← to_expr ``(has_lift_t ℕ %%α) >>= mk_instance',
    new_e ← to_expr ``(@coe ℕ %%α %%coe_nat 1),
    pr ← aux_simp e new_e,
    return ((), new_e, pr)
| _ := failed
end

/-
Core function
-/
meta def derive (e : expr) : tactic (expr × expr) :=
do
    e ← instantiate_mvars e,
    let cfg : simp_config := {fail_if_unchanged := ff},

    -- step 1: pre-processing numerals
    ((), new_e, pr1) ← simplify_bottom_up () aux_num e cfg,

    -- step 2: casts are moved outwards as much as possible using norm_cast lemmas
    ((), new_e, pr2) ← simplify_bottom_up () (λ a e, post a e <|> heur a e) new_e cfg,

    -- step 3: casts are simplified using simp_cast lemmas
    s ← simp_cast_attr.get_cache,
    (new_e, pr3) ← simplify s [] new_e cfg,

    guard (¬ new_e =ₐ e),
    pr ← mk_eq_trans pr2 pr3 >>= mk_eq_trans pr1,
    return (new_e, pr)

end norm_cast


namespace tactic
open tactic expr
open norm_cast

private meta def aux_mod_cast (e : expr) : tactic expr :=
match e with
| local_const _ lc _ _ := do
    e ← get_local lc,
    replace_at derive [e] tt,
    get_local lc
| e := do
    t ← infer_type e,
    e ← assertv `this t e,
    replace_at derive [e] tt,
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
    ctx ← local_context,
    replace_at derive ctx tt,
    assumption
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
Normalize the goal and the givin expression,
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

/- simp_cast lemmas -/

attribute [simp_cast] nat.cast_zero
attribute [simp_cast] int.coe_nat_zero
attribute [simp_cast] int.cast_zero
attribute [simp_cast] rat.cast_zero
attribute [simp_cast] complex.of_real_zero

attribute [simp_cast] nat.cast_one
attribute [simp_cast] int.coe_nat_one
attribute [simp_cast] int.cast_one
attribute [simp_cast] rat.cast_one
attribute [simp_cast] complex.of_real_one

attribute [simp_cast] nat.cast_id
attribute [simp_cast] int.cast_id
attribute [simp_cast] rat.cast_id

attribute [simp_cast] int.cast_coe_nat
attribute [simp_cast] int.cast_coe_nat'
attribute [simp_cast] rat.cast_coe_nat
attribute [simp_cast] rat.cast_coe_int
attribute [simp_cast] complex.of_real_int_cast
attribute [simp_cast] complex.of_real_nat_cast
attribute [simp_cast] complex.of_real_rat_cast

attribute [simp_cast] enat.coe_zero
attribute [simp_cast] enat.coe_one
attribute [simp_cast] enat.coe_get

attribute [simp_cast] rat.coe_nat_num
attribute [simp_cast] rat.coe_int_num
attribute [simp_cast] rat.coe_nat_denom

/- compositional norm_cast lemmas -/

attribute [norm_cast] nat.cast_succ
attribute [norm_cast] int.coe_nat_succ

attribute [norm_cast] nat.cast_add
attribute [norm_cast] int.coe_nat_add
attribute [norm_cast] int.cast_add
attribute [norm_cast] rat.cast_add
attribute [norm_cast] complex.of_real_add
attribute [norm_cast] enat.coe_add

attribute [norm_cast] int.cast_neg_succ_of_nat
attribute [norm_cast] int.cast_neg_of_nat
attribute [norm_cast] int.cast_neg
attribute [norm_cast] rat.cast_neg
attribute [norm_cast] complex.of_real_neg

attribute [norm_cast] nat.cast_sub
attribute [norm_cast] int.cast_sub_nat_nat
attribute [norm_cast] int.coe_nat_sub
attribute [norm_cast] int.cast_sub
attribute [norm_cast] rat.cast_sub
attribute [norm_cast] complex.of_real_sub

attribute [norm_cast] nat.cast_mul
attribute [norm_cast] int.coe_nat_mul
attribute [norm_cast] int.cast_mul
attribute [norm_cast] rat.cast_mul
attribute [norm_cast] complex.of_real_mul

attribute [norm_cast] rat.cast_inv
attribute [norm_cast] complex.of_real_inv

attribute [norm_cast] int.coe_nat_div
attribute [norm_cast] rat.cast_div
attribute [norm_cast] complex.of_real_div

attribute [norm_cast] nat.cast_min
attribute [norm_cast] int.cast_min
attribute [norm_cast] rat.cast_min

attribute [norm_cast] nat.cast_max
attribute [norm_cast] int.cast_max
attribute [norm_cast] rat.cast_max

attribute [norm_cast] int.coe_nat_abs
attribute [norm_cast] int.cast_abs
attribute [norm_cast] rat.cast_abs

attribute [norm_cast] nat.cast_pow
attribute [norm_cast] int.coe_nat_pow
attribute [norm_cast] int.cast_pow
attribute [norm_cast] rat.cast_pow
attribute [norm_cast] complex.of_real_pow
attribute [norm_cast] complex.of_real_fpow

attribute [norm_cast] nat.cast_bit0
@[norm_cast] lemma int.coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := by {unfold bit0, simp}
attribute [norm_cast] int.cast_bit0
attribute [norm_cast] rat.cast_bit0
attribute [norm_cast] complex.of_real_bit0

attribute [norm_cast] nat.cast_bit1
@[norm_cast] lemma int.coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := by {unfold bit1, unfold bit0, simp}
attribute [norm_cast] int.cast_bit1
attribute [norm_cast] rat.cast_bit1
attribute [norm_cast] complex.of_real_bit1

@[norm_cast]
lemma ite_lemma {α β : Type} [has_coe α β] {c : Prop} [decidable c] {a b : α} :
    ↑(ite c a b) = ite c (↑a : β) (↑b : β) :=
if h : c then
    by simp [h]
else
    by simp [h]

/- equivalence norm_cast lemmas -/

attribute [norm_cast] nat.cast_inj
attribute [norm_cast] int.coe_nat_inj'
attribute [norm_cast] int.cast_inj
attribute [norm_cast] rat.cast_inj
attribute [norm_cast] complex.of_real_inj

attribute [norm_cast] nat.cast_le
attribute [norm_cast] int.coe_nat_le
attribute [norm_cast] int.cast_le
attribute [norm_cast] rat.cast_le
attribute [norm_cast] enat.coe_le_coe

attribute [norm_cast] nat.cast_lt
attribute [norm_cast] int.coe_nat_lt
attribute [norm_cast] int.cast_lt
attribute [norm_cast] rat.cast_lt
attribute [norm_cast] enat.coe_lt_coe

attribute [norm_cast] int.coe_nat_dvd

/- special lemmas to unfold ≥, > and ≠ -/

@[norm_cast] lemma ge_from_le {α} [has_le α] : ∀ (x y : α), x ≥ y ↔ y ≤ x := by simp
@[norm_cast] lemma gt_from_lt {α} [has_lt α] : ∀ (x y : α), x > y ↔ y < x := by simp
@[norm_cast] lemma ne_from_not_eq {α} : ∀ (x y : α), x ≠ y ↔ ¬(x = y) := by simp
