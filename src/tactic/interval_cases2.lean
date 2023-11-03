/-
Copyright (c) 2022 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import tactic.norm_num

/-!
# Case bash on variables in finite intervals

This file provides the tactic `interval_cases'`. `interval_cases' n` will:
1. inspect hypotheses, looking for lower and upper bounds for `n` that are numeric literals
   (anything interpretable as an integer),
   and also make use of additional bounds for the type of `n`
   (for example if `n : ℕ`, then the bound `0 ≤ n` is automatically included).
2. from these bounds, determine the smallest interval containing `n`.
2. case split, creating goals for each value of `n` in this interval.

The variable `n` can belong to `ℕ`, `ℤ`, or `ℕ+`.
Only bounds on which `expr.to_int` succeeds will be considered.

You can also give additional bounds to consider using `interval_cases' n using [hl, hu]`.
-/

open set

namespace tactic

namespace interval_cases'

meta def normalize_ineq : expr → tactic (list expr)
| prf := do
  t ← infer_type prf,
  match t with
  | `(_ ∧ _) :=
    (++) <$> (mk_app ``and.left [prf] >>= normalize_ineq)
         <*> (mk_app ``and.right [prf] >>= normalize_ineq)
  | `(_ ≤ _) := pure [prf]
  | `(_ < _) := pure [prf]
  | `(_ > _) := pure <$> mk_app ``gt.lt [prf]
  | `(_ ≥ _) := pure <$> mk_app ``ge.le [prf]
  | `(¬ (_ ≤ _)) := mk_app ``lt_of_not_ge [prf] >>= normalize_ineq
  | `(¬ (_ < _)) := mk_app ``le_of_not_gt [prf] >>= normalize_ineq
  | `(¬ (_ ≥ _)) := mk_app ``lt_of_not_ge [prf] >>= normalize_ineq
  | `(¬ (_ > _)) := mk_app ``le_of_not_gt [prf] >>= normalize_ineq
  | _ := pure []
  end

/-- When an upper bound, `prf : (%%n < val)`. When a lower bound, `prf : (val ≤ %%n)`. -/
meta structure bound :=
(val : ℤ) (prf : expr)

meta def bound.max (b1 b2 : bound) : bound :=
if b1.val < b2.val then b2 else b1

meta def bound.min (b1 b2 : bound) : bound :=
if b1.val < b2.val then b1 else b2

/-- Look for upper bounds for `n` that are explicit integers. -/
meta def get_upper_bound (n : expr) (prf : expr) : tactic bound :=
do t ← infer_type prf,
   match t with
   | `(%%n' < %%b) :=
     do guard (n = n'),
        val ← b.to_int,
        pure $ bound.mk val prf
   | `(%%n' ≤ %%b) :=
     do guard (n = n'),
        val ← b.to_int,
        tn ← infer_type n,
        prf' ← match tn with
               | `(ℕ) := to_expr ``(nat.lt_add_one_iff.mpr %%prf)
               | `(ℕ+) := to_expr ``(pnat.lt_add_one_iff.mpr %%prf)
               | `(ℤ) := to_expr ``(int.lt_add_one_iff.mpr %%prf)
               | _ := failed
               end,
        pure $ bound.mk (val + 1) prf'
   | _ := failed
   end

/-- Look for lower bounds for `n` that are explicit integers. -/
meta def get_lower_bound (n : expr) (prf : expr) : tactic bound :=
do t ← infer_type prf,
   match t with
   | `(%%b ≤ %%n') :=
     do guard (n = n'),
        val ← b.to_int,
        pure $ bound.mk val prf
   | `(%%b < %%n') :=
     do guard (n = n'),
        val ← b.to_int,
        tn ← infer_type n,
        prf' ← match tn with
               | `(ℕ) := to_expr ``(nat.add_one_le_iff.mpr %%prf)
               | `(ℕ+) := to_expr ``(pnat.add_one_le_iff.mpr %%prf)
               | `(ℤ) := to_expr ``(int.add_one_le_iff.mpr %%prf)
               | _ := failed
               end,
        pure $ bound.mk (val + 1) prf'
   | _ := failed
   end

meta def additional_bounds (n : expr) : tactic (list expr) :=
do t ← infer_type n,
   match t with
   | `(ℕ) := pure <$> to_expr ``(zero_le %%n)
   | `(ℕ+) := pure <$> to_expr ``(pnat.one_le %%n)
   | _ := pure []
   end

/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
meta def get_bounds (n : expr) (hyps : list pexpr) : tactic (bound × bound) :=
do
  hyps ← monad.mapm to_expr hyps,
  hyps ← (++ hyps) <$> local_context,
  ineqs ← additional_bounds n,
  ineqs ← hyps.mfoldl (λ l h, (++ l) <$> normalize_ineq h) ineqs,
  --monad.mapm infer_type ineqs >>= trace ,
  ubounds ← list.reduce_option <$> monad.mapm (λ x, (try_core (get_upper_bound n x))) ineqs,
  lbounds ← list.reduce_option <$> monad.mapm (λ x, (try_core (get_lower_bound n x))) ineqs,
  match ubounds with
  | [] := fail "No upper bound located"
  | (u::us) :=
    match lbounds with
    | [] := fail "No lower bound located"
    | (l::ls) := pure (list.foldl bound.max l ls, list.foldl bound.min u us)
    end
  end

meta def int.to_pexpr : ℤ → pexpr
| (int.of_nat n) := nat.to_pexpr n
| -[1+n] := ``(- %%(nat.to_pexpr (n + 1)))

class has_exhaustible_ico (α : Type*) [preorder α] [has_add α] [has_one α] :=
(succ (n : α) {lo hi : α} (h : lo ≤ n ∧ n < hi) : n = lo ∨ lo + 1 ≤ n ∧ n < hi)

/-- The expressions produced by `has_exhaustible_ico` have a `lo + 1`, which needs to be
converted to a pure literal. -/
meta def int_norm (n : expr) (lo : ℤ) : tactic expr :=
do t ← infer_type n,
   to_expr ``(by norm_num : %%(int.to_pexpr lo) + (1 : %%t) = %%(int.to_pexpr (lo + 1)))

lemma rw_left_le {α : Type*} [preorder α] {x y z : α} (e : x = z) (h : x ≤ y) : z ≤ y := by rwa [←e]

/-- returns proof that `lo ≤ n ∧ n < hi → n = lo ∨ n = lo + 1 ∨ ... ∨ n = lo + (hi - 1) ∨ false`. -/
meta def mk_prop (n : expr) : ℤ → ℤ → tactic expr
| lo hi :=
do
  t ← infer_type n,
  let pelo := int.to_pexpr lo,
  let pehi := int.to_pexpr hi,
  if h : hi ≤ lo
  then do
    e ← to_expr ``(by norm_num : ¬ (%%pelo : %%t) < %%pehi),
    to_expr ``(λ (h : %%pelo ≤ %%n ∧ %%n < %%pehi), %%e (lt_of_le_of_lt h.1 h.2))
  else do
    pf ← mk_prop (lo + 1) hi,
    e ← int_norm n lo,
    p ← to_expr ``(λ (h : %%(int.to_pexpr lo) ≤ %%n ∧ %%n < %%(int.to_pexpr hi)),
      or.imp_right (λ x, %%pf (and.imp_left (rw_left_le %%e) x)) (has_exhaustible_ico.succ %%n h)),
    pure p

instance : has_exhaustible_ico ℕ :=
{ succ := λ n lo hi, begin
    obtain (rfl|h) := eq_or_ne n lo,
    simp,
    rw [ne.le_iff_lt h.symm, nat.add_one_le_iff],
    intro h,
    exact or.inr h,
  end }

instance : has_exhaustible_ico ℤ :=
{ succ := λ n lo hi, begin
    obtain (rfl|h) := eq_or_ne n lo,
    simp,
    rw [ne.le_iff_lt h.symm, int.add_one_le_iff],
    intro h,
    exact or.inr h,
  end }

instance : has_exhaustible_ico ℕ+ :=
{ succ := λ n lo hi, begin
    obtain (rfl|h) := eq_or_ne n lo,
    simp,
    rw [ne.le_iff_lt h.symm, pnat.add_one_le_iff],
    intro h,
    exact or.inr h,
  end }

/-- Take the disjunction produced by `mk_prop` then case split and substitute with it. -/
meta def cases_subst : expr → tactic unit
| e := do
  t ← infer_type e,
  match t with
  | `(false) := do h ← to_expr ``(false.elim %%e),
                   tactic.exact h
  | `(_ ∨ _) :=
    focus1 (do [(_, [a]), (_, [b])] ← tactic.cases e,
               focus' [try_core (subst a) >> pure (), cases_subst b])
  | _ := try_core (subst e) >> pure ()
  end

end interval_cases'

open interval_cases'

namespace interactive

setup_tactic_parser

/--
`interval_cases' n` searches for upper and lower bounds for an expression `n`,
and, if bounds are found, splits into separate cases for each possible value of `n`.

As an example, in
```lean
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases' n,
  all_goals { simp }
end
```
after `interval_cases' n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also give additional bounds to use as `interval_cases' n using [h1, h2, ...]`.
When processing bounds, they are normalized, and conjunctions are automatically split.
```lean
example (n : ℕ) (h : n ∈ set.Ico 1 4) : n * n < 16 :=
begin
  interval_cases' n using [set.mem_Ico.mp h]; norm_num
end
```

You can specify a name `h` for the new hypothesis,
as `interval_cases' n with h` or `interval_cases' n using [h1, h2, ...] with h`.
This is useful for when substitution fails, for example in the following:
```lean
example (n : ℕ) (f : ℕ → ℤ) (w₁ : f n > -2) (w₂ : f n < 2) : f n ∈ ({-1, 0, 1} : set ℤ) :=
begin
  interval_cases' f n with h,
  all_goals { simp [h] }
end
```
-/
meta def interval_cases' (n : parse texpr)
  (add_hyps : parse (tk "using" *> pexpr_list)?)
  (lname : parse (tk "with" *> ident)?) :
  tactic unit :=
do
  n ← to_expr n,

  (bl, bu) ← get_bounds n (option.get_or_else add_hyps []),
  /-trace bl.val,
  infer_type bl.prf >>= trace,
  trace bu.val,
  infer_type bu.prf >>= trace,-/

  nm ← if h : lname.is_some then pure $ option.get h else get_unused_name `this,
  p ← to_expr ``(and.intro %%bl.prf %%bu.prf) >>= note nm,

  a ← mk_prop n bl.val bu.val,
  p' ← to_expr ``(%%a %%p) >>= note nm,
  tactic.clear p,

  focus1 $ cases_subst p',

  pure ()

/--
`interval_cases' n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases' n,
  all_goals {simp}
end
```
after `interval_cases' n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also give additional bound to use, as `interval_cases n [h1, h2, ...]`.

You can also explicitly specify a name to use for the hypothesis added,
as `interval_cases n with hn` or `interval_cases n [h1, h2, ...] with hn`.

-/
add_tactic_doc
{ name       := "interval_cases'",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.interval_cases'],
  tags       := ["case bashing"] }

end interactive

end tactic
