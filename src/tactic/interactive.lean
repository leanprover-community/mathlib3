
/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Sebastien Gouezel, Scott Morrison
-/
import tactic.lint

open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
namespace interactive
open interactive interactive.types expr

/-- Similar to `constructor`, but does not reorder goals. -/
meta def fconstructor : tactic unit := concat_tags tactic.fconstructor

/-- `try_for n { tac }` executes `tac` for `n` ticks, otherwise uses `sorry` to close the goal.
Never fails. Useful for debugging. -/
meta def try_for (max : parse parser.pexpr) (tac : itactic) : tactic unit :=
do max ← i_to_expr_strict max >>= tactic.eval_expr nat,
  λ s, match _root_.try_for max (tac s) with
  | some r := r
  | none   := (tactic.trace "try_for timeout, using sorry" >> admit) s
  end

/-- Multiple subst. `substs x y z` is the same as `subst x, subst y, subst z`. -/
meta def substs (l : parse ident*) : tactic unit :=
l.mmap' (λ h, get_local h >>= tactic.subst) >> try (tactic.reflexivity reducible)

/-- Unfold coercion-related definitions -/
meta def unfold_coes (loc : parse location) : tactic unit :=
unfold [
  ``coe, ``coe_t, ``has_coe_t.coe, ``coe_b,``has_coe.coe,
  ``lift, ``has_lift.lift, ``lift_t, ``has_lift_t.lift,
  ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe] loc

/-- Unfold auxiliary definitions associated with the current declaration. -/
meta def unfold_aux : tactic unit :=
do tgt ← target,
   name ← decl_name,
   let to_unfold := (tgt.list_names_with_prefix name),
   guard (¬ to_unfold.empty),
   -- should we be using simp_lemmas.mk_default?
   simp_lemmas.mk.dsimplify to_unfold.to_list tgt >>= tactic.change

/-- For debugging only. This tactic checks the current state for any
missing dropped goals and restores them. Useful when there are no
goals to solve but "result contains meta-variables". -/
meta def recover : tactic unit :=
metavariables >>= tactic.set_goals

/-- Like `try { tac }`, but in the case of failure it continues
from the failure state instead of reverting to the original state. -/
meta def continue (tac : itactic) : tactic unit :=
λ s, result.cases_on (tac s)
 (λ a, result.success ())
 (λ e ref, result.success ())

/-- Move goal `n` to the front. -/
meta def swap (n := 2) : tactic unit :=
do gs ← get_goals,
   match gs.nth (n-1) with
   | (some g) := set_goals (g :: gs.remove_nth (n-1))
   | _        := skip
   end

/-- `rotate n` cyclically shifts the goals `n` times.
 `rotate` defaults to `rotate 1`. -/
meta def rotate (n := 1) : tactic unit := tactic.rotate n

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
meta def clear_ : tactic unit := tactic.repeat $ do
  l ← local_context,
  l.reverse.mfirst $ λ h, do
    name.mk_string s p ← return $ local_pp_name h,
    guard (s.front = '_'),
    cl ← infer_type h >>= is_class, guard (¬ cl),
    tactic.clear h

meta def apply_iff_congr_core : tactic unit :=
applyc ``iff_of_eq

meta def congr_core' : tactic unit :=
do tgt ← target,
   apply_eq_congr_core tgt
   <|> apply_heq_congr_core
   <|> apply_iff_congr_core
   <|> fail "congr tactic failed"

/--
Same as the `congr` tactic, but takes an optional argument which gives
the depth of recursive applications. This is useful when `congr`
is too aggressive in breaking down the goal. For example, given
`⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`. -/
meta def congr' : parse (with_desc "n" small_nat)? → tactic unit
| (some 0) := failed
| o        := focus1 (assumption <|> (congr_core' >>
  all_goals (reflexivity <|> `[apply proof_irrel_heq] <|>
             `[apply proof_irrel] <|> try (congr' (nat.pred <$> o)))))

/--
Acts like `have`, but removes a hypothesis with the same name as
this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
then after `replace h := f h` the goal will be `h : q ⊢ goal`,
where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
This can be used to simulate the `specialize` and `apply at` tactics
of Coq. -/
meta def replace (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
do let h := h.get_or_else `this,
  old ← try_core (get_local h),
  «have» h q₁ q₂,
  match old, q₂ with
  | none,   _      := skip
  | some o, some _ := tactic.clear o
  | some o, none   := swap >> tactic.clear o >> swap
  end

/-- Make every propositions in the context decidable -/
meta def classical := tactic.classical

private meta def generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"


private meta def generalize_arg_p : parser (pexpr × name) :=
with_desc "expr = id" $ parser.pexpr 0 >>= generalize_arg_p_aux

@[nolint def_lemma]
lemma {u} generalize_a_aux {α : Sort u}
  (h : ∀ x : Sort u, (α → x) → x) : α := h α id

/--
Like `generalize` but also considers assumptions
specified by the user. The user can also specify to
omit the goal.
-/
meta def generalize_hyp  (h : parse ident?) (_ : parse $ tk ":")
  (p : parse generalize_arg_p)
  (l : parse location) :
  tactic unit :=
do h' ← get_unused_name `h,
   x' ← get_unused_name `x,
   g ← if ¬ l.include_goal then
       do refine ``(generalize_a_aux _),
          some <$> (prod.mk <$> tactic.intro x' <*> tactic.intro h')
   else pure none,
   n ← l.get_locals >>= tactic.revert_lst,
   generalize h () p,
   intron n,
   match g with
     | some (x',h') :=
        do tactic.apply h',
           tactic.clear h',
           tactic.clear x'
     | none := return ()
   end

/--
Similar to `refine` but generates equality proof obligations
for every discrepancy between the goal and the type of the rule.
`convert e using n` (with `n : ℕ`) bounds the depth of the search
for discrepancies, analogous to `congr' n`.
-/
meta def convert (sym : parse (with_desc "←" (tk "<-")?)) (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
do v ← mk_mvar,
   if sym.is_some
     then refine ``(eq.mp %%v %%r)
     else refine ``(eq.mpr %%v %%r),
   gs ← get_goals,
   set_goals [v],
   try (congr' n),
   gs' ← get_goals,
   set_goals $ gs' ++ gs

meta def compact_decl_aux : list name → binder_info → expr → list expr → tactic (list (list name × binder_info × expr))
| ns bi t [] := pure [(ns.reverse, bi, t)]
| ns bi t (v'@(local_const n pp bi' t') :: xs) :=
  do t' ← infer_type v',
     if bi = bi' ∧ t = t'
       then compact_decl_aux (pp :: ns) bi t xs
       else do vs ← compact_decl_aux [pp] bi' t' xs,
               pure $ (ns.reverse, bi, t) :: vs
| ns bi t (_ :: xs) := compact_decl_aux ns bi t xs

meta def compact_decl : list expr → tactic (list (list name × binder_info × expr))
| [] := pure []
| (v@(local_const n pp bi t) :: xs)  :=
  do t ← infer_type v,
     compact_decl_aux [pp] bi t xs
| (_ :: xs) := compact_decl xs

meta def clean_ids : list name :=
[``id, ``id_rhs, ``id_delta, ``hidden]

/--
Remove identity functions from a term. These are normally
automatically generated with terms like `show t, from p` or
`(p : t)` which translate to some variant on `@id t p` in
order to retain the type. -/
meta def clean (q : parse texpr) : tactic unit :=
do tgt : expr ← target,
   e ← i_to_expr_strict ``(%%q : %%tgt),
   tactic.exact $ e.replace (λ e n,
     match e with
     | (app (app (const n _) _) e') :=
       if n ∈ clean_ids then some e' else none
     | (app (lam _ _ _ (var 0)) e') := some e'
     | _ := none
     end)

meta def source_fields (missing : list name) (e : pexpr) : tactic (list (name × pexpr)) :=
do e ← to_expr e,
   t ← infer_type e,
   let struct_n : name := t.get_app_fn.const_name,
   fields ← expanded_field_list struct_n,
   let exp_fields := fields.filter (λ x, x.2 ∈ missing),
   exp_fields.mmap $ λ ⟨p,n⟩,
     (prod.mk n ∘ to_pexpr) <$> mk_mapp (n.update_prefix p) [none,some e]

meta def collect_struct' : pexpr → state_t (list $ expr×structure_instance_info) tactic pexpr | e :=
do some str ← pure (e.get_structure_instance_info)
       | e.traverse collect_struct',
   v ← monad_lift mk_mvar,
   modify (list.cons (v,str)),
   pure $ to_pexpr v

meta def collect_struct (e : pexpr) : tactic $ pexpr × list (expr×structure_instance_info) :=
prod.map id list.reverse <$> (collect_struct' e).run []

meta def refine_one (str : structure_instance_info) :
  tactic $ list (expr×structure_instance_info) :=
do    tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      exp_fields ← expanded_field_list struct_n,
      let missing_f := exp_fields.filter (λ f, (f.2 : name) ∉ str.field_names),
      (src_field_names,src_field_vals) ← (@list.unzip name _ ∘ list.join) <$> str.sources.mmap (source_fields $ missing_f.map prod.snd),
      let provided  := exp_fields.filter (λ f, (f.2 : name) ∈ str.field_names),
      let missing_f' := missing_f.filter (λ x, x.2 ∉ src_field_names),
      vs ← mk_mvar_list missing_f'.length,
      (field_values,new_goals) ← list.unzip <$> (str.field_values.mmap collect_struct : tactic _),
      e' ← to_expr $ pexpr.mk_structure_instance
          { struct := some struct_n
          , field_names  := str.field_names  ++ missing_f'.map prod.snd ++ src_field_names
          , field_values := field_values ++ vs.map to_pexpr         ++ src_field_vals },
      tactic.exact e',
      gs ← with_enable_tags (
        mzip_with (λ (n : name × name) v, do
           set_goals [v],
           try (interactive.unfold (provided.map $ λ ⟨s,f⟩, f.update_prefix s) (loc.ns [none])),
           apply_auto_param
             <|> apply_opt_param
             <|> (set_main_tag [`_field,n.2,n.1]),
           get_goals)
        missing_f' vs),
      set_goals gs.join,
      return new_goals.join

meta def refine_recursively : expr × structure_instance_info → tactic (list expr) | (e,str) :=
do set_goals [e],
   rs ← refine_one str,
   gs ← get_goals,
   gs' ← rs.mmap refine_recursively,
   return $ gs'.join ++ gs


/--
`refine_struct { .. }` acts like `refine` but works only with structure instance
literals. It creates a goal for each missing field and tags it with the name of the
field so that `have_field` can be used to generically refer to the field currently
being refined.

As an example, we can use `refine_struct` to automate the construction semigroup
instances:
```
refine_struct ( { .. } : semigroup α ),
-- case semigroup, mul
-- α : Type u,
-- ⊢ α → α → α

-- case semigroup, mul_assoc
-- α : Type u,
-- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)
```
-/
meta def refine_struct : parse texpr → tactic unit | e :=
do (x,xs) ← collect_struct e,
   refine x,
   gs ← get_goals,
   xs' ← xs.mmap refine_recursively,
   set_goals (xs'.join ++ gs)

/--
`guard_hyp h := t` fails if the hypothesis `h` does not have type `t`.
We use this tactic for writing tests.
Fixes `guard_hyp` by instantiating meta variables
-/
meta def guard_hyp' (n : parse ident) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do h ← get_local n >>= infer_type >>= instantiate_mvars, guard_expr_eq h p

/--
`guard_expr_strict t := e` fails if the expr `t` is not equal to `e`. By contrast
to `guard_expr`, this tests strict (syntactic) equality.
We use this tactic for writing tests.
-/
meta def guard_expr_strict (t : expr) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do e ← to_expr p, guard (t = e)

/--
`guard_target_strict t` fails if the target of the main goal is not syntactically `t`.
We use this tactic for writing tests.
-/
meta def guard_target_strict (p : parse texpr) : tactic unit :=
do t ← target, guard_expr_strict t p


/--
`guard_hyp_strict h := t` fails if the hypothesis `h` does not have type syntactically equal
to `t`.
We use this tactic for writing tests.
-/
meta def guard_hyp_strict (n : parse ident) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do h ← get_local n >>= infer_type >>= instantiate_mvars, guard_expr_strict h p

meta def guard_hyp_nums (n : ℕ) : tactic unit :=
do k ← local_context,
   guard (n = k.length) <|> fail format!"{k.length} hypotheses found"

meta def guard_tags (tags : parse ident*) : tactic unit :=
do (t : list name) ← get_main_tag,
   guard (t = tags)

/-- `success_if_fail_with_msg { tac } msg` succeeds if the interactive tactic `tac` fails with
    error message `msg` (for test writing purposes). -/
meta def success_if_fail_with_msg (tac : tactic.interactive.itactic) :=
tactic.success_if_fail_with_msg tac

meta def get_current_field : tactic name :=
do [_,field,str] ← get_main_tag,
   expr.const_name <$> resolve_name (field.update_prefix str)

meta def field (n : parse ident) (tac : itactic) : tactic unit :=
do gs ← get_goals,
   ts ← gs.mmap get_tag,
   ([g],gs') ← pure $ (list.zip gs ts).partition (λ x, x.snd.nth 1 = some n),
   set_goals [g.1],
   tac, done,
   set_goals $ gs'.map prod.fst

/--
`have_field`, used after `refine_struct _` poses `field` as a local constant
with the type of the field of the current goal:

```
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```
-/
meta def have_field : tactic unit :=
propagate_tags $
get_current_field
>>= mk_const
>>= note `field none
>>  return ()

/-- `apply_field` functions as `have_field, apply field, clear field` -/
meta def apply_field : tactic unit :=
propagate_tags $
get_current_field >>= applyc

/--`apply_rules hs n`: apply the list of rules `hs` (given as pexpr) and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times.
`n` is 50 by default. `hs` can contain user attributes: in this case all theorems with this
attribute are added to the list of rules.

example, with or without user attribute:
```
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }

attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

lemma my_test {a b c d e : real} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules mono_rules
-- any of the following lines would also work:
-- add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3
-- by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]
-- by apply_rules [mono_rules]
```
-/
meta def apply_rules (hs : parse pexpr_list_or_texpr) (n : nat := 50) : tactic unit :=
tactic.apply_rules hs n

meta def return_cast (f : option expr) (t : option (expr × expr))
  (es : list (expr × expr × expr))
  (e x x' eq_h : expr) :
  tactic (option (expr × expr) × list (expr × expr × expr)) :=
(do guard (¬ e.has_var),
    unify x x',
    u ← mk_meta_univ,
    f ← f <|> mk_mapp ``_root_.id [(expr.sort u : expr)],
    t' ← infer_type e,
    some (f',t) ← pure t | return (some (f,t'), (e,x',eq_h) :: es),
    infer_type e >>= is_def_eq t,
    unify f f',
    return (some (f,t), (e,x',eq_h) :: es)) <|>
return (t, es)

meta def list_cast_of_aux (x : expr) (t : option (expr × expr))
  (es : list (expr × expr × expr)) :
  expr → tactic (option (expr × expr) × list (expr × expr × expr))
| e@`(cast %%eq_h %%x') := return_cast none t es e x x' eq_h
| e@`(eq.mp %%eq_h %%x') := return_cast none t es e x x' eq_h
| e@`(eq.mpr %%eq_h %%x') := mk_eq_symm eq_h >>= return_cast none t es e x x'
| e@`(@eq.subst %%α %%p %%a %%b  %%eq_h %%x') := return_cast p t es e x x' eq_h
| e@`(@eq.substr %%α %%p %%a %%b %%eq_h %%x') := mk_eq_symm eq_h >>= return_cast p t es e x x'
| e@`(@eq.rec %%α %%a %%f %%x' _  %%eq_h) := return_cast f t es e x x' eq_h
| e@`(@eq.rec_on %%α %%a %%f %%b  %%eq_h %%x') := return_cast f t es e x x' eq_h
| e := return (t,es)

meta def list_cast_of (x tgt : expr) : tactic (list (expr × expr × expr)) :=
(list.reverse ∘ prod.snd) <$> tgt.mfold (none, []) (λ e i es, list_cast_of_aux x es.1 es.2 e)

private meta def h_generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `heq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"

private meta def h_generalize_arg_p : parser (pexpr × name) :=
with_desc "expr == id" $ parser.pexpr 0 >>= h_generalize_arg_p_aux

/--
`h_generalize Hx : e == x` matches on `cast _ e` in the goal and replaces it with
`x`. It also adds `Hx : e == x` as an assumption. If `cast _ e` appears multiple
times (not necessarily with the same proof), they are all replaced by `x`. `cast`
`eq.mp`, `eq.mpr`, `eq.subst`, `eq.substr`, `eq.rec` and `eq.rec_on` are all treated
as casts.

`h_generalize Hx : e == x with h` adds hypothesis `α = β` with `e : α, x : β`.

`h_generalize Hx : e == x with _` chooses automatically chooses the name of
assumption `α = β`.

`h_generalize! Hx : e == x` reverts `Hx`.

when `Hx` is omitted, assumption `Hx : e == x` is not added.
-/
meta def h_generalize (rev : parse (tk "!")?)
     (h : parse ident_?)
     (_ : parse (tk ":"))
     (arg : parse h_generalize_arg_p)
     (eqs_h : parse ( (tk "with" >> pure <$> ident_) <|> pure [])) :
  tactic unit :=
do let (e,n) := arg,
   let h' := if h = `_ then none else h,
   h' ← (h' : tactic name) <|> get_unused_name ("h" ++ n.to_string : string),
   e ← to_expr e,
   tgt ← target,
   ((e,x,eq_h)::es) ← list_cast_of e tgt | fail "no cast found",
   interactive.generalize h' () (to_pexpr e, n),
   asm ← get_local h',
   v ← get_local n,
   hs ← es.mmap (λ ⟨e,_⟩, mk_app `eq [e,v]),
   (eqs_h.zip [e]).mmap' (λ ⟨h,e⟩, do
        h ← if h ≠ `_ then pure h else get_unused_name `h,
        () <$ note h none eq_h ),
   hs.mmap' (λ h,
     do h' ← assert `h h,
        tactic.exact asm,
        try (rewrite_target h'),
        tactic.clear h' ),
   when h.is_some (do
     (to_expr ``(heq_of_eq_rec_left %%eq_h %%asm)
       <|> to_expr ``(heq_of_eq_mp %%eq_h %%asm))
     >>= note h' none >> pure ()),
   tactic.clear asm,
   when rev.is_some (interactive.revert [n])

/-- `choose a b h using hyp` takes an hypothesis `hyp` of the form
`∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b` for some `P : X → Y → A → B → Prop` and outputs
into context a function `a : X → Y → A`, `b : X → Y → B` and a proposition `h` stating
`∀ (x : X) (y : Y), P x y (a x y) (b x y)`. It presumably also works with dependent versions.

Example:

```lean
example (h : ∀n m : ℕ, ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i := ℕ → ℕ → ℕ,
  guard_hyp j := ℕ → ℕ → ℕ,
  guard_hyp h := ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n,
  trivial
end
```
-/
meta def choose (first : parse ident) (names : parse ident*) (tgt : parse (tk "using" *> texpr)?) :
  tactic unit := do
tgt ← match tgt with
  | none := get_local `this
  | some e := tactic.i_to_expr_strict e
  end,
tactic.choose tgt (first :: names),
try (interactive.simp none tt [simp_arg_type.expr ``(exists_prop)] [] (loc.ns $ some <$> names)),
try (tactic.clear tgt)

/--
The goal of `field_simp` is to reduce an expression in a field to an expression of the form `n / d`
where neither `n` nor `d` contains any division symbol, just using the simplifier (with a carefully
crafted simpset named `field_simps`) to reduce the number of division symbols whenever possible by
iterating the following steps:

- write an inverse as a division
- in any product, move the division to the right
- if there are several divisions in a product, group them together at the end and write them as a
  single division
- reduce a sum to a common denominator

If the goal is an equality, this simpset will also clear the denominators, so that the proof
can normally be concluded by an application of `ring` or `ring_exp`.

`field_simp [hx, hy]` is a short form for `simp [-one_div_eq_inv, hx, hy] with field_simps`

Note that this naive algorithm will not try to detect common factors in denominators to reduce the
complexity of the resulting expression. Instead, it relies on the ability of `ring` to handle
complicated expressions in the next step.

As always with the simplifier, reduction steps will only be applied if the preconditions of the
lemmas can be checked. This means that proofs that denominators are nonzero should be included. The
fact that a product is nonzero when all factors are, and that a power of a nonzero number is
nonzero, are included in the simpset, but more complicated assertions (especially dealing with sums)
should be given explicitly. If your expression is not completely reduced by the simplifier
invocation, check the denominators of the resulting expression and provide proofs that they are
nonzero to enable further progress.

The invocation of `field_simp` removes the lemma `one_div_eq_inv` (which is marked as a simp lemma
in core) from the simpset, as this lemma works against the algorithm explained above.

For example,
```lean
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
  a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) :=
begin
  field_simp [hx, hy],
  ring
end
```
-/
meta def field_simp (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
let attr_names := `field_simps :: attr_names,
    hs := simp_arg_type.except `one_div_eq_inv :: hs in
propagate_tags (simp_core cfg.to_simp_config cfg.discharger no_dflt hs attr_names locat)

meta def guard_expr_eq' (t : expr) (p : parse $ tk ":=" *> texpr) : tactic unit :=
do e ← to_expr p, is_def_eq t e

/--
`guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
meta def guard_target' (p : parse texpr) : tactic unit :=
do t ← target, guard_expr_eq' t p

/--
a weaker version of `trivial` that tries to solve the goal by reflexivity or by reducing it to true,
unfolding only `reducible` constants. -/
meta def triv : tactic unit :=
tactic.triv' <|> tactic.reflexivity reducible <|> tactic.contradiction <|> fail "triv tactic failed"

/--
Similar to `existsi`. `use x` will instantiate the first term of an `∃` or `Σ` goal with `x`.
It will then try to close the new goal using `triv`, or try to simplify it by applying `exists_prop`.
Unlike `existsi`, `x` is elaborated with respect to the expected type.
`use` will alternatively take a list of terms `[x0, ..., xn]`.

`use` will work with constructors of arbitrary inductive types.

Examples:

example (α : Type) : ∃ S : set α, S = S :=
by use ∅

example : ∃ x : ℤ, x = x :=
by use 42

example : ∃ n > 0, n = n :=
begin
  use 1,
  -- goal is now 1 > 0 ∧ 1 = 1, whereas it would be ∃ (H : 1 > 0), 1 = 1 after existsi 1.
  exact ⟨zero_lt_one, rfl⟩,
end

example : ∃ a b c : ℤ, a + b + c = 6 :=
by use [1, 2, 3]

example : ∃ p : ℤ × ℤ, p.1 = 1 :=
by use ⟨1, 42⟩

example : Σ x y : ℤ, (ℤ × ℤ) × ℤ :=
by use [1, 2, 3, 4, 5]

inductive foo
| mk : ℕ → bool × ℕ → ℕ → foo

example : foo :=
by use [100, tt, 4, 3]
-/
meta def use (l : parse pexpr_list_or_texpr) : tactic unit :=
focus1 $
  tactic.use l;
  try (triv <|> (do
        `(Exists %%p) ← target,
        to_expr ``(exists_prop.mpr) >>= tactic.apply >> skip))

/--
`clear_aux_decl` clears every `aux_decl` in the local context for the current goal.
This includes the induction hypothesis when using the equation compiler and
`_let_match` and `_fun_match`.

It is useful when using a tactic such as `finish`, `simp *` or `subst` that may use these
auxiliary declarations, and produce an error saying the recursion is not well founded.
-/
meta def clear_aux_decl : tactic unit := tactic.clear_aux_decl

meta def loc.get_local_pp_names : loc → tactic (list name)
| loc.wildcard := list.map expr.local_pp_name <$> local_context
| (loc.ns l) := return l.reduce_option

meta def loc.get_local_uniq_names (l : loc) : tactic (list name) :=
list.map expr.local_uniq_name <$> l.get_locals

/--
The logic of `change x with y at l` fails when there are dependencies.
`change'` mimics the behavior of `change`, except in the case of `change x with y at l`.
In this case, it will correctly replace occurences of `x` with `y` at all possible hypotheses in `l`.
As long as `x` and `y` are defeq, it should never fail.
-/
meta def change' (q : parse texpr) : parse (tk "with" *> texpr)? → parse location → tactic unit
| none (loc.ns [none]) := do e ← i_to_expr q, change_core e none
| none (loc.ns [some h]) := do eq ← i_to_expr q, eh ← get_local h, change_core eq (some eh)
| none _ := fail "change-at does not support multiple locations"
| (some w) l :=
  do l' ← loc.get_local_pp_names l,
     l'.mmap' (λ e, try (change_with_at q w e)),
     when l.include_goal $ change q w (loc.ns [none])

meta def convert_to_core (r : pexpr) : tactic unit :=
do tgt ← target,
   h   ← to_expr ``(_ : %%tgt = %%r),
   rewrite_target h,
   swap

/--
`convert_to g using n` attempts to change the current goal to `g`,
using `congr' n` to resolve discrepancies.

`convert_to g` defaults to using `congr' 1`.
-/
meta def convert_to (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
match n with
  | none     := convert_to_core r >> `[congr' 1]
  | (some 0) := convert_to_core r
  | (some o) := convert_to_core r >> congr' o
end

/-- `ac_change g using n` is `convert_to g using n; try {ac_refl}` -/
meta def ac_change (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
convert_to r n; try ac_refl

private meta def opt_dir_with : parser (option (bool × name)) :=
(do tk "with",
   arrow ← (tk "<-")?,
   h ← ident,
   return (arrow.is_some, h)) <|> return none

/--
`set a := t with h` is a variant of `let a := t`.
It adds the hypothesis `h : a = t` to the local context and replaces `t` with `a` everywhere it can.
`set a := t with ←h` will add `h : t = a` instead.
`set! a := t with h` does not do any replacing.
-/
meta def set (h_simp : parse (tk "!")?) (a : parse ident) (tp : parse ((tk ":") >> texpr)?) (_ : parse (tk ":=")) (pv : parse texpr)
  (rev_name : parse opt_dir_with) :=
do let vt := match tp with | some t := t | none := pexpr.mk_placeholder end,
   let pv := ``(%%pv : %%vt),
   v ← to_expr pv,
   tp ← infer_type v,
   definev a tp v,
   when h_simp.is_none $ change' pv (some (expr.const a [])) loc.wildcard,
   match rev_name with
   | some (flip, id) :=
     do nv ← get_local a,
        pf ← to_expr (cond flip ``(%%pv = %%nv) ``(%%nv = %%pv)) >>= assert id,
        reflexivity
   | none := skip
   end

/--
`clear_except h₀ h₁` deletes all the assumptions it can except for `h₀` and `h₁`.
-/
meta def clear_except (xs : parse ident *) : tactic unit :=
do let ns := name_set.of_list xs,
   local_context >>= mmap' (λ h : expr,
     when (¬ ns.contains h.local_pp_name) $
       try $ tactic.clear h) ∘ list.reverse

meta def format_names (ns : list name) : format :=
format.join $ list.intersperse " " (ns.map to_fmt)

private meta def format_binders : list name × binder_info × expr → tactic format
| (ns, binder_info.default, t) := pformat!"({format_names ns} : {t})"
| (ns, binder_info.implicit, t) := pformat!"{{{format_names ns} : {t}}"
| (ns, binder_info.strict_implicit, t) := pformat!"⦃{format_names ns} : {t}⦄"
| ([n], binder_info.inst_implicit, t) :=
  if "_".is_prefix_of n.to_string
    then pformat!"[{t}]"
    else pformat!"[{format_names [n]} : {t}]"
| (ns, binder_info.inst_implicit, t) := pformat!"[{format_names ns} : {t}]"
| (ns, binder_info.aux_decl, t) := pformat!"({format_names ns} : {t})"

meta def mk_paragraph_aux (right_margin : ℕ) : format → format → ℕ → list format → format
| par ln len [] := par ++ format.line ++ ln
| par ln len (x :: xs) :=
  let len' := x.to_string.length in
  if len + len' ≤ right_margin then
    mk_paragraph_aux par (ln ++ x ++ " ") (len + len' + 1) xs
  else
    mk_paragraph_aux (par ++ format.line ++ ln) ("  " ++ x ++ " ") len' xs

/-- `mk_paragraph right_margin ls` packs `ls` into a paragraph where the lines have
length at most `right_margin` -/
meta def mk_paragraph (right_margin : ℕ) : list format → format :=
mk_paragraph_aux right_margin "" "" 0

/--
Format the current goal as a stand-alone example. Useful for testing tactic.

  * `extract_goal`: formats the statement as an `example` declaration
  * `extract_goal my_decl`: formats the statement as a `lemma` or `def` declaration
    called `my_decl`
  * `extract_goal with i j k:` only use local constants `i`, `j`, `k` in the declaration

Examples:

```lean
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
begin
  extract_goal,
     -- prints:
     -- example {i j k : ℕ} (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
     -- begin

     -- end
  extract_goal my_lemma
     -- lemma my_lemma {i j k : ℕ} (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
     -- begin

     -- end
end

example {i j k x y z w p q r m n : ℕ} (h₀ : i ≤ j) (h₁ : j ≤ k) (h₁ : k ≤ p) (h₁ : p ≤ q) : i ≤ k :=
begin
  extract_goal my_lemma,
    -- prints:
    -- lemma my_lemma {i j k x y z w p q r m n : ℕ} (h₀ : i ≤ j) (h₁ : j ≤ k)
    --   (h₁ : k ≤ p) (h₁ : p ≤ q) : i ≤ k :=
    -- begin

    -- end

  extract_goal my_lemma with i j k
    -- prints:
    -- lemma my_lemma {i j k : ℕ} : i ≤ k :=
    -- begin

    -- end
end
```

-/
meta def extract_goal (n : parse ident?) (vs : parse with_ident_list) : tactic unit :=
do (cxt,_) ← solve_aux `(true) $
       when (¬ vs.empty) (clear_except vs) >>
       local_context,
   tgt ← target,
   is_prop ← is_prop tgt,
   let title := match n, is_prop with
                | none, _ := to_fmt "example"
                | (some n), tt := format!"lemma {n}"
                | (some n), ff := format!"def {n}"
                end,
   cxt ← compact_decl cxt,
   cxt' ← cxt.init.mmap format_binders,
   cxt'' ← cxt.last'.traverse $ λ x, pformat!"{format_binders x} :",
   stmt ← pformat!"{tgt} :=",
   let fmt := mk_paragraph 80 $ title :: cxt' ++ [cxt''.get_or_else ":", stmt],
   trace fmt,
   trace!"begin\n  \nend"

/-- Turns a `nonempty α` instance into an `inhabited α` instance.
  If the target is a prop, this is done constructively;
  otherwise, it uses `classical.choice`. -/
meta def inhabit (t : parse parser.pexpr) (inst_name : parse ident?) : tactic unit :=
do ty ← i_to_expr t,
   nm ← get_unused_name `inst,
   mcond (target >>= is_prop)
   (do mk_mapp `nonempty.elim_to_inhabited [ty, none] >>= tactic.apply <|>
         fail "could not infer nonempty instance",
       introI $ inst_name.get_or_else nm)
   (do mk_mapp `classical.inhabited_of_nonempty' [ty, none] >>= note nm none <|>
         fail "could not infer nonempty instance",
       resetI)

/-- `revert_deps n₁ n₂ ...` reverts all the hypotheses that depend on one of `n₁, n₂, ...`
  It does not revert `n₁, n₂, ...` themselves (unless they depend on another `nᵢ`). -/
meta def revert_deps (ns : parse ident*) : tactic unit :=
propagate_tags $ ns.reverse.mmap' $ λ n, get_local n >>= tactic.revert_deps

/-- `revert_after n` reverts all the hypotheses after `n`. -/
meta def revert_after (n : parse ident) : tactic unit :=
propagate_tags $ get_local n >>= tactic.revert_after >> skip

/-- `clear_value n₁ n₂ ...` clears the bodies of the local definitions `n₁, n₂ ...`, changing them
  into regular hypotheses. A hypothesis `n : α := t` is changed to `n : α`. -/
meta def clear_value (ns : parse ident*) : tactic unit :=
propagate_tags $ ns.reverse.mmap' $ λ n, get_local n >>= tactic.clear_value

/--
`generalize' : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.

`generalize' h : e = x` in addition registers the hypothesis `h : e = x`.

`generalize'` is similar to `generalize`. The difference is that `generalize' : e = x` also succeeds when `e`
  does not occur in the goal. It is similar to `set`, but the resulting hypothesis `x` is not a local definition.
-/
meta def generalize' (h : parse ident?) (_ : parse $ tk ":") (p : parse generalize_arg_p) : tactic unit :=
propagate_tags $
do let (p, x) := p,
   e ← i_to_expr p,
   some h ← pure h | tactic.generalize' e x >> skip,
   tgt ← target,
   -- if generalizing fails, fall back to not replacing anything
   tgt' ← do {
     ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize' e x >> target),
     to_expr ``(Π x, %%e = x → %%(tgt'.binding_body.lift_vars 0 1))
   } <|> to_expr ``(Π x, %%e = x → %%tgt),
   t ← assert h tgt',
   swap,
   exact ``(%%t %%e rfl),
   intro x,
   intro h

end interactive
end tactic
