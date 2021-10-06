/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import tactic.lint.basic

/-!
# Linter for simplification lemmas

This files defines several linters that prevent common mistakes when declaring simp lemmas:

 * `simp_nf` checks that the left-hand side of a simp lemma is not simplified by a different lemma.
 * `simp_var_head` checks that the head symbol of the left-hand side is not a variable.
 * `simp_comm` checks that commutativity lemmas are not marked as simplification lemmas.
-/

open tactic expr

/-- `simp_lhs_rhs ty` returns the left-hand and right-hand side of a simp lemma with type `ty`. -/
private meta def simp_lhs_rhs : expr → tactic (expr × expr) | ty := do
ty ← head_beta ty,
-- We only detect a fixed set of simp relations here.
-- This is somewhat justified since for a custom simp relation R,
-- the simp lemma `R a b` is implicitly converted to `R a b ↔ true` as well.
match ty with
| `(¬ %%lhs) := pure (lhs, `(false))
| `(%%lhs = %%rhs) := pure (lhs, rhs)
| `(%%lhs ↔ %%rhs) := pure (lhs, rhs)
| (expr.pi n bi a b) := do
  l ← mk_local' n bi a,
  simp_lhs_rhs (b.instantiate_var l)
| ty := pure (ty, `(true))
end

/-- `simp_lhs ty` returns the left-hand side of a simp lemma with type `ty`. -/
private meta def simp_lhs (ty : expr): tactic expr :=
prod.fst <$> simp_lhs_rhs ty

/--
`simp_is_conditional_core ty` returns `none` if `ty` is a conditional simp
lemma, and `some lhs` otherwise.
-/
private meta def simp_is_conditional_core : expr → tactic (option expr) | ty := do
ty ← head_beta ty,
match ty with
| `(¬ %%lhs) := pure lhs
| `(%%lhs = _) := pure lhs
| `(%%lhs ↔ _) := pure lhs
| (expr.pi n bi a b) := do
  l ← mk_local' n bi a,
  some lhs ← simp_is_conditional_core (b.instantiate_var l) | pure none,
  if bi ≠ binder_info.inst_implicit ∧
      ¬ (lhs.abstract_local l.local_uniq_name).has_var then
    pure none
  else
    pure lhs
| ty := pure ty
end

/--
`simp_is_conditional ty` returns true iff the simp lemma with type `ty` is conditional.
-/
private meta def simp_is_conditional (ty : expr) : tactic bool :=
option.is_none <$> simp_is_conditional_core ty

private meta def heuristic_simp_lemma_extraction (prf : expr) : tactic (list name) :=
prf.list_constant.to_list.mfilter is_simp_lemma

/-- Checks whether two expressions are equal for the simplifier. That is,
they are reducibly-definitional equal, and they have the same head symbol. -/
meta def is_simp_eq (a b : expr) : tactic bool :=
if a.get_app_fn.const_name ≠ b.get_app_fn.const_name then pure ff else
succeeds $ is_def_eq a b transparency.reducible

/-- Reports declarations that are simp lemmas whose left-hand side is not in simp-normal form. -/
meta def simp_nf_linter (timeout := 200000) (d : declaration) : tactic (option string) := do
tt ← is_simp_lemma d.to_name | pure none,
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
-- In this case, ignore the declaration if it is not a valid simp lemma by itself.
tt ← is_valid_simp_lemma_cnst d.to_name | pure none,
[] ← get_eqn_lemmas_for ff d.to_name | pure none,
try_for timeout $
retrieve $ do
g ← mk_meta_var d.type,
set_goals [g],
unfreezing intros,
(lhs, rhs) ← target >>= simp_lhs_rhs,
sls ← simp_lemmas.mk_default,
let sls' := sls.erase [d.to_name],
(lhs', prf1, ns1) ← decorate_error "simplify fails on left-hand side:" $
  simplify sls [] lhs {fail_if_unchanged := ff},
prf1_lems ← heuristic_simp_lemma_extraction prf1,
if d.to_name ∈ prf1_lems then pure none else do
is_cond ← simp_is_conditional d.type,
(rhs', prf2, ns2) ← decorate_error "simplify fails on right-hand side:" $
  simplify sls [] rhs {fail_if_unchanged := ff},
lhs'_eq_rhs' ← is_simp_eq lhs' rhs',
lhs_in_nf ← is_simp_eq lhs' lhs,
if lhs'_eq_rhs' then do
  used_lemmas ← heuristic_simp_lemma_extraction (prf1 prf2),
  pure $ pure $ "simp can prove this:\n"
    ++ "  by simp only " ++ to_string used_lemmas ++ "\n"
    ++ "One of the lemmas above could be a duplicate.\n"
    ++ "If that's not the case try reordering lemmas or adding @[priority].\n"
else if ¬ lhs_in_nf then do
  lhs ← pp lhs,
  lhs' ← pp lhs',
  pure $ format.to_string $
    to_fmt "Left-hand side simplifies from"
      ++ lhs.group.indent 2 ++ format.line
      ++ "to" ++ lhs'.group.indent 2 ++ format.line
      ++ "using " ++ (to_fmt prf1_lems).group.indent 2 ++ format.line
      ++ "Try to change the left-hand side to the simplified term!\n"
else if ¬ is_cond ∧ lhs = lhs' then
  pure $ some $ "Left-hand side does not simplify.\nYou need to debug this yourself using " ++
"`set_option trace.simplify.rewrite true`"
else
  pure none

/--
This note gives you some tips to debug any errors that the simp-normal form linter raises.

The reason that a lemma was considered faulty is because its left-hand side is not in simp-normal
form.
These lemmas are hence never used by the simplifier.

This linter gives you a list of other simp lemmas: look at them!

Here are some tips depending on the error raised by the linter:

  1. 'the left-hand side reduces to XYZ':
     you should probably use XYZ as the left-hand side.

  2. 'simp can prove this':
     This typically means that lemma is a duplicate, or is shadowed by another lemma:

     2a. Always put more general lemmas after specific ones:
      ```
      @[simp] lemma zero_add_zero : 0 + 0 = 0 := rfl
      @[simp] lemma add_zero : x + 0 = x := rfl
      ```

      And not the other way around!  The simplifier always picks the last matching lemma.

     2b. You can also use `@[priority]` instead of moving simp-lemmas around in the file.

      Tip: the default priority is 1000.
      Use `@[priority 1100]` instead of moving a lemma down,
      and `@[priority 900]` instead of moving a lemma up.

     2c. Conditional simp lemmas are tried last. If they are shadowed
         just remove the `simp` attribute.

     2d. If two lemmas are duplicates, the linter will complain about the first one.
         Try to fix the second one instead!
         (You can find it among the other simp lemmas the linter prints out!)

  3. 'try_for tactic failed, timeout':
     This typically means that there is a loop of simp lemmas.
     Try to apply squeeze_simp to the right-hand side (removing this lemma from the simp set) to see
     what lemmas might be causing the loop.

     Another trick is to `set_option trace.simplify.rewrite true` and
     then apply `try_for 10000 { simp }` to the right-hand side.  You will
     see a periodic sequence of lemma applications in the trace message.
-/
library_note "simp-normal form"

/-- A linter for simp lemmas whose lhs is not in simp-normal form, and which hence never fire. -/
@[linter] meta def linter.simp_nf : linter :=
{ test := simp_nf_linter,
  auto_decls := tt,
  no_errors_found := "All left-hand sides of simp lemmas are in simp-normal form.",
  errors_found := "SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.
see note [simp-normal form] for tips how to debug this.
https://leanprover-community.github.io/mathlib_docs/notes.html#simp-normal%20form" }

private meta def simp_var_head (d : declaration) : tactic (option string) := do
tt ← is_simp_lemma d.to_name | pure none,
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
-- In this case, ignore the declaration if it is not a valid simp lemma by itself.
tt ← is_valid_simp_lemma_cnst d.to_name | pure none,
lhs ← simp_lhs d.type,
head_sym@(expr.local_const _ _ _ _) ← pure lhs.get_app_fn | pure none,
head_sym ← pp head_sym,
pure $ format.to_string $ "Left-hand side has variable as head symbol: " ++ head_sym

/--
A linter for simp lemmas whose lhs has a variable as head symbol,
and which hence never fire.
-/
@[linter] meta def linter.simp_var_head : linter :=
{ test := simp_var_head,
  auto_decls := tt,
  no_errors_found :=
    "No left-hand sides of a simp lemma has a variable as head symbol.",
  errors_found := "LEFT-HAND SIDE HAS VARIABLE AS HEAD SYMBOL.\n" ++
    "Some simp lemmas have a variable as head symbol of the left-hand side:" }

private meta def simp_comm (d : declaration) : tactic (option string) := do
tt ← is_simp_lemma d.to_name | pure none,
-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
-- In this case, ignore the declaration if it is not a valid simp lemma by itself.
tt ← is_valid_simp_lemma_cnst d.to_name | pure none,
(lhs, rhs) ← simp_lhs_rhs d.type,
if lhs.get_app_fn.const_name ≠ rhs.get_app_fn.const_name then pure none else do
(lhs', rhs') ← (prod.snd <$> open_pis_metas d.type) >>= simp_lhs_rhs,
tt ← succeeds $ unify rhs lhs' transparency.reducible | pure none,
tt ← succeeds $ is_def_eq rhs lhs' transparency.reducible | pure none,
-- ensure that the second application makes progress:
ff ← succeeds $ unify lhs' rhs' transparency.reducible | pure none,
pure $ "should not be marked simp"

/-- A linter for commutativity lemmas that are marked simp. -/
@[linter] meta def linter.simp_comm : linter :=
{ test := simp_comm,
  auto_decls := tt,
  no_errors_found := "No commutativity lemma is marked simp.",
  errors_found := "COMMUTATIVITY LEMMA IS SIMP.\n" ++
    "Some commutativity lemmas are simp lemmas:" }
