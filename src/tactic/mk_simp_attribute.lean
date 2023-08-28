/-
Copyright (c) 2019 Rob Lewis All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Lewis
-/
import tactic.doc_commands
/-!
# User command to register `simp` attributes

In this file we define a command `mk_simp_attribute` that can be used to register `simp` sets.  We
also define all `simp` attributes that are used in the library and tag lemmas from Lean core with
these attributes.
-/

/-!
### User command
-/

section cmd

open interactive lean lean.parser

namespace tactic

/--
The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.

This command is preferred to using ``run_cmd mk_simp_attr `simp_name`` since it adds a doc string
to the attribute that is defined. If you need to create a simp set in a file where this command is
not available, you should use
```lean
run_cmd mk_simp_attr `simp_name
run_cmd add_doc_string `simp_attr.simp_name "Description of the simp set here"
```
-/
@[user_command]
meta def mk_simp_attribute_cmd (_ : parse $ tk "mk_simp_attribute") : lean.parser unit :=
do n ← ident,
   d ← parser.pexpr,
   d ← to_expr ``(%%d : option string),
   descr ← eval_expr (option string) d,
   with_list ← (tk "with" *> many ident) <|> return [],
   mk_simp_attr n with_list,
   add_doc_string (name.append `simp_attr n) $ descr.get_or_else $ "simp set for " ++ to_string n

add_tactic_doc
{ name                     := "mk_simp_attribute",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.mk_simp_attribute_cmd],
  tags                     := ["simplification"] }

end tactic

end cmd

/-!
### Attributes
-/

mk_simp_attribute equiv_rw_simp "The simpset `equiv_rw_simp` is used by the tactic `equiv_rw` to
simplify applications of equivalences and their inverses."

mk_simp_attribute field_simps "The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free."

mk_simp_attribute functor_norm "Simp set for functor_norm"

attribute [functor_norm] bind_assoc pure_bind bind_pure

mk_simp_attribute ghost_simps "Simplification rules for ghost equations"

mk_simp_attribute integral_simps "Simp set for integral rules."

mk_simp_attribute is_R_or_C_simps "Simp attribute for lemmas about `is_R_or_C`"

mk_simp_attribute mfld_simps "The simpset `mfld_simps` records several simp lemmas that are
especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
readability.

The typical use case is the following, in a file on manifolds:
If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste
its output. The list of lemmas should be reasonable (contrary to the output of
`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
enough.
"

attribute [mfld_simps] id.def function.comp.left_id set.mem_set_of_eq and_true true_and
  function.comp_app and_self eq_self_iff_true function.comp.right_id not_false_iff true_or or_true

mk_simp_attribute monad_norm none with functor_norm

mk_simp_attribute nontriviality "Simp lemmas for `nontriviality` tactic"

mk_simp_attribute parity_simps "Simp attribute for lemmas about `even`"

mk_simp_attribute push_cast "The `push_cast` simp attribute uses `norm_cast` lemmas
to move casts toward the leaf nodes of the expression."

mk_simp_attribute split_if_reduction
  "Simp set for if-then-else statements, used in the `split_ifs` tactic"

attribute [split_if_reduction] if_pos if_neg dif_pos dif_neg if_congr

mk_simp_attribute transport_simps
"The simpset `transport_simps` is used by the tactic `transport`
to simplify certain expressions involving application of equivalences,
and trivial `eq.rec` or `ep.mpr` conversions.
It's probably best not to adjust it without understanding the algorithm used by `transport`."

attribute [transport_simps] cast_eq

mk_simp_attribute typevec "simp set for the manipulation of typevec and arrow expressions"
