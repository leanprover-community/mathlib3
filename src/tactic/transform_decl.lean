/-
Copyright (c) 2017 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import tactic.core

namespace tactic

/-- `copy_attribute' attr_name src tgt p d_name` copy (user) attribute `attr_name` from
   `src` to `tgt` if it is defined for `src`; unlike `copy_attribute` the primed version also copies
   the parameter of the user attribute, in the user attribute case. Make it persistent if `p` is
   `tt`; if `p` is `none`, the copied attribute is made persistent iff it is persistent on `src`  -/
meta def copy_attribute' (attr_name : name) (src : name) (tgt : name) (p : option bool := none) :
tactic unit := do
  get_decl tgt <|> fail!"unknown declaration {tgt}",
  -- if the source doesn't have the attribute we do not error and simply return
  mwhen (succeeds (has_attribute attr_name src)) $
    do (p', prio) ← has_attribute attr_name src,
      let p := p.get_or_else p',
      s ← try_or_report_error (set_basic_attribute attr_name tgt p prio),
      sum.inr msg ← return s | skip,
      if msg =
        (format!("set_basic_attribute tactic failed, '{attr_name}' " ++
          "is not a basic attribute")).to_string
      then do
        user_attr_const ← (get_user_attribute_name attr_name >>= mk_const),
        tac ← eval_pexpr (tactic unit)
        ``(user_attribute.get_param_untyped %%user_attr_const %%src >>=
          λ x, user_attribute.set_untyped %%user_attr_const %%tgt x %%p %%prio),
        tac
      else fail msg

open expr
/-- Auxilliary function for `additive_test`. The bool argument *only* matters when applied
to exactly a constant. -/
meta def additive_test_aux (f : name → option name) (ignore : name_map $ list ℕ) :
  bool → expr → bool
| b (var n)                := tt
| b (sort l)               := tt
| b (const n ls)           := b || (f n).is_some
| b (mvar n m t)           := tt
| b (local_const n m bi t) := tt
| b (app e f)              := additive_test_aux tt e &&
  -- this might be inefficient.
  -- If it becomes a performance problem: we can give this info for the recursive call to `e`.
    match ignore.find e.get_app_fn.const_name with
    | some l := if e.get_app_num_args + 1 ∈ l then tt else additive_test_aux ff f
    | none   := additive_test_aux ff f
    end
| b (lam n bi e t)         := additive_test_aux ff t
| b (pi n bi e t)          := additive_test_aux ff t
| b (elet n g e f)         := additive_test_aux ff e && additive_test_aux ff f
| b (macro d args)         := tt

/--
`additive_test f replace_all ignore e` tests whether the expression `e` contains no constant
`nm` that is not applied to any arguments, and such that `f nm = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additive_test` applied to their first argument returns `tt`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
`f` is the dictionary of declarations that are in the `to_additive` dictionary.
We ignore all arguments specified in the `name_map` `ignore`.
If `replace_all` is `tt` the test always return `tt`.
-/
meta def additive_test (f : name → option name) (replace_all : bool) (ignore : name_map $ list ℕ)
  (e : expr) : bool :=
if replace_all then tt else additive_test_aux f ignore ff e

/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the dictionary `f`.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
meta def transform_decl_with_prefix_fun_aux (f : name → option name)
  (replace_all trace : bool) (relevant : name_map ℕ) (ignore reorder : name_map $ list ℕ)
  (pre tgt_pre : name) : name → command :=
λ src,
do
  -- if this declaration is not `pre` or an internal declaration, we do nothing.
  tt ← return (src = pre ∨ src.is_internal : bool) |
    if (f src).is_some then skip else fail!("@[to_additive] failed.
The declaration {pre} depends on the declaration {src} which is in the namespace {pre}, but " ++
"does not have the `@[to_additive]` attribute. This is not supported. Workaround: move {src} to " ++
"a different namespace."),
  env ← get_env,
  -- we find the additive name of `src`
  let tgt := src.map_prefix (λ n, if n = pre then some tgt_pre else none),
  -- we skip if we already transformed this declaration before
  ff ← return $ env.contains tgt | skip,
  decl ← get_decl src,
  -- we first transform all the declarations of the form `pre._proof_i`
  (decl.type.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
  (decl.value.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
  -- we transform `decl` using `f` and the configuration options.
  let decl :=
    decl.update_with_fun env (name.map_prefix f) (additive_test f replace_all ignore)
      relevant reorder tgt,
  -- o ← get_options, set_options $ o.set_bool `pp.all tt, -- print with pp.all (for debugging)
  pp_decl ← pp decl,
  when trace $ trace!"[to_additive] > generating\n{pp_decl}",
  decorate_error (format!"@[to_additive] failed. Type mismatch in additive declaration.
For help, see the docstring of `to_additive.attr`, section `Troubleshooting`.
Failed to add declaration\n{pp_decl}

Nested error message:\n").to_string $ do {
    if env.is_protected src then add_protected_decl decl else add_decl decl,
    -- we test that the declaration value type-checks, so that we get the decorated error message
    -- without this line, the type-checking might fail outside the `decorate_error`.
    decorate_error "proof doesn't type-check. " $ type_check decl.value }

/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the function `f`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_fun (f : name → option name) (replace_all trace : bool)
  (relevant : name_map ℕ) (ignore reorder : name_map $ list ℕ) (src tgt : name) (attrs : list name)
  : command :=
do -- In order to ensure that attributes are copied correctly we must transform declarations and
   -- attributes in the right order:
   -- first generate the transformed main declaration
   transform_decl_with_prefix_fun_aux f replace_all trace relevant ignore reorder src tgt src,
   ls ← get_eqn_lemmas_for tt src,
   -- now transform all of the equational lemmas
   ls.mmap' $
    transform_decl_with_prefix_fun_aux f replace_all trace relevant ignore reorder src tgt,
   -- copy attributes for the equational lemmas so that they know if they are refl lemmas
   ls.mmap' (λ src_eqn, do
    let tgt_eqn := src_eqn.map_prefix (λ n, if n = src then some tgt else none),
    attrs.mmap' (λ n, copy_attribute' n src_eqn tgt_eqn)),
   -- set the transformed equation lemmas as equation lemmas for the new declaration
   ls.mmap' (λ src_eqn, do
    e ← get_env,
    let tgt_eqn := src_eqn.map_prefix (λ n, if n = src then some tgt else none),
    set_env (e.add_eqn_lemma tgt_eqn)),
   -- copy attributes for the main declaration, this needs the equational lemmas to exist already
   attrs.mmap' (λ n, copy_attribute' n src tgt)

/--
Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the dictionary `dict`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_dict (dict : name_map name) (replace_all trace : bool)
  (relevant : name_map ℕ) (ignore reorder : name_map $ list ℕ) (src tgt : name) (attrs : list name)
  : command :=
transform_decl_with_prefix_fun dict.find replace_all trace relevant ignore reorder src tgt attrs

end tactic
