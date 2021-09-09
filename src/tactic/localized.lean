/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import tactic.core

/-!
# Localized notation

This consists of two user-commands which allow you to declare notation and commands localized to a
locale.

See the tactic doc entry below for more information.

The code is inspired by code from Gabriel Ebner from the
[hott3 repository](https://github.com/gebner/hott3).
-/

open lean lean.parser interactive tactic native

@[user_attribute]
meta def localized_attr : user_attribute (rb_lmap name string) unit := {
  name := "_localized",
  descr := "(interal) attribute that flags localized commands",
  parser := failed,
  cache_cfg := ⟨λ ns, (do dcls ← ns.mmap (λ n, mk_const n >>= eval_expr (name × string)),
                          return $ rb_lmap.of_list dcls), []⟩ }

/-- Get all commands in the given locale and return them as a list of strings -/
meta def get_localized (ns : list name) : tactic (list string) :=
do m ← localized_attr.get_cache,
   ns.mfoldl (λ l nm, match m.find nm with
   | [] := fail format!"locale {nm} does not exist"
   | new_l := return $ l.append new_l
   end) []

/-- Execute all commands in the given locale -/
@[user_command] meta def open_locale_cmd (_ : parse $ tk "open_locale") : parser unit :=
do ns ← many ident,
   cmds ← get_localized ns,
   cmds.mmap' emit_code_here

/-- Add a new command to a locale and execute it right now.
  The new command is added as a declaration to the environment with name `_localized_decl.<number>`.
  This declaration has attribute `_localized` and as value a name-string pair. -/
@[user_command] meta def localized_cmd (_ : parse $ tk "localized") : parser unit :=
do cmd ← parser.pexpr, cmd ← i_to_expr cmd, cmd ← eval_expr string cmd,
   let cmd := "local " ++ cmd,
   emit_code_here cmd,
   tk "in",
   nm ← ident,
   env ← get_env,
   let dummy_decl_name := mk_num_name `_localized_decl
     ((string.hash (cmd ++ nm.to_string) + env.fingerprint) % unsigned_sz),
   add_decl (declaration.defn dummy_decl_name [] `(name × string)
    (reflect (⟨nm, cmd⟩ : name × string)) (reducibility_hints.regular 1 tt) ff),
   localized_attr.set dummy_decl_name unit.star tt

/--
This consists of two user-commands which allow you to declare notation and commands localized to a
locale.

* Declare notation which is localized to a locale using:
```lean
localized "infix ` ⊹ `:60 := my_add" in my.add
```

* After this command it will be available in the same section/namespace/file, just as if you wrote
  `local infix ` ⊹ `:60 := my_add`

* You can open it in other places. The following command will declare the notation again as local
  notation in that section/namespace/file:
```lean
open_locale my.add
```

* More generally, the following will declare all localized notation in the specified locales.
```lean
open_locale locale1 locale2 ...
```

* You can also declare other localized commands, like local attributes
```lean
localized "attribute [simp] le_refl" in le
```

* To see all localized commands in a given locale, run:
```lean
run_cmd print_localized_commands [`my.add].
```

* To see a list of all locales with localized commands, run:
```lean
run_cmd do
  m ← localized_attr.get_cache,
  tactic.trace m.keys -- change to `tactic.trace m.to_list` to list all the commands in each locale
```

* Warning: You have to give full names of all declarations used in localized notation,
  so that the localized notation also works when the appropriate namespaces are not opened.
-/
add_tactic_doc
{ name                     := "localized notation",
  category                 := doc_category.cmd,
  decl_names               := [`localized_cmd, `open_locale_cmd],
  tags                     := ["notation", "type classes"] }

/-- Print all commands in a given locale -/
meta def print_localized_commands (ns : list name) : tactic unit :=
do cmds ← get_localized ns, cmds.mmap' trace

-- you can run `open_locale classical` to get the decidability of all propositions, and downgrade
-- the priority of decidability instances that make Lean run through all the algebraic hierarchy
-- whenever it wants to solve a decidability question
localized "attribute [instance, priority 9] classical.prop_decidable" in classical
localized "attribute [instance, priority 8] eq.decidable decidable_eq_of_decidable_le" in classical


localized "postfix `?`:9001 := optional" in parser
localized "postfix *:9001 := lean.parser.many" in parser
