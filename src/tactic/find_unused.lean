/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.core

/-!
This is a development file. When writing a new theory one often tries
multiple variations of the same definitions: `foo`, `foo'`, `foo₂`,
`foo₃`, etc. Once the main definition or theorem has been written,
it's time to clean up and the file can contain a lot of dead code.
Mark the main declarations with `@[main_declaration]` and
`#list_unused_decls` will show the redundancy.

Some of the so-called "unused" declarations may turn out to be useful
after all. The oversight can be corrected by marking those as
`@[main_declaration]`, `#list_unused_decls` will revise the list of
unused declarations. By default, the list of unused declarations will
not include any dependency of the main declarations.

The `@[main_declaration]` attribute should be removed before submitting
code to mathlib as it is merely a tool for cleaning up a module.
-/

namespace tactic

/-- Attribute `needed` is used to mark declarations that are featured
in the current file.  Then, the `#unneeded` command can be used to
list the declaration present in the file that do not support the main
features of the file. -/
@[user_attribute]
meta def main_declaration_attr : user_attribute :=
{ name := `main_declaration,
  descr := "tag essential declarations to help identify unused definitions" }

/-- `update_unsed_decls_list n m` removes from the map of unneeded declarations those
referenced by declaration named `n` which is considerred to be a
main declaration -/
private meta def update_unsed_decls_list : name → name_map declaration → tactic (name_map declaration)
| n m :=
  do d ← get_decl n,
     if m.contains n then do
       let m := m.erase n,
       let ns := d.value.list_constant.union d.type.list_constant,
       ns.mfold m update_unsed_decls_list
     else pure m

/-- In the current file, list all the declaration that are not marked as `@[needed]` and
that are not referenced by such declarations -/
meta def all_unused : tactic (name_map declaration) :=
do ds ← local_decls,
   ls ← ds.keys.mfilter (succeeds ∘ user_attribute.get_param_untyped main_declaration_attr),
   ds ← ls.mfoldl (flip update_unsed_decls_list) ds,
   ds.mfilter $ λ n d, do
     e ← get_env,
     return $ !d.is_auto_or_internal e

setup_tactic_parser

/-- The command `#list_unused_decls` lists the declarations that do not support the main features of
the present file. The main features of a file are taken as the declaration tagged with @[needed]. -/
@[user_command]
meta def unused_decls_cmd (_ : parse $ tk "#list_unused_decls") : lean.parser unit :=
show tactic unit, from
do ds ← all_unused,
   ds.to_list.mmap' $ λ ⟨n,_⟩, trace!"#print {n}"

add_tactic_doc
{ name                     := "#list_unused_decls",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.unused_decls_cmd],
  tags                     := ["debugging"] }

end tactic
