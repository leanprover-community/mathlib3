/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.core

/-!
# list_unused_decls

`#list_unused_decls` is a command used for theory development.
When writing a new theory one often tries
multiple variations of the same definitions: `foo`, `foo'`, `foo₂`,
`foo₃`, etc. Once the main definition or theorem has been written,
it's time to clean up and the file can contain a lot of dead code.
Mark the main declarations with `@[main_declaration]` and
`#list_unused_decls` will show the declarations in the file
that are not needed to define the main declarations.

Some of the so-called "unused" declarations may turn out to be useful
after all. The oversight can be corrected by marking those as
`@[main_declaration]`. `#list_unused_decls` will revise the list of
unused declarations. By default, the list of unused declarations will
not include any dependency of the main declarations.

The `@[main_declaration]` attribute should be removed before submitting
code to mathlib as it is merely a tool for cleaning up a module.
-/

namespace tactic

/-- Attribute `main_declaration` is used to mark declarations that are featured
in the current file.  Then, the `#list_unused_decls` command can be used to
list the declaration present in the file that are not used by the main
declarations of the file. -/
@[user_attribute]
meta def main_declaration_attr : user_attribute :=
{ name := `main_declaration,
  descr := "tag essential declarations to help identify unused definitions" }

/-- `update_unsed_decls_list n m` removes from the map of unneeded declarations those
referenced by declaration named `n` which is considerred to be a
main declaration -/
private meta def update_unsed_decls_list :
  name → name_map declaration → tactic (name_map declaration)
| n m :=
  do d ← get_decl n,
     if m.contains n then do
       let m := m.erase n,
       let ns := d.value.list_constant.union d.type.list_constant,
       ns.mfold m update_unsed_decls_list
     else pure m

/-- In the current file, list all the declaration that are not marked as `@[main_declaration]` and
that are not referenced by such declarations -/
meta def all_unused (fs : list (option string)) : tactic (name_map declaration) :=
do ds ← get_decls_from fs,
   ls ← ds.keys.mfilter (succeeds ∘ user_attribute.get_param_untyped main_declaration_attr),
   ds ← ls.mfoldl (flip update_unsed_decls_list) ds,
   ds.mfilter $ λ n d, do
     e ← get_env,
     return $ !d.is_auto_or_internal e

/-- expecting a string literal (e.g. `"src/tactic/find_unused.lean"`)
-/
meta def parse_file_name (fn : pexpr) : tactic (option string) :=
some <$> (to_expr fn >>= eval_expr string) <|> fail "expecting: \"src/dir/file-name\""

setup_tactic_parser

/-- The command `#list_unused_decls` lists the declarations that that
are not used the main features of the present file. The main features
of a file are taken as the declaration tagged with
`@[main_declaration]`.

A list of files can be given to `#list_unused_decls` as follows:

```lean
#list_unused_decls ["src/tactic/core.lean","src/tactic/interactive.lean"]
```

They are given in a list that contains file names written as Lean
strings. With a list of files, the declarations from all those files
in addition to the declarations above `#list_unused_decls` in the
current file will be considered and their interdependencies will be
analyzed to see which declarations are unused by declarations marked
as `@[main_declaration]`. The files listed must be imported by the
current file. The path of the file names is expected to be relative to
the root of the project (i.e. the location of `leanpkg.toml` when it
is present).

Neither `#list_unused_decls` nor `@[main_declaration]` should appear
in a finished mathlib development. -/
@[user_command]
meta def unused_decls_cmd (_ : parse $ tk "#list_unused_decls") : lean.parser unit :=
do fs ← pexpr_list,
   show tactic unit, from
   do fs ← fs.mmap parse_file_name,
      ds ← all_unused $ none :: fs,
      ds.to_list.mmap' $ λ ⟨n,_⟩, trace!"#print {n}"

add_tactic_doc
{ name                     := "#list_unused_decls",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.unused_decls_cmd],
  tags                     := ["debugging"] }

end tactic
