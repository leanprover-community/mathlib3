/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.buffer.parser
import tactic.doc_commands

open lean.parser tactic interactive parser

/--
`restate_axiom` takes a structure field, and makes a new, definitionally simplified copy of it.
If the existing field name ends with a `'`, the new field just has the prime removed. Otherwise,
we append `_lemma`.
The main application is to provide clean versions of structure fields that have been tagged with
an auto_param.
-/
meta def restate_axiom (d : declaration) (new_name : name) : tactic unit :=
do (levels, type, value, reducibility, trusted) ← pure (match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    (levels, type, value, reducibility, trusted)
  | _ := undefined
  end),
  (s, u) ← mk_simp_set ff [] [],
  new_type ← (s.dsimplify [] type) <|> pure (type),
  prop ← is_prop new_type,
  let new_decl := if prop then
      declaration.thm new_name levels new_type (task.pure value)
    else
      declaration.defn new_name levels new_type value reducibility trusted,
  updateex_env $ λ env, env.add new_decl

private meta def name_lemma (old : name) (new : option name := none) : tactic name :=
match new with
| none :=
  match old.components.reverse with
  | last :: most := (do let last := last.to_string,
                       let last := if last.to_list.ilast = ''' then
                                     (last.to_list.reverse.drop 1).reverse.as_string
                                   else last ++ "_lemma",
                       return (mk_str_name old.get_prefix last)) <|> failed
  | nil          := undefined
  end
| (some new) := return (mk_str_name old.get_prefix new.to_string)
end

/--
`restate_axiom` makes a new copy of a structure field, first definitionally simplifying the type.
This is useful to remove `auto_param` or `opt_param` from the statement.

As an example, we have:
```lean
structure A :=
(x : ℕ)
(a' : x = 1 . skip)

example (z : A) : z.x = 1 := by rw A.a' -- rewrite tactic failed, lemma is not an equality nor a iff

restate_axiom A.a'
example (z : A) : z.x = 1 := by rw A.a
```

By default, `restate_axiom` names the new lemma by removing a trailing `'`, or otherwise appending
`_lemma` if there is no trailing `'`. You can also give `restate_axiom` a second argument to
specify the new name, as in
```lean
restate_axiom A.a f
example (z : A) : z.x = 1 := by rw A.f
```
-/
@[user_command] meta def restate_axiom_cmd (_ : parse $ tk "restate_axiom") : lean.parser unit :=
do from_lemma ← ident,
   new_name ← optional ident,
   from_lemma_fully_qualified ← resolve_constant from_lemma,
  d ← get_decl from_lemma_fully_qualified <|>
    fail ("declaration " ++ to_string from_lemma ++ " not found"),
  do {
    new_name ← name_lemma from_lemma_fully_qualified new_name,
    restate_axiom d new_name }

add_tactic_doc
{ name                     := "restate_axiom",
  category                 := doc_category.cmd,
  decl_names               := [`restate_axiom_cmd],
  tags                     := ["renaming", "environment"] }
