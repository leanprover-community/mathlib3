/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import data.buffer.parser

open lean.parser tactic interactive parser

/-- 
`restate_axiom` takes a structure field, and makes a new, definitionally simplified copy of it, appending `_lemma` to the name.
The main application is to provide clean versions of structure fields that have been tagged with an auto_param.
-/
meta def restate_axiom (d : declaration) (new_name : name) : tactic unit :=
do (levels, type, value, reducibility, trusted) ← pure (match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    (levels, type, value, reducibility, trusted)
  | _ := undefined
  end),
  (s, u) ← mk_simp_set ff [] [],
  new_type ← (s.dsimplify [] type) <|> pure (type),
  updateex_env $ λ env, env.add (declaration.defn new_name levels new_type value reducibility trusted)

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

@[user_command] meta def restate_axiom_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "restate_axiom") : lean.parser unit :=
do from_lemma ← ident,
   new_name ← optional ident,
   from_lemma_fully_qualified ← resolve_constant from_lemma,
  d ← get_decl from_lemma_fully_qualified <|>
    fail ("declaration " ++ to_string from_lemma ++ " not found"),
  do {
    new_name ← name_lemma from_lemma_fully_qualified new_name,
    restate_axiom d new_name
  }

