/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import data.buffer.parser

open lean.parser tactic interactive parser

@[user_attribute] meta def field_lemma_attr : user_attribute :=
{ name := `field_lemma, descr := "This definition was automatically generated from a structure field by `restate_axiom`." }

/- Make lemma takes a structure field, and makes a new, definitionally simplified copy of it, appending `_lemma` to the name.
   The main application is to provide clean versions of structure fields that have been tagged with an auto_param. -/
meta def restate_axiom (d : declaration) (new_name : name) : tactic unit :=
do (levels, type, value, reducibility, trusted) ← pure (match d.to_definition with
  | declaration.defn name levels type value reducibility trusted :=
    (levels, type, value, reducibility, trusted)
  | _ := undefined
  end),
  (s, u) ← mk_simp_set ff [] [],
  new_type ← (s.dsimplify [] type) <|> pure (type),
  updateex_env $ λ env, env.add (declaration.defn new_name levels new_type value reducibility trusted),
  field_lemma_attr.set new_name () tt

private meta def name_lemma (n : name) :=
match n.components.reverse with
| last :: most := mk_str_name n.get_prefix (last.to_string ++ "_lemma")
| nil          := undefined
end

@[user_command] meta def restate_axiom_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "restate_axiom") : lean.parser unit :=
do from_lemma ← ident,
   from_lemma_fully_qualified ← resolve_constant from_lemma,
  d ← get_decl from_lemma_fully_qualified <|>
    fail ("declaration " ++ to_string from_lemma ++ " not found"),
  do {
    restate_axiom d (name_lemma from_lemma_fully_qualified)
  }.

