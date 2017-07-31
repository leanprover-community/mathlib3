/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

This file defines an alias command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

/ -- doc string - /
alias alias1 alias2 ... → my_theorem

This produces defs or theorems of the form:

/ -- doc string - /
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/ -- doc string - /
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
-/
open lean.parser tactic interactive

@[user_attribute] def alias_attr : user_attribute :=
{ name := `alias, descr := "This definition is an alias of another." }

@[user_command] meta def alias_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "alias") : lean.parser unit :=
do aliases ← many ident,
  tk "→" <|> tk "->",
  old ← ident,
  d ← (do old ← resolve_constant old, get_decl old) <|>
    fail ("theorem " ++ to_string old ++ " not found"),
  updateex_env $ λ env, aliases.mfoldl (λ env al,
  env.add (match d.to_definition with
  | (declaration.defn n ls t v h tr) :=
    declaration.defn al ls t (expr.const n (level.param <$> ls))
      reducibility_hints.abbrev tt
  | (declaration.thm n ls t v)       :=
    declaration.thm al ls t $ task.pure $ expr.const n (level.param <$> ls)
  | _ := undefined
  end)) env,
  aliases.mmap' $ λ al, set_basic_attribute `alias al,
  match meta_info.doc_string with
  | none := skip
  | some s := aliases.mmap' $ λ al, add_doc_string al s
  end
