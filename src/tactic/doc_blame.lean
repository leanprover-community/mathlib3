/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Robert Y. Lewis
-/
import tactic.core
open tactic declaration environment

/-- Print the declaration name if it's a definition without a docstring -/
meta def print_item (use_thms : bool) : declaration → tactic unit
| (defn n _ _ _ _ _) := doc_string n >> skip <|> trace n
| (cnst n _ _ _) := doc_string n >> skip <|> trace n
| (thm n _ _ _) := when use_thms (doc_string n >> skip <|> trace n)
| _ := skip

/-- Print all definitions in the current file without a docstring -/
meta def print_docstring_orphans (use_thms : bool) : tactic unit :=
do curr_env ← get_env,
   let local_decls : list declaration := curr_env.fold [] $ λ x t,
     if environment.in_current_file' curr_env (to_name x) &&
        not (to_name x).is_internal &&
        not (is_auto_generated curr_env x) then x::t
     else t,
   local_decls.mmap' (print_item use_thms)

setup_tactic_parser

reserve prefix `#doc_blame`:max

@[user_command]
meta def doc_cmd (_ : decl_meta_info) (_ : parse $ tk "#doc_blame") : lean.parser unit :=
do use_thms ← (tk "!") >> return tt <|> return ff,
   print_docstring_orphans use_thms
