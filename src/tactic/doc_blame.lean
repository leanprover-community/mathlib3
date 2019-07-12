import tactic.core
open tactic declaration environment

/-- test that name was not auto-generated -/
@[reducible] def name.is_not_auto (n : name) : Prop :=
n.components.ilast ∉ [`no_confusion, `rec_on, `cases_on, `no_confusion_type, `sizeof,
                      `rec, `mk, `sizeof_spec, `inj_arrow, `has_sizeof_inst, `inj_eq, `inj]

/-- Print the declaration name if it's a definition without a docstring -/
meta def print_item (use_thms : bool) (env : environment) : declaration → tactic unit
| (defn n _ _ _ _ _) := doc_string n >> skip <|> when n.is_not_auto (trace n)
| (cnst n _ _ _) := doc_string n >> skip <|> when n.is_not_auto (trace n)
| (thm n _ _ _) := when use_thms (doc_string n >> skip <|> when n.is_not_auto (trace n))
| _ := skip

/-- Print all definitions in the current file without a docstring -/
meta def print_docstring_orphans (use_thms : bool) : tactic unit :=
do curr_env ← get_env,
   let local_decls : list declaration := curr_env.fold [] $ λ x t,
     if environment.in_current_file' curr_env (to_name x) && not (to_name x).is_internal then x::t
     else t,
   local_decls.mmap' (print_item use_thms curr_env)

setup_tactic_parser

reserve prefix `#doc_blame`:max

@[user_command]
meta def doc_cmd (_ : decl_meta_info) (_ : parse $ tk "#doc_blame") : lean.parser unit :=
do use_thms ← (tk "!") >> return tt <|> return ff,
   print_docstring_orphans use_thms
