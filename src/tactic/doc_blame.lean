import tactic.interactive

open tactic declaration environment

/-- test that name was not auto-generated -/
@[reducible] def name.is_not_auto (n : name) : Prop :=
n.components.ilast ∉ [`no_confusion, `rec_on, `cases_on, `no_confusion_type, `sizeof,
                      `rec, `mk, `sizeof_spec, `inj_arrow, `has_sizeof_inst, `inj_eq, `inj]

/-- Print the declaration name if it's a definition without a docstring -/
meta def print_item (env : environment) (decl : declaration) : tactic unit :=
match decl with
| (defn n _ _ _ _ _) := do { ds ← doc_string decl.to_name, skip } <|>
                          when n.is_not_auto (trace n)
| (cnst n _ _ _) := do { ds ← doc_string decl.to_name, skip } <|>
                          when n.is_not_auto (trace n)
| _ := skip
end

/-- Print all definitions in the current file without a docstring -/
meta def print_docstring_orphans : tactic unit :=
do curr_env ← get_env,
   let decls := curr_env.fold [] list.cons,
   let local_decls := decls.filter
     (λ x, environment.in_current_file' curr_env (to_name x) && not (to_name x).is_internal),
local_decls.mmap' (print_item curr_env)

setup_tactic_parser

reserve prefix `#doc_blame`:max

@[user_command]
meta def doc_cmd (_ : decl_meta_info) (_ : parse $ tk "#doc_blame") : lean.parser unit :=
print_docstring_orphans
