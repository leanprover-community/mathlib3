import all

namespace tactic

meta def list_decls : tactic unit :=
do env ← get_env,
   env.get_decl_names.mmap' trace

end tactic

run_cmd tactic.list_decls
