import tactic.with_local_reducibility

namespace test

open tactic
open tactic.decl_reducibility

meta def guard_decl_reducibility (n : name) (r : decl_reducibility) :=
do x ← get_decl_reducibility n,
   guard (x = r)

-- Test declarations

@[irreducible] def wlr_irred : ℕ := 1
def wlr_semired : ℕ := 2
@[reducible] def wlr_red : ℕ := 3

-- Test get_decl_reducibility

run_cmd (guard_decl_reducibility ``wlr_irred irreducible)
run_cmd (guard_decl_reducibility ``wlr_semired semireducible)
run_cmd (guard_decl_reducibility ``wlr_red reducible)

run_cmd success_if_fail (get_decl_reducibility `wlr_nonexistent)

section

-- Test that original reducibility is hidden by local attributes

local attribute [reducible] wlr_irred
local attribute [irreducible] wlr_red

run_cmd (guard_decl_reducibility ``wlr_irred reducible)
run_cmd (guard_decl_reducibility ``wlr_red irreducible)

end

-- Test set_decl_reducibility

run_cmd do
  set_decl_reducibility ``wlr_red semireducible,
  guard_decl_reducibility ``wlr_red semireducible,
  set_decl_reducibility ``wlr_red irreducible,
  guard_decl_reducibility ``wlr_red irreducible,
  set_decl_reducibility ``wlr_red reducible,
  guard_decl_reducibility ``wlr_red reducible

-- Test with_local_reducibility: normal exit

run_cmd do
  with_local_reducibility ``wlr_semired reducible
    (do guard_decl_reducibility ``wlr_semired reducible,
        with_local_reducibility ``wlr_semired irreducible
          (guard_decl_reducibility ``wlr_semired irreducible),
        guard_decl_reducibility ``wlr_semired reducible),
  guard_decl_reducibility ``wlr_semired semireducible

-- Test with_local_reducibility: abnormal exit

run_cmd do
  try (with_local_reducibility ``wlr_semired reducible
    (do guard_decl_reducibility ``wlr_semired reducible,
        (fail "" : tactic unit))),
  guard_decl_reducibility ``wlr_semired semireducible

end test
