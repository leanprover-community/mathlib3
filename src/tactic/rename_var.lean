import tactic.interactive

open expr

meta def expr.rename_var (old new : name) : expr → expr
| (pi n bi t b) := (pi (if n = old then new else n) bi (expr.rename_var t) (expr.rename_var b))
| (lam n bi t b) := (lam (if n = old then new else n) bi (expr.rename_var t) (expr.rename_var b))
| (app t b) := (app (expr.rename_var t) (expr.rename_var b))
| e := e

namespace tactic
meta def rename_var_at_goal (old new : name) : tactic unit :=
do
  old_tgt ← target,
  assert `htarget (expr.rename_var old new old_tgt),
  swap,
  get_local `htarget >>= tactic.exact

meta def rename_var_at_hyp (old new h : name) : tactic unit :=
do
  old_e ← get_local h >>= infer_type,
  eh ← get_local h,
  assertv h (expr.rename_var old new old_e) eh,
  clear eh
end tactic

namespace tactic.interactive
open tactic
setup_tactic_parser

/-- `rename_var old new` renames variable `old` to `new` in the goal.
    `rename_var old new at h` does the same in hypothesis `h`. -/
meta def rename_var (old : parse ident) (new : parse ident) (l : parse location) : tactic unit :=
do
  match l with
  | (loc.ns [some h]) := do
    rename_var_at_hyp old new h
  | (loc.ns [none]) := do
    rename_var_at_goal old new
  | _ := fail "rename_var needs exactly zero or one location."
  end
end tactic.interactive
