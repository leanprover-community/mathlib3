import system.io
import .io
import .serial

universe u

open tactic

namespace tcache

section
open interaction_monad

meta def resolve : option (unit → format) → string
| none := ""
| (some e) := to_string $ e ()

meta def interaction_monad_orelse' {α : Type u} (t₁ : tactic α) (t₂ : string → tactic α) : tactic α :=
λ s, result.cases_on (t₁ s)
  result.success
  (λ e ref₁ s', result.cases_on (t₂ (resolve e) s)
    result.success
    result.exception
  )

end

meta def trace {α : Type u} [has_to_tactic_format α] (hash : string) (a : thunk α) : tactic unit := do
  f ← has_to_tactic_format.to_tactic_format $ a (),
  when_tracing `tcache $ tactic.trace $ format!"tc@{hash} - {f}"

meta def timeit {α : Type u} (hash s : string) (f : thunk α) : α :=
if is_trace_enabled_for `tcache then _root_.timeit sformat!"tc@{hash} - {s}" (f ())
else f ()

meta def timetac {α : Type u} (hash s : string) (f : thunk (tactic α)) : tactic α :=
if is_trace_enabled_for `tcache then tactic.timetac sformat!"tc@{hash} - {s}" (f ())
else f ()

meta def sanitize_expr : expr → expr
| (expr.const n l) := expr.const n l
| (expr.app f a) := expr.app (sanitize_expr f) (sanitize_expr a)
| (expr.sort l) := expr.sort l
| (expr.pi n bi t v) := expr.pi n bi (sanitize_expr t) (sanitize_expr v)
| (expr.lam n bi t v) := expr.lam n bi (sanitize_expr t) (sanitize_expr v)
| (expr.var n) := expr.var n
| (expr.local_const n₁ n₂ bi v) := expr.const n₂ []
| (expr.mvar _ _ _) := expr.const name.anonymous []
| (expr.macro m _) := expr.const (expr.macro_def_name m) [] -- Do something with the `expr` list?
| (expr.elet _ _ _ _) := error "cannot sanitize elet!"

meta def hash_goal (e : expr) : tactic ℕ := do
  t ← infer_type e,
  return $ (sanitize_expr t).hash

meta def hash_goals (n : name) : tactic string := do
  -- FIXME this xor is probably really slow
  v ← get_goals >>= list.mfoldl (λ v d, nat.lxor v <$> hash_goal d) 0,
  return sformat!"{n}.{v}"

meta def cache_file_name (hash : string) : string :=
CACHE_DIR ++ "/" ++ hash ++ ".leancache"

meta def find_local_const (n : name) : list expr → expr
| [] := error sformat!"unknown const {n}"
| (e :: rest) :=
  if e.local_pp_name = n then e else find_local_const rest

meta def fixup_local_consts (lc : list expr) : expr → nat → option expr
| (expr.local_const _ n _ _) _ := some $ find_local_const n lc
| _ _ := none

variables (hash : string)

meta def solve_goal (pf : expr) : tactic unit := exact pf >> done

meta def deserialise_proof : io expr := do
  h ← io.mk_file_handle (cache_file_name hash) io.mode.read tt,
  pf ← io.deserialize h,
  io.fs.close h,
  return pf

meta def handle_recall_failed (pf : expr) (msg : string) : tactic unit := do
  s₂ ← infer_type pf,
  trace hash sformat!"failed to recall proof: {msg}\n\n{pf.to_raw_fmt}\n\n{s₂.to_raw_fmt}"

meta def try_cache (n : name) (lc : list expr) : tactic unit := do
  pf ← timetac hash "deserialising proof" $ unsafe_run_io $ deserialise_proof hash,
  let pf := timeit hash "loading proof took" (pf.replace $ fixup_local_consts lc),
  interaction_monad_orelse' (solve_goal pf) (handle_recall_failed hash pf)

meta def put_cache (n : name) (lc : list expr) (e : expr) : tactic unit := do
  interaction_monad_orelse' (do
    unsafe_run_io $ do {
      h ← io.mk_file_handle (cache_file_name hash) io.mode.write tt,
      io.serialize h e,
      io.fs.close h
    }
  ) $ λ msg,
  trace hash sformat!"proof serialisation failure: {msg}\n\n{e}\n\n{e.to_raw_fmt}"

meta def execute_capture (n : name) (t : tactic unit) : tactic expr := do
  [m] ← get_goals,
  t >> done,
  instantiate_mvars m

meta def try_recompute (n : name) (lc : list expr) (hash : string) (t : tactic unit) : tactic unit := do
  trace hash "need to regenerate proof",
  e ← timetac hash "success, took" $ execute_capture n t,
  put_cache hash n lc e

meta def discharge_goals (t : tactic unit) : tactic unit := do
  n ← decl_name,
  hash ← hash_goals n,
  lc ← local_context,
  try_cache hash n lc <|>
  try_recompute n lc hash t

meta def init_tcache : tactic unit := tactic.unsafe_run_io mk_cache_dir

meta def clear_tcache : tactic unit := tactic.unsafe_run_io rm_cache_dir

end tcache
