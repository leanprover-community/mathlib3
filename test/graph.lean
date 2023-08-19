import tactic.binder_matching
import system.io
import tactic.core
import algebra.algebra.basic
.

open tactic

meta def process_decl (d : declaration) : tactic (name × list name) :=
do
  let ty := d.type,
  (binders, e) ← get_pi_binders_nondep ty,
  let binders := binders.filter (λ b, b.2.info = binder_info.inst_implicit),
  let binders := binders.map (λ b, b.2.type.get_app_fn.const_name),
  let binders := binders.filter (≠ name.anonymous),
  (clsname, args) ← pure e.get_app_fn_args,
  matching_args ← args.mfilter (λ a, do {
    t ← infer_type a,
    (a_binders, a_base) ← mk_local_pis t,
    expr.sort u ← pure a_base | pure ff,
    pure tt
  }),
  -- check this is an application with variables
  matching_args.mmap (λ a, guard a.is_local_constant <|> fail!"{a} is not a constant"),
  pure (clsname.const_name, binders)

meta def find_url (n : name) : format :=
format!"https://leanprover-community.github.io/mathlib_docs/find/{n}"

meta def write (f : format) : io unit :=
io.put_str_ln (f.to_string)

/-- A version of `list.map` for `io` that does not consume the whole stack -/
def list.mmap_io {α β : Type*} (f : α → io β) (l : list α) : io (list β) :=
do
  (_, bs) ← io.iterate (l, ([] : list β)) (λ state, do {
    (a :: as, bs) ← pure state | return none,
    b ← f a,
    return (some (as, b :: bs))
  }),
  pure bs

meta def main : io unit:=
do
  infos ← io.run_tactic $ environment.get_decls <$> get_env,
  write "{",
  infos.mmap_io $ λ d, do {
    some _ ←  io.run_tactic $ try_core (has_attribute `instance d.to_name) | pure (),
    some (cls, edges) ←  io.run_tactic $ try_core (process_decl d) | pure (),
    write format!"  \"{d.to_name}\": {{ class: \"{cls}\", inputs: [",
    edges.mmap' (λ src, write format!"\"{src}\", "),
    write format!"] }},"
  },
  io.put_str_ln "}"
