import tactic.rewrite_search.core.types

namespace tactic.rewrite_search

namespace search_state
variables {α β γ δ : Type} (g : search_state α β γ δ)

meta def trace_tactic {ε : Type} [has_to_tactic_format ε] (fn : tactic ε) : tactic unit :=
if g.conf.trace then do ev ← fn, tactic.trace ev else tactic.skip

meta def trace {ε : Type} [has_to_tactic_format ε] (s : ε) : tactic unit :=
g.trace_tactic $ return s

meta def trace_vertex_added (v : vertex) : tactic unit :=
g.trace_tactic $ return format!"addV({v.id.to_string}): {v.pp}"

meta def trace_edge_added (e : edge) : tactic unit :=
g.trace_tactic $ return format!"addE: {e.f.to_string}→{e.t.to_string}"

meta def trace_search_finished (es : list edge) : tactic unit :=
g.trace "Done!"

meta def trace_dump {ε : Type} [has_to_tactic_format ε] (s : ε) : tactic unit :=
do fmt ← has_to_tactic_format.to_tactic_format s,
let str := fmt.to_string,
g.trace str

end search_state

namespace inst
variables {α β γ δ : Type} (i : inst α β γ δ)

meta def dump_rws : list (expr × expr × ℕ × ℕ) → tactic unit
| [] := tactic.skip
| (a :: rest) := do tactic.trace format!"→{a.1}\nPF:{a.2}", dump_rws rest

meta def dump_tokens : list token → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    tactic.trace format!"V{a.id.to_string}:{a.str}|{a.freq.get side.L}v{a.freq.get side.R}",
    dump_tokens rest

meta def dump_vertices : list vertex → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    let pfx : string := match a.parent with
      | none := "?"
      | some p := p.f.to_string
    end,
    i.g.trace_dump (to_string format!"V{a.id.to_string}:{a.pp}<-{pfx}:{a.root}"),
    dump_vertices rest

meta def dump_edges : list edge → tactic unit
| [] := tactic.skip
| (a :: rest) := do
    (vf, vt) ← i.g.get_endpoints a,
    i.g.trace_dump format!"E{vf.pp}→{vt.pp}",
    dump_edges rest

meta def dump_estimates : list (dist_estimate γ) → tactic unit
| [] := tactic.trace ""
| (a :: rest) := do
    (lpp, rpp) ← i.g.get_estimate_verts a,
    i.g.trace_dump format!"I{lpp}-{rpp}:{a.bnd.bound}",
    dump_estimates rest

end inst

end tactic.rewrite_search
