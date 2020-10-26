/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.rewrite_search.core.types

/-!
# Debugging mechanisms for rewrite_search.
-/

namespace tactic.rewrite_search

namespace search_state
variables (g : search_state)

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

end tactic.rewrite_search
