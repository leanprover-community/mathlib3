import tactic.rewrite_search.core

open tactic.rewrite_search

namespace tactic.rewrite_search.tracer.unit

open tactic

meta def init : tactic (init_result unit) := init_result.pure ()
meta def publish_vertex (_ : unit) (_ : vertex) : tactic unit := skip
meta def publish_edge (_ : unit) (_ : edge) : tactic unit := skip
meta def publish_visited (_ : unit) (_ : vertex) : tactic unit := skip
meta def publish_finished (_ : unit) (_ : list edge) : tactic unit := skip
meta def dump (_ : unit) (_ : string) : tactic unit := skip
meta def pause (_ : unit) : tactic unit := skip

end tactic.rewrite_search.tracer.unit

namespace tactic.rewrite_search.tracer

open unit

meta def unit_tracer : tracer_constructor unit := λ α β γ,
tracer.mk α β γ unit.init unit.publish_vertex unit.publish_edge unit.publish_visited unit.publish_finished unit.dump unit.pause

meta def no {δ : Type} (_ : tracer_constructor δ) : tracer_constructor unit := unit_tracer

end tactic.rewrite_search.tracer
