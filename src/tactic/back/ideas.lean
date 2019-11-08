import data.list.defs tactic.core tactic.norm_num

import .common

namespace back
namespace ideas

namespace list_iterate

meta structure config :=
(name : string)
(l : list expr)

structure state :=
(n : ℕ)

meta def startup (name : string) (l : back.config → tactic (list expr)) (cfg : back.config)
  : tactic config :=
do l ← l cfg,
   return ⟨name, l⟩

meta def init (penalty : ℕ) (cfg : config) (_ : expr) : state × ℕ × debug_msg :=
(⟨0⟩, penalty, maybe_debug $ return "li(init)")

meta def debug_comment (cfg : config) (n : ℕ) : debug_msg :=
maybe_debug $ do {
  match cfg.l.nth n with
  | none     := return format!"li({cfg.name})(exhausted)"
  | some lem := do pplem ← tactic.pp lem,
                   return format!"li({cfg.name})({pplem})"
  end
}

meta def step (cfg : config) (ts : tactic_state) (e : expr) (s : state)
  : tactic (list (state × ℕ × debug_msg) × list tactic_state) :=
do match cfg.l.nth s.n with
   | none     := do when_btrace $ do {
                      tactic.trace format!"li({cfg.name}) exhausted"
                    },
                    return ([], [])
   | some lem := do new ← tactic.try_apply_in_context lem ts e,
                    when_btrace $ do {
                      pplem ← tactic.pp lem,
                      let res := if new.is_some then "worked" else "failed",
                      tactic.trace format!"li({cfg.name}) applying:\n  \"{pplem}\", {res}"
                    },

                    return ([(⟨s.n + 1⟩, 0, debug_comment cfg (s.n + 1))], new.to_list)
   end

end list_iterate

section
open list_iterate

meta def list_iterate (name : string) (penalty : ℕ) (l : back.config → tactic (list expr))
  : idea :=
⟨name, startup name l, init penalty, step⟩

end

namespace tagged_lemmas

@[user_attribute]
meta def back_attr : user_attribute :=
{ name  := `back,
  descr := "`back` lemmas" }

meta def find_tagged_lemmas : tactic (list expr) :=
do l ← attribute.get_instances `back,
   l.mmap $ λ n, tactic.resolve_name n >>= tactic.i_to_expr_for_apply

end tagged_lemmas

namespace helper_tactics

meta inductive filter_graph
| leaf (penalty : ℕ) (t : tactic unit)
| vertex (penalty : ℕ) (l : list filter_graph)
| filter (f : tactic_state → expr → tactic bool) (n : filter_graph)

meta structure config :=
(g : filter_graph)

meta def startup (g : filter_graph) (cfg : back.config) : tactic config :=
return ⟨g⟩

meta def init (cfg : config) (_ : expr) : option (tactic unit) × ℕ × debug_msg :=
(none, 0, maybe_debug $ return "helper_tactics(init)")

meta def expand_graph (ts : tactic_state) (e : expr)
  : ℕ → filter_graph → tactic (list (tactic unit × ℕ))
| p₁ (filter_graph.leaf p₂ t) := return [(t, p₁ + p₂)]
| p₁ (filter_graph.vertex p₂ l) := list.join <$> (l.mmap $ expand_graph (p₁ + p₂))
| p₁ (filter_graph.filter f n) :=
  mcond (f ts e) (expand_graph p₁ n) (return [])

meta def step (cfg : config) (ts : tactic_state) (e : expr)
  : option (tactic unit) → tactic (list (option (tactic unit) × ℕ × debug_msg) × list tactic_state)
| none     := do when_btrace $ do {
                   tactic.trace format!"helper_tactics:\n  setup"
                 },
                 l ← expand_graph ts e 0 cfg.g,
                 return (l.map $ λ t, (some t.1, t.2, none), [])
| (some t) := do new ← tactic.try_tactic_in_context t ts e,
                 when_btrace $ do {
                   tactic.trace format!"helper_tactics:\n  trying, \"{new}\""
                 },
                 return ([], new.to_list)

meta def build (g : filter_graph) : idea := ⟨"helper_tactics", startup g, init, step⟩

end helper_tactics

/-- Idea: Local hypotheses -/
meta def local_hypotheses : idea :=
list_iterate "local_hypotheses" 0 (λ _, tactic.local_context)

/-- Idea: Passed lemmas -/
meta def passed_lemmas : idea :=
list_iterate "passed_lemmas" 0 (λ cfg, return cfg.passed_lemmas)

section
open tagged_lemmas

/-- Idea: Tagged lemmas -/
meta def tagged_lemmas : idea :=
list_iterate "tagged_lemmas" 0 (λ _, find_tagged_lemmas)

end

section
open helper_tactics helper_tactics.filter_graph

meta def helper_tactics_graph : filter_graph :=
filter (λ ts e, tactic.under_state ts $ tactic.is_proof e) $
  vertex 5 [
    leaf 10 $ tactic.interactive.norm_num1 (interactive.loc.ns [none]),
    leaf 50 $ tactic.interactive.simp none ff [] [] (interactive.loc.ns [none])
  ]

/-- Idea: Helper tactics -/
meta def helper_tactics : idea := build helper_tactics_graph

end

end ideas
end back
