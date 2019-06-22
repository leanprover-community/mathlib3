-- This file almost qualifies for inclusion in the `core` dir, but
-- the hooks into non-core pieces, i.e. providing defaults, and also
-- the external interface it exports is enough to keep it out here.
import .core

-- Default strategy, metric, and tracer used as a fallback by the engine
-- (so must be present)
import .strategy.pexplore
import .metric.edit_distance
import .tracer.unit

namespace tactic.rewrite_search

meta def pick_default_strategy : tactic unit :=
`[exact tactic.rewrite_search.strategy.pexplore]
meta def pick_default_metric   : tactic unit :=
`[exact tactic.rewrite_search.metric.edit_distance]
meta def pick_default_tracer   : tactic unit :=
`[exact tactic.rewrite_search.tracer.unit_tracer]

structure collect_cfg :=
(suggest         : list name := [])
(inflate_rws     : bool := ff)
(help_me         : bool := ff)

-- This is the "public" config structure which has convenient tactic-mode
-- invocation synatx. The data in this structure is extracted and transformed
-- into the internal representation of the settings and modules by
-- `try_mk_search_instance`.
meta structure config (α β γ δ : Type) extends collect_cfg, tactic.rewrite_all.cfg :=
(max_iterations  : ℕ := 500)
(optimal         : bool := tt)
(exhaustive      : bool := ff)
(trace           : bool := ff)
(trace_summary   : bool := ff)
(trace_rules     : bool := ff)
(explain         : bool := ff)
(explain_using_conv : bool := tt)
(metric          : metric_constructor β γ . pick_default_metric)
(strategy        : strategy_constructor α . pick_default_strategy)
(view            : tracer_constructor δ   . pick_default_tracer)

open tactic.rewrite_search.edit_distance
open tactic.rewrite_search.metric.edit_distance
open tactic.rewrite_search.strategy.pexplore

meta def default_config : config pexplore_state ed_state ed_partial unit := {}
meta def pick_default_config : tactic unit := `[exact tactic.rewrite_search.default_config]

variables {α β γ δ : Type}

meta def mk_fallback_config (orig : config α β γ δ)
  : config pexplore_state ed_state ed_partial unit :=
{orig with view     := by pick_default_tracer,
            metric   := by pick_default_metric,
            strategy := by pick_default_strategy}

meta def mk_initial_search_state (conf : core_cfg)
  (rw_cfg : tactic.rewrite_all.cfg) (rs : list (expr × bool))
  (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ)
  (strat_state : α) (metric_state : β) (tr_state : δ)
  : search_state α β γ δ :=
⟨tr, conf, rw_cfg, rs, strat_state, metric_state, table.create, table.create, table.create, none, tr_state, statistics.init⟩

meta def setup_instance (conf : core_cfg)
  (rw_cfg : tactic.rewrite_all.cfg) (rs : list (expr × bool))
  (s : strategy α β γ δ) (m : metric α β γ δ) (tr : tracer α β γ δ)
  (s_state : α) (m_state : β) (tr_state : δ)
  (eqn : sided_pair expr) : tactic (inst α β γ δ) :=
do let g := mk_initial_search_state conf rw_cfg rs s m tr s_state m_state tr_state,
   (g, vl) ← g.add_root_vertex eqn.l side.L,
   (g, vr) ← g.add_root_vertex eqn.r side.R,
   g ← s.startup g m vl vr,
   return ⟨m, s, g⟩

meta def instantiate_modules (cfg : config α β γ δ) : strategy α β γ δ × metric α β γ δ × tracer α β γ δ :=
(cfg.strategy β γ δ, cfg.metric α δ, cfg.view α β γ)

meta def try_mk_search_instance (cfg : config α β γ δ)
  (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic (option (inst α β γ δ)) :=
do let (s, m, t) := instantiate_modules cfg,
   init_result.try "tracer"   t.init $ λ tracer_state,
   init_result.try "metric"   m.init $ λ metric_state,
   init_result.try "strategy" s.init $ λ strat_state, do
   let conf : core_cfg := {
    max_iterations := cfg.max_iterations,
    optimal := cfg.optimal,
    exhaustive := cfg.exhaustive,
    trace := cfg.trace,
    trace_summary := cfg.trace_summary,
    trace_rules := cfg.trace_rules,
    explain := cfg.explain,
    explain_using_conv := cfg.explain_using_conv
  },
  option.some <$>
    setup_instance conf cfg.to_cfg rs s m t strat_state metric_state tracer_state eqn

open tactic

meta def try_search (cfg : config α β γ δ)
  (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic (option string) :=
do i ← try_mk_search_instance cfg rs eqn,
   match i with
   | none := return none
   | some i := do (i, result) ← i.search_until_solved,
                  match result with
                  | search_result.failure reason :=
                    tactic.fail reason
                  | search_result.success proof steps :=
                    tactic.exact proof >> some <$> i.explain proof steps
                  end

end

end tactic.rewrite_search
