import tactic.rewrite_search.core

import data.rat.basic

open tactic.rewrite_search
open tactic.rewrite_search.bound_progress

namespace tactic.rewrite_search.edit_distance

variables {α : Type} [decidable_eq α]

@[derive decidable_eq]
structure ed_partial :=
(prefix_length : dnum)
(suffix    : list (table_ref × dnum))
(l₂_toks   : list (table_ref × dnum))
(distances : list dnum) -- distances from the prefix of l₁ to each non-empty prefix of l₂

def compute_initial_distances_aux (weights : table dnum) : dnum → list table_ref → list dnum
| _ [] := []
| so_far (a :: rest) :=
  let so_far := so_far + (weights.iget a) in
  list.cons so_far (compute_initial_distances_aux so_far rest)

@[inline] def compute_initial_distances (weights : table dnum) (l : list table_ref) : list dnum :=
  compute_initial_distances_aux weights 0 l

@[inline] def empty_partial_edit_distance_data (weights : table dnum) (l₁ l₂ : list table_ref) : ed_partial :=
  ⟨ 0, l₁.map (λ r, (r, weights.iget r)), l₂.map (λ r, (r, weights.iget r)), compute_initial_distances weights l₂ ⟩

@[inline] def triples {α : Type} (p : ed_partial) (l₂ : list (α × dnum)): list (dnum × dnum × α × dnum) :=
p.distances.zip ((list.cons p.prefix_length p.distances).zip l₂)

universe u

--TODO explain me
@[inline] meta def fold_fn (h : table_ref) (wh : dnum) (n : dnum × list dnum) : dnum × dnum × table_ref × dnum → dnum × list dnum
| (a, b, r, wr) :=
  let m := if h = r then b else dnum.minl [
    /- deletion     -/ a + wh,
    /- substitution -/ b + dnum.max wr wh,
    /- insertion    -/ n.2.head + wh
  ] in (dnum.min m n.1, list.cons m n.2)

--TODO explain me
@[inline] meta def improve_bound_once (cur : dnum) (p : ed_partial) : bound_progress ed_partial :=
  match p.suffix with
    | [] := exactly p.distances.ilast p
    | ((h, wh) :: t) :=
      let new_prefix_length := p.prefix_length + wh in
      let initial : dnum × list dnum := (new_prefix_length, [new_prefix_length]) in
      let new_distances : dnum × list dnum := (triples p p.l₂_toks).foldl (fold_fn h wh) initial in
      at_least new_distances.1 ⟨ new_prefix_length, t, p.l₂_toks, new_distances.2.reverse.drop 1 ⟩
  end

meta def improve_bound_over (m : dnum) : bound_progress ed_partial → bound_progress ed_partial
| (exactly n p) := exactly n p
| (at_least n p) :=
  if n > m then
    at_least n p
  else
    improve_bound_over (improve_bound_once n p)

end tactic.rewrite_search.edit_distance

namespace tactic.rewrite_search.metric.edit_distance

open tactic.rewrite_search.edit_distance

@[derive has_reflect]
structure ed_config :=
(refresh_freq     : ℕ := 10)
(explain_thoughts : bool := ff)
(trace_weights    : bool := ff)

structure ed_state :=
(cfg     : ed_config)
(weights : table dnum)
def ed_state.init (cfg : ed_config := {}) : ed_state := ⟨cfg, table.create⟩

-- In future we might allow init_fn to return some internal weight state. At
-- the moment, it is just used to ensure that an external depedency (e.g.
-- external program or custom lean fork) is present.
meta def calc_weights_fn (α δ : Type) := search_state α ed_state ed_partial δ → tactic (table dnum)

meta structure calc_weights_block :=
(α δ : Type)
(fn : calc_weights_fn α δ)

meta structure ed_weight (α δ : Type) :=
(init : init_fn unit)
(calc_weights : calc_weights_fn α δ)

meta def ed_weight_constructor := Π α δ, ed_weight α δ

variables {α δ : Type} (g : search_state α ed_state ed_partial δ)

meta def ed_init (cfg : ed_config) (weight_init : init_fn unit) : tactic (init_result ed_state) := do
  init_result.chain "weight" weight_init $ λ _,
    init_result.pure $ ed_state.init cfg

meta def ed_init_bound (l r : vertex) : bound_progress ed_partial :=
  at_least 0 (empty_partial_edit_distance_data g.metric_state.weights l.tokens r.tokens)

meta def ed_reweight (fn : search_state α ed_state ed_partial δ → tactic (table dnum)) (g : search_state α ed_state ed_partial δ) : tactic (search_state α ed_state ed_partial δ) := do
  g ← g.reset_all_estimates ed_init_bound,
  weights ← fn g,
  if g.metric_state.cfg.trace_weights then
    let weight_pairs := (g.tokens.to_list.zip weights.to_list).map (
      λ p : token × dnum, to_string format!"{p.1.str}={p.2}"
    ) in
    tactic.trace format!"reweighted: {weight_pairs}"
  else
    tactic.skip,
  return $ g.mutate_metric {g.metric_state with weights := weights}

meta def ed_update (fn : calc_weights_fn α δ) (g : search_state α ed_state ed_partial δ) (itr : ℕ) : tactic (search_state α ed_state ed_partial δ) :=
  if g.metric_state.cfg.refresh_freq > 0 ∧ (itr % (g.metric_state.cfg.refresh_freq + 1) = 0) then do
    when g.metric_state.cfg.explain_thoughts $
      tactic.trace "pause! refreshing weights...",
    ed_reweight fn g
  else
    return g

meta def ed_improve_estimate_over (g : search_state α ed_state ed_partial δ) (m : dnum) (l r : vertex) (bnd : bound_progress ed_partial) : bound_progress ed_partial :=
  improve_bound_over m bnd

end tactic.rewrite_search.metric.edit_distance

namespace tactic.rewrite_search.metric
open tactic.rewrite_search.edit_distance
open edit_distance

meta def weight.none : ed_weight_constructor :=
λ α δ, ⟨init_result.pure (), λ g, return table.create⟩

meta def edit_distance (conf : ed_config := {})
  (w_cons : ed_weight_constructor := weight.none)
  : metric_constructor ed_state ed_partial :=
λ α δ, let w := w_cons α δ in
⟨ed_init conf w.init, ed_update w.calc_weights, ed_init_bound, ed_improve_estimate_over⟩

end tactic.rewrite_search.metric
