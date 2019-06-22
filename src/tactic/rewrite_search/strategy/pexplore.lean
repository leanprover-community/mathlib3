import tactic.rewrite_search.core

open tactic.rewrite_search
open tactic.rewrite_search.bound_progress

namespace tactic.rewrite_search.strategy.pexplore

structure pexplore_config :=
(pop_size      : ℕ := 100)
(pop_alternate : bool := tt)

structure pair_stream :=
(last_side : side)
(its : sided_pair rewriterator)

inductive ipair
| unresolved (p : pair) (de : table_ref) : ipair
| resolved (p : pair) (de : table_ref) (ps : pair_stream) : ipair

namespace ipair

def pair : ipair → pair
| (ipair.unresolved p _)   := p
| (ipair.resolved   p _ _) := p

def de : ipair → table_ref
| (ipair.unresolved _ vde)   := vde
| (ipair.resolved   _ vde _) := vde

def to_string : ipair → string
| (ipair.unresolved p de) := p.to_string ++ "@" ++ de.to_string ++ "?"
| (ipair.resolved p de _) := p.to_string ++ "@" ++ de.to_string ++ "!"

instance has_to_string : has_to_string ipair := ⟨ipair.to_string⟩

end ipair

structure pexplore_state :=
(conf              : pexplore_config)
(initial           : ipair)
(interesting_pairs : list ipair)
(done_pairs        : list pair)

variables {β γ δ : Type} (conf : pexplore_config)
          (m : metric pexplore_state β γ δ)
          (g : search_state pexplore_state β γ δ)

namespace pair_stream

meta def from_vertices (vl vr : vertex) : tactic (search_state pexplore_state β γ δ × pair_stream) := do
  (g, lhs_it) ← g.visit_vertex vl,
  (g, rhs_it) ← g.visit_vertex vr,
  return (g, ⟨side.L, ⟨lhs_it, rhs_it⟩⟩)

meta def from_estimate (de : dist_estimate γ) : tactic (search_state pexplore_state β γ δ × pair_stream) := do
  (vl, vr) ← g.get_estimate_verts de,
  from_vertices g vl vr

meta instance has_to_format_pair : has_to_format pair := ⟨λ p, to_string p⟩
meta instance has_to_format_option_pair : has_to_format (option pair) := ⟨λ op, match op with | none := "none" | some p := to_string p end⟩

meta def read_side (ps : pair_stream) (g : search_state pexplore_state β γ δ) (p : pair) (s : side) : tactic (search_state pexplore_state β γ δ × pair_stream × option pair) := do
  (g, it, nxt) ← (ps.its.get s).next g,
  let newp : option pair := match nxt with
  | some (v, e) := some ⟨p.get s.other, v.id⟩
  | none := none
  end,
  (vl, vr) ← g.lookup_pair p,
  return (g, {ps with last_side := s, its := ps.its.set s it}, newp)

meta def read (ps : pair_stream) (g : search_state pexplore_state β γ δ) (p : pair) : tactic (search_state pexplore_state β γ δ × pair_stream × option pair) := do
  let next_side := if g.strat_state.conf.pop_alternate then ps.last_side.other else ps.last_side,
  (g, ps, ret) ← ps.read_side g p next_side,
  match ret with
  | some _ := return (g, ps, ret)
  | none := ps.read_side g p next_side.other
  end

end pair_stream

-- updates rival's estimate tryg to beat candidate's estimate, stoppg if we do or we can'tbfs
-- go any further. We return true if we were able to beat candidate.
private meta def try_to_beat (candidate rival : dist_estimate γ) : tactic (search_state pexplore_state β γ δ × dist_estimate γ × bool) :=
let cbnd := candidate.bnd.bound in
match rival.bnd with
| exactly n _ := return (g, rival, n <= cbnd)
| at_least n p := do
  (g, attempt) ← g.improve_estimate_over m cbnd rival,
  return (g, attempt, attempt.bnd.bound < cbnd)
end

-- First is closer
private meta def sort_most_interesting : search_state pexplore_state β γ δ → ipair × dist_estimate γ → ipair × dist_estimate γ → tactic (search_state pexplore_state β γ δ × (ipair × dist_estimate γ) × (ipair × dist_estimate γ))
| g (a, a_de) (b, b_de) := do
  (g, new_b_de, better) ← try_to_beat m g a_de b_de,
  match better with
  -- b is guarenteed closer, so return it:
  | tt := return (g, (b, new_b_de), (a, a_de))
  -- otherwise:
  | ff := match a_de.bnd with
    -- b is further than the current estimate for a and the estimate for a is exact:
    | exactly k _ := return (g, (a, a_de), (b, new_b_de))
    -- or, b is futher than the current estimate for a but a might actually be worse, so check:
    | at_least k p := sort_most_interesting g (b, new_b_de) (a, a_de)
  end
end

private meta def find_most_interesting_aux : search_state pexplore_state β γ δ → ipair × dist_estimate γ → list ipair → list ipair → tactic (search_state pexplore_state β γ δ × ipair × list ipair)
| g (curr_best, curr_de) seen [] := return (g, curr_best, seen)
| g (curr_best, curr_de) seen (candidate :: rest) := do
  candidate_de ← g.estimates.get candidate.de,
  (g, (better, better_de), (worse, worse_de)) ← sort_most_interesting m g (curr_best, curr_de) (candidate, candidate_de),
  find_most_interesting_aux g (better, better_de) (worse :: seen) rest

meta def find_most_interesting : tactic (search_state pexplore_state β γ δ × option ipair × list ipair) :=
  match g.strat_state.interesting_pairs with
  | []          := return (g, none, [])
  | (a :: rest) := do
    a_de ← g.estimates.get a.de,
    (g, best, others) ← find_most_interesting_aux m g (a, a_de) [] rest,
    return (g, some best, others)
  end

meta def resolve_ipair : ipair → tactic (search_state pexplore_state β γ δ × ipair)
| (ipair.unresolved p ref) := do
  de ← g.estimates.get ref,
  (g, _) ← g.try_unify de.to_pair,
  (g, ps) ← pair_stream.from_estimate g de,
  return (g, ipair.resolved p ref ps)
| ip := return (g, ip)

meta def pop_ipairs_aux : search_state pexplore_state β γ δ → metric pexplore_state β γ δ → ℕ → ipair → tactic (search_state pexplore_state β γ δ × ipair × list ipair)
| g m        0 ip := return (g, ip, [])
| g m pop_size (ipair.unresolved p ref) := do
  (g, ip) ← resolve_ipair g (ipair.unresolved p ref),
  pop_ipairs_aux g m pop_size ip
| g m pop_size (ipair.resolved p ref ps) := do
  (g, ps, nxt) ← ps.read g p,
  let ip := ipair.resolved p ref ps,
  match nxt with
  | none := return (g.mutate_strat {g.strat_state with done_pairs := (p :: g.strat_state.done_pairs)}, ip, [])
  | some nxt := do
    match g.estimates.find (λ de, nxt = de.to_pair ∨ (nxt = de.to_pair.flip)) with
    | none := do
      (g, ref) ← g.alloc_estimate m nxt,
      let newip := ipair.unresolved nxt ref,
      (g, ip, others) ← pop_ipairs_aux g m (pop_size - 1) ip,
      return (g, ipair.resolved p ref ps, list.cons newip others)
    | some de := pop_ipairs_aux g m pop_size ip
    end
  end

meta def pop_ipairs (pop_size : ℕ) (ip : ipair) : tactic (search_state pexplore_state β γ δ × ipair × list ipair) := do
  (g, ip, new) ← pop_ipairs_aux g m pop_size ip,
  return (g, ip, new)

meta def pexplore_init : tactic (init_result pexplore_state) :=
  init_result.pure ⟨{}, ipair.unresolved pair.null table_ref.null, [], []⟩

meta def pexplore_startup (m : metric pexplore_state β γ δ) (l r : vertex) : tactic (search_state pexplore_state β γ δ) := do
  let p : pair := ⟨l.id, r.id⟩,
  (g, ref) ← g.alloc_estimate m p,
  let initial := ipair.unresolved p ref,
  return $ g.mutate_strat ⟨conf, initial, [initial], []⟩

-- TODO find our "best" pairs, corresponding to seen distance estimates within a certain
-- threshold of the absolute best, and return them.
meta def get_best_pairs : tactic (list pair) :=
  return g.strat_state.done_pairs

meta def clear_vertex (v : vertex) : vertex :=
  {v with rw_prog := none, rws := table.create, rw_front := table_ref.first, adj := table.create}

meta def pexplore_step : search_state pexplore_state β γ δ → metric pexplore_state β γ δ → ℕ → tactic (search_state pexplore_state β γ δ × status)
| g m itr := do
  (g, best, others) ← find_most_interesting m g,
  match (best, others) with
  | (none, []) := do
    bests ← get_best_pairs g,
    (g, success) ← g.be_desperate bests,
    if ¬success then
      return (g, status.abort "all interesting pairs exhausted!")
    else do
      -- TODO Be smarter. Reset all rewriterators and just roll with the interesting pairs we have?
      let initial := g.strat_state.initial,
      -- FIXME this is a real hack: we currently use existance of an entry in the
      -- distance estimate table to determine if we have seen a given interesting
      -- pair before. This needs to change, and until then we have to do:
      vl ← clear_vertex <$> g.vertices.get table_ref.first,
      vr ← clear_vertex <$> g.vertices.get table_ref.first.next,
      let g := {g with vertices := table.from_list [vl, vr], estimates := table.create},
      g ← pexplore_startup g.strat_state.conf g m vl vr,
      return (g, status.repeat)
  | (none, _) := pexplore_step g m itr
  | (some best, others) := do
    (g, best, new) ← pop_ipairs m g g.strat_state.conf.pop_size best,
    (new_head, s) ← pure $ match new with
    | [] := ([], status.repeat)
    | l  := (l.concat best, status.continue)
    end,
    return (g.mutate_strat {g.strat_state with interesting_pairs := new_head.append others }, s)
  end

end tactic.rewrite_search.strategy.pexplore

namespace tactic.rewrite_search.strategy

open pexplore

meta def pexplore (conf : pexplore_config := {}) : strategy_constructor pexplore_state :=
λ β γ δ, strategy.mk pexplore_init (pexplore_startup conf) pexplore_step

end tactic.rewrite_search.strategy
