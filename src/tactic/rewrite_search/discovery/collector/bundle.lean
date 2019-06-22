import data.rat.basic
import data.list

import lib.list
import tactic.rewrite_search.core.common

import ..types
import .common

open tactic

namespace tactic.rewrite_search.discovery

open tactic.rewrite_search

def BUNDLE_CHUNK_SIZE := 1

-- TODO Be smarter about calculating this.
meta def score_bundle (b : bundle_ref) (sample : list expr) : tactic ℕ := do
  mems ← b.get_members,
  mems.mfoldl (λ sum n, do
    e ← mk_const n,
    ret ← are_promising_rewrites (rewrite_list_from_lemma e) sample,
    return $ if ret then sum + 1 else sum
  ) 0

-- TODO report the lemma(s) which caused a selected bundle to be chosen,
-- so that that lemma could just be tagged individually.

-- TODO at the end of the search report which "desperations" things happened
-- (bundles added, random lemmas found and used) so that they can be addressed
-- more easily/conveniently.

def min_rel {α : Type} (l : list α) (r : α → α → Prop) [decidable_rel r] : option α :=
l.foldl (λ o a, match o with | none := some a | some b := if r b a then b else a end) none

meta def try_bundles (conf : core_cfg) (rs : list (expr × bool)) (p : progress) (sample : list expr) : tactic (progress × list (expr × bool)) :=
  if p.persistence < persistence.try_bundles then
    return (p, [])
  else do
    bs ← list.filter (λ b, b ∉ p.seen_bundles) <$> get_bundles,
    bs ← bs.mmap $ λ b, (do s ← score_bundle b sample, return (b, s)),
    (awful_bs, interesting_bs) ← pure $ bs.partition $ λ b, b.2 = 0,
    let p := {p with seen_bundles := p.seen_bundles.append (awful_bs.map prod.fst)},
    match min_rel interesting_bs (λ a b, a.2 > b.2) with
    | none := do
      if conf.trace_discovery then
      discovery_trace format!"Could not find any promising bundles of the {bs.length} non-suggested bundles considered: {bs.map $ λ b, b.1.bundle.name}"
      else skip,
      return (p, [])
    | some (b, score) := do
      if conf.trace_discovery then
      discovery_trace format!"Found a promising bundle (of {bs.length} considered) \"{b.bundle.name}\"! If we succeed, please suggest this bundle for consideration."
      else skip,
      ms ← b.get_members >>= load_names,
      return (p, rewrite_list_from_lemmas ms)
    end

end tactic.rewrite_search.discovery
