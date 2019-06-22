import tactic.rewrite_search.core.common

import ..types
import .common

open tactic

namespace tactic.rewrite_search.discovery

open tactic.rewrite_search

-- TODO print the lemmas which were being added
-- TODO use the metric to score the rewrites and pick the top few which are high-scoring
-- TODO only try some of of the "found rewrites" at a time and store the ones we've done in the progress

meta def try_everything (conf : core_cfg) (rs : list (expr × bool)) (p : progress) (sample : list expr) : tactic (progress × list (expr × bool)) := do
  if p.persistence < persistence.try_everything then
    return (p, [])
  else do
    my_prefix ← name.get_prefix <$> decl_name,
-- TODO this is a compromise with the time it takes to process
-- TODO implement banned namespaces (when this is removed) (maybe only go `n` heirachy levels up?)
    lems ← (list.filter_map $ λ rw : name × expr,
      if rw.1.get_prefix = my_prefix then
        some rw.1
      else
        none) <$> find_all_rewrites,
    lems ← load_names lems,
    let rws := (rewrite_list_from_lemmas lems).filter $ λ rw, rw ∉ rs,
    rws ← rws.mfilter $ λ rw, is_promising_rewrite rw sample,
    if conf.trace_discovery then do
      let n := rws.length,
      if n = 0 then
        discovery_trace "The entire current environment was searched, and no interesting rewrites could be found!"
      else do
        discovery_trace format!"The entire current environment was searched, and we have added {n} new rewrites(s) for consideration." ff,
        discovery_trace format!"Lemmas: {(rws.map prod.fst).erase_dup}"
    else skip,
    return (p, rws)

end tactic.rewrite_search.discovery
