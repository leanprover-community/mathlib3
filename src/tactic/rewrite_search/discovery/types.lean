import tactic.rewrite_search.core.common

import .common
import .bundle

universe u

namespace tactic.rewrite_search.discovery

open tactic.rewrite_search

meta def discovery_trace {α : Type u} [has_to_tactic_format α] (a : α) (nl : bool := tt) : tactic unit := do
  str ← tactic.pp a,
  let nlc := if nl then "\n" else "",
  cur ← tactic.decl_name,
  tactic.trace format!"(discovery@{cur}): {str}{nlc}"

meta def collector := core_cfg → list (expr × bool) → progress → list expr → tactic (progress × list (expr × bool))

end tactic.rewrite_search.discovery
