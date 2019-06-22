import tactic.rewrite_all

import ..screening

open tactic

namespace tactic.rewrite_search.discovery

meta def are_promising_rewrites (rws : list (expr × bool)) : list expr → tactic bool
| [] := return false
| (s :: rest) := do
-- TODO alternative (and probably better) condition:
-- tt if the rewrite list contains an expression not seen in the rewrite_search
-- instance, ff otherwise. Maybe too harsh/coarse?
  e ← mllist.empty (all_rewrites rws s),
  return e.down

meta def is_promising_rewrite (rw : expr × bool) : list expr → tactic bool :=
  are_promising_rewrites [rw]

end tactic.rewrite_search.discovery