import tactic.basic
import .store

open tactic tcache

namespace tactic

@[inline] meta def are_goals_present : tactic bool :=
lock_tactic_state $ do
   /- In a `run_cmd` or similar, there is a single goal
      with type `true`. If we can clear it using triv,
      disable caching. -/
   try triv,
   gs ← get_goals,
   return $ gs.length ≠ 0

@[inline] meta def if_goals_present {α : Type} (alt : tactic α) (t : tactic α) : tactic α :=
do r ← are_goals_present,
   if r then t else do
     hash ← decl_name >>= hash_goals,
     tcache.trace hash "skipping, no goals",
     alt

meta def tcache_core (t : tactic unit) : tactic unit := discharge_goals t
meta def tcache (t : tactic unit) : tactic unit := if_goals_present t (discharge_goals t)
meta def tc : tactic unit → tactic unit := tactic.tcache

meta def tcache_force {α : Type} (t : tactic α) : tactic α :=
if_goals_present t $ do
  init_tcache,
  tcache_core $ @unchecked_cast (tactic α) (tactic unit) t,
  return $ @unchecked_cast unit α ()

namespace interactive

meta def tcache (t : interactive.itactic) : tactic unit := tactic.tcache t
meta def tc (t : interactive.itactic) : tactic unit := tactic.tcache t

end interactive

end tactic


