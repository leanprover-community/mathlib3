import tactic.tcache.tactic

namespace tcache

open tactic

meta def execute_with (_ : unit) (tac : tactic unit) : tactic unit := tcache_core tac

meta def executor : interactive.executor tactic :=
{ config_type := unit, execute_with := execute_with }

end tcache
