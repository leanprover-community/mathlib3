import tactic.rw_hint
-- Now import a bunch of stuff, to see if `rw_hint` is still usable.
-- (Unfortunately, it's not!)
import topology.uniform_space.uniform_embedding
import algebraic_geometry.stalks
import measure_theory.l1_space
import set_theory.zfc

open tactic

example : 2 * (3 + 4) = 2 * 3 + 2 * 4 :=
begin
  -- rw_hint,
  -- Collecting all the rewrites (~20k) from the environment takes a few seconds,
  -- but is still reasonable:
  tactic.try_for 15000 (tactic.rewrite_search.discovery.find_all_rewrites),
  -- Unfortunately trying them all becomes too slow:
  -- tactic.try_for 50000 (do s ← tactic.rw_hint, guard $ "rw left_distrib" ∈ s),
  rw left_distrib,
end
