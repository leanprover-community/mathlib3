import tactic.rw_hint
-- Now import a bunch of stuff, to make sure `rw_hint` is still usable.
import topology.uniform_space.uniform_embedding
import algebraic_geometry.stalks
import measure_theory.l1_space
import set_theory.zfc

open tactic

example : 2 * (3 + 4) = 2 * 3 + 2 * 4 :=
begin
  -- rw_hint,
  try_for 5500 (do s ← tactic.rw_hint, guard $ "rw left_distrib" ∈ s),
  rw left_distrib,
end
