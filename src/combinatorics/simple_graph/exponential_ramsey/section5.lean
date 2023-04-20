import combinatorics.simple_graph.exponential_ramsey.section4
import combinatorics.simple_graph.graph_probability

open real

-- example {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) : 2 ^ ε ≤ 1 + ε :=
-- begin

-- end

example {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) : ε * log 2 ≤ log (1 + ε) :=
begin
  rw le_log_iff_exp_le,
  swap,
  { linarith },
  have := convex_on_exp.2,
end
