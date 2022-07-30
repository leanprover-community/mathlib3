import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition

import .mathlib
import .reachable_outside
import .ends

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           {V' : Type v}
           (G' : simple_graph V')
           {V'' : Type w}
           (G'' : simple_graph V'')

namespace ends

open ro_component
open simple_graph

lemma ends_product (Vinf : set.infinite (@set.univ V)) (V'inf : set.infinite (@set.univ V')) := sorry
--  ends box_prod G G' ≃ true
-- just want to say the cardinality is 1

end ends

end simple_graph
