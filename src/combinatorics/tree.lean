import .simple_graph


open finset
open_locale big_operators
universes u v

variables {V : Type u}

section classical
open_locale classical

namespace simple_graph

variables {V} (T : simple_graph_on V) (a b : V) --(S : simple_graph (λ v, v ≠ a))

--def leaf (v : V T) [fintype (neighbor_set v)] : Prop := degree v = 1


end simple_graph

end classical
