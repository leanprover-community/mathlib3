import topology.basic
import topology.order
import data.set.intervals.basic
import order.upper_lower

universes u v w
variables {α : Type u}

open  set topological_space

-- def Ici (a : α) := {x | a ≤ x}


class lower_topology (α : Type*) [t : topological_space α] [preorder α] : Prop :=
(topology_eq_generate_Ici_comp : t = generate_from {s | ∃a, s = (Ici a)ᶜ })

section lower_topology

variables [topological_space α] [partial_order α] [t : lower_topology α]
include t

#check t.topology_eq_generate_Ici_comp
#check generate_open.sUnion

lemma lower_open_is_lower {s : set α} [h: is_open s] : is_lower_set s :=
begin
  intro,
  intro,
  intro hba,
  intro ha,
  --suggest,
--simp [t.topology_eq_generate_Ici_comp],
  --convert @lower_topology.topology_eq_generate_Ici_comp α _ _ _,
  --rw h,
  rw t.topology_eq_generate_Ici_comp at h,
  sorry
end

end lower_topology
