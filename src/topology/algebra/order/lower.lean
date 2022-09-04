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

lemma is_open_iff_generate_Ici_comp {s : set α} :
  is_open s ↔ generate_open {s | ∃a, s = (Ici a)ᶜ} s :=
by rw [t.topology_eq_generate_Ici_comp]; refl

lemma ici_comp_is_lower (a : α) : is_lower_set (Ici a)ᶜ :=
begin
  intro c,
  finish,
end


#check t.topology_eq_generate_Ici_comp
#check generate_open.sUnion

#check is_lower_set_sUnion
#check is_lower_set.inter

lemma lower_open_is_lower {s : set α} [h: is_open s] : is_lower_set s :=
begin
  rw is_open_iff_generate_Ici_comp at h,
  induction h,
  case topological_space.generate_open.basic : { sorry },
  case topological_space.generate_open.univ : { sorry },
  case topological_space.generate_open.inter : { sorry },
  case topological_space.generate_open.sUnion : { sorry },
end

end lower_topology
