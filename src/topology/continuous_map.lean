import topology.subset_properties

@[protect_proj]
structure continuous_map (α : Type*) (β : Type*)
[topological_space α] [topological_space β] :=
(to_fun             : α → β)
(continuous_to_fun  : continuous to_fun)

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

instance : has_coe_to_fun (C(α, β)) := ⟨_, continuous_map.to_fun⟩

variables {α β} {f g : continuous_map α β}
@[ext] theorem ext (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

instance [inhabited β] : inhabited C(α, β) :=
⟨⟨λ _, default _, continuous_const⟩⟩

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

def const (b : β) : C(α, β) := ⟨λ x, b, continuous_const⟩

end continuous_map
