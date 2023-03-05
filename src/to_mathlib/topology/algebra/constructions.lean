import topology.algebra.constructions

variables {α : Type*} {β : Type*} {γ : Type*} {R K E : Type*}

section
variables [monoid α] [topological_space α] [t2_space α]

instance : t2_space αˣ := (units.embedding_embed_product).t2_space

end
