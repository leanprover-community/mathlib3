import topology.constructions

open topological_space

variables {B : Type*} {B' : Type*} (E₁ : B → Type*) (E₂ : B → Type*)

/-- -/
def total_space := Σ x, E₁ x

@[reducible, simp] def pullback_total_space_embedding (f : B' → B) :
  total_space (E₁ ∘ f) → B' × (total_space E₁) :=
λ z : total_space (E₁ ∘ f), (z.1, ⟨(f z.1), z.2⟩)

variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]
  [topological_space B']

variables {E₁ E₂}

instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial B F)) :=
topological_space.induced (proj (trivial B F)) t₁ ⊓
  topological_space.induced (trivial.proj_snd B F) t₂

@[priority 90, nolint unused_arguments fails_quickly]
instance pullback.total_space.topological_space {f : B' → B} :
  topological_space (total_space (E₁ ∘ f)) :=
induced (pullback_total_space_embedding E₁ f) prod.topological_space

@[priority 90, nolint unused_arguments]
instance test : topological_space (total_space (λ x, E₁ x × E₂ x)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space ((total_space E₁) × (total_space E₂)))

#lint
