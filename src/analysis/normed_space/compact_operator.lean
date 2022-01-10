import analysis.normed_space.basic

variables {𝕜 : Type*} [normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]

def compact_operator (T : E →ₗ[𝕜] F) : Prop :=
∀ s : set E, metric.bounded s → is_compact (closure (T '' s))

/-- If a compact operator preserves a submodule, its restriction to that submodule is compact. -/
lemma compact_operator.restrict_invariant {T : E →ₗ[𝕜] E} (hT : compact_operator T)
  {V : submodule 𝕜 E} (hV : ∀ v ∈ V, T v ∈ V) :
  compact_operator (T.restrict hV) :=
sorry
