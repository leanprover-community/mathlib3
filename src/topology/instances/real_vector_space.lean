import topology.algebra.module topology.instances.real

variables {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E]
  [topological_vector_space ℝ E] {F : Type*} [add_comm_group F] [vector_space ℝ F]
  [topological_space F] [topological_vector_space ℝ F] [t2_space F]

namespace add_monoid_hom

lemma map_real_smul (f : E →+ F) (hf : continuous f) (c : ℝ) (x : E) :
  f (c • x) = c • f x :=
suffices (λ c : ℝ, f (c • x)) = λ c : ℝ, c • f x, from congr_fun this c,
dense_embedding_of_rat.dense.equalizer
  (hf.comp $ continuous_id.smul continuous_const)
  (continuous_id.smul continuous_const)
  (funext $ λ r, f.map_rat_cast_smul r x)

/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
def to_real_linear_map (f : E →+ F) (hf : continuous f) : E →L[ℝ] F :=
⟨⟨f, f.map_add, f.map_real_smul hf⟩, hf⟩

lemma coe_to_real_linear_map (f : E →+ F) (hf : continuous f) :
  ⇑(f.to_real_linear_map hf) = f := rfl

end add_monoid_hom
