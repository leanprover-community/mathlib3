import analysis.convex.basic

open linear_map
universes u v

variables {E : Type u} {F : Type v}
variables [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F]

lemma segment_image (f : E →ₗ[ℝ] F) (a b : E) : f '' segment a b = segment (f a) (f b) :=
set.ext (λ x, by simp [segment_eq_image])
