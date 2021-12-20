import analysis.normed_space.basic
import analysis.seminorm

variables {𝕜 : Type*} {E : Type*} [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]

def seminorm.domain (s : seminorm 𝕜 E) := E

variables (s : seminorm 𝕜 E)

instance (s : seminorm 𝕜 E) : has_norm s.domain := ⟨s.to_fun⟩
instance (s : seminorm 𝕜 E) : add_comm_group s.domain :=
begin
  unfold seminorm.domain,
  apply_instance,
end

instance (s : seminorm 𝕜 E) : module 𝕜 s.domain :=
begin
  dunfold seminorm.domain,
  apply_instance,
end

def seminorm.to_core (s : seminorm 𝕜 E) :=
  semi_normed_group.core

lemma seminorm.is_core (s : seminorm 𝕜 E) : semi_normed_group.core s.domain :=
  ⟨ s.zero, s.triangle, s.neg⟩

instance (s : seminorm 𝕜 E) : semi_normed_group s.domain :=
  semi_normed_group.of_core s.domain s.is_core

protected def seminorm.uniform_space (s : seminorm 𝕜 E) : uniform_space E :=
(by apply_instance : uniform_space s.domain)

lemma seminorm.smul_le (s : seminorm 𝕜 E) (c : 𝕜) (x : E) : s (c • x) ≤ ∥c∥ * s x := by rw s.smul

instance (s : seminorm 𝕜 E) : semi_normed_space 𝕜 s.domain :=
  {to_module := _, norm_smul_le := s.smul_le}
