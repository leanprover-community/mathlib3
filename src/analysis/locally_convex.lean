import analysis.normed_space.basic
import analysis.seminorm

variables {𝕜 : Type*} {E : Type*} [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables {ι : Type*} [decidable_eq ι]

@[derive [add_comm_group, module 𝕜]] def seminorm.domain (s : seminorm 𝕜 E) := E

instance (s : seminorm 𝕜 E) : has_norm s.domain := ⟨s.to_fun⟩

lemma seminorm.is_core (s : seminorm 𝕜 E) : semi_normed_group.core s.domain :=
  ⟨s.zero, s.triangle, s.neg⟩

instance (s : seminorm 𝕜 E) : semi_normed_group s.domain :=
  semi_normed_group.of_core s.domain s.is_core

protected def seminorm.uniform_space (s : seminorm 𝕜 E) : uniform_space E :=
  (by apply_instance : uniform_space s.domain)

lemma seminorm.smul_le (s : seminorm 𝕜 E) (c : 𝕜) (x : E) : s (c • x) ≤ ∥c∥ * s x := by rw s.smul

instance (s : seminorm 𝕜 E) : semi_normed_space 𝕜 s.domain := {norm_smul_le := s.smul_le}

def seminorm.seminormed_top_group (s : seminorm 𝕜 E) :
  topological_add_group (s.domain) := (by apply_instance : topological_add_group s.domain)

def seminorm.add_group_top (s : seminorm 𝕜 E) : add_group_topology E :=
  { to_topological_space := s.uniform_space.to_topological_space,
  to_topological_add_group := s.seminormed_top_group }

@[derive [add_comm_group, module 𝕜]]
def with_seminorms (s : ι → seminorm 𝕜 E) := E

def with_seminorms_add_group_top (s : ι → seminorm 𝕜 E) : add_group_topology (with_seminorms s) :=
  ⨅ i, (s i).add_group_top

--instance (s : ι → seminorm 𝕜 E) : uniform_space (with_seminorms s) := ⨅ i, (s i).uniform_space
instance (s : ι → seminorm 𝕜 E) : topological_space (with_seminorms s) :=
  (with_seminorms_add_group_top s).to_topological_space
instance (s : ι → seminorm 𝕜 E) : topological_add_group (with_seminorms s) :=
  (with_seminorms_add_group_top s).to_topological_add_group


/-instance (s : ι → seminorm 𝕜 E) : has_continuous_smul 𝕜 (with_seminorms s) :=
begin
  sorry,
end-/

variables (s : ι → seminorm 𝕜 E) (i : ι)
#check (s i).seminormed_top_group
#check (s)


-- Todo: local convexity
