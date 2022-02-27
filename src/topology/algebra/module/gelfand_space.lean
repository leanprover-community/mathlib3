import topology.algebra.module.weak_dual
import algebra.algebra.spectrum

/-- The Gelfand space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def gelfand_space (𝕜 : Type*) (A : Type*) [comm_semiring 𝕜] [topological_space 𝕜]
  [semiring A] [topological_space A] [module 𝕜 A] :=
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

variables {𝕜 : Type*} {A : Type*} [topological_space 𝕜] [topological_space A]

namespace gelfand_space

section semiring

variables [comm_semiring 𝕜] [semiring A] [algebra 𝕜 A]

-- TODO: upgrade this to `alg_hom_class` when it gets defined.
instance : ring_hom_class (gelfand_space 𝕜 A) A 𝕜 :=
{ map_one := λ φ, φ.prop.1,
  map_mul := λ φ, φ.prop.2,
  ..subtype.add_monoid_hom_class (weak_dual 𝕜 A) A 𝕜 _ }

/-- An element of the Gelfand space, as an algebra homomorphism. -/
def to_alg_hom (φ : gelfand_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_one' := ring_hom_class.map_one _,
  map_mul' := ring_hom_class.map_mul _,
  map_zero' := ring_hom_class.map_zero _,
  map_add' := ring_hom_class.map_add _,
  commutes' := λ r, by rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id,
        ring_hom.id_apply, @coe_fn_coe_base' _ (weak_dual 𝕜 A), continuous_linear_map.map_smul,
        algebra.id.smul_eq_mul, ←@coe_fn_coe_base', map_one, mul_one] }

end semiring

section ring

variables [comm_ring 𝕜] [ring A] [algebra 𝕜 A]

lemma apply_mem_spectrum [nontrivial 𝕜] (φ : gelfand_space 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
(to_alg_hom φ).apply_mem_spectrum a

end ring

end gelfand_space
