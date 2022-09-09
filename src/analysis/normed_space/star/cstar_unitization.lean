import algebra.algebra.unitization
import analysis.normed_space.star.basic
import algebra.star.star_alg_hom

.

open unitization

/-- The coercion from a non-unital ⋆-algebre `A` over `𝕜` to its unitization `unitization 𝕜 A`
realized as a non-unital algebra homomorphism. -/
@[simps]
def coe_non_unital_star_alg_hom (𝕜 A : Type*) [comm_semiring 𝕜] [star_add_monoid 𝕜]
  [non_unital_semiring A] [has_star A] [module 𝕜 A] :
  A →⋆ₙₐ[𝕜] unitization 𝕜 A :=
{ to_fun := coe, map_star' := coe_star, .. coe_non_unital_alg_hom 𝕜 A, }

variables {𝕜 A : Type*}
  [comm_semiring 𝕜] [star_ring 𝕜] [non_unital_semiring A] [star_ring A]
  [module 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] [star_module 𝕜 A]
  {B : Type*} [ring B] [star_ring B] [algebra 𝕜 B] [star_module 𝕜 B]

/-- Non-unital ⋆-algebra homomorphisms from `A` into a unital ⋆-algebra `B` over `𝕜` lift uniquely
to `unitization 𝕜 A →⋆ₐ[𝕜] B`. This is the universal property of the unitization. -/
--@[simps apply_apply]
def star_unitization.lift : (A →⋆ₙₐ[𝕜] B) ≃ (unitization 𝕜 A →⋆ₐ[𝕜] B) :=
{ to_fun := λ φ,
  { to_fun := λ x, algebra_map 𝕜 B x.fst + φ x.snd,
    map_star' := λ x,
    begin
      induction x using unitization.ind,
      simp only [map_star, star_add, fst_add, fst_star, fst_coe, star_zero, add_zero,
        algebra_map_star_comm, snd_add, snd_star, snd_inl, zero_add],
    end,
    .. unitization.lift φ.to_non_unital_alg_hom, },
  inv_fun := λ φ, φ.to_non_unital_star_alg_hom.comp (coe_non_unital_star_alg_hom 𝕜 A),
  left_inv := λ φ, by { ext, simp, },
  right_inv := sorry, } --λ φ, unitization.alg_hom_ext' (by { ext, simp }), }

/-
lemma lift_symm_apply (φ : unitization R A →ₐ[R] C) (a : A) :
  unitization.lift.symm φ a = φ a := rfl -/

end alg_hom
