/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import ring_theory.derivation.basic
import ring_theory.ideal.quotient_operations

/-!
# Results

- `derivation_to_square_zero_equiv_lift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

-/

section to_square_zero

universes u v w

variables {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [comm_semiring A] [comm_ring B]
variables [algebra R A] [algebra R B] (I : ideal B) (hI : I ^ 2 = ⊥)

/-- If `f₁ f₂ : A →ₐ[R] B` are two lifts of the same `A →ₐ[R] B ⧸ I`,
  we may define a map `f₁ - f₂ : A →ₗ[R] I`. -/
def diff_to_ideal_of_quotient_comp_eq (f₁ f₂ : A →ₐ[R] B)
  (e : (ideal.quotient.mkₐ R I).comp f₁ = (ideal.quotient.mkₐ R I).comp f₂) :
  A →ₗ[R] I :=
linear_map.cod_restrict (I.restrict_scalars _) (f₁.to_linear_map - f₂.to_linear_map)
begin
  intro x,
  change f₁ x - f₂ x ∈ I,
  rw [← ideal.quotient.eq, ← ideal.quotient.mkₐ_eq_mk R, ← alg_hom.comp_apply, e],
  refl,
end

@[simp]
lemma diff_to_ideal_of_quotient_comp_eq_apply (f₁ f₂ : A →ₐ[R] B)
  (e : (ideal.quotient.mkₐ R I).comp f₁ = (ideal.quotient.mkₐ R I).comp f₂) (x : A) :
  ((diff_to_ideal_of_quotient_comp_eq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
rfl

variables [algebra A B] [is_scalar_tower R A B]

include hI

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each lift `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to a `R`-derivation from `A` to `I`. -/
def derivation_to_square_zero_of_lift
  (f : A →ₐ[R] B) (e : (ideal.quotient.mkₐ R I).comp f = is_scalar_tower.to_alg_hom R A (B ⧸ I)) :
  derivation R A I :=
begin
  refine
  { map_one_eq_zero' := _,
    leibniz' := _,
    ..(diff_to_ideal_of_quotient_comp_eq I f (is_scalar_tower.to_alg_hom R A B) _) },
  { rw e, ext, refl },
  { ext, change f 1 - algebra_map A B 1 = 0, rw [map_one, map_one, sub_self] },
  { intros x y,
    let F := diff_to_ideal_of_quotient_comp_eq I f (is_scalar_tower.to_alg_hom R A B)
      (by { rw e, ext, refl }),
    have : (f x - algebra_map A B x) * (f y - algebra_map A B y) = 0,
    { rw [← ideal.mem_bot, ← hI, pow_two],
      convert (ideal.mul_mem_mul (F x).2 (F y).2) using 1 },
    ext,
    dsimp only [submodule.coe_add, submodule.coe_mk, linear_map.coe_mk,
      diff_to_ideal_of_quotient_comp_eq_apply, submodule.coe_smul_of_tower,
      is_scalar_tower.coe_to_alg_hom', linear_map.to_fun_eq_coe],
    simp only [map_mul, sub_mul, mul_sub, algebra.smul_def] at ⊢ this,
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this,
    rw this,
    ring }
end

lemma derivation_to_square_zero_of_lift_apply (f : A →ₐ[R] B)
  (e : (ideal.quotient.mkₐ R I).comp f = is_scalar_tower.to_alg_hom R A (B ⧸ I))
  (x : A) : (derivation_to_square_zero_of_lift I hI f e x : B) = f x - algebra_map A B x := rfl

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps {attrs := []}]
def lift_of_derivation_to_square_zero (f : derivation R A I) :
  A →ₐ[R] B :=
{ to_fun := λ x, f x + algebra_map A B x,
  map_one' := by rw [map_one, f.map_one_eq_zero, submodule.coe_zero, zero_add],
  map_mul' := λ x y, begin
    have : (f x : B) * (f y) = 0,
    { rw [← ideal.mem_bot, ← hI, pow_two], convert (ideal.mul_mem_mul (f x).2 (f y).2) using 1 },
    simp only [map_mul, f.leibniz, add_mul, mul_add, submodule.coe_add,
      submodule.coe_smul_of_tower, algebra.smul_def, this],
    ring
  end,
  commutes' := λ r,
    by simp only [derivation.map_algebra_map, eq_self_iff_true, zero_add, submodule.coe_zero,
      ←is_scalar_tower.algebra_map_apply R A B r],
  map_zero' := ((I.restrict_scalars R).subtype.comp f.to_linear_map +
    (is_scalar_tower.to_alg_hom R A B).to_linear_map).map_zero,
  ..((I.restrict_scalars R).subtype.comp f.to_linear_map +
    (is_scalar_tower.to_alg_hom R A B).to_linear_map : A →ₗ[R] B) }

@[simp] lemma lift_of_derivation_to_square_zero_mk_apply (d : derivation R A I) (x : A) :
  ideal.quotient.mk I (lift_of_derivation_to_square_zero I hI d x) = algebra_map A (B ⧸ I) x :=
by { rw [lift_of_derivation_to_square_zero_apply, map_add,
  ideal.quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add], refl }

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`,
there is a 1-1 correspondance between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps]
def derivation_to_square_zero_equiv_lift :
  derivation R A I ≃
    { f : A →ₐ[R] B // (ideal.quotient.mkₐ R I).comp f = is_scalar_tower.to_alg_hom R A (B ⧸ I) } :=
begin
  refine ⟨λ d, ⟨lift_of_derivation_to_square_zero I hI d, _⟩, λ f,
    (derivation_to_square_zero_of_lift I hI f.1 f.2 : _), _, _⟩,
  { ext x, exact lift_of_derivation_to_square_zero_mk_apply I hI d x },
  { intro d, ext x, exact add_sub_cancel (d x : B) (algebra_map A B x) },
  { rintro ⟨f, hf⟩, ext x,  exact sub_add_cancel (f x) (algebra_map A B x) }
end

end to_square_zero
