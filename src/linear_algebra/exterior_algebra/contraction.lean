/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.exterior_algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.tensor_product
import linear_algebra.prod

/-!
# Contraction in Exterior Algebras
-/

universes u1 u2 u3

variables {R : Type u1} [comm_ring R]
variables {M : Type u2} [add_comm_group M] [module R M]

namespace exterior_algebra

variables (B : module.dual R M)

/-- The map `g v (x, y) = (ι R v * x, -ι R v * y + B v • x)` -/
def g (B : module.dual R M) :
  M →ₗ[R] module.End R (exterior_algebra R M × exterior_algebra R M) :=
begin
  have v_mul := (algebra.lmul R (exterior_algebra R M)).to_linear_map.comp (ι R),
  have l := v_mul.compl₂ (linear_map.fst _ _ (exterior_algebra R M)),
  have r := -v_mul.compl₂ (linear_map.snd _ (exterior_algebra R M) _) +
            B.smul_right (linear_map.fst _ (exterior_algebra R M) (exterior_algebra R M)),
  exact
    { to_fun := λ v, (l v).prod (r v),
      map_add' := λ v₂ v₂, linear_map.ext $ λ x, prod.ext
        (linear_map.congr_fun (l.map_add _ _) x) (linear_map.congr_fun (r.map_add _ _) x),
      map_smul' := λ c v, linear_map.ext $ λ x, prod.ext
        (linear_map.congr_fun (l.map_smul _ _) x) (linear_map.congr_fun (r.map_smul _ _) x), },
end

lemma g_apply_apply (v : M) (x : exterior_algebra R M × exterior_algebra R M) :
  g B v x = (ι R v * x.fst, -(ι R v * x.snd) + B v • x.fst) :=
rfl

lemma g_g (v : M) (x : exterior_algebra R M × exterior_algebra R M) : g B v (g B v x) = 0 :=
begin
  simp only [g_apply_apply],
  rw [neg_mul_eq_mul_neg, neg_add, neg_neg, mul_add, mul_neg_eq_neg_mul_symm, mul_smul_comm,
    ←sub_eq_add_neg, sub_add_cancel, ←mul_assoc, ←mul_assoc, ι_sq_zero, zero_mul, zero_mul],
  refl,
end

lemma g_comp_g (v : M) : (g B v).comp (g B v) = 0 :=
linear_map.ext $ g_g B v

/-- Intermediate result for `exterior_algebra.contract`. -/
def g' : exterior_algebra R M →ₐ[R] module.End R (exterior_algebra R M × exterior_algebra R M) :=
exterior_algebra.lift R ⟨g B, λ v, (g_comp_g B v : _)⟩

/-- Contract an element of the exterior algebra with an element `B : module.dual R M`. -/
def contract : exterior_algebra R M →ₗ[R] exterior_algebra R M :=
(linear_map.snd _ _ _).comp ((g' B).to_linear_map.flip (1, 0))

@[simp] lemma contract_ι (x : M) : contract B (ι R x) = algebra_map R _ (B x) :=
begin
  dsimp [contract, g'],
  simp only [lift_ι_apply, g_apply_apply, mul_zero, neg_zero, zero_add],
  rw algebra.algebra_map_eq_smul_one,
end

@[simp] lemma contract_algebra_map (r : R) : contract B (algebra_map R _ r) = 0 :=
begin
  dsimp [contract, g'],
  simp only [alg_hom.commutes, prod.smul_mk, module.algebra_map_End_apply, smul_zero],
end

/-- TODO: generalize `ι R b` to an arbitrary element `b`. -/
lemma contract_ι_mul_ι (a b : M) :
  contract B (ι R a * ι R b) = contract B (ι R a) * ι R b - ι R a * contract B (ι R b) :=
begin
  dsimp [contract, g'],
  simp_rw [alg_hom.map_mul, linear_map.mul_apply, lift_ι_apply, g_apply_apply, mul_zero, neg_zero,
    zero_add, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, neg_add_eq_sub],
end

end exterior_algebra
