/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.quadratic_form.isometry
import linear_algebra.quadratic_form.prod
/-!
# Quadratic form structures related to `module.dual`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `bilin_form.dual_prod R M`, the bilinear form on `(f, x) : module.dual R M × M` defined as
  `f x`.
* `quadratic_form.dual_prod R M`, the quadratic form on `(f, x) : module.dual R M × M` defined as
  `f x`.
* `quadratic_form.to_dual_prod : M × M →ₗ[R] module.dual R M × M` a form-preserving map from
  `(Q.prod $ -Q)` to `quadratic_form.dual_prod R M`. Note that we do not have the morphism
  version of `quadratic_form.isometry`, so for now this is stated without full bundling.

-/

variables (R M N : Type*)

namespace bilin_form

section semiring
variables [comm_semiring R] [add_comm_monoid M] [module R M]

/-- The symmetric bilinear form on `module.dual R M × M` defined as
`B (f, x) (g, y) = f y + g x`. -/
@[simps]
def dual_prod : bilin_form R (module.dual R M × M) :=
linear_map.to_bilin $
  (linear_map.applyₗ.comp (linear_map.snd R (module.dual R M) M)).compl₂
    (linear_map.fst R (module.dual R M) M) +
  ((linear_map.applyₗ.comp (linear_map.snd R (module.dual R M) M)).compl₂
    (linear_map.fst R (module.dual R M) M)).flip

lemma is_symm_dual_prod : (dual_prod R M).is_symm :=
λ x y, add_comm _ _

end semiring

section ring
variables [comm_ring R] [add_comm_group M] [module R M]

lemma nondenerate_dual_prod :
  (dual_prod R M).nondegenerate ↔ function.injective (module.dual.eval R M) :=
begin
  classical,
  rw nondegenerate_iff_ker_eq_bot,
  rw linear_map.ker_eq_bot,
  let e := linear_equiv.prod_comm R _ _
    ≪≫ₗ module.dual_prod_dual_equiv_dual R (module.dual R M) M,
  let h_d := e.symm.to_linear_map.comp (dual_prod R M).to_lin,
  refine (function.injective.of_comp_iff e.symm.injective (dual_prod R M).to_lin).symm.trans _,
  rw [←linear_equiv.coe_to_linear_map, ←linear_map.coe_comp],
  change function.injective h_d ↔ _,
  have : h_d = linear_map.prod_map (linear_map.id) (module.dual.eval R M),
  { refine linear_map.ext (λ x, prod.ext _ _),
    { ext,
      dsimp [h_d, module.dual.eval, linear_equiv.prod_comm],
      simp },
    { ext,
      dsimp [h_d, module.dual.eval, linear_equiv.prod_comm],
      simp } },
  rw [this, linear_map.coe_prod_map],
  refine prod.map_injective.trans _,
  exact and_iff_right function.injective_id,
end

end ring

end bilin_form

namespace quadratic_form

section semiring
variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [module R M] [module R N]

/-- The quadratic form on `module.dual R M × M` defined as `Q (f, x) = f x`. -/
@[simps]
def dual_prod : quadratic_form R (module.dual R M × M) :=
{ to_fun := λ p, p.1 p.2,
  to_fun_smul := λ a p, by rw [prod.smul_fst, prod.smul_snd, linear_map.smul_apply,
                               linear_map.map_smul, smul_eq_mul, smul_eq_mul, mul_assoc],
  exists_companion' := ⟨bilin_form.dual_prod R M, λ p q, begin
    rw [bilin_form.dual_prod_apply, prod.fst_add, prod.snd_add, linear_map.add_apply, map_add,
      map_add, add_right_comm _ (q.1 q.2), add_comm (q.1 p.2) (p.1 q.2), ←add_assoc, ←add_assoc],
  end⟩ }

@[simp]
lemma _root_.bilin_form.dual_prod.to_quadratic_form :
  (bilin_form.dual_prod R M).to_quadratic_form = 2 • dual_prod R M :=
ext $ λ a, (two_nsmul _).symm

variables {R M N}

/-- Any module isomorphism induces a quadratic isomorphism between the corresponding `dual_prod.` -/
@[simps]
def dual_prod_isometry (f : M ≃ₗ[R] N) :
  (dual_prod R M).isometry (dual_prod R N) :=
{ to_linear_equiv := f.dual_map.symm.prod f,
  map_app' := λ x, fun_like.congr_arg x.fst $ f.symm_apply_apply _ }

/-- `quadratic_form.dual_prod` commutes (isometrically) with `quadratic_form.prod`. -/
@[simps]
def dual_prod_prod_isometry :
  (dual_prod R (M × N)).isometry ((dual_prod R M).prod (dual_prod R N)) :=
{ to_linear_equiv :=
  ((module.dual_prod_dual_equiv_dual R M N).symm.prod (linear_equiv.refl R (M × N)))
    ≪≫ₗ linear_equiv.prod_prod_prod_comm R _ _ M N,
  map_app' := λ m,
    (m.fst.map_add _ _).symm.trans $ fun_like.congr_arg m.fst $ prod.ext (add_zero _) (zero_add _) }

end semiring

section ring
variables [comm_ring R] [add_comm_group M] [module R M]

variables {R M}

/-- The isometry sending `(Q.prod $ -Q)` to `(quadratic_form.dual_prod R M)`.

This is `σ` from Proposition 4.8, page 84 of
[*Hermitian K-Theory and Geometric Applications*][hyman1973]; though we swap the order of the pairs.
-/
@[simps]
def to_dual_prod (Q : quadratic_form R M) [invertible (2 : R)] :
  M × M →ₗ[R] module.dual R M × M :=
linear_map.prod
  (Q.associated.to_lin.comp (linear_map.fst _ _ _)
    + Q.associated.to_lin.comp (linear_map.snd _ _ _))
  ((linear_map.fst _ _ _ - linear_map.snd _ _ _))

lemma to_dual_prod_isometry [invertible (2 : R)] (Q : quadratic_form R M) (x : M × M) :
  quadratic_form.dual_prod R M (to_dual_prod Q x) = (Q.prod $ -Q) x :=
begin
  dsimp only [to_dual_prod, associated, associated_hom],
  dsimp,
  simp [polar_comm _ x.1 x.2, ←sub_add, mul_sub, sub_mul, smul_sub, submonoid.smul_def,
    ←sub_eq_add_neg (Q x.1) (Q x.2)],
end

-- TODO: show that `to_dual_prod` is an equivalence

end ring

end quadratic_form
