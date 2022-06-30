/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import data.polynomial

/-!
# Modules over `R[X]`

## Main definitions

* `module_with_End E` : A type synonym for a `R`-module which explicitly mentions a given
  endomorphism `E`. It naturally comes with a `R[X]`-module structure, where the action of `X` is
  given by `E`.

## Main statements

* `module_with_End.polynomial_linear_equiv_semiconj` : equivalence between `R[X]`-linear maps and
  `R`-linear maps compatible with the action of `X`. See also
  `module_with_End.polynomial_lequiv_equiv_semiconj` for the restriction to linear isomorphisms.

## Tags

Module, polynomial
-/


variables {R M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]
open_locale polynomial


open polynomial module

/--A type synonym for a `R`-module which explicitly mentions a given endomorphism.-/
@[nolint unused_arguments has_inhabited_instance]
def module_with_End (E : End R M) := M

namespace module_with_End
variables {E : End R M}

instance : add_comm_monoid (module_with_End E) := (infer_instance : add_comm_monoid M)
instance : module R (module_with_End E) := (infer_instance : module R M)
/--The type conversion `M → module_with_End E`, as a `R`-linear isomorphism.-/
def of_module (E : End R M) : M ≃ₗ[R] module_with_End E := linear_equiv.refl R M
instance apply_module : module (End R M) (module_with_End E) :=
(infer_instance : module (End R M) M)

/-- Recursor for `module_with_End`. -/
@[elab_as_eliminator]
def rec {motive : module_with_End E → Sort*}
  (h : Π m, motive (of_module E m)) (m : module_with_End E) : motive m :=
h $ (of_module E).symm m

/--Defines a `R[X]`-module structure on a `R`-module given an endomorphism `E` which defines the
action of `X`.-/
noncomputable instance polynomial_module : module R[X] (module_with_End E) :=
comp_hom M (aeval E).to_ring_hom
lemma smul_def (P : R[X]) (u : M) :
  P • of_module E u = of_module E (aeval E P u) := rfl

lemma X_smul (u : M) : (X : R[X]) • of_module E u = of_module E (E u) :=
by rw [smul_def, aeval_X]
lemma C_smul (a : R) (u : M) : (C a) • of_module E u = of_module E (a • u) :=
by rw [smul_def, aeval_C, algebra_map_End_apply]

instance is_scalar_tower : is_scalar_tower R R[X] (module_with_End E) :=
⟨λ a P u, begin
  induction u using module_with_End.rec,
  rw [smul_def, alg_hom.map_smul, linear_map.smul_apply, (of_module E).map_smul, ← smul_def]
end⟩

/--A `R[X]`-module is a `R`-module with an endomorphism (given by the action of `X`).-/
noncomputable def of_polynomial_module [module R[X] M] [is_scalar_tower R R[X] M] :
  M ≃ₗ[R[X]] module_with_End (algebra.lsmul R M (X : R[X])) :=
{ map_smul' := λ P u, by
    rw [linear_equiv.to_fun_eq_coe, ring_hom.id_apply, smul_def, aeval_alg_hom_apply, aeval_X_left,
      alg_hom.id_apply, algebra.lsmul_coe],
  ..of_module _}

variables {E} {N : Type*} [add_comm_monoid N] [module R N] {F : End R N}
open linear_map linear_equiv

/--A `R[X]`-linear map is a `R`-linear map compatible with the action of `X`.-/
def polynomial_linear_of_semiconj {L : M →ₗ[R] N} (h : L.comp E = F.comp L) :
  module_with_End E →ₗ[R[X]] module_with_End F :=
{ map_smul' := λ P u, begin
    rw [linear_map.to_fun_eq_coe, ring_hom.id_apply],
    apply P.induction_on',
    { intros p q hp hq, rw [add_smul, add_smul, map_add, hp, hq] },
    { intros n a,
      have : L.comp (E ^ n) = (F ^ n).comp L,
      { induction n with n ih,
        { rw [pow_zero, one_eq_id, comp_id, pow_zero, one_eq_id, id_comp] },
        { rw [pow_succ, mul_eq_comp, ← linear_map.comp_assoc, h, linear_map.comp_assoc, ih,
            ← linear_map.comp_assoc, ← mul_eq_comp, ← pow_succ] } },
      induction u using module_with_End.rec,
      rw [comp_apply, comp_apply, coe_to_linear_map, coe_to_linear_map, smul_def, aeval_monomial,
        mul_apply, algebra_map_End_apply, symm_apply_apply, L.map_smul,
        comp_apply, comp_apply, coe_to_linear_map, coe_to_linear_map, smul_def, aeval_monomial,
        mul_apply, algebra_map_End_apply, symm_apply_apply, ← comp_apply, ← comp_apply, this] }
  end,
  ..(of_module F).to_linear_map.comp $ L.comp $ (of_module E).symm.to_linear_map }
@[simp] lemma polynomial_linear_of_semiconj_apply {L : M →ₗ[R] N} (h : L.comp E = F.comp L)
  (u : M) : polynomial_linear_of_semiconj h (of_module E u) = of_module F (L u) := rfl

/--A `R[X]`-linear isomorphism is a `R`-linear isomorphism compatible with the action of `X`.-/
def polynomial_lequiv_of_semiconj {L : M ≃ₗ[R] N}
  (h : (L : M →ₗ[R] N).comp E = F.comp (L : M →ₗ[R] N)) :
  module_with_End E ≃ₗ[R[X]] module_with_End F :=
{ map_smul' := (polynomial_linear_of_semiconj h).map_smul',
  ..(of_module E).symm.trans $ L.trans (of_module F) }
@[simp] lemma polynomial_lequiv_of_semiconj_apply {L : M ≃ₗ[R] N}
  (h : (L : M →ₗ[R] N).comp E = F.comp (L : M →ₗ[R] N)) (u : M) :
  polynomial_lequiv_of_semiconj h u = L u := rfl

/--A `R[X]`-linear map is a `R`-linear map compatible with the action of `X`.-/
noncomputable def semiconj_of_polynomial_linear (L : module_with_End E →ₗ[R[X]] module_with_End F) :
  { L : M →ₗ[R] N // L.comp E = F.comp L } :=
⟨(of_module F).symm.to_linear_map.comp $ (L.restrict_scalars R).comp (of_module E).to_linear_map,
begin
  ext u,
  simp only [comp_apply, coe_to_linear_map, linear_map.restrict_scalars_apply],
  rw [← X_smul, L.map_smul, symm_apply_eq, ← X_smul, apply_symm_apply]
end⟩
@[simp] lemma semiconj_of_polynomial_linear_apply (L : module_with_End E →ₗ[R[X]] module_with_End F)
  (u : M) : of_module F (semiconj_of_polynomial_linear L u) = L (of_module E u) := rfl

/--A `R[X]`-linear isomorphism is a `R`-linear isomorphism compatible with the action of `X`.-/
noncomputable def semiconj_of_polynomial_lequiv (L : module_with_End E ≃ₗ[R[X]] module_with_End F) :
  { L : M ≃ₗ[R] N // (L : M →ₗ[R] N).comp E = F.comp (L : M →ₗ[R] N) } :=
⟨(of_module E).trans $ (L.restrict_scalars R).trans (of_module F).symm,
begin
  ext u,
  simp only [comp_apply, linear_equiv.coe_coe, trans_apply, linear_equiv.restrict_scalars_apply],
  rw [← X_smul, L.map_smul, symm_apply_eq, ← X_smul, apply_symm_apply]
end⟩
@[simp] lemma semiconj_of_polynomial_lequiv_apply (L : module_with_End E ≃ₗ[R[X]] module_with_End F)
  (u : M) : of_module F (semiconj_of_polynomial_lequiv L u) = L (of_module E u) := rfl

/--Equivalence between `R[X]`-linear maps and `R`-linear maps compatible with the action of `X`.-/
@[simps] noncomputable def polynomial_linear_equiv_semiconj :
  (module_with_End E →ₗ[R[X]] module_with_End F) ≃ { L : M →ₗ[R] N // L.comp E = F.comp L } :=
{ to_fun := semiconj_of_polynomial_linear,
  inv_fun := λ L, polynomial_linear_of_semiconj L.prop,
  left_inv := λ L, by ext u; refl,
  right_inv := λ L, by ext u; refl }

/--Equivalence between `R[X]`-linear isomorphisms and `R`-linear isomorphisms compatible with the
action of `X`.-/
@[simps] noncomputable def polynomial_lequiv_equiv_semiconj :
  (module_with_End E ≃ₗ[R[X]] module_with_End F) ≃
  { L : M ≃ₗ[R] N // (L : M →ₗ[R] N).comp E = F.comp (L : M →ₗ[R] N) } :=
{ to_fun := semiconj_of_polynomial_lequiv,
  inv_fun := λ L, polynomial_lequiv_of_semiconj L.prop,
  left_inv := λ L, by ext u; refl,
  right_inv := λ L, by ext u; refl }

end module_with_End
