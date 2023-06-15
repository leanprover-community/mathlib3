/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ideal.operations
import algebra.module.torsion
import algebra.ring.idempotents
import linear_algebra.finite_dimensional
import ring_theory.ideal.local_ring

/-!
# The module `I ⧸ I ^ 2`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `ideal.cotangent_equiv_ideal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

namespace ideal

variables {R S S' : Type*} [comm_ring R] [comm_semiring S] [algebra S R]
variables [comm_semiring S'] [algebra S' R] [algebra S S'] [is_scalar_tower S S' R] (I : ideal R)

/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
@[derive [add_comm_group, module (R ⧸ I)]]
def cotangent : Type* := I ⧸ (I • ⊤ : submodule R I)

instance : inhabited I.cotangent := ⟨0⟩

instance cotangent.module_of_tower : module S I.cotangent :=
submodule.quotient.module' _

instance : is_scalar_tower S S' I.cotangent :=
begin
  delta cotangent,
  constructor,
  intros s s' x,
  rw [← @is_scalar_tower.algebra_map_smul S' R, ← @is_scalar_tower.algebra_map_smul S' R,
    ← smul_assoc, ← is_scalar_tower.to_alg_hom_apply S S' R, map_smul],
  refl
end

instance [is_noetherian R I] : is_noetherian R I.cotangent := by { delta cotangent, apply_instance }

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps apply (lemmas_only)]
def to_cotangent : I →ₗ[R] I.cotangent := submodule.mkq _

lemma map_to_cotangent_ker : I.to_cotangent.ker.map I.subtype = I ^ 2 :=
by simp [ideal.to_cotangent, submodule.map_smul'', pow_two]

lemma mem_to_cotangent_ker {x : I} : x ∈ I.to_cotangent.ker ↔ (x : R) ∈ I ^ 2 :=
begin
  rw ← I.map_to_cotangent_ker,
  simp,
end

lemma to_cotangent_eq {x y : I} : I.to_cotangent x = I.to_cotangent y ↔ (x - y : R) ∈ I ^ 2 :=
begin
  rw [← sub_eq_zero, ← map_sub],
  exact I.mem_to_cotangent_ker
end

lemma to_cotangent_eq_zero (x : I) : I.to_cotangent x = 0 ↔ (x : R) ∈ I ^ 2 :=
I.mem_to_cotangent_ker

lemma to_cotangent_surjective : function.surjective I.to_cotangent :=
submodule.mkq_surjective _

lemma to_cotangent_range : I.to_cotangent.range = ⊤ :=
submodule.range_mkq _

lemma cotangent_subsingleton_iff :
  subsingleton I.cotangent ↔ is_idempotent_elem I :=
begin
  split,
  { introI H,
    refine (pow_two I).symm.trans (le_antisymm (ideal.pow_le_self two_ne_zero) _),
    exact λ x hx, (I.to_cotangent_eq_zero ⟨x, hx⟩).mp (subsingleton.elim _ _) },
  { exact λ e, ⟨λ x y, quotient.induction_on₂' x y $ λ x y,
      I.to_cotangent_eq.mpr $ ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩ }
end

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangent_to_quotient_square : I.cotangent →ₗ[R] R ⧸ I ^ 2 :=
submodule.mapq (I • ⊤) (I ^ 2) I.subtype
  (by { rw [← submodule.map_le_iff_le_comap, submodule.map_smul'', submodule.map_top,
    submodule.range_subtype, smul_eq_mul, pow_two], exact rfl.le })

lemma to_quotient_square_comp_to_cotangent : I.cotangent_to_quotient_square.comp I.to_cotangent =
  (I ^ 2).mkq.comp (submodule.subtype I) :=
linear_map.ext $ λ _, rfl

@[simp]
lemma to_cotangent_to_quotient_square (x : I) : I.cotangent_to_quotient_square (I.to_cotangent x) =
  (I ^ 2).mkq x := rfl

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangent_ideal (I : ideal R) : ideal (R ⧸ I ^ 2) :=
begin
  haveI : @ring_hom_surjective R (R ⧸ I ^ 2) _ _ _ := ⟨ideal.quotient.mk_surjective⟩,
  let rq := (I ^ 2)^.quotient.mk,
  exact submodule.map rq.to_semilinear_map I,
end

lemma cotangent_ideal_square (I : ideal R) : I.cotangent_ideal ^ 2 = ⊥ :=
begin
  rw [eq_bot_iff, pow_two I.cotangent_ideal, ← smul_eq_mul],
  intros x hx,
  apply submodule.smul_induction_on hx,
  { rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩, apply (submodule.quotient.eq _).mpr _,
    rw [sub_zero, pow_two], exact ideal.mul_mem_mul hx hy },
  { intros x y hx hy, exact add_mem hx hy }
end

lemma to_quotient_square_range :
  I.cotangent_to_quotient_square.range = I.cotangent_ideal.restrict_scalars R :=
begin
  transitivity (I.cotangent_to_quotient_square.comp I.to_cotangent).range,
  { rw [linear_map.range_comp, I.to_cotangent_range, submodule.map_top] },
  { rw [to_quotient_square_comp_to_cotangent, linear_map.range_comp, I.range_subtype], ext, refl }
end

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable
def cotangent_equiv_ideal : I.cotangent ≃ₗ[R] I.cotangent_ideal :=
begin
  refine
  { ..(I.cotangent_to_quotient_square.cod_restrict (I.cotangent_ideal.restrict_scalars R)
    (λ x, by { rw ← to_quotient_square_range, exact linear_map.mem_range_self _ _ })),
    ..(equiv.of_bijective _ ⟨_, _⟩) },
  { rintros x y e,
    replace e := congr_arg subtype.val e,
    obtain ⟨x, rfl⟩ := I.to_cotangent_surjective x,
    obtain ⟨y, rfl⟩ := I.to_cotangent_surjective y,
    rw I.to_cotangent_eq,
    dsimp only [to_cotangent_to_quotient_square, submodule.mkq_apply] at e,
    rwa submodule.quotient.eq at e },
  { rintro ⟨_, x, hx, rfl⟩,
    refine ⟨I.to_cotangent ⟨x, hx⟩, subtype.ext rfl⟩ }
end

@[simp, nolint simp_nf]
lemma cotangent_equiv_ideal_apply (x : I.cotangent) :
  ↑(I.cotangent_equiv_ideal x) = I.cotangent_to_quotient_square x := rfl

lemma cotangent_equiv_ideal_symm_apply (x : R) (hx : x ∈ I) :
  I.cotangent_equiv_ideal.symm ⟨(I ^ 2).mkq x, submodule.mem_map_of_mem hx⟩ =
    I.to_cotangent ⟨x, hx⟩ :=
begin
  apply I.cotangent_equiv_ideal.injective,
  rw I.cotangent_equiv_ideal.apply_symm_apply,
  ext,
  refl
end

variables {A B : Type*} [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]

/-- The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of `f`. -/
def _root_.alg_hom.ker_square_lift (f : A →ₐ[R] B) : A ⧸ f.to_ring_hom.ker ^ 2 →ₐ[R] B :=
begin
  refine { commutes' := _, ..(ideal.quotient.lift (f.to_ring_hom.ker ^ 2) f.to_ring_hom _) },
  { intros a ha, exact ideal.pow_le_self two_ne_zero ha },
  { intro r, rw [is_scalar_tower.algebra_map_apply R A, ring_hom.to_fun_eq_coe,
      ideal.quotient.algebra_map_eq, ideal.quotient.lift_mk], exact f.map_algebra_map r },
end

lemma _root_.alg_hom.ker_ker_sqare_lift (f : A →ₐ[R] B) :
  f.ker_square_lift.to_ring_hom.ker = f.to_ring_hom.ker.cotangent_ideal :=
begin
  apply le_antisymm,
  { intros x hx, obtain ⟨x, rfl⟩ := ideal.quotient.mk_surjective x, exact ⟨x, hx, rfl⟩ },
  { rintros _ ⟨x, hx, rfl⟩, exact hx }
end

/-- The quotient ring of `I ⧸ I ^ 2` is `R ⧸ I`. -/
def quot_cotangent : ((R ⧸ I ^ 2) ⧸ I.cotangent_ideal) ≃+* R ⧸ I :=
begin
  refine (ideal.quot_equiv_of_eq (ideal.map_eq_submodule_map _ _).symm).trans _,
  refine (double_quot.quot_quot_equiv_quot_sup _ _).trans _,
  exact (ideal.quot_equiv_of_eq (sup_eq_right.mpr $ ideal.pow_le_self two_ne_zero)),
end

end ideal

namespace local_ring

variables (R : Type*) [comm_ring R] [local_ring R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
@[reducible] def cotangent_space : Type* := (maximal_ideal R).cotangent

instance : module (residue_field R) (cotangent_space R) :=
ideal.cotangent.module _

instance : is_scalar_tower R (residue_field R) (cotangent_space R) :=
module.is_torsion_by_set.is_scalar_tower _

instance [is_noetherian_ring R] : finite_dimensional (residue_field R) (cotangent_space R) :=
module.finite.of_restrict_scalars_finite R _ _

end local_ring
