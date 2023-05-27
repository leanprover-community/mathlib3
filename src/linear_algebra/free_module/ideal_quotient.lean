/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import data.zmod.quotient
import linear_algebra.free_module.finite.basic
import linear_algebra.free_module.pid
import linear_algebra.quotient_pi

/-! # Ideals in free modules over PIDs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main results

 - `ideal.quotient_equiv_pi_span`: `S ⧸ I`, if `S` is finite free as a module over a PID `R`,
   can be written as a product of quotients of `R` by principal ideals.

-/

open_locale big_operators

variables {ι R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
variables [is_domain R] [is_principal_ideal_ring R] [is_domain S] [fintype ι]

/-- We can write the quotient of an ideal over a PID as a product of quotients by principal ideals.
-/
noncomputable def ideal.quotient_equiv_pi_span
  (I : ideal S) (b : basis ι R S) (hI : I ≠ ⊥) :
  (S ⧸ I) ≃ₗ[R] Π i, (R ⧸ ideal.span ({I.smith_coeffs b hI i} : set R)) :=
begin
  -- Choose `e : S ≃ₗ I` and a basis `b'` for `S` that turns the map
  -- `f := ((submodule.subtype I).restrict_scalars R).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := I.smith_coeffs b hI,
  let b' := I.ring_basis b hI,
  let ab := I.self_basis b hI,
  have ab_eq := I.self_basis_def b hI,
  let e : S ≃ₗ[R] I := b'.equiv ab (equiv.refl _),
  let f : S →ₗ[R] S := (I.subtype.restrict_scalars R).comp (e : S →ₗ[R] I),
  let f_apply : ∀ x, f x = b'.equiv ab (equiv.refl _) x := λ x, rfl,
  have ha : ∀ i, f (b' i) = a i • b' i,
  { intro i, rw [f_apply, b'.equiv_apply, equiv.refl_apply, ab_eq] },
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i,
  { intro x, simp_rw [ab.mem_ideal_iff', ab_eq],
    have : ∀ (c : ι → R) i, b'.repr (∑ (j : ι), c j • a j • b' j) i = a i * c i,
    { intros c i,
      simp only [← mul_action.mul_smul, b'.repr_sum_self, mul_comm] },
    split,
    { rintro ⟨c, rfl⟩ i, exact ⟨c i, this c i⟩ },
    { rintros ha,
      choose c hc using ha, exact ⟨c, b'.ext_elem (λ i, trans (hc i) (this c i).symm)⟩ } },

  -- Now we map everything through the linear equiv `S ≃ₗ (ι → R)`,
  -- which maps `I` to `I' := Π i, a i ℤ`.
  let I' : submodule R (ι → R) := submodule.pi set.univ (λ i, ideal.span ({a i} : set R)),
  have : submodule.map (b'.equiv_fun : S →ₗ[R] (ι → R)) (I.restrict_scalars R) = I',
  { ext x,
    simp only [submodule.mem_map, submodule.mem_pi, ideal.mem_span_singleton, set.mem_univ,
               submodule.restrict_scalars_mem, mem_I_iff, smul_eq_mul, forall_true_left,
               linear_equiv.coe_coe, basis.equiv_fun_apply],
    split,
    { rintros ⟨y, hy, rfl⟩ i, exact hy i },
    { rintros hdvd,
      refine ⟨∑ i, x i • b' i, λ i, _, _⟩; rwa b'.repr_sum_self,
      { exact hdvd i } } },
  refine ((submodule.quotient.restrict_scalars_equiv R I).restrict_scalars R).symm.trans _,
  any_goals { apply ring_hom.id }, any_goals { apply_instance },
  refine (submodule.quotient.equiv (I.restrict_scalars R) I' b'.equiv_fun this).trans _,
  any_goals { apply ring_hom.id }, any_goals { apply_instance },
  classical,
  let := submodule.quotient_pi (show Π i, submodule R R, from λ i, ideal.span ({a i} : set R)),
  exact this
end

/-- Ideal quotients over a free finite extension of `ℤ` are isomorphic to a direct product of
`zmod`. -/
noncomputable def ideal.quotient_equiv_pi_zmod
  (I : ideal S) (b : basis ι ℤ S) (hI : I ≠ ⊥) :
  (S ⧸ I) ≃+ Π i, (zmod (I.smith_coeffs b hI i).nat_abs) :=
let a := I.smith_coeffs b hI,
    e := I.quotient_equiv_pi_span b hI,
    e' : (Π (i : ι), (ℤ ⧸ ideal.span ({a i} : set ℤ))) ≃+ Π (i : ι), zmod (a i).nat_abs :=
  add_equiv.Pi_congr_right (λ i, ↑(int.quotient_span_equiv_zmod (a i)))
in (↑(e : (S ⧸ I) ≃ₗ[ℤ] _) : (S ⧸ I ≃+ _)).trans e'

/-- A nonzero ideal over a free finite extension of `ℤ` has a finite quotient.

Can't be an instance because of the side condition `I ≠ ⊥`, and more importantly,
because the choice of `fintype` instance is non-canonical.
-/
noncomputable def ideal.fintype_quotient_of_free_of_ne_bot [module.free ℤ S] [module.finite ℤ S]
  (I : ideal S) (hI : I ≠ ⊥) :
  fintype (S ⧸ I) :=
let b := module.free.choose_basis ℤ S,
    a := I.smith_coeffs b hI,
    e := I.quotient_equiv_pi_zmod b hI
in by haveI : ∀ i, ne_zero (a i).nat_abs :=
    (λ i, ⟨int.nat_abs_ne_zero_of_ne_zero (ideal.smith_coeffs_ne_zero b I hI i)⟩); classical;
  exact fintype.of_equiv (Π i, zmod (a i).nat_abs) e.symm
