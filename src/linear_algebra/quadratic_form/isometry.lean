/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/

import linear_algebra.quadratic_form.basic

/-!
# Isometries with respect to quadratic forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `quadratic_form.isometry`: `linear_equiv`s which map between two different quadratic forms
* `quadratic_form.equvialent`: propositional version of the above

## Main results

* `equivalent_weighted_sum_squares`: in finite dimensions, any quadratic form is equivalent to a
  parametrization of `quadratic_form.weighted_sum_squares`.
-/

variables {ι R K M M₁ M₂ M₃ V : Type*}

namespace quadratic_form

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R M₁] [module R M₂] [module R M₃]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_nonempty_instance] structure isometry
  (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) extends M₁ ≃ₗ[R] M₂ :=
(map_app' : ∀ m, Q₂ (to_fun m) = Q₁ m)

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometry between them:
a linear equivalence that transforms one quadratic form into the other. -/
def equivalent (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) := nonempty (Q₁.isometry Q₂)

namespace isometry

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

instance : has_coe (Q₁.isometry Q₂) (M₁ ≃ₗ[R] M₂) := ⟨isometry.to_linear_equiv⟩

@[simp] lemma to_linear_equiv_eq_coe (f : Q₁.isometry Q₂) : f.to_linear_equiv = f := rfl

instance : has_coe_to_fun (Q₁.isometry Q₂) (λ _, M₁ → M₂) := ⟨λ f, ⇑(f : M₁ ≃ₗ[R] M₂)⟩

@[simp] lemma coe_to_linear_equiv (f : Q₁.isometry Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f := rfl

@[simp] lemma map_app (f : Q₁.isometry Q₂) (m : M₁) : Q₂ (f m) = Q₁ m := f.map_app' m

/-- The identity isometry from a quadratic form to itself. -/
@[refl]
def refl (Q : quadratic_form R M) : Q.isometry Q :=
{ map_app' := λ m, rfl,
  .. linear_equiv.refl R M }

/-- The inverse isometry of an isometry between two quadratic forms. -/
@[symm]
def symm (f : Q₁.isometry Q₂) : Q₂.isometry Q₁ :=
{ map_app' := by { intro m, rw ← f.map_app, congr, exact f.to_linear_equiv.apply_symm_apply m },
  .. (f : M₁ ≃ₗ[R] M₂).symm }

/-- The composition of two isometries between quadratic forms. -/
@[trans]
def trans (f : Q₁.isometry Q₂) (g : Q₂.isometry Q₃) : Q₁.isometry Q₃ :=
{ map_app' := by { intro m, rw [← f.map_app, ← g.map_app], refl },
  .. (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) }

end isometry

namespace equivalent

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

@[refl]
lemma refl (Q : quadratic_form R M) : Q.equivalent Q := ⟨isometry.refl Q⟩

@[symm]
lemma symm (h : Q₁.equivalent Q₂) : Q₂.equivalent Q₁ := h.elim $ λ f, ⟨f.symm⟩

@[trans]
lemma trans (h : Q₁.equivalent Q₂) (h' : Q₂.equivalent Q₃) : Q₁.equivalent Q₃ :=
h'.elim $ h.elim $ λ f g, ⟨f.trans g⟩

end equivalent

variables [fintype ι] {v : basis ι R M}

/-- A quadratic form composed with a `linear_equiv` is isometric to itself. -/
def isometry_of_comp_linear_equiv (Q : quadratic_form R M) (f : M₁ ≃ₗ[R] M) :
  Q.isometry (Q.comp (f : M₁ →ₗ[R] M)) :=
{ map_app' :=
  begin
    intro,
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.to_fun_eq_coe,
               linear_equiv.apply_symm_apply, f.apply_symm_apply],
  end,
  .. f.symm }

/-- A quadratic form is isometric to its bases representations. -/
noncomputable def isometry_basis_repr (Q : quadratic_form R M) (v : basis ι R M) :
  isometry Q (Q.basis_repr v) :=
isometry_of_comp_linear_equiv Q v.equiv_fun.symm

variables [field K] [invertible (2 : K)] [add_comm_group V] [module K V]

/-- Given an orthogonal basis, a quadratic form is isometric with a weighted sum of squares. -/
noncomputable def isometry_weighted_sum_squares (Q : quadratic_form K V)
  (v : basis (fin (finite_dimensional.finrank K V)) K V)
  (hv₁ : (associated Q).is_Ortho v) :
  Q.isometry (weighted_sum_squares K (λ i, Q (v i))) :=
begin
  let iso := Q.isometry_basis_repr v,
  refine ⟨iso, λ m, _⟩,
  convert iso.map_app m,
  rw basis_repr_eq_of_is_Ortho _ _ hv₁,
end

variables [finite_dimensional K V]

open bilin_form

lemma equivalent_weighted_sum_squares (Q : quadratic_form K V) :
  ∃ w : fin (finite_dimensional.finrank K V) → K, equivalent Q (weighted_sum_squares K w) :=
let ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_is_symm _ Q) in
  ⟨_, ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩

lemma equivalent_weighted_sum_squares_units_of_nondegenerate'
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank K V) → Kˣ,
    equivalent Q (weighted_sum_squares K w) :=
begin
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_is_symm _ Q),
  have hv₂ := hv₁.not_is_ortho_basis_self_of_nondegenerate hQ,
  simp_rw [is_ortho, associated_eq_self_apply] at hv₂,
  exact ⟨λ i, units.mk0 _ (hv₂ i), ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩,
end

end quadratic_form
