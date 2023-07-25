/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.module.equiv

/-!
# The general linear group of linear maps

The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See also `matrix.general_linear_group`

## Main definitions

* `linear_map.general_linear_group`

-/

namespace linear_map

variables (R M : Type*)

variables [semiring R] [add_comm_monoid M] [module R M]
variables (R M)

/-- The group of invertible linear maps from `M` to itself -/
@[reducible] def general_linear_group := (M →ₗ[R] M)ˣ

namespace general_linear_group
variables {R M}

instance : has_coe_to_fun (general_linear_group R M) (λ _, M → M) := by apply_instance

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def to_linear_equiv (f : general_linear_group R M) : (M ≃ₗ[R] M) :=
{ inv_fun := f.inv.to_fun,
  left_inv := λ m, show (f.inv * f.val) m = m,
    by erw f.inv_val; simp,
  right_inv := λ m, show (f.val * f.inv) m = m,
    by erw f.val_inv; simp,
  ..f.val }

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def of_linear_equiv (f : (M ≃ₗ[R] M)) : general_linear_group R M :=
{ val := f,
  inv := (f.symm : M →ₗ[R] M),
  val_inv := linear_map.ext $ λ _, f.apply_symm_apply _,
  inv_val := linear_map.ext $ λ _, f.symm_apply_apply _ }

variables (R M)

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def general_linear_equiv : general_linear_group R M ≃* (M ≃ₗ[R] M) :=
{ to_fun := to_linear_equiv,
  inv_fun := of_linear_equiv,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl },
  map_mul' := λ x y, by {ext, refl} }

@[simp] lemma general_linear_equiv_to_linear_map (f : general_linear_group R M) :
  (general_linear_equiv R M f : M →ₗ[R] M) = f :=
by {ext, refl}

@[simp] lemma coe_fn_general_linear_equiv (f : general_linear_group R M) :
  ⇑(general_linear_equiv R M f) = (f : M → M) :=
rfl

end general_linear_group

end linear_map

section

variables {R M : Type*} [ring R] [add_comm_group M] [module R M] (T : M →ₗ[R] M)

namespace linear_equiv

/-- any invertible linear map can be written as a linear equivalence -/
def of_invertible [invertible T] : M ≃ₗ[R] M :=
linear_map.general_linear_group.to_linear_equiv (unit_of_invertible T)

lemma coe_of_invertible [invertible T] :
  ⇑(linear_equiv.of_invertible T) = T := rfl

@[simp] lemma coe_linear_map_of_invertible [invertible T] :
  ↑(linear_equiv.of_invertible T) = T := by { ext, refl }

@[simp] lemma coe_linear_map_of_invertible_symm [invertible T] :
  ↑((linear_equiv.of_invertible T).symm) = (⅟ T) := by { ext, refl }

lemma coe_of_invertible_symm [invertible T] :
  ⇑(linear_equiv.of_invertible T).symm = (⅟ T : _) := rfl

end linear_equiv

-- TODO: generalize the following result to any monoid
/-- a linear map `S` commutes with an invertible linear map `T` if and only if
`(⅟T).comp (S.comp T) = S` -/
lemma commute_with_invertible_linear_map_iff_conj_eq_self [invertible T] (S : M →ₗ[R] M) :
  _root_.commute S T ↔ (⅟ T).comp (S.comp T) = S :=
by { change _ ↔ _ * _ = S, rw [← coe_inv_unit_of_invertible, units.inv_mul_eq_iff_eq_mul], refl }

end
