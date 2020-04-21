/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import linear_algebra.matrix
import linear_algebra.tensor_product

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive,
symmetric and alternating bilinear forms.

A bilinear form on an R-module V, is a function from V x V to R,
that is linear in both arguments

## Notations

Given any term B of type bilin_form, due to a coercion, can use
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

universes u v w

/-- A bilinear form over a module  -/
structure bilin_form (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] :=
(bilin : M → M → R)
(bilin_add_left : ∀ (x y z : M), bilin (x + y) z = bilin x z + bilin y z)
(bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * (bilin x y))
(bilin_add_right : ∀ (x y z : M), bilin x (y + z) = bilin x y + bilin x z)
(bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * (bilin x y))

/-- A linear map with two arguments is a bilinear form. -/
def linear_map.to_bilin {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
  (f : M →ₗ[R] M →ₗ[R] R) : bilin_form R M :=
{ bilin := λ x y, f x y,
  bilin_add_left := λ x y z, (linear_map.map_add f x y).symm ▸ linear_map.add_apply (f x) (f y) z,
  bilin_smul_left := λ a x y, by {rw linear_map.map_smul, rw linear_map.smul_apply, rw smul_eq_mul},
  bilin_add_right := λ x y z, linear_map.map_add (f x) y z,
  bilin_smul_right := λ a x y, linear_map.map_smul (f x) a y }

namespace bilin_form

variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {B : bilin_form R M}

instance : has_coe_to_fun (bilin_form R M) :=
⟨_, λ B, B.bilin⟩

@[simp] lemma coe_fn_mk (f : M → M → R) (h₁ h₂ h₃ h₄) :
  (bilin_form.mk f h₁ h₂ h₃ h₄ : M → M → R) = f :=
rfl

lemma coe_fn_congr : Π {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
| _ _ _ _ rfl rfl := rfl

lemma add_left (x y z : M) : B (x + y) z = B x z + B y z := bilin_add_left B x y z

lemma smul_left (a : R) (x y : M) : B (a • x) y = a * (B x y) := bilin_smul_left B a x y

lemma add_right (x y z : M) : B x (y + z) = B x y + B x z := bilin_add_right B x y z

lemma smul_right (a : R) (x y : M) : B x (a • y) = a * (B x y) := bilin_smul_right B a x y

lemma zero_left (x : M) :
B 0 x = 0 := by {rw [←@zero_smul R _ _ _ _ (0 : M), smul_left, zero_mul]}

lemma zero_right (x : M) :
B x 0 = 0 := by rw [←@zero_smul _ _ _ _ _ (0 : M), smul_right, ring.zero_mul]

lemma neg_left (x y : M) :
B (-x) y = -(B x y) := by rw [←@neg_one_smul R _ _, smul_left, neg_one_mul]

lemma neg_right (x y : M) :
B x (-y) = -(B x y) := by rw [←@neg_one_smul R _ _, smul_right, neg_one_mul]

lemma sub_left (x y z : M) :
B (x - y) z = B x z - B y z := by rw [sub_eq_add_neg, add_left, neg_left]; refl

lemma sub_right (x y z : M) :
B x (y - z) = B x y - B x z := by rw [sub_eq_add_neg, add_right, neg_right]; refl

variable {D : bilin_form R M}
@[ext] lemma ext (H : ∀ (x y : M), B x y = D x y) : B = D := by {cases B, cases D, congr, funext, exact H _ _}

instance : add_comm_group (bilin_form R M) :=
{ add := λ B D, { bilin := λ x y, B x y + D x y,
                  bilin_add_left := λ x y z, by {rw add_left, rw add_left, ac_refl},
                  bilin_smul_left := λ a x y, by {rw [smul_left, smul_left, mul_add]},
                  bilin_add_right := λ x y z, by {rw add_right, rw add_right, ac_refl},
                  bilin_smul_right := λ a x y, by {rw [smul_right, smul_right, mul_add]} },
  add_assoc := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin coe_fn has_coe_to_fun.coe bilin, rw add_assoc},
  zero := { bilin := λ x y, 0,
            bilin_add_left := λ x y z, (add_zero 0).symm,
            bilin_smul_left := λ a x y, (mul_zero a).symm,
            bilin_add_right := λ x y z, (zero_add 0).symm,
            bilin_smul_right := λ a x y, (mul_zero a).symm },
  zero_add := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_add},
  add_zero := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_zero},
  neg := λ B, { bilin := λ x y, - (B.1 x y),
                bilin_add_left := λ x y z, by rw [bilin_add_left, neg_add],
                bilin_smul_left := λ a x y, by rw [bilin_smul_left, mul_neg_eq_neg_mul_symm],
                bilin_add_right := λ x y z, by rw [bilin_add_right, neg_add],
                bilin_smul_right := λ a x y, by rw [bilin_smul_right, mul_neg_eq_neg_mul_symm] },
  add_left_neg := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw neg_add_self},
  add_comm := by {intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_comm} }

lemma add_apply (x y : M) : (B + D) x y = B x y + D x y := rfl

instance : inhabited (bilin_form R M) := ⟨0⟩

section

variables {R₂ : Type*} [comm_ring R₂] [module R₂ M] (F : bilin_form R₂ M) (f : M → M)

instance to_module : module R₂ (bilin_form R₂ M) :=
{ smul := λ c B, { bilin := λ x y, c * B x y,
                    bilin_add_left := λ x y z, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_left, left_distrib]},
                    bilin_smul_left := λ a x y, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_smul_left, ←mul_assoc, mul_comm c, mul_assoc]},
                    bilin_add_right := λ x y z, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_right, left_distrib]},
                    bilin_smul_right := λ a x y, by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_smul_right, ←mul_assoc, mul_comm c, mul_assoc]} },
  smul_add := λ c B D, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw left_distrib},
  add_smul := λ c B D, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw right_distrib},
  mul_smul := λ a c D, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw mul_assoc},
  one_smul := λ B, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw one_mul},
  zero_smul := λ B, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_mul},
  smul_zero := λ B, by {ext, unfold coe_fn has_coe_to_fun.coe bilin, rw mul_zero} }

lemma smul_apply (a : R₂) (x y : M) : (a • F) x y = a • (F x y) := rfl

/-- `B.to_linear_map` applies B on the left argument, then the right.  -/
def to_linear_map : M →ₗ[R₂] M →ₗ[R₂] R₂ :=
linear_map.mk₂ R₂ F.1 (bilin_add_left F) (bilin_smul_left F) (bilin_add_right F) (bilin_smul_right F)

/-- Bilinear forms are equivalent to linear maps with two arguments. -/
def bilin_linear_map_equiv : (bilin_form R₂ M) ≃ₗ[R₂] (M →ₗ[R₂] M →ₗ[R₂] R₂) :=
{ to_fun := to_linear_map,
  add := λ B D, rfl,
  smul := λ a B, rfl,
  inv_fun := linear_map.to_bilin,
  left_inv := λ B, by {ext, refl},
  right_inv := λ B, by {ext, refl} }

@[norm_cast]
lemma coe_fn_to_linear_map (x : M) : ⇑(F.to_linear_map x) = F x := rfl

lemma map_sum_left {α} (B : bilin_form R₂ M) (t : finset α) (g : α → M) (w : M) :
  B (t.sum g) w = t.sum (λ i, B (g i) w) :=
show B.to_linear_map (t.sum g) w = t.sum (λ i, B (g i) w),
by { rw [B.to_linear_map.map_sum, linear_map.coe_fn_sum, finset.sum_apply], norm_cast }

lemma map_sum_right {α} (B : bilin_form R₂ M) (t : finset α) (g : α → M) (v : M) :
  B v (t.sum g) = t.sum (λ i, B v (g i)) :=
(B.to_linear_map v).map_sum

end

section comp

variables {N : Type w} [add_comm_group N] [module R N]

/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp (B : bilin_form R N) (l r : M →ₗ[R] N) : bilin_form R M :=
{ bilin := λ x y, B (l x) (r y),
  bilin_add_left := λ x y z, by simp [add_left],
  bilin_smul_left := λ x y z, by simp [smul_left],
  bilin_add_right := λ x y z, by simp [add_right],
  bilin_smul_right := λ x y z, by simp [smul_right] }

/-- Apply a linear map to the left argument of a bilinear form. -/
def comp_left (B : bilin_form R M) (f : M →ₗ[R] M) : bilin_form R M :=
B.comp f linear_map.id

/-- Apply a linear map to the right argument of a bilinear form. -/
def comp_right (B : bilin_form R M) (f : M →ₗ[R] M) : bilin_form R M :=
B.comp linear_map.id f

@[simp] lemma comp_left_comp_right (B : bilin_form R M) (l r : M →ₗ[R] M) :
  (B.comp_left l).comp_right r = B.comp l r := rfl

@[simp] lemma comp_right_comp_left (B : bilin_form R M) (l r : M →ₗ[R] M) :
  (B.comp_right r).comp_left l = B.comp l r := rfl

@[simp] lemma coe_fn_comp (B : bilin_form R N) (l r : M →ₗ[R] N) (v w) :
  B.comp l r v w = B (l v) (r w) := rfl

@[simp] lemma coe_fn_comp_left (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_left f v w = B (f v) w := rfl

@[simp] lemma coe_fn_comp_right (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_right f v w = B v (f w) := rfl

end comp

/-- The proposition that two elements of a bilinear form space are orthogonal -/
def is_ortho (B : bilin_form R M) (x y : M) : Prop :=
B x y = 0

lemma ortho_zero (x : M) :
is_ortho B (0 : M) x := zero_left x

section

variables {R₃ : Type*} [domain R₃] [module R₃ M] {G : bilin_form R₃ M}

theorem ortho_smul_left {x y : M} {a : R₃} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G (a • x) y) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_left, H, ring.mul_zero] },
  { rw [smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

theorem ortho_smul_right {x y : M} {a : R₃} (ha : a ≠ 0) :
(is_ortho G x y) ↔ (is_ortho G x (a • y)) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_right, H, ring.mul_zero] },
  { rw [smul_right, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

end

end bilin_form

section matrix
variables {R : Type u} [comm_ring R]
variables {n o : Type w} [fintype n] [fintype o]

open bilin_form finset matrix
open_locale matrix

/-- The linear map from `matrix n n R` to bilinear forms on `n → R`. -/
def matrix.to_bilin_formₗ : matrix n n R →ₗ[R] bilin_form R (n → R) :=
{ to_fun := λ M,
  { bilin := λ v w, (row v ⬝ M ⬝ col w) ⟨⟩ ⟨⟩,
    bilin_add_left := λ x y z, by simp [matrix.add_mul],
    bilin_smul_left := λ a x y, by simp,
    bilin_add_right := λ x y z, by simp [matrix.mul_add],
    bilin_smul_right := λ a x y, by simp,
  },
  add := λ f g, by { ext, simp [add_apply, matrix.mul_add, matrix.add_mul] },
  smul := λ f g, by { ext, simp [smul_apply] } }

/-- The map from `matrix n n R` to bilinear forms on `n → R`. -/
def matrix.to_bilin_form : matrix n n R → bilin_form R (n → R) :=
matrix.to_bilin_formₗ.to_fun

lemma matrix.to_bilin_form_apply (M : matrix n n R) (v w : n → R) :
(M.to_bilin_form : (n → R) → (n → R) → R) v w = (row v ⬝ M ⬝ col w) ⟨⟩ ⟨⟩ := rfl

variables [decidable_eq n] [decidable_eq o]

/-- The linear map from bilinear forms on `n → R` to `matrix n n R`. -/
def bilin_form.to_matrixₗ : bilin_form R (n → R) →ₗ[R] matrix n n R :=
{ to_fun := λ B i j, B (λ n, if n = i then 1 else 0) (λ n, if n = j then 1 else 0),
  add := λ f g, rfl,
  smul := λ f g, rfl }

/-- The map from bilinear forms on `n → R` to `matrix n n R`. -/
def bilin_form.to_matrix : bilin_form R (n → R) → matrix n n R :=
bilin_form.to_matrixₗ.to_fun

lemma bilin_form.to_matrix_apply (B : bilin_form R (n → R)) (i j : n) :
  B.to_matrix i j = B (λ n, if n = i then 1 else 0) (λ n, if n = j then 1 else 0) := rfl

lemma bilin_form.to_matrix_smul (B : bilin_form R (n → R)) (x : R) :
  (x • B).to_matrix = x • B.to_matrix :=
by { ext, refl }

open bilin_form
lemma bilin_form.to_matrix_comp (B : bilin_form R (n → R)) (l r : (o → R) →ₗ[R] (n → R)) :
  (B.comp l r).to_matrix = l.to_matrixᵀ ⬝ B.to_matrix ⬝ r.to_matrix :=
begin
  ext i j,
  simp only [to_matrix_apply, coe_fn_comp, mul_val, sum_mul],
  have sum_smul_eq : Π (f : (o → R) →ₗ[R] (n → R)) (i : o),
    f (λ n, ite (n = i) 1 0) = univ.sum (λ k, f.to_matrix k i • λ n, ite (n = k) (1 : R) 0),
  { intros f i,
    ext j,
    change f (λ n, ite (n = i) 1 0) j = univ.sum (λ k n, f.to_matrix k i * ite (n = k) (1 : R) 0) j,
    simp [linear_map.to_matrix, linear_map.to_matrixₗ, eq_comm] },
  simp_rw [sum_smul_eq, map_sum_right, map_sum_left, smul_right, mul_comm, smul_left],
  refl
end

lemma bilin_form.to_matrix_comp_left (B : bilin_form R (n → R)) (f : (n → R) →ₗ[R] (n → R)) :
  (B.comp_left f).to_matrix = f.to_matrixᵀ ⬝ B.to_matrix :=
by simp [comp_left, bilin_form.to_matrix_comp]

lemma bilin_form.to_matrix_comp_right (B : bilin_form R (n → R)) (f : (n → R) →ₗ[R] (n → R)) :
  (B.comp_right f).to_matrix = B.to_matrix ⬝ f.to_matrix :=
by simp [comp_right, bilin_form.to_matrix_comp]

lemma bilin_form.mul_to_matrix_mul (B : bilin_form R (n → R)) (M : matrix o n R) (N : matrix n o R) :
  M ⬝ B.to_matrix ⬝ N = (B.comp (Mᵀ.to_lin) (N.to_lin)).to_matrix :=
by { ext, simp [B.to_matrix_comp (Mᵀ.to_lin) (N.to_lin), to_lin_to_matrix] }

lemma bilin_form.mul_to_matrix (B : bilin_form R (n → R)) (M : matrix n n R) :
  M ⬝ B.to_matrix = (B.comp_left (Mᵀ.to_lin)).to_matrix :=
by { ext, simp [B.to_matrix_comp_left (Mᵀ.to_lin), to_lin_to_matrix] }

lemma bilin_form.to_matrix_mul (B : bilin_form R (n → R)) (M : matrix n n R) :
  B.to_matrix ⬝ M = (B.comp_right (M.to_lin)).to_matrix :=
by { ext, simp [B.to_matrix_comp_right (M.to_lin), to_lin_to_matrix] }

/-- Bilinear forms are linearly equivalent to matrices. -/
def bilin_form_equiv_matrix : bilin_form R (n → R) ≃ₗ[R] matrix n n R :=
{ inv_fun := matrix.to_bilin_form,
  left_inv := λ B, show B.to_matrix.to_bilin_form = B,
  begin
    ext,
    rw [matrix.to_bilin_form_apply, B.mul_to_matrix_mul, bilin_form.to_matrix_apply, coe_fn_comp],
    { apply coe_fn_congr; ext; simp [mul_vec] },
    apply_instance
  end,
  right_inv := λ M, by { ext, simp [bilin_form.to_matrixₗ, matrix.to_bilin_form_apply, mul_val] },
  ..bilin_form.to_matrixₗ }

end matrix

namespace refl_bilin_form

open refl_bilin_form bilin_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M] {B : bilin_form R M}

/-- The proposition that a bilinear form is reflexive -/
def is_refl (B : bilin_form R M) : Prop := ∀ (x y : M), B x y = 0 → B y x = 0

variable (H : is_refl B)

lemma eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_sym {x y : M} :
is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

end refl_bilin_form

namespace sym_bilin_form

open sym_bilin_form bilin_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M] {B : bilin_form R M}

/-- The proposition that a bilinear form is symmetric -/
def is_sym (B : bilin_form R M) : Prop := ∀ (x y : M), B x y = B y x

variable (H : is_sym B)

lemma sym (x y : M) : B x y = B y x := H x y

lemma is_refl : refl_bilin_form.is_refl B := λ x y H1, H x y ▸ H1

lemma ortho_sym {x y : M} :
is_ortho B x y ↔ is_ortho B y x := refl_bilin_form.ortho_sym (is_refl H)

end sym_bilin_form

namespace alt_bilin_form

open alt_bilin_form bilin_form

variables {R : Type*} {M : Type*} [ring R] [add_comm_group M] [module R M] {B : bilin_form R M}

/-- The proposition that a bilinear form is alternating -/
def is_alt (B : bilin_form R M) : Prop := ∀ (x : M), B x x = 0

variable (H : is_alt B)
include H

lemma self_eq_zero (x : M) : B x x = 0 := H x

lemma neg (x y : M) :
- B x y = B y x :=
begin
  have H1 : B (x + y) (x + y) = 0,
  { exact self_eq_zero H (x + y) },
  rw [add_left, add_right, add_right,
    self_eq_zero H, self_eq_zero H, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

end alt_bilin_form
