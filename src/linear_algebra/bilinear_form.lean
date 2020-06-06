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
symmetric and alternating bilinear forms. Adjoints of linear maps
with respect to a bilinear form are also introduced.

A bilinear form on an R-module M, is a function from M x M to R,
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

/-- A map with two arguments that is linear in both is a bilinear form -/
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

lemma neg_apply (x y : M) : (-B) x y = -(B x y) := rfl

instance : inhabited (bilin_form R M) := ⟨0⟩

section

variables {R₂ : Type*} [comm_ring R₂] [module R₂ M] (F : bilin_form R₂ M) (f : M → M)

instance to_module : module R₂ (bilin_form R₂ M) :=
{ smul := λ c B,
  { bilin := λ x y, c * B x y,
    bilin_add_left := λ x y z,
      by {unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_left, left_distrib]},
    bilin_smul_left := λ a x y, by {unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_smul_left, ←mul_assoc, mul_comm c, mul_assoc]},
    bilin_add_right := λ x y z, by {unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_add_right, left_distrib]},
    bilin_smul_right := λ a x y, by {unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_smul_right, ←mul_assoc, mul_comm c, mul_assoc]} },
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

/-- Bilinear forms are equivalent to maps with two arguments that is linear in both. -/
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
by { rw [B.to_linear_map.map_sum, linear_map.coe_fn_sum, finset.sum_apply], refl }

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

@[simp] lemma comp_apply (B : bilin_form R N) (l r : M →ₗ[R] N) (v w) :
  B.comp l r v w = B (l v) (r w) := rfl

@[simp] lemma comp_left_apply (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_left f v w = B (f v) w := rfl

@[simp] lemma comp_right_apply (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_right f v w = B v (f w) := rfl

end comp

section lin_mul_lin

variables {R₂ : Type*} [comm_ring R₂] [module R₂ M] {N : Type w} [add_comm_group N] [module R₂ N]

/-- `lin_mul_lin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def lin_mul_lin (f g : M →ₗ[R₂] R₂) : bilin_form R₂ M :=
{ bilin := λ x y, f x * g y,
  bilin_add_left := λ x y z, by simp [add_mul],
  bilin_smul_left := λ x y z, by simp [mul_assoc],
  bilin_add_right := λ x y z, by simp [mul_add],
  bilin_smul_right := λ x y z, by simp [mul_left_comm] }

variables {f g : M →ₗ[R₂] R₂}

@[simp] lemma lin_mul_lin_apply (x y) : lin_mul_lin f g x y = f x * g y := rfl

@[simp] lemma lin_mul_lin_comp (l r : N →ₗ[R₂] M) :
  (lin_mul_lin f g).comp l r = lin_mul_lin (f.comp l) (g.comp r) :=
rfl

@[simp] lemma lin_mul_lin_comp_left (l : M →ₗ[R₂] M) :
  (lin_mul_lin f g).comp_left l = lin_mul_lin (f.comp l) g :=
rfl

@[simp] lemma lin_mul_lin_comp_right (r : M →ₗ[R₂] M) :
  (lin_mul_lin f g).comp_right r = lin_mul_lin f (g.comp r) :=
rfl

end lin_mul_lin

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
    bilin_smul_right := λ a x y, by simp },
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
  simp only [to_matrix_apply, comp_apply, mul_val, sum_mul],
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

@[simp] lemma to_matrix_to_bilin_form (B : bilin_form R (n → R)) :
  B.to_matrix.to_bilin_form = B :=
begin
  ext,
  rw [matrix.to_bilin_form_apply, B.mul_to_matrix_mul, bilin_form.to_matrix_apply, comp_apply],
  { apply coe_fn_congr; ext; simp [mul_vec], },
  { apply_instance, },
end

@[simp] lemma to_bilin_form_to_matrix (M : matrix n n R) :
  M.to_bilin_form.to_matrix = M :=
by { ext, simp [bilin_form.to_matrix_apply, matrix.to_bilin_form_apply, mul_val], }

/-- Bilinear forms are linearly equivalent to matrices. -/
def bilin_form_equiv_matrix : bilin_form R (n → R) ≃ₗ[R] matrix n n R :=
{ inv_fun   := matrix.to_bilin_form,
  left_inv  := to_matrix_to_bilin_form,
  right_inv := to_bilin_form_to_matrix,
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

namespace bilin_form

section linear_adjoints

variables {R : Type u} [comm_ring R]
variables {M : Type v} [add_comm_group M] [module R M]
variables {M₂ : Type v} [add_comm_group M₂] [module R M₂]
variables (B B' : bilin_form R M) (B₂ : bilin_form R M₂)
variables (f f' : M →ₗ[R] M₂) (g g' : M₂ →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def is_adjoint_pair := ∀ ⦃x y⦄, B₂ (f x) y = B x (g y)

variables {B B' B₂ f f' g g'}

lemma is_adjoint_pair.eq (h : is_adjoint_pair B B₂ f g) :
  ∀ {x y}, B₂ (f x) y = B x (g y) := h

lemma is_adjoint_pair_iff_comp_left_eq_comp_right (f g : module.End R M) :
  is_adjoint_pair B B' f g ↔ B'.comp_left f = B.comp_right g :=
begin
  split; intros h,
  { ext x y, rw [comp_left_apply, comp_right_apply], apply h, },
  { intros x y, rw [←comp_left_apply, ←comp_right_apply], rw h, },
end

lemma is_adjoint_pair_zero : is_adjoint_pair B B₂ 0 0 :=
λ x y, by simp only [bilin_form.zero_left, bilin_form.zero_right, linear_map.zero_apply]

lemma is_adjoint_pair_id : is_adjoint_pair B B 1 1 := λ x y, rfl

lemma is_adjoint_pair.add (h : is_adjoint_pair B B₂ f g) (h' : is_adjoint_pair B B₂ f' g') :
  is_adjoint_pair B B₂ (f + f') (g + g') :=
λ x y, by rw [linear_map.add_apply, linear_map.add_apply, add_left, add_right, h, h']

lemma is_adjoint_pair.sub (h : is_adjoint_pair B B₂ f g) (h' : is_adjoint_pair B B₂ f' g') :
  is_adjoint_pair B B₂ (f - f') (g - g') :=
λ x y, by rw [linear_map.sub_apply, linear_map.sub_apply, sub_left, sub_right, h, h']

lemma is_adjoint_pair.smul (c : R) (h : is_adjoint_pair B B₂ f g) :
  is_adjoint_pair B B₂ (c • f) (c • g) :=
λ x y, by rw [linear_map.smul_apply, linear_map.smul_apply, smul_left, smul_right, h]

lemma is_adjoint_pair.comp {M₃ : Type v} [add_comm_group M₃] [module R M₃] {B₃ : bilin_form R M₃}
  {f' : M₂ →ₗ[R] M₃} {g' : M₃ →ₗ[R] M₂}
  (h : is_adjoint_pair B B₂ f g) (h' : is_adjoint_pair B₂ B₃ f' g') :
  is_adjoint_pair B B₃ (f'.comp f) (g.comp g') :=
λ x y, by rw [linear_map.comp_apply, linear_map.comp_apply, h', h]

lemma is_adjoint_pair.mul
  {f g f' g' : module.End R M} (h : is_adjoint_pair B B f g) (h' : is_adjoint_pair B B f' g') :
  is_adjoint_pair B B (f * f') (g' * g) :=
λ x y, by rw [linear_map.mul_app, linear_map.mul_app, h, h']

variables (B B' B₂)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def is_pair_self_adjoint (f : module.End R M) := is_adjoint_pair B B' f f

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def is_pair_self_adjoint_submodule : submodule R (module.End R M) :=
{ carrier := { f | is_pair_self_adjoint B B' f },
  zero    := is_adjoint_pair_zero,
  add     := λ f g hf hg, hf.add hg,
  smul    := λ c f h, h.smul c, }

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def is_self_adjoint (f : module.End R M) := is_adjoint_pair B B f f

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def is_skew_adjoint (f : module.End R M) := is_adjoint_pair B B f (-f)

lemma is_skew_adjoint_iff_neg_self_adjoint (f : module.End R M) :
  B.is_skew_adjoint f ↔ is_adjoint_pair (-B) B f f :=
show (∀ x y, B (f x) y = B x ((-f) y)) ↔ ∀ x y, B (f x) y = (-B) x (f y),
by simp only [linear_map.neg_apply, bilin_form.neg_apply, bilin_form.neg_right]

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def self_adjoint_submodule := is_pair_self_adjoint_submodule B B

@[simp] lemma mem_self_adjoint_submodule (f : module.End R M) :
  f ∈ B.self_adjoint_submodule ↔ B.is_self_adjoint f := iff.rfl

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skew_adjoint_submodule := is_pair_self_adjoint_submodule (-B) B

@[simp] lemma mem_skew_adjoint_submodule (f : module.End R M) :
  f ∈ B.skew_adjoint_submodule ↔ B.is_skew_adjoint f :=
by { rw is_skew_adjoint_iff_neg_self_adjoint, exact iff.rfl, }

end linear_adjoints

end bilin_form

section matrix_adjoints
open_locale matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n]
variables (J J₂ A B : matrix n n R)

/-- The condition for the square matrices `A`, `B` to be an adjoint pair with respect to the square
matrices `J`, `J₂`. -/
def matrix.is_adjoint_pair := Aᵀ ⬝ J₂ = J ⬝ B

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def matrix.is_self_adjoint := matrix.is_adjoint_pair J J A A

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def matrix.is_skew_adjoint := matrix.is_adjoint_pair J J A (-A)

lemma matrix_is_adjoint_pair_bilin_form :
  matrix.is_adjoint_pair J J₂ A B ↔
  bilin_form.is_adjoint_pair J.to_bilin_form J₂.to_bilin_form A.to_lin B.to_lin :=
begin
  classical,
  rw bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right,
  have h : ∀ (B B' : bilin_form R (n → R)), B = B' ↔ B.to_matrix = B'.to_matrix := λ B B', by {
    split; intros h, { rw h, }, { rw [←to_matrix_to_bilin_form B, h, to_matrix_to_bilin_form B'], }, },
  rw [h, J₂.to_bilin_form.to_matrix_comp_left A.to_lin, J.to_bilin_form.to_matrix_comp_right B.to_lin,
      to_lin_to_matrix, to_lin_to_matrix, to_bilin_form_to_matrix, to_bilin_form_to_matrix],
  refl,
end

variables [decidable_eq n]

/-- Given a pair of square matrices `J`, `J₂` defining bilinear forms on the free module, there
is a natural embedding from the corresponding submodule of pair-self-adjoint endomorphisms into the
module of matrices. -/
def pair_self_adjoint_matrices_linear_embedding :
  bilin_form.is_pair_self_adjoint_submodule J.to_bilin_form J₂.to_bilin_form →ₗ[R] matrix n n R :=
linear_equiv_matrix'.to_linear_map.comp
  (bilin_form.is_pair_self_adjoint_submodule J.to_bilin_form J₂.to_bilin_form).subtype

lemma pair_self_adjoint_matrices_linear_embedding_apply
  (f : bilin_form.is_pair_self_adjoint_submodule J.to_bilin_form J₂.to_bilin_form) :
  (pair_self_adjoint_matrices_linear_embedding J J₂ : _ →ₗ _) f = (f : module.End R (n → R)).to_matrix := rfl

lemma pair_self_adjoint_matrices_linear_embedding_injective :
  function.injective (pair_self_adjoint_matrices_linear_embedding J J₂) :=
λ f g h, by { apply set_coe.ext, exact linear_equiv_matrix'.injective h, }

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pair_self_adjoint_matrices_submodule : submodule R (matrix n n R) :=
  (pair_self_adjoint_matrices_linear_embedding J J₂).range

@[simp] lemma mem_pair_self_adjoint_matrices_submodule :
  A ∈ (pair_self_adjoint_matrices_submodule J J₂) ↔ matrix.is_adjoint_pair J J₂ A A :=
begin
  change A ∈ (pair_self_adjoint_matrices_linear_embedding J J₂).range ↔ matrix.is_adjoint_pair J J₂ A A,
  rw [matrix_is_adjoint_pair_bilin_form, linear_map.mem_range],
  simp only [pair_self_adjoint_matrices_linear_embedding_apply], split,
  { rintros ⟨⟨A', hA'⟩, h⟩, rw ←h, rw to_matrix_to_lin, exact hA', },
  { intros h, exact ⟨⟨A.to_lin, h⟩, to_lin_to_matrix⟩, },
end

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def self_adjoint_matrices_submodule : submodule R (matrix n n R) :=
  pair_self_adjoint_matrices_submodule J J

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skew_adjoint_matrices_submodule : submodule R (matrix n n R) :=
  pair_self_adjoint_matrices_submodule (-J) J

end matrix_adjoints
