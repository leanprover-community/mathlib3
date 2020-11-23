/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import linear_algebra.matrix
import linear_algebra.tensor_product
import linear_algebra.nonsingular_inverse

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive,
symmetric and alternating bilinear forms. Adjoints of linear maps
with respect to a bilinear form are also introduced.

A bilinear form on an R-(semi)module M, is a function from M x M to R,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

## Notations

Given any term B of type bilin_form, due to a coercion, can use
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.

In this file we use the following type variables:
 - `M`, `M'`, ... are semimodules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative ring `R₂`

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open_locale big_operators

universes u v w

/-- `bilin_form R M` is the type of `R`-bilinear functions `M → M → R`. -/
structure bilin_form (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] :=
(bilin : M → M → R)
(bilin_add_left : ∀ (x y z : M), bilin (x + y) z = bilin x z + bilin y z)
(bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * (bilin x y))
(bilin_add_right : ∀ (x y z : M), bilin x (y + z) = bilin x y + bilin x z)
(bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * (bilin x y))

variables {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]
variables {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁]
variables {R₂ : Type u} {M₂ : Type v} [comm_ring R₂] [add_comm_group M₂] [module R₂ M₂]
variables {B : bilin_form R M} {B₁ : bilin_form R₁ M₁} {B₂ : bilin_form R₂ M₂}

namespace bilin_form

instance : has_coe_to_fun (bilin_form R M) :=
⟨_, λ B, B.bilin⟩

@[simp] lemma coe_fn_mk (f : M → M → R) (h₁ h₂ h₃ h₄) :
  (bilin_form.mk f h₁ h₂ h₃ h₄ : M → M → R) = f :=
rfl

lemma coe_fn_congr : Π {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
| _ _ _ _ rfl rfl := rfl

@[simp]
lemma add_left (x y z : M) : B (x + y) z = B x z + B y z := bilin_add_left B x y z

@[simp]
lemma smul_left (a : R) (x y : M) : B (a • x) y = a * (B x y) := bilin_smul_left B a x y

@[simp]
lemma add_right (x y z : M) : B x (y + z) = B x y + B x z := bilin_add_right B x y z

@[simp]
lemma smul_right (a : R) (x y : M) : B x (a • y) = a * (B x y) := bilin_smul_right B a x y

@[simp]
lemma zero_left (x : M) : B 0 x = 0 :=
by { rw [←@zero_smul R _ _ _ _ (0 : M), smul_left, zero_mul] }

@[simp]
lemma zero_right (x : M) : B x 0 = 0 :=
by rw [←@zero_smul _ _ _ _ _ (0 : M), smul_right, zero_mul]

@[simp]
lemma neg_left (x y : M₁) : B₁ (-x) y = -(B₁ x y) :=
by rw [←@neg_one_smul R₁ _ _, smul_left, neg_one_mul]

@[simp]
lemma neg_right (x y : M₁) : B₁ x (-y) = -(B₁ x y) :=
by rw [←@neg_one_smul R₁ _ _, smul_right, neg_one_mul]

@[simp]
lemma sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_left, neg_left]

@[simp]
lemma sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_right, neg_right]

variable {D : bilin_form R M}
@[ext] lemma ext (H : ∀ (x y : M), B x y = D x y) : B = D :=
by { cases B, cases D, congr, funext, exact H _ _ }

instance : add_comm_monoid (bilin_form R M) :=
{ add := λ B D, { bilin := λ x y, B x y + D x y,
                  bilin_add_left := λ x y z, by { rw add_left, rw add_left, ac_refl },
                  bilin_smul_left := λ a x y, by { rw [smul_left, smul_left, mul_add] },
                  bilin_add_right := λ x y z, by { rw add_right, rw add_right, ac_refl },
                  bilin_smul_right := λ a x y, by { rw [smul_right, smul_right, mul_add] } },
  add_assoc := by { intros, ext, unfold bilin coe_fn has_coe_to_fun.coe bilin, rw add_assoc },
  zero := { bilin := λ x y, 0,
            bilin_add_left := λ x y z, (add_zero 0).symm,
            bilin_smul_left := λ a x y, (mul_zero a).symm,
            bilin_add_right := λ x y z, (zero_add 0).symm,
            bilin_smul_right := λ a x y, (mul_zero a).symm },
  zero_add := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_add },
  add_zero := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_zero },
  add_comm := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_comm } }

instance : add_comm_group (bilin_form R₁ M₁) :=
{ neg := λ B, { bilin := λ x y, - (B.1 x y),
                bilin_add_left := λ x y z, by rw [bilin_add_left, neg_add],
                bilin_smul_left := λ a x y, by rw [bilin_smul_left, mul_neg_eq_neg_mul_symm],
                bilin_add_right := λ x y z, by rw [bilin_add_right, neg_add],
                bilin_smul_right := λ a x y, by rw [bilin_smul_right, mul_neg_eq_neg_mul_symm] },
  add_left_neg := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw neg_add_self },
  .. bilin_form.add_comm_monoid }

@[simp]
lemma add_apply (x y : M) : (B + D) x y = B x y + D x y := rfl

@[simp]
lemma neg_apply (x y : M₁) : (-B₁) x y = -(B₁ x y) := rfl

instance : inhabited (bilin_form R M) := ⟨0⟩

section

instance {R : Type*} [comm_semiring R] [semimodule R M] : semimodule R (bilin_form R M) :=
{ smul := λ c B,
  { bilin := λ x y, c * B x y,
    bilin_add_left := λ x y z,
      by { unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_left, left_distrib] },
    bilin_smul_left := λ a x y, by { unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_smul_left, ←mul_assoc, mul_comm c, mul_assoc] },
    bilin_add_right := λ x y z, by { unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_add_right, left_distrib] },
    bilin_smul_right := λ a x y, by { unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_smul_right, ←mul_assoc, mul_comm c, mul_assoc] } },
  smul_add := λ c B D, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw left_distrib },
  add_smul := λ c B D, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw right_distrib },
  mul_smul := λ a c D, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw mul_assoc },
  one_smul := λ B, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw one_mul },
  zero_smul := λ B, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_mul },
  smul_zero := λ B, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw mul_zero } }

@[simp]
lemma smul_apply {R : Type*} [comm_semiring R] [semimodule R M]
  (B : bilin_form R M) (a : R) (x y : M) :
  (a • B) x y = a • (B x y) :=
rfl

end

end bilin_form

section equiv_lin

/-- A map with two arguments that is linear in both is a bilinear form.

This is an auxiliary definition for the full linear equivalence `linear_map.to_bilin`.
-/
def linear_map.to_bilin_aux (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) : bilin_form R₂ M₂ :=
{ bilin := λ x y, f x y,
  bilin_add_left := λ x y z, (linear_map.map_add f x y).symm ▸ linear_map.add_apply (f x) (f y) z,
  bilin_smul_left := λ a x y, by rw [linear_map.map_smul, linear_map.smul_apply, smul_eq_mul],
  bilin_add_right := λ x y z, linear_map.map_add (f x) y z,
  bilin_smul_right := λ a x y, linear_map.map_smul (f x) a y }

/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/
def linear_map.to_bilin : (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) ≃ₗ[R₂] bilin_form R₂ M₂ :=
{ to_fun := linear_map.to_bilin_aux,
  inv_fun := λ F, linear_map.mk₂ R₂ F
    F.bilin_add_left F.bilin_smul_left F.bilin_add_right  F.bilin_smul_right,
  map_add' := λ B D, rfl,
  map_smul' := λ a B, rfl,
  left_inv := λ B, by { ext, refl },
  right_inv := λ B, by { ext, refl } }

/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/
def bilin_form.to_lin : bilin_form R₂ M₂ ≃ₗ[R₂] (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) :=
linear_map.to_bilin.symm

@[simp] lemma linear_map.to_bilin_aux_eq (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) :
  linear_map.to_bilin_aux f = linear_map.to_bilin f :=
rfl

@[simp] lemma linear_map.to_bilin_symm :
  (linear_map.to_bilin.symm : bilin_form R₂ M₂ ≃ₗ _) = bilin_form.to_lin := rfl

@[simp] lemma bilin_form.to_lin_symm :
  (bilin_form.to_lin.symm : _ ≃ₗ bilin_form R₂ M₂) = linear_map.to_bilin :=
linear_map.to_bilin.symm_symm

@[simp, norm_cast]
lemma to_linear_map_apply (x : M₂) : ⇑(bilin_form.to_lin B₂ x) = B₂ x := rfl

@[simp]
lemma map_sum_left {α} (t : finset α) (g : α → M₂) (w : M₂) :
  B₂ (∑ i in t, g i) w = ∑ i in t, B₂ (g i) w :=
show bilin_form.to_lin B₂ (∑ i in t, g i) w = ∑ i in t, bilin_form.to_lin B₂ (g i) w,
by rw [linear_map.map_sum, linear_map.coe_fn_sum, finset.sum_apply]

@[simp]
lemma map_sum_right {α} (t : finset α) (w : M₂) (g : α → M₂) :
  B₂ w (∑ i in t, g i) = ∑ i in t, B₂ w (g i) :=
show bilin_form.to_lin B₂ w (∑ i in t, g i) = ∑ i in t, bilin_form.to_lin B₂ w (g i),
from linear_map.map_sum _

end equiv_lin

namespace bilin_form

section comp

variables {M' : Type w} [add_comm_monoid M'] [semimodule R M']

/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp (B : bilin_form R M') (l r : M →ₗ[R] M') : bilin_form R M :=
{ bilin := λ x y, B (l x) (r y),
  bilin_add_left := λ x y z, by rw [linear_map.map_add, add_left],
  bilin_smul_left := λ x y z, by rw [linear_map.map_smul, smul_left],
  bilin_add_right := λ x y z, by rw [linear_map.map_add, add_right],
  bilin_smul_right := λ x y z, by rw [linear_map.map_smul, smul_right] }

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

@[simp] lemma comp_apply (B : bilin_form R M') (l r : M →ₗ[R] M') (v w) :
  B.comp l r v w = B (l v) (r w) := rfl

@[simp] lemma comp_left_apply (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_left f v w = B (f v) w := rfl

@[simp] lemma comp_right_apply (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_right f v w = B v (f w) := rfl

lemma comp_injective (B₁ B₂ : bilin_form R M') (l r : M →ₗ[R] M')
  (hₗ : function.surjective l) (hᵣ : function.surjective r) :
  B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ :=
begin
  split; intros h,
  { -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext,
    cases hₗ x with x' hx, subst hx,
    cases hᵣ y with y' hy, subst hy,
    rw [←comp_apply, ←comp_apply, h], },
  { -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h, },
end

end comp

section lin_mul_lin

variables {M₂' : Type*} [add_comm_group M₂'] [module R₂ M₂']

/-- `lin_mul_lin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def lin_mul_lin (f g : M₂ →ₗ[R₂] R₂) : bilin_form R₂ M₂ :=
{ bilin := λ x y, f x * g y,
  bilin_add_left := λ x y z, by rw [linear_map.map_add, add_mul],
  bilin_smul_left := λ x y z, by rw [linear_map.map_smul, smul_eq_mul, mul_assoc],
  bilin_add_right := λ x y z, by rw [linear_map.map_add, mul_add],
  bilin_smul_right := λ x y z, by rw [linear_map.map_smul, smul_eq_mul, mul_left_comm] }

variables {f g : M₂ →ₗ[R₂] R₂}

@[simp] lemma lin_mul_lin_apply (x y) : lin_mul_lin f g x y = f x * g y := rfl

@[simp] lemma lin_mul_lin_comp (l r : M₂' →ₗ[R₂] M₂) :
  (lin_mul_lin f g).comp l r = lin_mul_lin (f.comp l) (g.comp r) :=
rfl

@[simp] lemma lin_mul_lin_comp_left (l : M₂ →ₗ[R₂] M₂) :
  (lin_mul_lin f g).comp_left l = lin_mul_lin (f.comp l) g :=
rfl

@[simp] lemma lin_mul_lin_comp_right (r : M₂ →ₗ[R₂] M₂) :
  (lin_mul_lin f g).comp_right r = lin_mul_lin f (g.comp r) :=
rfl

end lin_mul_lin

/-- The proposition that two elements of a bilinear form space are orthogonal -/
def is_ortho (B : bilin_form R M) (x y : M) : Prop :=
B x y = 0

lemma ortho_zero (x : M) : is_ortho B (0 : M) x :=
zero_left x

section

variables {R₃ M₃ : Type*} [domain R₃] [add_comm_group M₃] [module R₃ M₃] {G : bilin_form R₃ M₃}

@[simp]
theorem ortho_smul_left {x y : M₃} {a : R₃} (ha : a ≠ 0) :
  is_ortho G (a • x) y ↔ is_ortho G x y :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }},
  { rw [smul_left, H, mul_zero] },
end

@[simp]
theorem is_ortho_smul_right {x y : M₃} {a : R₃} (ha : a ≠ 0) :
  is_ortho G x (a • y) ↔ is_ortho G x y :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_right, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }},
  { rw [smul_right, H, mul_zero] },
end

end

end bilin_form

section matrix
variables {n o : Type*} [fintype n] [fintype o]

open bilin_form finset matrix
open_locale matrix

/-- The linear map from `matrix n n R` to bilinear forms on `n → R`. -/
def matrix.to_bilin_formₗ : matrix n n R₂ →ₗ[R₂] bilin_form R₂ (n → R₂) :=
{ to_fun := λ M,
  { bilin := λ v w, (row v ⬝ M ⬝ col w) ⟨⟩ ⟨⟩,
    bilin_add_left := λ x y z, by simp [matrix.add_mul],
    bilin_smul_left := λ a x y, by simp,
    bilin_add_right := λ x y z, by simp [matrix.mul_add],
    bilin_smul_right := λ a x y, by simp },
  map_add' := λ f g, by { ext, simp [bilin_form.add_apply, matrix.mul_add, matrix.add_mul] },
  map_smul' := λ f g, by { ext, simp [bilin_form.smul_apply] } }

/-- The map from `matrix n n R` to bilinear forms on `n → R`. -/
def matrix.to_bilin_form : matrix n n R₂ → bilin_form R₂ (n → R₂) :=
matrix.to_bilin_formₗ.to_fun

lemma matrix.to_bilin_form_apply (M : matrix n n R₂) (v w : n → R₂) :
(M.to_bilin_form : (n → R₂) → (n → R₂) → R₂) v w = (row v ⬝ M ⬝ col w) ⟨⟩ ⟨⟩ := rfl

variables [decidable_eq n] [decidable_eq o]

/-- The linear map from bilinear forms on `n → R` to `matrix n n R`. -/
def bilin_form.to_matrixₗ : bilin_form R₂ (n → R₂) →ₗ[R₂] matrix n n R₂ :=
{ to_fun := λ B i j, B (λ n, if n = i then 1 else 0) (λ n, if n = j then 1 else 0),
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl }

/-- The map from bilinear forms on `n → R` to `matrix n n R`. -/
def bilin_form.to_matrix : bilin_form R₂ (n → R₂) → matrix n n R₂ :=
bilin_form.to_matrixₗ.to_fun

lemma bilin_form.to_matrix_apply (B : bilin_form R₂ (n → R₂)) (i j : n) :
  B.to_matrix i j = B (λ n, if n = i then 1 else 0) (λ n, if n = j then 1 else 0) := rfl

lemma bilin_form.to_matrix_smul (B : bilin_form R₂ (n → R₂)) (x : R₂) :
  (x • B).to_matrix = x • B.to_matrix :=
by { ext, refl }

open bilin_form
lemma bilin_form.to_matrix_comp (B : bilin_form R₂ (n → R₂)) (l r : (o → R₂) →ₗ[R₂] (n → R₂)) :
  (B.comp l r).to_matrix = l.to_matrix'ᵀ ⬝ B.to_matrix ⬝ r.to_matrix' :=
begin
  ext i j,
  simp only [to_matrix_apply, transpose_apply, comp_apply, mul_apply, sum_mul],
  have sum_smul_eq : Π (f : (o → R₂) →ₗ[R₂] (n → R₂)) (i : o),
    f (λ n, ite (n = i) 1 0) = ∑ k, linear_map.to_matrix' f k i • λ n, ite (n = k) (1 : R₂) 0,
  { intros f i,
    ext j,
    change f (λ n, ite (n = i) 1 0) j =
        (∑ k, λ n, linear_map.to_matrix' f k i * ite (n = k) (1 : R₂) 0) j,
      simp_rw [finset.sum_apply, mul_boole, finset.sum_ite_eq],
      rw [if_pos (finset.mem_univ j), linear_map.to_matrix'_apply] },
  simp_rw [sum_smul_eq, map_sum_right, map_sum_left, smul_right, smul_left, mul_comm]
end

lemma bilin_form.to_matrix_comp_left (B : bilin_form R₂ (n → R₂)) (f : (n → R₂) →ₗ[R₂] (n → R₂)) :
  (B.comp_left f).to_matrix = f.to_matrix'ᵀ ⬝ B.to_matrix :=
by simp [comp_left, bilin_form.to_matrix_comp]

lemma bilin_form.to_matrix_comp_right (B : bilin_form R₂ (n → R₂)) (f : (n → R₂) →ₗ[R₂] (n → R₂)) :
  (B.comp_right f).to_matrix = B.to_matrix ⬝ f.to_matrix' :=
by simp [comp_right, bilin_form.to_matrix_comp]

lemma bilin_form.mul_to_matrix_mul (B : bilin_form R₂ (n → R₂))
  (M : matrix o n R₂) (N : matrix n o R₂) :
  M ⬝ B.to_matrix ⬝ N = (B.comp Mᵀ.to_lin' N.to_lin').to_matrix :=
by { ext, simp [B.to_matrix_comp Mᵀ.to_lin' N.to_lin', to_lin_to_matrix] }

lemma bilin_form.mul_to_matrix (B : bilin_form R₂ (n → R₂)) (M : matrix n n R₂) :
  M ⬝ B.to_matrix = (B.comp_left Mᵀ.to_lin').to_matrix :=
by { ext, simp [B.to_matrix_comp_left Mᵀ.to_lin', to_lin_to_matrix] }

lemma bilin_form.to_matrix_mul (B : bilin_form R₂ (n → R₂)) (M : matrix n n R₂) :
  B.to_matrix ⬝ M = (B.comp_right M.to_lin').to_matrix :=
by { ext, simp [B.to_matrix_comp_right M.to_lin', to_lin_to_matrix] }

@[simp] lemma to_matrix_to_bilin_form (B : bilin_form R₂ (n → R₂)) :
  B.to_matrix.to_bilin_form = B :=
begin
  ext,
  rw [matrix.to_bilin_form_apply, B.mul_to_matrix_mul, bilin_form.to_matrix_apply, comp_apply],
  { apply coe_fn_congr; ext; simp [mul_vec], },
  { apply_instance, },
end

@[simp] lemma to_bilin_form_to_matrix (M : matrix n n R₂) :
  M.to_bilin_form.to_matrix = M :=
by { ext, simp [bilin_form.to_matrix_apply, matrix.to_bilin_form_apply, mul_apply], }

/-- Bilinear forms are linearly equivalent to matrices. -/
def bilin_form_equiv_matrix : bilin_form R₂ (n → R₂) ≃ₗ[R₂] matrix n n R₂ :=
{ inv_fun   := matrix.to_bilin_form,
  left_inv  := to_matrix_to_bilin_form,
  right_inv := to_bilin_form_to_matrix,
  ..bilin_form.to_matrixₗ }

lemma matrix.to_bilin_form_comp {n o : Type w} [fintype n] [fintype o] [decidable_eq o]
  (M : matrix n n R₂) (P Q : matrix n o R₂) :
  M.to_bilin_form.comp P.to_lin' Q.to_lin' = (Pᵀ ⬝ M ⬝ Q).to_bilin_form :=
by { haveI : decidable_eq n := λ _ _, classical.prop_decidable _,
  rw [←to_matrix_to_bilin_form (Pᵀ ⬝ M ⬝ Q).to_bilin_form,
       ←to_matrix_to_bilin_form (M.to_bilin_form.comp P.to_lin' Q.to_lin'),
       bilin_form.to_matrix_comp, to_bilin_form_to_matrix, to_bilin_form_to_matrix,
       linear_map.to_matrix'_to_lin', linear_map.to_matrix'_to_lin'] }

end matrix

namespace refl_bilin_form

open refl_bilin_form bilin_form

/-- The proposition that a bilinear form is reflexive -/
def is_refl (B : bilin_form R M) : Prop := ∀ (x y : M), B x y = 0 → B y x = 0

variable (H : is_refl B)

lemma eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_sym {x y : M} :
  is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

end refl_bilin_form

namespace sym_bilin_form

open sym_bilin_form bilin_form

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

/-- The proposition that a bilinear form is alternating -/
def is_alt (B : bilin_form R M) : Prop := ∀ (x : M), B x x = 0

variable (H : is_alt B)
include H

lemma self_eq_zero (x : M) : B x x = 0 := H x

lemma neg (H : is_alt B₁) (x y : M₁) :
  - B₁ x y = B₁ y x :=
begin
  have H1 : B₁ (x + y) (x + y) = 0,
  { exact self_eq_zero H (x + y) },
  rw [add_left, add_right, add_right,
    self_eq_zero H, self_eq_zero H, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

end alt_bilin_form

namespace bilin_form

section linear_adjoints

variables (B) (F : bilin_form R M)
variables {M' : Type*} [add_comm_monoid M'] [semimodule R M']
variables (B' : bilin_form R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def is_adjoint_pair := ∀ ⦃x y⦄, B' (f x) y = B x (g y)

variables {B B' B₂ f f' g g'}

lemma is_adjoint_pair.eq (h : is_adjoint_pair B B' f g) :
  ∀ {x y}, B' (f x) y = B x (g y) := h

lemma is_adjoint_pair_iff_comp_left_eq_comp_right (f g : module.End R M) :
  is_adjoint_pair B F f g ↔ F.comp_left f = B.comp_right g :=
begin
  split; intros h,
  { ext x y, rw [comp_left_apply, comp_right_apply], apply h, },
  { intros x y, rw [←comp_left_apply, ←comp_right_apply], rw h, },
end

lemma is_adjoint_pair_zero : is_adjoint_pair B B' 0 0 :=
λ x y, by simp only [bilin_form.zero_left, bilin_form.zero_right, linear_map.zero_apply]

lemma is_adjoint_pair_id : is_adjoint_pair B B 1 1 := λ x y, rfl

lemma is_adjoint_pair.add (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B B' f' g') :
  is_adjoint_pair B B' (f + f') (g + g') :=
λ x y, by rw [linear_map.add_apply, linear_map.add_apply, add_left, add_right, h, h']

variables {M₁' : Type*} [add_comm_group M₁'] [module R₁ M₁']
variables {B₁' : bilin_form R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

lemma is_adjoint_pair.sub (h : is_adjoint_pair B₁ B₁' f₁ g₁) (h' : is_adjoint_pair B₁ B₁' f₁' g₁') :
  is_adjoint_pair B₁ B₁' (f₁ - f₁') (g₁ - g₁') :=
λ x y, by rw [linear_map.sub_apply, linear_map.sub_apply, sub_left, sub_right, h, h']

variables {M₂' : Type*} [add_comm_group M₂'] [module R₂ M₂']
variables {B₂' : bilin_form R₂ M₂'} {f₂ f₂' : M₂ →ₗ[R₂] M₂'} {g₂ g₂' : M₂' →ₗ[R₂] M₂}

lemma is_adjoint_pair.smul (c : R₂) (h : is_adjoint_pair B₂ B₂' f₂ g₂) :
  is_adjoint_pair B₂ B₂' (c • f₂) (c • g₂) :=
λ x y, by rw [linear_map.smul_apply, linear_map.smul_apply, smul_left, smul_right, h]

variables {M'' : Type*} [add_comm_monoid M''] [semimodule R M'']
variables (B'' : bilin_form R M'')

lemma is_adjoint_pair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'}
  (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B' B'' f' g') :
  is_adjoint_pair B B'' (f'.comp f) (g.comp g') :=
λ x y, by rw [linear_map.comp_apply, linear_map.comp_apply, h', h]

lemma is_adjoint_pair.mul
  {f g f' g' : module.End R M} (h : is_adjoint_pair B B f g) (h' : is_adjoint_pair B B f' g') :
  is_adjoint_pair B B (f * f') (g' * g) :=
λ x y, by rw [linear_map.mul_app, linear_map.mul_app, h, h']

variables (B B' B₁ B₂) (F₂ : bilin_form R₂ M₂)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def is_pair_self_adjoint (f : module.End R M) := is_adjoint_pair B F f f

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def is_pair_self_adjoint_submodule : submodule R₂ (module.End R₂ M₂) :=
{ carrier   := { f | is_pair_self_adjoint B₂ F₂ f },
  zero_mem' := is_adjoint_pair_zero,
  add_mem'  := λ f g hf hg, hf.add hg,
  smul_mem' := λ c f h, h.smul c, }

@[simp] lemma mem_is_pair_self_adjoint_submodule (f : module.End R₂ M₂) :
  f ∈ is_pair_self_adjoint_submodule B₂ F₂ ↔ is_pair_self_adjoint B₂ F₂ f :=
by refl

lemma is_pair_self_adjoint_equiv (e : M₂' ≃ₗ[R₂] M₂) (f : module.End R₂ M₂) :
  is_pair_self_adjoint B₂ F₂ f ↔
    is_pair_self_adjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) :=
begin
  have hₗ : (F₂.comp ↑e ↑e).comp_left (e.symm.conj f) = (F₂.comp_left f).comp ↑e ↑e :=
    by { ext, simp [linear_equiv.symm_conj_apply], },
  have hᵣ : (B₂.comp ↑e ↑e).comp_right (e.symm.conj f) = (B₂.comp_right f).comp ↑e ↑e :=
    by { ext, simp [linear_equiv.conj_apply], },
  have he : function.surjective (⇑(↑e : M₂' →ₗ[R₂] M₂) : M₂' → M₂) := e.surjective,
  show bilin_form.is_adjoint_pair _ _ _ _  ↔ bilin_form.is_adjoint_pair _ _ _ _,
  rw [is_adjoint_pair_iff_comp_left_eq_comp_right, is_adjoint_pair_iff_comp_left_eq_comp_right,
      hᵣ, hₗ, comp_injective _ _ ↑e ↑e he he],
end

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def is_self_adjoint (f : module.End R M) := is_adjoint_pair B B f f

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def is_skew_adjoint (f : module.End R₁ M₁) := is_adjoint_pair B₁ B₁ f (-f)

lemma is_skew_adjoint_iff_neg_self_adjoint (f : module.End R₁ M₁) :
  B₁.is_skew_adjoint f ↔ is_adjoint_pair (-B₁) B₁ f f :=
show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y),
by simp only [linear_map.neg_apply, bilin_form.neg_apply, bilin_form.neg_right]

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def self_adjoint_submodule := is_pair_self_adjoint_submodule B₂ B₂

@[simp] lemma mem_self_adjoint_submodule (f : module.End R₂ M₂) :
  f ∈ B₂.self_adjoint_submodule ↔ B₂.is_self_adjoint f := iff.rfl

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skew_adjoint_submodule := is_pair_self_adjoint_submodule (-B₂) B₂

@[simp] lemma mem_skew_adjoint_submodule (f : module.End R₂ M₂) :
  f ∈ B₂.skew_adjoint_submodule ↔ B₂.is_skew_adjoint f :=
by { rw is_skew_adjoint_iff_neg_self_adjoint, exact iff.rfl, }

end linear_adjoints

end bilin_form

section matrix_adjoints
open_locale matrix

variables {n : Type w} [fintype n]
variables (J J₂ A A' : matrix n n R₂)

/-- The condition for the square matrices `A`, `A'` to be an adjoint pair with respect to the square
matrices `J`, `J₂`. -/
def matrix.is_adjoint_pair := Aᵀ ⬝ J₂ = J ⬝ A'

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def matrix.is_self_adjoint := matrix.is_adjoint_pair J J A A

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def matrix.is_skew_adjoint := matrix.is_adjoint_pair J J A (-A)

@[simp] lemma matrix_is_adjoint_pair_bilin_form [decidable_eq n] :
  bilin_form.is_adjoint_pair J.to_bilin_form J₂.to_bilin_form A.to_lin' A'.to_lin' ↔
    matrix.is_adjoint_pair J J₂ A A' :=
begin
  rw bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right,
  have h : ∀ (B B' : bilin_form R₂ (n → R₂)), B = B' ↔ B.to_matrix = B'.to_matrix,
  { intros B B',
    split; intros h,
    { rw h },
    { rw [←to_matrix_to_bilin_form B, h, to_matrix_to_bilin_form B'] } },
  rw [h, J₂.to_bilin_form.to_matrix_comp_left A.to_lin',
      J.to_bilin_form.to_matrix_comp_right A'.to_lin', linear_map.to_matrix'_to_lin',
      linear_map.to_matrix'_to_lin', to_bilin_form_to_matrix, to_bilin_form_to_matrix],
  refl,
end

lemma matrix.is_adjoint_pair_equiv [decidable_eq n] (P : matrix n n R₂) (h : is_unit P) :
  (Pᵀ ⬝ J ⬝ P).is_adjoint_pair (Pᵀ ⬝ J ⬝ P) A A' ↔
    J.is_adjoint_pair J (P ⬝ A ⬝ P⁻¹) (P ⬝ A' ⬝ P⁻¹) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
begin
  let u := P.nonsing_inv_unit h',
  let v := Pᵀ.nonsing_inv_unit (P.is_unit_det_transpose h'),
  let x := Aᵀ * Pᵀ * J,
  let y := J * P * A',
  suffices : x * ↑u = ↑v * y ↔ ↑v⁻¹ * x = y * ↑u⁻¹,
  { dunfold matrix.is_adjoint_pair,
    repeat { rw matrix.transpose_mul, },
    simp only [←matrix.mul_eq_mul, ←mul_assoc, P.transpose_nonsing_inv h'],
    conv_lhs { to_rhs, rw [mul_assoc, mul_assoc], congr, skip, rw ←mul_assoc, },
    conv_rhs { rw [mul_assoc, mul_assoc], conv { to_lhs, congr, skip, rw ←mul_assoc }, },
    exact this, },
  rw units.eq_mul_inv_iff_mul_eq, conv_rhs { rw mul_assoc, }, rw v.inv_mul_eq_iff_eq_mul,
end

variables [decidable_eq n]

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pair_self_adjoint_matrices_submodule : submodule R₂ (matrix n n R₂) :=
(bilin_form.is_pair_self_adjoint_submodule J.to_bilin_form J₂.to_bilin_form).map
  (linear_map.to_matrix' : ((n → R₂) →ₗ[R₂] n → R₂) ≃ₗ[R₂] matrix n n R₂)

@[simp] lemma mem_pair_self_adjoint_matrices_submodule :
  A ∈ (pair_self_adjoint_matrices_submodule J J₂) ↔ matrix.is_adjoint_pair J J₂ A A :=
begin
  simp only [pair_self_adjoint_matrices_submodule, linear_equiv.coe_coe,
    linear_map.to_matrix'_apply, submodule.mem_map, bilin_form.mem_is_pair_self_adjoint_submodule],
  split,
  { rintros ⟨f, hf, hA⟩,
    have hf' : f = A.to_lin' := by rw [←hA, matrix.to_lin'_to_matrix'], rw hf' at hf,
    rw ←matrix_is_adjoint_pair_bilin_form, exact hf, },
  { intros h, refine ⟨A.to_lin', _, linear_map.to_matrix'_to_lin' _⟩,
    exact (matrix_is_adjoint_pair_bilin_form _ _ _ _).mpr h, },
end

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def self_adjoint_matrices_submodule : submodule R₂ (matrix n n R₂) :=
  pair_self_adjoint_matrices_submodule J J

@[simp] lemma mem_self_adjoint_matrices_submodule :
  A ∈ self_adjoint_matrices_submodule J ↔ J.is_self_adjoint A :=
by { erw mem_pair_self_adjoint_matrices_submodule, refl, }

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skew_adjoint_matrices_submodule : submodule R₂ (matrix n n R₂) :=
  pair_self_adjoint_matrices_submodule (-J) J

@[simp] lemma mem_skew_adjoint_matrices_submodule :
  A ∈ skew_adjoint_matrices_submodule J ↔ J.is_skew_adjoint A :=
begin
  erw mem_pair_self_adjoint_matrices_submodule,
  simp [matrix.is_skew_adjoint, matrix.is_adjoint_pair],
end

end matrix_adjoints
