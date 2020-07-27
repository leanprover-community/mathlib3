import algebra.category.Module.monoidal
import algebra.category.Algebra.basic
import category_theory.monoidal.internal

universes v u

open category_theory

lemma lcongr_fun {R : Type*} [semiring R] {M N : Type*} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N]
  {f g : M →ₗ[R] N} (h : f = g) (m : M) : f m = g m :=
congr_fun (congr_arg linear_map.to_fun h) m

def algebra_linear_map (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] :
  R →ₗ[R] A :=
{ map_smul' := λ x y, begin dsimp, simp [algebra.smul_def], end,
  ..algebra_map R A }

@[simp]
lemma algebra_linear_map_apply (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] (r : R) :
  algebra_linear_map R A r = algebra_map R A r := rfl

open_locale tensor_product

def mul_linear_map (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] :
  A ⊗[R] A →ₗ[R] A :=
tensor_product.lift (algebra.lmul R A)

@[simp] lemma mul_linear_map_apply (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] {x y} :
  mul_linear_map R A (x ⊗ₜ y) = x * y :=
begin
  dsimp [mul_linear_map],
  simp,
end

namespace Module

variables {R : Type u} [comm_ring R]

namespace Mon_Module_equivalence_Algebra

@[simps]
instance (A : Mon_ (Module R)) : ring A.X :=
{ one := A.one (1 : R),
  mul := λ x y, A.mul (x ⊗ₜ y),
  one_mul := λ x, by { convert lcongr_fun A.one_mul ((1 : R) ⊗ₜ x), simp, },
  mul_one := λ x, by { convert lcongr_fun A.mul_one (x ⊗ₜ (1 : R)), simp, },
  mul_assoc := λ x y z, by convert lcongr_fun A.mul_assoc ((x ⊗ₜ y) ⊗ₜ z),
  left_distrib := λ x y z,
  begin
    convert A.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z),
    rw ←tensor_product.tmul_add,
    refl,
  end,
  right_distrib := λ x y z,
  begin
    convert A.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z),
    rw ←tensor_product.add_tmul,
    refl,
  end,
  ..(by apply_instance : add_comm_group A.X) }

instance (A : Mon_ (Module R)) : algebra R A.X :=
{ map_zero' := A.one.map_zero,
  map_one' := rfl,
  map_mul' := λ x y,
  begin
    have h := lcongr_fun A.one_mul.symm (x ⊗ₜ (A.one y)),
    rwa [monoidal_category.left_unitor_hom_apply, ←A.one.map_smul] at h,
  end,
  commutes' := λ r a,
  begin dsimp,
    have h₁ := lcongr_fun A.one_mul (r ⊗ₜ a),
    have h₂ := lcongr_fun A.mul_one (a ⊗ₜ r),
    exact h₁.trans h₂.symm,
  end,
  smul_def' := λ r a, by { convert (lcongr_fun A.one_mul (r ⊗ₜ a)).symm, simp, },
  ..A.one }

@[simp] lemma algebra_map (A : Mon_ (Module R)) (r : R) : algebra_map R A.X r = A.one r := rfl

/--
Converting a monoid object in `Module R` to a bundled algebra.
-/
@[simps]
def functor : Mon_ (Module R) ⥤ Algebra R :=
{ obj := λ A, Algebra.of R A.X,
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := lcongr_fun f.one_hom (1 : R),
    map_mul' := λ x y, lcongr_fun f.mul_hom (x ⊗ₜ y),
    commutes' := λ r, lcongr_fun f.one_hom r,
    ..(f.hom.to_add_monoid_hom) }, }.

@[simps]
def inverse_obj (A : Algebra.{u} R) : Mon_ (Module.{u} R) :=
{ X := Module.of R A,
  one := algebra_linear_map R A,
  mul := mul_linear_map.{u u u} R A,
  one_mul' :=
  begin
    ext x,
    dsimp,
    rw [mul_linear_map_apply, monoidal_category.left_unitor_hom_apply, algebra.smul_def],
    refl,
  end,
  mul_one' :=
  begin
    ext x,
    dsimp,
    rw [mul_linear_map_apply, monoidal_category.right_unitor_hom_apply,
      ←algebra.commutes, algebra.smul_def],
    refl,
  end,
  mul_assoc' :=
  begin
    ext xy z,
    dsimp,
    apply tensor_product.induction_on xy,
    { simp only [linear_map.map_zero, tensor_product.zero_tmul], },
    { intros x y, dsimp, simp [mul_assoc], },
    { intros x y hx hy, dsimp, simp [tensor_product.add_tmul, hx, hy], },
  end }

/--
Converting a bundled algebra to a monoid object in `Module R`.
-/
@[simps]
def inverse : Algebra.{u} R ⥤ Mon_ (Module.{u} R) :=
{ obj := inverse_obj,
  map := λ A B f,
  { hom := f.to_linear_map, }, }.

end Mon_Module_equivalence_Algebra

open Mon_Module_equivalence_Algebra
-- set_option pp.notation false
-- set_option pp.implicit true
/--
The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def Mon_Module_equivalence_Algebra : Mon_ (Module R) ≌ Algebra R :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A,
    { hom := { hom := { to_fun := id, map_add' := λ x y, rfl, map_smul' := λ r a, rfl, } },
      inv := { hom := { to_fun := id, map_add' := λ x y, rfl, map_smul' := λ r a, rfl, } } })
    (sorry),
  counit_iso := nat_iso.of_components (λ A,
  { hom :=
    { to_fun := id,
      map_zero' := rfl,
      map_one' := begin dsimp [(1), has_one.one, monoid.one, Mon_Module_equivalence_Algebra.ring], simp, end,
      map_add' := λ x y, rfl,
      map_mul' := λ x y, begin dsimp, refl, end,
      commutes' := sorry, },
    inv := sorry}) (sorry), }.

/--
The equivalence `Mon_ (Type u) ≌ Mon.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
def Mon_Module_equivalence_Algebra_forget :
  Mon_Module_equivalence_Algebra.functor ⋙ forget₂ (Algebra R) (Module R) ≅ Mon_.forget :=
sorry
-- nat_iso.of_components (λ A, iso.refl _) (by tidy)

end Module
