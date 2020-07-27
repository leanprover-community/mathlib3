import algebra.category.Module.monoidal
import algebra.category.Algebra.basic
import category_theory.monoidal.internal

universes v u

open category_theory

lemma lcongr_fun {R : Type*} [semiring R] {M N : Type*} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N]
  {f g : M →ₗ[R] N} (h : f = g) (m : M) : f m = g m :=
congr_fun (congr_arg linear_map.to_fun h) m

lemma algebra_linear_map (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] :
  R →ₗ[R] A :=
{ map_smul' := λ x y, begin dsimp, simp [algebra.smul_def], end,
  ..algebra_map R A }

open_locale tensor_product

lemma mul_linear_map (R : Type*) [comm_semiring R] (A : Type*) [semiring A] [algebra R A] :
  A ⊗[R] A →ₗ[R] A :=
tensor_product.lift
{ to_fun := λ x,
  { to_fun := λ y, x * y,
    map_add' := sorry,
    map_smul' := sorry, },
  map_add' := sorry,
  map_smul' := sorry, }


namespace Module

variables {R : Type u} [comm_ring R]

namespace Mon_Module_equivalence_Algebra

/--
Converting a monoid object in `Module R` to a bundled algebra.
-/
def functor : Mon_ (Module R) ⥤ Algebra R :=
{ obj := λ A,
  { carrier := A.X,
    is_ring :=
    { one := A.one (1 : R),
      mul := λ x y, A.mul (x ⊗ₜ y),
      one_mul := λ x, by { convert lcongr_fun A.one_mul ((1 : R) ⊗ₜ x), simp, },
      mul_one := λ x, by { convert lcongr_fun A.mul_one (x ⊗ₜ (1 : R)), simp, },
      mul_assoc := λ x y z, by convert lcongr_fun A.mul_assoc ((x ⊗ₜ y) ⊗ₜ z),
      left_distrib := sorry,
      right_distrib := sorry,
      ..(by apply_instance : add_comm_group A.X) },
    is_algebra :=
    sorry },
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := lcongr_fun f.one_hom (1 : R),
    map_mul' := λ x y, lcongr_fun f.mul_hom (x ⊗ₜ y),
    commutes' := sorry,
    ..(f.hom.to_add_monoid_hom) }, }.

/--
Converting a bundled algebra to a monoid object in `Module R`.
-/
def inverse : Algebra R ⥤ Mon_ (Module R) :=
{ obj := λ A,
  { X := Module.of R A,
    one := algebra_linear_map R A,
    mul := mul_linear_map R A,
    one_mul' := sorry,
    mul_one' := sorry,
    mul_assoc' := by { ext, simp [mul_assoc], sorry, }, },
  map := λ A B f,
  { hom := f.to_linear_map, }, }.

end Mon_Module_equivalence_Algebra

open Mon_Module_equivalence_Algebra

/--
The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
def Mon_Module_equivalence_Algebra : Mon_ (Module R) ≌ Algebra R :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A, { hom := { hom := sorry, }, inv := { hom := sorry, }})
    (sorry),
  counit_iso := nat_iso.of_components (λ A,
  { hom := sorry,
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
