import category_theory.monoidal.internal.Module
import category_theory.monoidal.transport
import ring_theory.tensor_product
import algebraic_geometry.GroupObject.Algebra2
universes v u
noncomputable theory
open category_theory

namespace Module

lemma monoidal_category.tensor_hom_tmul {R : Type u} [comm_ring R] (M N P Q : Module.{u} R)
  (f : M ⟶ N) (g : P ⟶ Q) (x : M) (y : P) :
  (f ⊗ g) (tensor_product.tmul R x y) = tensor_product.tmul R (f x) (g y) :=
tensor_product.map_tmul _ _ _ _

lemma tensor_μ_def {R : Type u} [comm_ring R] (X Y : Module.{u} R × Module.{u} R) :
  tensor_μ (Module.{u} R) X Y
    = (tensor_product.tensor_tensor_tensor_comm R X.1 X.2 Y.1 Y.2).to_linear_map :=
begin
  apply tensor_product.ext_fourfold',
  intros,
  simpa only [tensor_μ, Module.monoidal_category.associator_hom_apply,
    Module.monoidal_category.braiding_hom_apply, Module.comp_def, linear_map.comp_apply,
    Module.monoidal_category.associator_inv_apply, Module.monoidal_category.hom_apply,
    linear_equiv.coe_to_linear_map, tensor_product.tensor_tensor_tensor_comm_tmul],
end
namespace Mon_Module_equivalence_Algebra

variables {R : Type u} [comm_ring R] (A : Mon_ (Module.{u} R))
open_locale tensor_product

lemma one_def : (1 : A.X) = A.one 1 := rfl
lemma mul_def (x y : A.X) : x * y = A.mul (x ⊗ₜ y) := rfl

end Mon_Module_equivalence_Algebra
end Module
section

variables (C : Type*) [category C] [monoidal_category C] [symmetric_category C]
lemma Mon_.tensor_unit : (𝟙_ (Mon_ C)) = Mon_.trivial C := rfl
@[simp] lemma Mon_.tensor_unit_one : (𝟙_ (Mon_ C)).one = 𝟙 _ := rfl
@[simp] lemma Mon_.tensor_unit_mul : (𝟙_ (Mon_ C)).mul = (λ_ (𝟙_ C)).hom := rfl
@[simp] lemma Mon_.tensor_one (X Y : Mon_ C) :
  (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl
@[simp] lemma Mon_.tensor_mul (X Y : Mon_ C) :
  (X ⊗ Y).mul = tensor_μ C (X.X, Y.X) (X.X, Y.X) ≫ (X.mul ⊗ Y.mul) := rfl
lemma Mon_.tensor_X (X Y : Mon_ C) : (X ⊗ Y).X = X.X ⊗ Y.X := rfl
@[simp] lemma Mon_.tensor_hom {M N P Q : Mon_ C} (f : M ⟶ N) (g : P ⟶ Q) :
  (f ⊗ g).hom = f.hom ⊗ g.hom := rfl
@[simp] lemma Mon_.associator (M N P : Mon_ C) :
  α_ M N P = Mon_.iso_of_iso (α_ M.X N.X P.X) Mon_.one_associator Mon_.mul_associator := rfl
@[simp] lemma Mon_.left_unitor (M : Mon_ C) :
  λ_ M = Mon_.iso_of_iso (λ_ M.X) Mon_.one_left_unitor Mon_.mul_left_unitor := rfl
@[simp] lemma Mon_.right_unitor (M : Mon_ C) :
  ρ_ M = Mon_.iso_of_iso (ρ_ M.X) Mon_.one_right_unitor Mon_.mul_right_unitor := rfl

end

namespace Algebra
variables (R : Type u) [comm_ring R]
open Module.Mon_Module_equivalence_Algebra category_theory.monoidal_category

instance : monoidal_category (Algebra.{u} R) :=
monoidal.transport Module.Mon_Module_equivalence_Algebra
#check Module.monoidal_category.associator
def tensor_def (X Y : Algebra.{u} R) :
  X ⊗ Y ≅ (Module.Mon_Module_equivalence_Algebra.functor.obj
    (Module.Mon_Module_equivalence_Algebra.inverse.obj X ⊗
    Module.Mon_Module_equivalence_Algebra.inverse.obj Y)) := iso.refl _
#check tensor_product.assoc
#check Module.Mon_Module_equivalence_Algebra_forget
#check linear_map.mul'

variables {A B : Type u} [ring A] [ring B][algebra R A] [algebra R B]

instance : smul_comm_class R (tensor_product R A B) (tensor_product R A B) :=
by sorry

lemma tensor_tensor_tensor_comm_comp_mul' (A B : Type u) [ring A] [ring B]
  [algebra R A] [algebra R B] :
  (tensor_product.map (linear_map.mul' R A) (linear_map.mul' R B)).comp
  (tensor_product.tensor_tensor_tensor_comm R A B A B).to_linear_map
  = linear_map.mul' R (tensor_product R A B) :=
begin
  apply tensor_product.ext_fourfold',
  intros w x y z,
  simp only [linear_map.coe_comp, linear_equiv.coe_to_linear_map, function.comp_app,
    tensor_product.tensor_tensor_tensor_comm_tmul, tensor_product.map_tmul, linear_map.mul'_apply,
    algebra.tensor_product.tmul_mul_tmul],
end

lemma tensor_product.ext_iff {R : Type*} [comm_ring R] {M N P : Type*}
  [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
  [module R M] [module R N] [module R P]
  (f g : tensor_product R M N →ₗ[R] P) :
  f = g ↔ ∀ (x : M) (y : N), f (tensor_product.tmul R x y) = g (tensor_product.tmul R x y) :=
⟨λ h x y, h ▸ rfl, λ h, tensor_product.ext' h⟩

def tensor_iso (X Y : Algebra.{u} R) :
  X ⊗ Y ≅ Algebra.of R (tensor_product R X Y) :=
alg_equiv.to_Algebra_iso
(alg_equiv.of_linear_equiv (linear_equiv.refl _ _)
begin
  intros x y,
  dsimp,
  rw Module.tensor_μ_def,
  sorry
  --exact (tensor_product.ext_iff _ _).1
end sorry)

























#exit
def ε : R →ₐ[R] Algebra.of R (𝟙_ (Mon_ (Module.{u} R))).X :=
alg_hom.of_linear_map linear_map.id rfl
(λ x y,
  begin
    rw [mul_def (𝟙_ (Mon_ (Module.{u} R))), Mon_.tensor_unit_mul,
      Module.monoidal_category.left_unitor_hom_apply],
    refl,
  end)

variables {R} (X Y : Mon_ (Module.{u} R))

def nice : Module.of R (Algebra.of R X.X) ≅ X.X :=
Module.Mon_Module_equivalence_Algebra_forget.app _

-- why is ring_zero a simp lemma....
def μ (X Y : Mon_ (Module.{u} R)) :
  Algebra.of R X.X ⊗ Algebra.of R Y.X ⟶ Algebra.of R (X ⊗ Y).X :=
alg_hom.of_linear_map (tensor_product.map (nice X).hom (nice Y).hom) rfl $
begin
  intros x y,
  refine x.induction_on _ _ _,
  { simp only [zero_mul, map_zero, Mon_.X.ring_mul, Mon_.tensor_mul,
     coe_comp, function.comp_app, tensor_product.zero_tmul] },
  { intros w z,
    refine y.induction_on _ _ _,
    { simp only [mul_zero, map_zero], },
    { intros x y,
      refl, },
    { intros a b ha hb,
      simp only [mul_add, map_add, tensor_product.map_tmul, linear_map.coe_mk, id.def, ha, hb] }},
  { intros a b ha hb,
    simp only [add_mul, map_add, tensor_product.map_tmul, linear_map.coe_mk, id.def, ha, hb] }
end

#exit
def monoidal_Mon_Module_equivalence_Algebra :
  monoidal_functor (Mon_ (Module.{u} R)) (Algebra.{u} R) :=
{ ε := ε R,
  μ := μ,
  μ_natural' := λ X Y W Z f g, by ext; refl,
  associativity' := _,
  left_unitality' := _,
  right_unitality' := _,
  ε_is_iso := _,
  μ_is_iso := _, ..Module.Mon_Module_equivalence_Algebra.functor }


#check monoidal_functor
def tensor_obj (A B : Algebra.{u} R) : A ⊗ B ≅ Algebra.of R (tensor_product R A B) :=
begin
  show Module.Mon_Module_equivalence_Algebra.functor.obj _ ≅ _,
  dsimp,
  refine alg_equiv.to_Algebra_iso _,
  exact
  { map_mul' := _,
  map_add' := _,
  commutes' := _, .. equiv.refl _ },
end




end Algebra
