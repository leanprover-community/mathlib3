import category_theory.monoidal.of_has_finite_products
import category_theory.monoidal.Mon_
import algebra.category.Group.limits
import algebra.category.Group.biproducts
import algebra.category.Group.abelian
import category_theory.elementwise
import linear_algebra.tensor_product

noncomputable theory

universes u

open category_theory category_theory.monoidal_category category_theory.limits
open_locale zero_object tensor_product

namespace AddCommGroup

@[simps] def to_int_linear_map {X Y : AddCommGroup.{u}} (f : X ⟶ Y) : X →ₗ[ℤ] Y :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := λ n x, by rw [ring_hom.id_apply, map_zsmul] }

namespace Mon_

@[simps] def left_unitor (X : AddCommGroup.{u}) :
  of ((of (ulift ℤ) : AddCommGroup.{u}) ⊗[ℤ] X) ≅ X :=
{ hom :=
  { to_fun := tensor_product.lift
    { to_fun := λ (z : ulift ℤ),
      { to_fun := λ (x : X), ulift.down z • x,
        map_add' := λ (x y : X), smul_add _ _ _,
        map_smul' := λ (r : ℤ) (x : X), by rw [smul_comm, ring_hom.id_apply] },
      map_add' := λ ⟨m⟩ ⟨n⟩,
      begin
        ext1 x,
        simpa only [ulift.add_down, linear_map.coe_mk, linear_map.add_apply] using add_smul _ _ _,
      end,
      map_smul' := λ r ⟨r'⟩,
      begin
        ext1 x,
        simpa only [zsmul_eq_mul, ulift.mul_down, ulift.int_cast_down, int.cast_id,
          linear_map.coe_mk, eq_int_cast, linear_map.mul_apply, module.End.int_cast_apply] using
          mul_smul _ _ _,
      end },
    map_zero' := map_zero _,
    map_add' := map_add _ },
  inv :=
  { to_fun := λ x, ulift.up 1 ⊗ₜ x,
    map_zero' := tensor_product.tmul_zero _ _,
    map_add' := tensor_product.tmul_add _ },
  hom_inv_id' :=
  begin
    ext1,
    induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero], },
    { simp only [comp_apply, add_monoid_hom.coe_mk, tensor_product.lift.tmul, linear_map.coe_mk,
        tensor_product.tmul_smul, id_apply],
      rw [tensor_product.smul_tmul'],
      congr' 1,
      ext1,
      simp only [ulift.smul_down, algebra.id.smul_eq_mul, mul_one], },
    { simp only [map_add, ha, hb] }
  end,
  inv_hom_id' :=
  begin
    ext1,
    simp only [comp_apply, add_monoid_hom.coe_mk, tensor_product.lift.tmul, linear_map.coe_mk,
      one_zsmul, id_apply],
  end }

@[simps] def right_unitor (X : AddCommGroup.{u}) :
  of (X ⊗[ℤ] (of (ulift ℤ) : AddCommGroup.{u})) ≅ X :=
{ hom := (tensor_product.lift
  { to_fun := λ (x : X),
    { to_fun := λ z, ulift.down z • x,
      map_add' := λ (a b : ulift ℤ), by { rw ←add_smul, refl, },
      map_smul' := λ (r : ℤ) ⟨r'⟩, by { rw [ring_hom.id_apply, ←smul_assoc], refl, } },
    map_add' := λ x y,
    begin
      ext1 ⟨m⟩,
      simp only [smul_add, linear_map.coe_mk, linear_map.add_apply],
    end,
    map_smul' := λ r x,
    begin
      ext1 ⟨m⟩,
      simp only [linear_map.coe_mk, eq_int_cast, int.cast_id, linear_map.smul_apply],
      rw smul_comm,
    end }).to_add_monoid_hom,
  inv :=
  { to_fun := λ x, x ⊗ₜ ulift.up 1,
    map_zero' := tensor_product.zero_tmul _ _,
    map_add' := λ _ _, tensor_product.add_tmul _ _ _, },
  hom_inv_id' :=
  begin
    ext1 x,
    induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero] },
    { simp only [linear_map.coe_mk, comp_apply, linear_map.to_add_monoid_hom_coe,
        tensor_product.lift.tmul, add_monoid_hom.coe_mk, id_apply],
      rw tensor_product.smul_tmul,
      congr' 1, ext1,
      simp only [ulift.smul_down, algebra.id.smul_eq_mul, mul_one], },
    { simp only [map_add, ha, hb], },
  end,
  inv_hom_id' :=
  begin
    ext1,
    simp only [linear_map.coe_mk, comp_apply, add_monoid_hom.coe_mk, one_zsmul, id_apply,
      linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul],
  end }

@[simps] def tensor_monoidal_category : category_theory.monoidal_category AddCommGroup.{u} :=
{ tensor_obj := λ X Y, of (X ⊗[ℤ] Y),
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g,
    (tensor_product.map (to_int_linear_map f) (to_int_linear_map g)).to_add_monoid_hom,
  tensor_id' := λ X Y, add_monoid_hom.ext $ λ z,
  begin
    induction z using tensor_product.induction_on with _ _ x y ihx ihy,
    { rw [id_apply, map_zero] },
    { erw [tensor_product.map_tmul], },
    { rw [map_add, ihx, ihy, map_add], },
  end,
  tensor_comp' := λ _ _ _ _ _ _ f₁ f₂ g₁ g₂, add_monoid_hom.ext $ λ z,
  begin
    induction z using tensor_product.induction_on with _ _ x y ihx ihy,
    { rw [comp_apply, map_zero, map_zero, map_zero], },
    { erw [tensor_product.map_tmul], },
    { rw [map_add, ihx, ihy, map_add], },
  end,
  tensor_unit := of (ulift.{u} ℤ),
  associator := λ X Y Z,
  { hom :=
    { to_fun := (tensor_product.assoc ℤ X Y Z),
      map_zero' := (tensor_product.assoc ℤ X Y Z).map_zero,
      map_add' := (tensor_product.assoc ℤ X Y Z).map_add },
    inv :=
    { to_fun := (tensor_product.assoc ℤ X Y Z).symm,
      map_zero' := (tensor_product.assoc ℤ X Y Z).symm.map_zero,
      map_add' := (tensor_product.assoc ℤ X Y Z).symm.map_add },
    hom_inv_id' :=
    begin
      ext1,
      simp only [comp_apply, add_monoid_hom.coe_mk, linear_equiv.symm_apply_apply, id_apply],
    end,
    inv_hom_id' :=
    begin
      ext1,
      simp only [comp_apply, add_monoid_hom.coe_mk, linear_equiv.apply_symm_apply, id_apply],
    end },
  associator_naturality' := λ _ _ _ _ _ _ f₁ f₂ f₃,
  begin
    ext1 z,
    induction z using tensor_product.induction_on with x y x y ihx ihy,
    { rw [map_zero, comp_apply, map_zero, map_zero], },
    { simp only [comp_apply, add_monoid_hom.coe_mk, linear_map.to_add_monoid_hom_coe,
        tensor_product.map_tmul, to_int_linear_map_apply],
      induction x using tensor_product.induction_on with a b a b iha ihb,
      { rw [map_zero, tensor_product.zero_tmul, map_zero, tensor_product.zero_tmul, map_zero,
          map_zero], },
      { simp only [tensor_product.map_tmul, to_int_linear_map_apply, tensor_product.assoc_tmul,
          linear_map.to_add_monoid_hom_coe], },
      { simp only [map_add, iha, ihb, tensor_product.add_tmul], }, },
    { simp only [map_add, ihx, ihy], },
  end,
  left_unitor := left_unitor,
  left_unitor_naturality' := λ X Y f,
  begin
    ext1 z,
    induction z using tensor_product.induction_on with x y x y ihx ihy,
    { simp only [map_zero], },
    { simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul,
        to_int_linear_map_apply, id_apply, left_unitor_hom_apply, tensor_product.lift.tmul,
        linear_map.coe_mk],
      rw map_zsmul f, },
    { simp only [map_add, ihx, ihy], },
  end,
  right_unitor := right_unitor,
  right_unitor_naturality' := λ X Y f,
  begin
    ext1 z,
    induction z using tensor_product.induction_on with x y x y ihx ihy,
    { simp only [map_zero], },
    { simp only [right_unitor_hom, comp_apply, linear_map.to_add_monoid_hom_coe,
        tensor_product.map_tmul, to_int_linear_map_apply, id_apply, tensor_product.lift.tmul,
        linear_map.coe_mk],
      rw map_zsmul f, },
    { simp only [map_add, ihx, ihy], },
  end,
  pentagon' := λ A B C D,
  begin
    ext1 z,
    induction z using tensor_product.induction_on with x d x d ihx ihd,
    { simp only [map_zero] },
    { induction x using tensor_product.induction_on with x c x c ihx ihc,
      { simp only [map_zero, tensor_product.zero_tmul], },
      { induction x using tensor_product.induction_on with a b a b ihx ihy,
        { simp only [map_zero, tensor_product.zero_tmul], },
        { simp only [comp_apply, add_monoid_hom.coe_mk, id_apply, linear_map.to_add_monoid_hom_coe,
            tensor_product.map_tmul, to_int_linear_map_apply, tensor_product.assoc_tmul], },
        { simp only [map_add, ihx, ihy, tensor_product.add_tmul], }, },
      { simp only [map_add, ihx, ihc, tensor_product.add_tmul], }, },
    { simp only [map_add, ihx, ihd] },
  end,
  triangle' := λ X Y,
  begin
    ext1 z,
    induction z using tensor_product.induction_on with x y x y ihx ihy,
    { simp only [map_zero] },
    { induction x using tensor_product.induction_on with x z x z ihx ihz,
      { simp only [map_zero, tensor_product.zero_tmul] },
      { simp only [comp_apply, add_monoid_hom.coe_mk, id_apply, tensor_product.assoc_tmul,
          linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul, to_int_linear_map_apply,
          left_unitor_hom_apply, tensor_product.lift.tmul, linear_map.coe_mk,
          tensor_product.tmul_smul, right_unitor_hom],
        rw [tensor_product.smul_tmul', tensor_product.smul_tmul], },
      { simp only [map_add, ihx, ihz, tensor_product.add_tmul], }, },
    { simp only [map_add, ihx, ihy], },
  end }

local attribute [instance] tensor_monoidal_category

instance (R : Mon_ AddCommGroup.{u}) : has_one R.X :=
⟨R.one (ulift.up 1 : of (ulift.{u} ℤ))⟩

lemma one_def {R : Mon_ AddCommGroup.{u}} : 1 = R.one (ulift.up 1) := rfl

instance (R : Mon_ AddCommGroup.{u}) : has_mul R.X :=
⟨λ x y, R.mul (x ⊗ₜ y)⟩

lemma mul_def {R : Mon_ AddCommGroup.{u}} (x y : R.X) : x * y = R.mul (x ⊗ₜ y) := rfl

lemma one_mul {R : Mon_ AddCommGroup.{u}} (x : R.X) : (1 : R.X) * x = x :=
begin
  rw [mul_def, one_def],
  convert add_monoid_hom.congr_fun R.one_mul (ulift.up 1 ⊗ₜ x),
  simp only [tensor_monoidal_category_left_unitor, left_unitor_hom_apply, tensor_product.lift.tmul,
    linear_map.coe_mk, one_zsmul],
end

lemma mul_one {R : Mon_ AddCommGroup.{u}} (x : R.X) : x * (1 : R.X)= x :=
begin
  rw [mul_def, one_def],
  convert add_monoid_hom.congr_fun R.mul_one (x ⊗ₜ ulift.up 1),
  simp only [tensor_monoidal_category_right_unitor, right_unitor_hom,
    linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul, linear_map.coe_mk, one_zsmul],
end

lemma mul_assoc {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  x * y * z = x * (y * z) :=
add_monoid_hom.congr_fun R.mul_assoc ((x ⊗ₜ y) ⊗ₜ z)

lemma mul_add {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  x * (y + z) = x * y + x * z :=
begin
  rw [mul_def, mul_def, mul_def, ←R.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z)],
  congr,
  rw tensor_product.tmul_add,
end

lemma add_mul {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  (x + y) * z = x * z + y * z :=
begin
  rw [mul_def, mul_def, mul_def, ←R.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z)],
  congr,
  rw tensor_product.add_tmul,
end

instance (R : Mon_ AddCommGroup.{u}) : ring R.X :=
{ one := 1,
  mul := (*),
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  left_distrib := mul_add,
  right_distrib := add_mul,
  ..(infer_instance : add_comm_group R.X) }

end Mon_

end AddCommGroup
