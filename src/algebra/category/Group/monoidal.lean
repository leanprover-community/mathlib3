import category_theory.monoidal.Mon_
import algebra.category.Group.abelian
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

lemma one_mul' {R : Mon_ AddCommGroup.{u}} (x : R.X) : (1 : R.X) * x = x :=
begin
  rw [mul_def, one_def],
  convert add_monoid_hom.congr_fun R.one_mul (ulift.up 1 ⊗ₜ x),
  simp only [tensor_monoidal_category_left_unitor, left_unitor_hom_apply, tensor_product.lift.tmul,
    linear_map.coe_mk, one_zsmul],
end

lemma mul_one' {R : Mon_ AddCommGroup.{u}} (x : R.X) : x * (1 : R.X)= x :=
begin
  rw [mul_def, one_def],
  convert add_monoid_hom.congr_fun R.mul_one (x ⊗ₜ ulift.up 1),
  simp only [tensor_monoidal_category_right_unitor, right_unitor_hom,
    linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul, linear_map.coe_mk, one_zsmul],
end

lemma mul_assoc' {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  x * y * z = x * (y * z) :=
add_monoid_hom.congr_fun R.mul_assoc ((x ⊗ₜ y) ⊗ₜ z)

lemma mul_add' {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  x * (y + z) = x * y + x * z :=
begin
  rw [mul_def, mul_def, mul_def, ←R.mul.map_add (x ⊗ₜ y) (x ⊗ₜ z)],
  congr,
  rw tensor_product.tmul_add,
end

lemma add_mul' {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  (x + y) * z = x * z + y * z :=
begin
  rw [mul_def, mul_def, mul_def, ←R.mul.map_add (x ⊗ₜ z) (y ⊗ₜ z)],
  congr,
  rw tensor_product.add_tmul,
end

def Mon_is_ring (R : Mon_ AddCommGroup.{u}) : ring R.X :=
{ one := 1,
  mul := (*),
  one_mul := one_mul',
  mul_one := mul_one',
  mul_assoc := mul_assoc',
  left_distrib := mul_add',
  right_distrib := add_mul',
  ..(infer_instance : add_comm_group R.X) }

local attribute [instance] Mon_is_ring

@[simps] def Mon_to_Ring : Mon_ AddCommGroup.{u} ⥤ Ring.{u} :=
{ obj := λ M, Ring.of M.X,
  map := λ _ _ f,
  { to_fun := f.hom,
    map_one' := add_monoid_hom.congr_fun f.one_hom (ulift.up 1),
    map_mul' := λ x y, add_monoid_hom.congr_fun f.mul_hom _,
  map_zero' := map_zero _,
  map_add' := map_add _ },
  map_id' := λ M, ring_hom.ext $ λ x,
  begin
    simp only [Mon_.id_hom', ring_hom.coe_mk, id_apply],
  end,
  map_comp' := λ A B C f g, ring_hom.ext $ λ x,
  begin
    simp only [Mon_.comp_hom', ring_hom.coe_mk, comp_apply],
  end }

lemma zmul_comm {R : Type u} [ring R] (x : R) (z : ℤ) :
  (z : R) * x = x * z :=
int.induction_on z (by simp only [algebra_map.coe_zero, zero_mul, mul_zero])
(λ n hn, begin
  simp only [int.cast_add, int.cast_coe_nat, algebra_map.coe_one] at hn ⊢,
  rw [add_mul, hn, one_mul, mul_add, mul_one],
end) $ λ n hn, begin
  simp only [int.cast_sub, int.cast_neg, int.cast_coe_nat, algebra_map.coe_one, neg_mul, mul_neg, neg_inj] at hn ⊢,
  rw [sub_mul, neg_mul, hn, one_mul, mul_sub, mul_one, mul_neg],
end

lemma one_map_ulift_int {A : Mon_ AddCommGroup.{u}} (z : ℤ) :
  A.one (ulift.up z) = z :=
begin
  induction z using int.induction_on with n hn n hn,
  { simpa only [algebra_map.coe_zero] using A.one.map_zero, },
  { simp only [int.cast_add, int.cast_coe_nat, algebra_map.coe_one] at hn ⊢,
    erw [←hn, A.one.map_add (ulift.up n) (ulift.up 1)],
    congr' 1, },
  { simp only [int.cast_sub, int.cast_neg, int.cast_coe_nat, algebra_map.coe_one] at hn ⊢,
    erw [←hn, A.one.map_sub (ulift.up (-n)) (ulift.up 1)],
    congr' 1 },
end

@[simps] def Ring_to_Mon_.obj (R : Ring.{u}) : Mon_ AddCommGroup.{u} :=
{ X := of R,
  one :=
  { to_fun := λ (z : ulift ℤ), (algebra_map ℤ R) z.down,
    map_zero' := map_zero _,
    map_add' := λ ⟨m⟩ ⟨n⟩, map_add _ _ _ },
  mul := (tensor_product.lift
  { to_fun := λ x,
    { to_fun := λ y, (x * y : R),
      map_add' := mul_add x,
      map_smul' := λ (z : ℤ) r,
      begin
        rw [ring_hom.id_apply, zsmul_eq_mul, zsmul_eq_mul, ←mul_assoc, ←zmul_comm, mul_assoc],
      end },
    map_add' := λ x y, linear_map.ext $ λ z,
    begin
      simp only [linear_map.coe_mk, linear_map.add_apply],
      rw add_mul,
    end,
    map_smul' := λ z r, begin
      rw [ring_hom.id_apply],
      ext1,
      simp only [zsmul_eq_mul, linear_map.coe_mk, linear_map.mul_apply, module.End.int_cast_apply],
      rw mul_assoc,
    end }).to_add_monoid_hom,
  one_mul' := begin
    ext1 z,
    induction z using tensor_product.induction_on with z x z x ihz ihx,
    { simp only [map_zero] },
    { simp only [zsmul_eq_mul, linear_map.coe_mk, eq_int_cast, tensor_monoidal_category_tensor_hom,
        comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul,
        to_int_linear_map_apply, add_monoid_hom.coe_mk, id_apply, tensor_product.lift.tmul,
        tensor_monoidal_category_left_unitor, left_unitor_hom_apply], },
    { simp only [map_add, ihz, ihx], },
  end,
  mul_one' := begin
    ext1 z,
    induction z using tensor_product.induction_on with x z x z ihx ihz,
    { simp only [map_zero] },
    { simp only [zsmul_eq_mul, linear_map.coe_mk, eq_int_cast, tensor_monoidal_category_tensor_hom,
        comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul, id_apply,
        to_int_linear_map_apply, add_monoid_hom.coe_mk, tensor_product.lift.tmul,
        tensor_monoidal_category_right_unitor, right_unitor_hom],
      rw zmul_comm, },
    { simp only [map_add, ihx, ihz], },
  end,
  mul_assoc' := begin
    ext1 z,
    induction z using tensor_product.induction_on with z c z c ihz ihc,
    { simp only [map_zero], },
    { simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_monoidal_category_tensor_hom,
        tensor_product.map_tmul, to_int_linear_map_apply, id_apply,
        tensor_monoidal_category_associator_hom_apply],
      induction z using tensor_product.induction_on with z b z b ihz ihb,
      { simp only [map_zero, tensor_product.zero_tmul], },
      { simp only [tensor_product.lift.tmul, linear_map.coe_mk, tensor_product.assoc_tmul, id_apply,
          to_int_linear_map_apply, tensor_product.map_tmul, linear_map.to_add_monoid_hom_coe],
        rw mul_assoc, },
      { simp only [map_add, ihz, ihb, tensor_product.add_tmul], }, },
    { simp only [map_add, ihz, ihc], },
  end }

@[simps] def Ring_to_Mon_ : Ring.{u} ⥤ Mon_ AddCommGroup.{u} :=
{ obj := Ring_to_Mon_.obj,
  map := λ X Y f,
  { hom := f.to_add_monoid_hom,
    one_hom' :=
    begin
      ext1 ⟨z⟩,
      simp only [ring_hom.to_add_monoid_hom_eq_coe, comp_apply, Ring_to_Mon_.obj_one_apply,
        eq_int_cast, ring_hom.coe_add_monoid_hom, map_int_cast],
    end,
    mul_hom' :=
    begin
      ext1 z,
      induction z using tensor_product.induction_on with x y x y hx hy,
      { simp only [map_zero], },
      { simp only [Ring_to_Mon_.obj_mul, ring_hom.to_add_monoid_hom_eq_coe, comp_apply,
          linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul, linear_map.coe_mk,
          ring_hom.coe_add_monoid_hom, map_mul, tensor_monoidal_category_tensor_hom,
          tensor_product.map_tmul, to_int_linear_map_apply], },
      { simp only [map_add, hx, hy], },
    end },
  map_id' := λ R,
  begin
    ext,
    simp only [ring_hom.to_add_monoid_hom_eq_coe, ring_hom.coe_add_monoid_hom, id_apply,
      Mon_.id_hom'],
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext,
    simp only [ring_hom.to_add_monoid_hom_eq_coe, comp_apply, ring_hom.coe_add_monoid_hom,
      Mon_.comp_hom'],
  end }

@[simps] def Mon_equiv_Ring.unit_iso.components_hom (A : Mon_ AddCommGroup.{u}) :
  A ⟶ Ring_to_Mon_.obj (Ring.of A.X) :=
{ hom := add_monoid_hom.id _,
  one_hom' := add_monoid_hom.ext $ λ ⟨z⟩,
  begin
    simp only [comp_apply, add_monoid_hom.id_apply],
    erw one_map_ulift_int,
    refl,
  end,
  mul_hom' := add_monoid_hom.ext $ λ z, tensor_product.induction_on z
    (by simp only [map_zero]) (λ (x : A.X) (y : A.X),
    begin
      rw [comp_apply, add_monoid_hom.id_apply, tensor_monoidal_category_tensor_hom,
        comp_apply, linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul,
        to_int_linear_map_apply, to_int_linear_map_apply, add_monoid_hom.id_apply,
        add_monoid_hom.id_apply],
      change A.mul _ = (Ring_to_Mon_.obj (Ring.of A.X)).mul _,
      rw [Ring_to_Mon_.obj_mul, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
        linear_map.coe_mk, linear_map.coe_mk, mul_def],
    end) $ λ x y h₁ h₂, by simp only [map_add, h₁, h₂] }

@[simps] def Mon_equiv_Ring.unit_iso.components_inv (A : Mon_ AddCommGroup.{u}) :
  Ring_to_Mon_.obj (Ring.of A.X) ⟶ A :=
{ hom := add_monoid_hom.id _,
  one_hom' := add_monoid_hom.ext $ λ ⟨z⟩,
  begin
    simp only [comp_apply, add_monoid_hom.id_apply],
    change (Ring_to_Mon_.obj (Ring.of A.X)).one (ulift.up z) = A.one (ulift.up z),
    rw [Ring_to_Mon_.obj_one_apply, one_map_ulift_int z],
    refl,
  end,
  mul_hom' := add_monoid_hom.ext $ λ z, tensor_product.induction_on z
    (by simp only [map_zero]) (λ (x y : A.X),
    begin
      rw [comp_apply, add_monoid_hom.id_apply, tensor_monoidal_category_tensor_hom, comp_apply,
        linear_map.to_add_monoid_hom_coe, tensor_product.map_tmul, to_int_linear_map_apply,
        to_int_linear_map_apply, add_monoid_hom.id_apply, add_monoid_hom.id_apply],
      change (Ring_to_Mon_.obj (Ring.of A.X)).mul _ = A.mul _,
      rw [Ring_to_Mon_.obj_mul, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
        linear_map.coe_mk, linear_map.coe_mk, mul_def],
    end) $ λ a b ha hb, by simp only [map_add, ha, hb] }


@[simps] def Mon_equiv_Ring.unit_iso :
  𝟭 (Mon_ AddCommGroup.{u}) ≅ Mon_to_Ring.{u} ⋙ Ring_to_Mon_.{u} :=
nat_iso.of_components (λ A,
{ hom := Mon_equiv_Ring.unit_iso.components_hom A,
  inv := Mon_equiv_Ring.unit_iso.components_inv A,
  hom_inv_id' :=
  begin
    ext,
    simp only [Mon_.comp_hom', comp_apply, Mon_.id_hom', id_apply],
    refl,
  end,
  inv_hom_id' :=
  begin
    ext,
    simp only [Mon_.comp_hom', comp_apply, Mon_.id_hom', id_apply],
    refl,
  end }) $ λ X Y f,
begin
  ext,
  simp only [Mon_.comp_hom', comp_apply, functor.id_map, functor.comp_map, Ring_to_Mon__map_hom,
    ring_hom.to_add_monoid_hom_eq_coe, ring_hom.coe_add_monoid_hom, Mon_to_Ring_map_apply],
  refl,
end

@[simps] def Mon_equiv_Ring.counit_iso.component_hom (R : Ring.{u}) :
  Ring.of (Ring_to_Mon_.obj R).X ⟶ R :=
{ to_fun := λ x, x,
  map_one' :=
  begin
    rw [one_def],
    change (algebra_map _ _) _ = _,
    rw map_one,
  end,
  map_mul' := λ x y, by rw [mul_def, Ring_to_Mon_.obj_mul, linear_map.to_add_monoid_hom_coe,
    tensor_product.lift.tmul, linear_map.coe_mk, linear_map.coe_mk],
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simps] def Mon_equiv_Ring.counit_iso.component_inv (R : Ring.{u}) :
  R ⟶ Ring.of (Ring_to_Mon_.obj R).X :=
{ to_fun := λ x, x,
  map_one' :=
  begin
    rw one_def,
    change _ = (algebra_map _ _) _,
    rw (algebra_map _ _).map_one,
  end,
  map_mul' := λ x y, by erw [mul_def, Ring_to_Mon_.obj_mul, linear_map.to_add_monoid_hom_coe,
    tensor_product.lift.tmul, linear_map.coe_mk],
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simps] def Mon_equiv_Ring.counit_iso :
  Ring_to_Mon_ ⋙ Mon_to_Ring ≅ 𝟭 Ring.{u} :=
nat_iso.of_components (λ R,
{ hom := Mon_equiv_Ring.counit_iso.component_hom _,
  inv := Mon_equiv_Ring.counit_iso.component_inv _,
  hom_inv_id' :=
  begin
    ext,
    simp only [comp_apply, Mon_equiv_Ring.counit_iso.component_hom_apply,
      Mon_equiv_Ring.counit_iso.component_inv_apply, id_apply],
  end,
  inv_hom_id' :=
  begin
    ext,
    simp only [comp_apply, Mon_equiv_Ring.counit_iso.component_inv_apply,
      Mon_equiv_Ring.counit_iso.component_hom_apply, id_apply],
  end }) $ λ X Y f,
begin
  ext,
  simp only [comp_apply, Mon_equiv_Ring.counit_iso.component_hom_apply, functor.comp_map,
    Mon_to_Ring_map_apply, Ring_to_Mon__map_hom, ring_hom.to_add_monoid_hom_eq_coe,
    ring_hom.coe_add_monoid_hom, functor.id_map],
end

@[simps] def Mon_equiv_Ring : Mon_ AddCommGroup.{u} ≌ Ring.{u} :=
{ functor := Mon_to_Ring,
  inverse := Ring_to_Mon_,
  unit_iso := Mon_equiv_Ring.unit_iso,
  counit_iso := Mon_equiv_Ring.counit_iso,
  functor_unit_iso_comp' := λ A,
  begin
    ext,
    simp only [comp_apply, Mon_to_Ring_map_apply, Mon_equiv_Ring.unit_iso_hom_app_hom_apply,
      Mon_equiv_Ring.counit_iso_hom_app_apply, id_apply],
  end }

end Mon_

end AddCommGroup
