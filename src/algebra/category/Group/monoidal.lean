import category_theory.monoidal.Mon_
import algebra.category.Group
import algebra.category.Ring
import linear_algebra.tensor_product
import category_theory.closed.monoidal
import category_theory.monoidal.Mod
import algebra.category.Module.basic

noncomputable theory

universes u v w

open category_theory category_theory.monoidal_category category_theory.limits

namespace AddCommGroup

@[simps] def to_int_linear_map {X Y : AddCommGroup.{u}} (f : X ⟶ Y) : X →ₗ[ℤ] Y :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := λ n x, by rw [ring_hom.id_apply, map_zsmul] }

@[simps] def to_int_linear_map₂ {X Y Z : AddCommGroup.{u}}
  (f : X ⟶  of (Y ⟶ Z)) : X →ₗ[ℤ] (Y →ₗ[ℤ] Z) :=
{ to_fun := λ x,
  { to_fun := λ y, (f x).to_fun y,
    map_add' := λ y y', by rw [add_monoid_hom.to_fun_eq_coe, map_add],
    map_smul' := λ r y, by rw [add_monoid_hom.to_fun_eq_coe, map_zsmul, ring_hom.id_apply] },
  map_add' := λ x y,
  begin
    ext z,
    simp only [linear_map.coe_mk, linear_map.add_apply, add_monoid_hom.to_fun_eq_coe, map_add,
      add_monoid_hom.add_apply],
  end,
  map_smul' := λ r x,
  begin
    ext z,
    simpa only [linear_map.coe_mk, linear_map.smul_apply, add_monoid_hom.to_fun_eq_coe, map_zsmul,
      ring_hom.id_apply],
  end }

namespace monoidal

namespace tensor_monoidal_category

open_locale zero_object tensor_product

def tensor_obj' (X Y : AddCommGroup.{u}) : AddCommGroup := AddCommGroup.of (X ⊗[ℤ] Y)

@[simps] def tensor_hom' {X₁ Y₁ X₂ Y₂ : AddCommGroup.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
  tensor_obj' X₁ X₂ ⟶ tensor_obj' Y₁ Y₂ :=
(tensor_product.map (to_int_linear_map f) (to_int_linear_map g)).to_add_monoid_hom

lemma tensor_id' (X Y : AddCommGroup.{u}) : tensor_hom' (𝟙 X) (𝟙 Y) = 𝟙 (tensor_obj' X Y) :=
begin
  ext z,
  induction z using tensor_product.induction_on with _ _ x y ihx ihy,
  { rw [id_apply, map_zero] },
  { erw [tensor_product.map_tmul], },
  { rw [map_add, ihx, ihy, map_add], },
end

lemma tensor_comp' {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : AddCommGroup}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
  tensor_hom' (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom' f₁ f₂ ≫ tensor_hom' g₁ g₂ :=
begin
  ext1 z,
  induction z using tensor_product.induction_on with _ _ x y ihx ihy,
  { rw [comp_apply, map_zero, map_zero, map_zero], },
  { erw [tensor_product.map_tmul], },
  { rw [map_add, ihx, ihy, map_add], },
end

def tensor_unit' : AddCommGroup.{u} := AddCommGroup.of (ulift.{u} ℤ)

@[simps] def associator' (X Y Z : AddCommGroup) :
  tensor_obj' (tensor_obj' X Y) Z ≅ tensor_obj' X (tensor_obj' Y Z) :=
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
  end }

lemma associator_naturality' {X₁ X₂ X₃ Y₁ Y₂ Y₃ : AddCommGroup}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  tensor_hom' (tensor_hom' f₁ f₂) f₃ ≫ (associator' Y₁ Y₂ Y₃).hom =
  (associator' X₁ X₂ X₃).hom ≫ tensor_hom' f₁ (tensor_hom' f₂ f₃) :=
begin
  ext1 z,
  induction z using tensor_product.induction_on with x y x y ihx ihy,
  { rw [map_zero, comp_apply, map_zero, map_zero], },
  { simp only [comp_apply, add_monoid_hom.coe_mk, linear_map.to_add_monoid_hom_coe,
      tensor_product.map_tmul, to_int_linear_map_apply],
    induction x using tensor_product.induction_on with a b a b iha ihb,
    { rw [tensor_product.zero_tmul, map_zero, map_zero, map_zero, map_zero], },
    { simp only [tensor_hom'_apply, tensor_product.map_tmul, to_int_linear_map_apply,
        associator'_hom_apply, tensor_product.assoc_tmul], },
    { simp only [map_add, iha, ihb, tensor_product.add_tmul], }, },
  { simp only [map_add, ihx, ihy], },
end

@[simps] def left_unitor' (X : AddCommGroup.{u}) :
  AddCommGroup.of (AddCommGroup.of (ulift.{u} ℤ) ⊗[ℤ] X) ≅ X :=
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

@[simps] def right_unitor' (X : AddCommGroup.{u}) :
  AddCommGroup.of (X ⊗[ℤ] AddCommGroup.of (ulift.{u} ℤ)) ≅ X :=
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

lemma left_unitor_naturality' {X Y : AddCommGroup} (f : X ⟶ Y) :
  tensor_hom' (𝟙 tensor_unit') f ≫ (left_unitor' Y).hom = (left_unitor' X).hom ≫ f :=
begin
  ext1 z,
  induction z using tensor_product.induction_on with x y x y ihx ihy,
  { simp only [map_zero], },
  { simp only [comp_apply, tensor_hom'_apply, tensor_product.map_tmul, to_int_linear_map_apply,
      id_apply, left_unitor'_hom_apply, tensor_product.lift.tmul, linear_map.coe_mk],
    rw map_zsmul f, },
  { simp only [map_add, ihx, ihy], },
end

lemma right_unitor_naturality' {X Y : AddCommGroup} (f : X ⟶ Y) :
  tensor_hom' f (𝟙 tensor_unit') ≫ (right_unitor' Y).hom = (right_unitor' X).hom ≫ f :=
begin
  ext1 z,
  induction z using tensor_product.induction_on with x y x y ihx ihy,
  { simp only [map_zero], },
  { simp only [right_unitor'_hom, comp_apply, tensor_hom'_apply, tensor_product.map_tmul,
      to_int_linear_map_apply, id_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
      linear_map.coe_mk],
    rw map_zsmul f, },
  { simp only [map_add, ihx, ihy], },
end

lemma pentagon' (W X Y Z : AddCommGroup) :
  tensor_hom' (associator' W X Y).hom (𝟙 Z) ≫
    (associator' W (tensor_obj' X Y) Z).hom ≫ tensor_hom' (𝟙 W) (associator' X Y Z).hom =
  (associator' (tensor_obj' W X) Y Z).hom ≫ (associator' W X (tensor_obj' Y Z)).hom :=
begin
  ext1 z,
  induction z using tensor_product.induction_on with x d x d ihx ihd,
  { simp only [map_zero] },
  { induction x using tensor_product.induction_on with x c x c ihx ihc,
    { simp only [map_zero, tensor_product.zero_tmul], },
    { induction x using tensor_product.induction_on with a b a b ihx ihy,
      { simp only [map_zero, tensor_product.zero_tmul], },
      { simp only [comp_apply, tensor_hom'_apply, tensor_product.map_tmul, to_int_linear_map_apply,
          associator'_hom_apply, tensor_product.assoc_tmul, id_apply], },
      { simp only [map_add, ihx, ihy, tensor_product.add_tmul], }, },
    { simp only [map_add, ihx, ihc, tensor_product.add_tmul], }, },
  { simp only [map_add, ihx, ihd] },
end

lemma triangle' (X Y : AddCommGroup) :
  (associator' X tensor_unit' Y).hom ≫ tensor_hom' (𝟙 X) (left_unitor' Y).hom =
  tensor_hom' (right_unitor' X).hom (𝟙 Y) :=
begin
  ext1 z,
  induction z using tensor_product.induction_on with x y x y ihx ihy,
  { simp only [map_zero] },
  { induction x using tensor_product.induction_on with x z x z ihx ihz,
    { simp only [map_zero, tensor_product.zero_tmul] },
    { simp only [comp_apply, associator'_hom_apply, tensor_product.assoc_tmul, tensor_hom'_apply,
        tensor_product.map_tmul, to_int_linear_map_apply, id_apply, left_unitor'_hom_apply,
        tensor_product.lift.tmul, linear_map.coe_mk, tensor_product.tmul_smul, right_unitor'_hom,
        linear_map.to_add_monoid_hom_coe],
      rw [tensor_product.smul_tmul', tensor_product.smul_tmul], },
    { simp only [map_add, ihx, ihz, tensor_product.add_tmul], }, },
  { simp only [map_add, ihx, ihy], },
end

end tensor_monoidal_category

section

open tensor_monoidal_category

@[simps] def tensor_monoidal_category : category_theory.monoidal_category AddCommGroup.{u} :=
{ tensor_obj := tensor_obj',
  tensor_hom := λ _ _ _ _, tensor_hom',
  tensor_unit := tensor_unit',
  associator := associator',
  left_unitor := left_unitor',
  right_unitor := right_unitor',

  tensor_id' := tensor_id',
  tensor_comp' := λ _ _ _ _ _ _, tensor_comp',
  associator_naturality' := λ _ _ _ _ _ _, associator_naturality',
  left_unitor_naturality' := λ _ _, left_unitor_naturality',
  right_unitor_naturality' := λ _ _, right_unitor_naturality',
  pentagon' := pentagon',
  triangle' := triangle' }

end

local attribute [instance] tensor_monoidal_category

section closed

open tensor_product

@[simps] def ihom_obj' (A B : AddCommGroup.{u}) : AddCommGroup.{u} :=
of (A ⟶ B)

@[simps] def ihom_map' (A : AddCommGroup.{u}) {X Y : AddCommGroup} (f : X ⟶ Y) :
  (ihom_obj' A X ⟶ ihom_obj' A Y) :=
{ to_fun := λ (g : A ⟶ X), g ≫ f,
  map_zero' := zero_comp,
  map_add' := λ g₁ g₂, preadditive.add_comp _ _ _ _ _ _ }

lemma ihom_map'_id (A X : AddCommGroup) : ihom_map' A (𝟙 X) = 𝟙 (ihom_obj' A X) :=
begin
  ext g a y,
  simp only [ihom_map'_apply, category.comp_id, id_apply],
end

lemma ihom_map'_comp (A) {X Y Z : AddCommGroup} (f : X ⟶ Y) (g : Y ⟶ Z) :
  ihom_map' A (f ≫ g) = ihom_map' A f ≫ ihom_map' A g :=
begin
  ext g a y,
  simp only [ihom_map'_apply, comp_apply],
end

@[simps] def ihom (A : AddCommGroup.{u}) : AddCommGroup.{u} ⥤ AddCommGroup.{u} :=
{ obj := ihom_obj' A,
  map := λ _ _, ihom_map' A,
  map_id' := ihom_map'_id A,
  map_comp' := λ _ _ _, ihom_map'_comp A }

namespace tensor_left_ihom_adj

@[simps] def hom_equiv'.from_tensor (A X Y : AddCommGroup.{u}) (f : (tensor_left A).obj X ⟶ Y) :
  X ⟶ (ihom A).obj Y :=
{ to_fun := λ x, ({ to_fun := λ a, a ⊗ₜ x,
    map_zero' := zero_tmul _ _,
    map_add' := λ _ _, add_tmul _ _ _ } : A ⟶ AddCommGroup.of (tensor_product ℤ A X)) ≫ f,
  map_zero' := add_monoid_hom.ext $ λ a,
  begin
    simp only [tmul_zero, comp_apply, add_monoid_hom.coe_mk, map_zero, ihom_obj'_str_zero_apply],
  end,
  map_add' := λ x₁ x₂, add_monoid_hom.ext $ λ a,
  begin
    simp only [comp_apply, add_monoid_hom.coe_mk, ihom_obj'_str_add_apply, tmul_add, map_add],
  end }

@[simps] def hom_equiv'.to_tensor (A X Y : AddCommGroup.{u}) (f : X ⟶ (ihom A).obj Y) :
  ((tensor_left A).obj X ⟶ Y) :=
{ to_fun := tensor_product.lift
  { to_fun := λ (a : A), to_int_linear_map
    ({ to_fun := λ x, (f x).to_fun a,
      map_zero' := by rw [map_zero, add_monoid_hom.to_fun_eq_coe, ihom_obj'_str_zero_apply],
      map_add' := λ x y, by rw [map_add, add_monoid_hom.to_fun_eq_coe, add_monoid_hom.to_fun_eq_coe,
        add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply] } : X ⟶ Y),
    map_add' := λ a₁ a₂,
    begin
      ext x,
      simp only [add_monoid_hom.to_fun_eq_coe, map_add, to_int_linear_map_apply,
        add_monoid_hom.coe_mk, linear_map.add_apply],
    end,
    map_smul' := λ z a,
    begin
      ext x,
      simp only [add_monoid_hom.to_fun_eq_coe, to_int_linear_map_apply, add_monoid_hom.coe_mk,
        eq_int_cast, int.cast_id, linear_map.smul_apply],
      rw map_zsmul,
    end },
  map_zero' := map_zero _,
  map_add' := λ z₁ z₂, map_add _ _ _ }

@[simps] def hom_equiv' (A X Y : AddCommGroup) : ((tensor_left A).obj X ⟶ Y) ≃ (X ⟶ (ihom A).obj Y) :=
{ to_fun := hom_equiv'.from_tensor A _ _,
  inv_fun := hom_equiv'.to_tensor A _ _,
  left_inv := λ g,
  begin
    ext z,
    simp only [hom_equiv'.from_tensor_apply, add_monoid_hom.to_fun_eq_coe, comp_apply,
      add_monoid_hom.coe_mk, hom_equiv'.to_tensor_apply],
    induction z using tensor_product.induction_on,
    { simp only [map_zero] },
    { simp only [add_monoid_hom.coe_mk, lift.tmul, linear_map.coe_mk, to_int_linear_map_apply], },
    { simp only [map_add, *], },
  end,
  right_inv := λ g,
  begin
    ext z,
    simp only [add_monoid_hom.to_fun_eq_coe, hom_equiv'.from_tensor_apply, comp_apply,
      add_monoid_hom.coe_mk, hom_equiv'.to_tensor_apply, lift.tmul, linear_map.coe_mk,
      to_int_linear_map_apply],
  end }

@[simps] def unit' (A : AddCommGroup.{u}) :
  𝟭 AddCommGroup ⟶ tensor_left A ⋙ ihom A :=
{ app := λ X,
  { to_fun := λ (x : X),
    { to_fun := λ a, a ⊗ₜ x,
      map_zero' := zero_tmul _ _,
      map_add' := λ _ _, add_tmul _ _ _ },
    map_zero' := add_monoid_hom.ext $ λ x, by simp only [tmul_zero, add_monoid_hom.coe_mk,
      ihom_obj'_str_zero_apply],
    map_add' := λ (x x' : X), add_monoid_hom.ext $ λ a,
    begin
      simpa only [add_monoid_hom.coe_mk, ihom_obj'_str_add_apply] using tmul_add _ _ _,
    end },
  naturality' := λ X Y f,
  begin
    ext (x : X) a,
    simp only [add_monoid_hom.coe_mk, functor.id_map, comp_apply, functor.comp_map, tensor_left_map,
      tensor_monoidal_category_tensor_hom, ihom_map, ihom_map'_apply, map_tmul,  id_apply,
      tensor_monoidal_category.tensor_hom'_apply, to_int_linear_map_apply],
  end }

@[simps] def counit' (A : AddCommGroup.{u}) : ihom A ⋙ tensor_left A ⟶ 𝟭 AddCommGroup :=
{ app := λ X, (tensor_product.lift
  { to_fun := λ a,
    { to_fun := λ (g : A →+ X), g a,
      map_add' := λ g h, add_monoid_hom.add_apply _ _ _,
      map_smul' := λ (z : ℤ) g, by { simp only [add_monoid_hom.coe_smul, pi.smul_apply,
        eq_int_cast, int.cast_id], } },
    map_add' := λ a b,
    begin
      ext g,
      simp only [map_add, linear_map.coe_mk, linear_map.add_apply],
    end,
    map_smul' := λ (z : ℤ) a,
    begin
      ext g,
      simp only [eq_int_cast, int.cast_id, linear_map.coe_mk, linear_map.smul_apply],
      rw map_zsmul,
    end }).to_add_monoid_hom,
  naturality' := λ X Y f,
  begin
    ext z,
    simp only [functor.comp_map, ihom_map, tensor_left_map, tensor_monoidal_category_tensor_hom,
      comp_apply, tensor_monoidal_category.tensor_hom'_apply, linear_map.to_add_monoid_hom_coe,
      functor.id_map],
    induction z using tensor_product.induction_on,
    { simp only [map_zero] },
    { simp only [linear_map.coe_mk, map_tmul, to_int_linear_map_apply, id_apply, ihom_map'_apply,
        lift.tmul, comp_apply] },
    { simp only [map_add, *] }
  end }

lemma hom_equiv_unit' (A : AddCommGroup.{u}) {X Y : AddCommGroup.{u}}
  {f : (tensor_left A).obj X ⟶ Y} :
  (hom_equiv' A X Y) f = (unit' A).app X ≫ (ihom A).map f :=
begin
  ext x a,
  simp only [hom_equiv'_apply, hom_equiv'.from_tensor_apply, comp_apply, add_monoid_hom.coe_mk,
    ihom_map, ihom_map'_apply, unit'_app_apply_apply],
end

lemma hom_equiv_counit' (A : AddCommGroup.{u}) {X Y : AddCommGroup.{u}}
  {g : X ⟶ (ihom A).obj Y} :
  ((hom_equiv' A X Y).symm) g = (tensor_left A).map g ≫ (counit' A).app Y :=
begin
  ext x a,
  simp only [add_monoid_hom.to_fun_eq_coe, hom_equiv'_symm_apply, hom_equiv'.to_tensor_apply,
    tensor_left_map, tensor_monoidal_category_tensor_hom, counit'_app, comp_apply,
    tensor_monoidal_category.tensor_hom'_apply, linear_map.to_add_monoid_hom_coe],
  induction x using tensor_product.induction_on,
  { simp only [map_zero] },
  { simp only [lift.tmul, linear_map.coe_mk, to_int_linear_map_apply, add_monoid_hom.coe_mk,
      map_tmul, id_apply] },
  { simp only [map_add, *] }
end

end tensor_left_ihom_adj

open tensor_left_ihom_adj

instance (A : AddCommGroup.{u}) : closed A :=
{ is_adj :=
  { right := ihom A,
    adj :=
    { hom_equiv := hom_equiv' A,
      unit := unit' A,
      counit := counit' A,
      hom_equiv_unit' := λ _ _ _, hom_equiv_unit' A,
      hom_equiv_counit' := λ _ _ _, hom_equiv_counit' A } } }

instance : monoidal_closed AddCommGroup.{u} :=
{ closed' := λ A, infer_instance }

@[simps] def curry {A B C : AddCommGroup.{u}} (f : A ⊗ B ⟶ C) : B ⟶ of (A ⟶ C) :=
hom_equiv'.from_tensor A B C f

@[simps] def curry' {A B C : AddCommGroup.{u}} (f : A ⊗ B ⟶ C) : A ⟶ of (B ⟶ C) :=
{ to_fun := λ a,
  { to_fun := λ b, (curry f b).to_fun a,
    map_zero' := by rw [add_monoid_hom.to_fun_eq_coe, map_zero, zero_apply],
    map_add' := λ x y, by simp only [add_monoid_hom.to_fun_eq_coe, map_add,
      add_monoid_hom.add_apply] },
  map_zero' := add_monoid_hom.ext $ λ b, by simp only [add_monoid_hom.to_fun_eq_coe, map_zero,
    add_monoid_hom.coe_mk, ihom_obj'_str_zero_apply],
  map_add' := λ x y, add_monoid_hom.ext $ λ z, by simp only [add_monoid_hom.to_fun_eq_coe,
    curry_apply_apply, add_monoid_hom.coe_mk, ihom_obj'_str_add_apply, add_tmul, map_add] }

@[simps] def uncurry {A B C : AddCommGroup.{u}} (f : B ⟶ of (A ⟶ C)) : A ⊗ B ⟶ C :=
hom_equiv'.to_tensor A B C f

@[simps] def uncurry' {A B C : AddCommGroup.{u}} (f : A ⟶ of (B ⟶ C)) : A ⊗ B ⟶ C :=
(tensor_product.lift
  { to_fun := λ a,
    { to_fun := λ b, uncurry f (b ⊗ₜ a),
      map_add' := λ x y, by rw [add_tmul, map_add],
      map_smul' := λ (z : ℤ) x, by simp only [uncurry_apply, lift.tmul, ring_hom.id_apply,
        map_zsmul, linear_map.smul_apply] },
    map_add' :=
    begin
      intros a b,
      ext c,
      simp only [map_add, uncurry_apply, lift.tmul, linear_map.coe_mk, linear_map.add_apply],
    end,
    map_smul' :=
    begin
      intros z a,
      ext b,
      simp only [map_zsmul, linear_map.smul_apply, tmul_smul, linear_map.coe_mk, eq_int_cast,
        int.cast_id],
    end }).to_add_monoid_hom

end closed

section Mon_

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
  simp only [tensor_monoidal_category_left_unitor, tensor_monoidal_category.left_unitor'_hom_apply,
    tensor_product.lift.tmul, linear_map.coe_mk, one_zsmul],
end

lemma mul_one' {R : Mon_ AddCommGroup.{u}} (x : R.X) : x * (1 : R.X)= x :=
begin
  rw [mul_def, one_def],
  convert add_monoid_hom.congr_fun R.mul_one (x ⊗ₜ ulift.up 1),
  simp only [tensor_monoidal_category_right_unitor, tensor_monoidal_category.right_unitor'_hom,
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
        comp_apply, tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
        to_int_linear_map_apply, add_monoid_hom.coe_mk, id_apply, linear_map.to_add_monoid_hom_coe,
        tensor_product.lift.tmul, tensor_monoidal_category_left_unitor,
        tensor_monoidal_category.left_unitor'_hom_apply], },
    { simp only [map_add, ihz, ihx], },
  end,
  mul_one' := begin
    ext1 z,
    induction z using tensor_product.induction_on with x z x z ihx ihz,
    { simp only [map_zero] },
    { simp only [zsmul_eq_mul, linear_map.coe_mk, eq_int_cast, tensor_monoidal_category_tensor_hom,
        comp_apply, tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul, id_apply,
        to_int_linear_map_apply, add_monoid_hom.coe_mk, linear_map.to_add_monoid_hom_coe,
        tensor_product.lift.tmul, tensor_monoidal_category_right_unitor,
        tensor_monoidal_category.right_unitor'_hom],
      rw zmul_comm, },
    { simp only [map_add, ihx, ihz], },
  end,
  mul_assoc' := begin
    ext1 z,
    induction z using tensor_product.induction_on with z c z c ihz ihc,
    { simp only [map_zero], },
    {
      simp only [comp_apply, linear_map.to_add_monoid_hom_coe, tensor_monoidal_category_tensor_hom,
        tensor_product.map_tmul, to_int_linear_map_apply, id_apply,
        tensor_monoidal_category.associator'_hom_apply],
      induction z using tensor_product.induction_on with z b z b ihz ihb,
      { simp only [map_zero, tensor_product.zero_tmul], },
      { simp only [linear_map.coe_mk, tensor_monoidal_category.tensor_hom'_apply,
          tensor_product.map_tmul, to_int_linear_map_apply, linear_map.to_add_monoid_hom_coe,
          tensor_product.lift.tmul, id_apply, tensor_monoidal_category_associator,
          tensor_monoidal_category.associator'_hom_apply, tensor_product.assoc_tmul],
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
      { simp only [Ring_to_Mon_.obj_mul, ring_hom.to_add_monoid_hom_eq_coe, comp_apply,  map_mul,
          linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul, linear_map.coe_mk,
          ring_hom.coe_add_monoid_hom, tensor_monoidal_category_tensor_hom, to_int_linear_map_apply,
          tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul], },
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
        comp_apply, tensor_monoidal_category.tensor_hom', linear_map.to_add_monoid_hom_coe,
        tensor_product.map_tmul, to_int_linear_map_apply, to_int_linear_map_apply,
        add_monoid_hom.id_apply, add_monoid_hom.id_apply],
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
        tensor_monoidal_category.tensor_hom', linear_map.to_add_monoid_hom_coe,
        tensor_product.map_tmul, to_int_linear_map_apply, to_int_linear_map_apply,
        add_monoid_hom.id_apply, add_monoid_hom.id_apply],
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

section Mod

variables (R : Mon_ AddCommGroup.{u}) (M : Mod R)

local attribute [instance] Mon_is_ring

instance has_smul_Mon_Mod : has_smul R.X M.X :=
{ smul := λ r x, M.act (r ⊗ₜ x) }

instance mul_action_Mon_Mod : mul_action R.X M.X :=
{ one_smul := λ x,
  begin
    convert fun_like.congr_fun M.one_act ((ulift.up 1 : ulift ℤ) ⊗ₜ x),
    simp only [tensor_monoidal_category_left_unitor, linear_map.coe_mk, one_zsmul,
      tensor_monoidal_category.left_unitor'_hom_apply, tensor_product.lift.tmul],
  end,
  mul_smul := λ x y b, fun_like.congr_fun M.assoc ((x ⊗ₜ y) ⊗ₜ b),
  ..AddCommGroup.monoidal.has_smul_Mon_Mod R M }

instance distrib_mul_action_Mon_Mod : distrib_mul_action R.X M.X :=
{ smul_zero := λ r, show (M.act) (r ⊗ₜ 0) = 0, by rw [tensor_product.tmul_zero, map_zero],
  smul_add := λ r x y, show M.act _ = M.act _ + M.act _, by rw [tensor_product.tmul_add, map_add],
  ..AddCommGroup.monoidal.mul_action_Mon_Mod R M }

instance module_Mon_Mod : module R.X M.X :=
{ add_smul := λ r x y, show M.act _ = M.act _ + M.act _, by rw [tensor_product.add_tmul, map_add],
  zero_smul := λ x, show M.act _ = _, by rw [tensor_product.zero_tmul, map_zero],
  ..AddCommGroup.monoidal.distrib_mul_action_Mon_Mod R M }

namespace Mod_equiv_Module

def Module_from_Mod_obj (M : Mod R) : Module R.X :=
Module.of R.X M.X

lemma Module_from_Mod_obj_smul (r : R.X) (M : Mod R) (m : Module_from_Mod_obj R M) :
  @has_smul.smul R.X (Module_from_Mod_obj R M) _ r m = M.act (r ⊗ₜ m) := rfl

@[simps] def Module_from_Mod_map {M M' : Mod R} (f : M ⟶ M') :
  Module_from_Mod_obj _ M ⟶ Module_from_Mod_obj _ M' :=
{ to_fun := λ x, f.hom x,
  map_add' := f.hom.map_add,
  map_smul' := λ r x, fun_like.congr_fun f.act_hom (r ⊗ₜ x) }

@[simps] def Module_from_Mod : Mod R ⥤ Module.{u} R.X :=
{ obj := Module_from_Mod_obj _,
  map := λ _ _, Module_from_Mod_map _,
  map_id' := λ M,
  begin
    ext,
    simp only [Module_from_Mod_map_apply, Mod.id_hom', id_apply],
  end,
  map_comp' := λ M M' M'' f g,
  begin
    ext,
    simp only [Module_from_Mod_map_apply, Mod.comp_hom', comp_apply],
  end }

@[simps] def Mod_from_Module_obj_act (M : Module R.X) :
  R.X ⊗ of M ⟶ of M :=
(tensor_product.lift $ @to_int_linear_map₂ R.X (of M) (of M)
{ to_fun := λ r,
  { to_fun := λ m, @has_smul.smul R.X M _ r m,
    map_zero' := smul_zero _,
    map_add' := λ x y, by rw smul_add },
  map_zero' :=
  begin
    ext,
    simp only [zero_smul, add_monoid_hom.coe_mk, ihom_obj'_str_zero_apply],
  end,
  map_add' := λ x y,
  begin
    ext z,
    simp only [add_monoid_hom.coe_mk, ihom_obj'_str_add_apply],
    rw add_smul,
  end }).to_add_monoid_hom

lemma Mon_one_ulift_smul_eq_zsmul (a : ℤ) (M : Module R.X) {b : M} :
  (R.one) (ulift.up a) • b = a • b :=
begin
  induction a using int.induction_on with n hn n hn,
  { erw [R.one.map_zero, zero_smul, zero_zsmul], },
  { erw [R.one.map_add ⟨n⟩ ⟨1⟩, add_smul, add_zsmul, hn, one_zsmul],
    congr,
    convert one_smul _ _, },
  { erw [sub_zsmul, one_zsmul, R.one.map_sub ⟨-n⟩ ⟨1⟩, sub_smul, sub_eq_add_neg, hn],
    congr,
    convert one_smul _ _, },
end

lemma Mod_from_Module_obj_one_act (M : Module R.X) (x : (of (ulift ℤ) ⊗ of M)) :
  ((R.one ⊗ 𝟙 (of M)) ≫ Mod_from_Module_obj_act R M) x =
  ((λ_ (of M)).hom) x :=
begin
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero] },
  { simp only [tensor_monoidal_category_tensor_hom, comp_apply,
      tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
      to_int_linear_map_apply, id_apply, Mod_from_Module_obj_act_apply, tensor_product.lift.tmul,
      to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk, tensor_monoidal_category_left_unitor,
      tensor_monoidal_category.left_unitor'_hom_apply, linear_map.coe_mk],
    cases a,
    apply Mon_one_ulift_smul_eq_zsmul R, },
  { rw [map_add, map_add, ha, hb] },
end

lemma Mod_from_Module_obj_assoc (M : Module R.X) (x : ((R.X ⊗ R.X) ⊗ of M)) :
  ((R.mul ⊗ 𝟙 (of ↥M)) ≫ Mod_from_Module_obj_act R M) x =
  ((α_ R.X R.X (of ↥M)).hom ≫ (𝟙 R.X ⊗ Mod_from_Module_obj_act R M) ≫
    Mod_from_Module_obj_act R M) x :=
begin
  induction x using tensor_product.induction_on with x c x c hx hc,
  { simp only [map_zero] },
  { induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [tensor_product.zero_tmul, map_zero], },
    { simp only [tensor_monoidal_category_tensor_hom, comp_apply,
        tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
        to_int_linear_map_apply, id_apply, Mod_from_Module_obj_act_apply, tensor_product.lift.tmul,
        to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk, tensor_monoidal_category_associator,
        tensor_monoidal_category.associator'_hom_apply, tensor_product.assoc_tmul],
      rw [←mul_smul],
      refl, },
    { rw [tensor_product.add_tmul, map_add, ha, hb, map_add], }, },
  { rw [map_add, hx, hc, map_add], },
end


@[simps] def Mod_from_Module_obj (M : Module R.X) : Mod R :=
{ X := of M,
  act := Mod_from_Module_obj_act R M,
  one_act' := by { ext, apply Mod_from_Module_obj_one_act },
  assoc' := by { ext x, apply Mod_from_Module_obj_assoc, } }

@[simps] def Mod_from_Module_map {M M' : Module R.X} (f : M ⟶ M') :
  Mod_from_Module_obj R M ⟶ Mod_from_Module_obj R M' :=
{ hom := f.to_add_monoid_hom,
  act_hom' :=
  begin
    ext x,
    induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero] },
    { simp only [Mod_from_Module_obj_act_2, comp_apply, Mod_from_Module_obj_act_apply,
        tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk,
        linear_map.to_add_monoid_hom_coe, linear_map.map_smulₛₗ, ring_hom.id_apply,
        tensor_monoidal_category_tensor_hom, tensor_monoidal_category.tensor_hom'_apply,
        tensor_product.map_tmul, to_int_linear_map_apply, id_apply], },
    { rw [map_add, ha, hb, map_add] },
  end }

@[simps] def Mod_from_Module : Module R.X ⥤ Mod R :=
{ obj := Mod_from_Module_obj R,
  map := λ _ _, Mod_from_Module_map R,
  map_id' := λ M,
  begin
    ext,
    simp only [Mod_from_Module_map_hom, linear_map.to_add_monoid_hom_coe, Mod.id_hom', id_apply],
  end,
  map_comp' := λ _ _ _ f g,
  begin
    ext,
    simp only [Mod_from_Module_map_hom, linear_map.to_add_monoid_hom_coe, Mod.comp_hom',
      comp_apply],
  end }

@[simps] def unit_iso :
  𝟭 (Mod R) ≅ Module_from_Mod R ⋙ Mod_from_Module R :=
nat_iso.of_components (λ M,
{ hom :=
  { hom := add_monoid_hom.id _,
    act_hom' :=
    begin
      ext x,
      induction x using tensor_product.induction_on with a b a b ha hb,
      { simp only [map_zero] },
      { dsimp,
        simpa only [comp_apply, add_monoid_hom.id_apply, tensor_monoidal_category.tensor_hom'_apply,
          tensor_product.map_tmul, to_int_linear_map_apply, id_apply, Mod_from_Module_obj_act_apply,
          tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk] },
      { rw [map_add, ha, hb, map_add], },
    end },
  inv :=
  { hom := add_monoid_hom.id _,
    act_hom' :=
    begin
      ext x,
      induction x using tensor_product.induction_on with a b a b ha hb,
      { simp only [map_zero] },
      { dsimp,
        simpa only [comp_apply, add_monoid_hom.id_apply, tensor_monoidal_category.tensor_hom'_apply,
          tensor_product.map_tmul, to_int_linear_map_apply, id_apply, Mod_from_Module_obj_act_apply,
          tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk] },
      { rw [map_add, ha, hb, map_add], },
    end },
  hom_inv_id' :=
  begin
    ext (x : M.X),
    simp only [comp_apply, add_monoid_hom.id_apply, id_apply, Mod.comp_hom', Mod.id_hom'],
  end,
  inv_hom_id' :=
  begin
    ext (x : M.X),
    simp only [comp_apply, add_monoid_hom.id_apply, id_apply, Mod.comp_hom', Mod.id_hom'],
  end }) $ λ M M' f,
begin
  ext (x : M.X),
  simp only [comp_apply, add_monoid_hom.id_apply, Mod.comp_hom', functor.id_map, functor.comp_map,
    Module_from_Mod_map_2, Mod_from_Module_map_2, Mod_from_Module_map_hom,
    linear_map.to_add_monoid_hom_coe, Module_from_Mod_map_apply],
end

@[simps] def counit_iso :
  Mod_from_Module R ⋙ Module_from_Mod R ≅ 𝟭 (Module.{u} R.X) :=
nat_iso.of_components (λ M, linear_equiv.to_Module_iso'
  { to_fun := λ x, x,
    map_add' := λ x y, rfl,
    map_smul' := λ r x,
    begin
      dsimp at *,
      rw Module_from_Mod_obj_smul,
      change Mod_from_Module_obj_act _ _ _ = _,
      simp only [Mod_from_Module_obj_act_apply, tensor_product.lift.tmul,
        to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk],
    end,
    inv_fun := λ x, x,
    left_inv := λ x, rfl,
    right_inv := λ x, rfl }) $ λ M M' l, by { ext, refl, }

end Mod_equiv_Module

@[simps] def Mod_equiv_Module : Mod R ≌ Module.{u} R.X :=
{ functor := Mod_equiv_Module.Module_from_Mod R,
  inverse := Mod_equiv_Module.Mod_from_Module R,
  unit_iso := Mod_equiv_Module.unit_iso R,
  counit_iso := Mod_equiv_Module.counit_iso R,
  functor_unit_iso_comp' := λ M,
  begin
    ext,
    simp only [Mod_equiv_Module.Module_from_Mod_map_2, Module.coe_comp, function.comp_app,
      Mod_equiv_Module.Module_from_Mod_map_apply, Mod_equiv_Module.unit_iso_hom_app_hom_apply,
      Mod_equiv_Module.counit_iso_hom_app_apply, Module.id_apply],
  end }

namespace Mod_equiv_Module'

variable (S : Ring.{u})

instance (M : Mod (Ring_to_Mon_.obj S)) : module S M.X :=
{ smul := λ s m, M.act (s ⊗ₜ m),
  one_smul := λ m,
  begin
    convert fun_like.congr_fun M.one_act ((ulift.up 1 : ulift ℤ) ⊗ₜ m),
    { simp only [to_int_linear_map_apply, Ring_to_Mon_.obj_one_apply, eq_int_cast,
        algebra_map.coe_one] },
    { simp only [tensor_monoidal_category_left_unitor, one_zsmul,
        tensor_monoidal_category.left_unitor'_hom_apply, tensor_product.lift.tmul,
        linear_map.coe_mk], }
  end,
  mul_smul := λ x y z,
  begin
    convert fun_like.congr_fun M.assoc ((x ⊗ₜ y) ⊗ₜ z),
    simp only [Ring_to_Mon_.obj_mul, to_int_linear_map_apply, linear_map.to_add_monoid_hom_coe,
      tensor_product.lift.tmul, linear_map.coe_mk],
  end,
  smul_zero := λ s, show M.act (s ⊗ₜ 0) = 0, by rw [tensor_product.tmul_zero, map_zero],
  smul_add := λ s x y, show M.act _ = M.act _ + M.act _, by rw [tensor_product.tmul_add, map_add],
  add_smul := λ s t x, show M.act _ = M.act _ + M.act _, by rw [tensor_product.add_tmul, map_add],
  zero_smul := λ x, show M.act _ = 0, by rw [tensor_product.zero_tmul, map_zero] }

lemma Mod_to_Module_smul_def (M : Mod (Ring_to_Mon_.obj S)) (s : S) (m : M.X) :
  s • m = M.act (s ⊗ₜ m) := rfl

@[simps] def Mod_to_Module : Mod (Ring_to_Mon_.obj S) ⥤ Module S :=
{ obj := λ M, Module.of S M.X,
  map := λ M M' l,
  { to_fun := l.hom,
    map_add' := l.hom.map_add,
    map_smul' := λ s x, fun_like.congr_fun l.act_hom (s ⊗ₜ x), },
  map_id' := λ M,
  begin
    ext m,
    simp only [Mod.id_hom', linear_map.coe_mk, id_apply],
  end,
  map_comp' := λ _ _ _ f g,
  begin
    ext m,
    simp only [Mod.comp_hom', linear_map.coe_mk, comp_apply],
  end }

@[simps] def Module_to_Mod_obj_act (M : Module S) : (Ring_to_Mon_.obj S).X ⊗ of M ⟶ of M :=
(tensor_product.lift $ @to_int_linear_map₂ (of S) (of M) (of M)
{ to_fun    := λ s,
  { to_fun    := λ m, (s • m : M),
    map_zero' := smul_zero _,
    map_add'  := λ x y, by rw smul_add },
  map_zero' := by { ext, simp only [zero_smul, add_monoid_hom.coe_mk, ihom_obj'_str_zero_apply], },
  map_add'  := λ s t, by { ext, simp only [add_monoid_hom.coe_mk, ihom_obj'_str_add_apply],
    convert add_smul _ _ _ } }).to_add_monoid_hom

lemma Module_to_Mod_obj_one_act (M : Module S) :
  ((Ring_to_Mon_.obj S).one ⊗ 𝟙 (of M)) ≫ Module_to_Mod_obj_act S M = (λ_ (of ↥M)).hom :=
begin
  ext x,
  induction x using tensor_product.induction_on with a b a b ha hb,
  { simp only [map_zero], },
  { cases a,
    simp only [tensor_monoidal_category_tensor_hom, comp_apply,
      tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul, to_int_linear_map_apply,
      Ring_to_Mon_.obj_one_apply, eq_int_cast, id_apply, Module_to_Mod_obj_act_apply,
      tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk,
      tensor_monoidal_category_left_unitor, tensor_monoidal_category.left_unitor'_hom_apply,
      linear_map.coe_mk],
    change (algebra_map ℤ S a) • _ = _,
    induction a using int.induction_on with n hn n hn,
    { rw [map_zero, zero_smul, zero_zsmul] },
    { rw [map_add, add_smul, map_one, one_smul, hn, add_smul, one_zsmul] },
    { rw [map_sub, sub_smul, map_one, one_smul, hn, sub_smul, one_zsmul] }, },
  { rw [map_add, ha, hb, map_add], },
end

lemma Module_to_Mod_obj_assoc (M : Module S) :
  ((Ring_to_Mon_.obj S).mul ⊗ 𝟙 (of M)) ≫ Module_to_Mod_obj_act S M =
  (α_ (Ring_to_Mon_.obj S).X (Ring_to_Mon_.obj S).X (of M)).hom ≫
    (𝟙 (Ring_to_Mon_.obj S).X ⊗ Module_to_Mod_obj_act S M) ≫ Module_to_Mod_obj_act S M :=
begin
  ext x,
  induction x using tensor_product.induction_on with x c x c hx hc,
  { simp only [map_zero] },
  { induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero, tensor_product.zero_tmul] },
    { simp only [Ring_to_Mon_.obj_mul, tensor_monoidal_category_tensor_hom, comp_apply,
        tensor_monoidal_category.tensor_hom'_apply, tensor_product.map_tmul,
        to_int_linear_map_apply, linear_map.to_add_monoid_hom_coe, tensor_product.lift.tmul,
        linear_map.coe_mk, id_apply, Module_to_Mod_obj_act_apply, to_int_linear_map₂_apply_apply,
        add_monoid_hom.coe_mk, tensor_monoidal_category_associator,
        tensor_monoidal_category.associator'_hom_apply, tensor_product.assoc_tmul],
      convert mul_smul _ _ _, },
    { rw [tensor_product.add_tmul, map_add, ha, hb, map_add] } },
  { rw [map_add, hx, hc, map_add] }
end

@[simps] def Module_to_Mod_obj (M : Module S) : Mod (Ring_to_Mon_.obj S) :=
{ X := of M,
  act := Module_to_Mod_obj_act S M,
  one_act' := Module_to_Mod_obj_one_act S M,
  assoc' := Module_to_Mod_obj_assoc S M }

@[simps] def Module_to_Mod_map (M M' : Module S) (l : M ⟶ M') :
  Module_to_Mod_obj S M ⟶ Module_to_Mod_obj S M' :=
{ hom := l.to_add_monoid_hom,
  act_hom' :=
  begin
    ext x,
    induction x using tensor_product.induction_on with a b a b ha hb,
    { simp only [map_zero] },
    { simp only [Module_to_Mod_obj_act_2, comp_apply, Module_to_Mod_obj_act_apply,
        tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk,
        linear_map.to_add_monoid_hom_coe, linear_map.map_smulₛₗ, ring_hom.id_apply,
        tensor_monoidal_category_tensor_hom, tensor_monoidal_category.tensor_hom'_apply,
      tensor_product.map_tmul, to_int_linear_map_apply, id_apply]},
    { rw [map_add, ha, hb, map_add] }
  end }

@[simps] def Module_to_Mod : Module S ⥤ Mod (Ring_to_Mon_.obj S) :=
{ obj := Module_to_Mod_obj S,
  map := Module_to_Mod_map S,
  map_id' := λ M,
  begin
    ext,
    simp only [Module_to_Mod_map_hom, linear_map.to_add_monoid_hom_coe, Mod.id_hom', id_apply],
  end,
  map_comp' := λ _ _ _ f g,
  begin
    ext,
    simp only [Module_to_Mod_map_hom, linear_map.to_add_monoid_hom_coe, Mod.comp_hom', comp_apply],
  end }

@[simps] def unit_iso :
  𝟭 (Mod (Ring_to_Mon_.obj S)) ≅ Mod_to_Module S ⋙ Module_to_Mod S :=
nat_iso.of_components (λ M,
{ hom :=
  { hom := add_monoid_hom.id _,
    act_hom' :=
    begin
      ext x,
      induction x using tensor_product.induction_on with a b a b ha hb,
      { simp only [map_zero] },
      { dsimp,
        simpa only [comp_apply, add_monoid_hom.id_apply, tensor_monoidal_category.tensor_hom'_apply,
          tensor_product.map_tmul, to_int_linear_map_apply, id_apply, Module_to_Mod_obj_act_apply,
          tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk] },
      { rw [map_add, ha, hb, map_add] }
    end },
  inv :=
  { hom := add_monoid_hom.id _,
    act_hom' :=
    begin
      ext x,
      induction x using tensor_product.induction_on with a b a b ha hb,
      { simp only [map_zero] },
      { dsimp,
        simpa only [comp_apply, add_monoid_hom.id_apply, tensor_monoidal_category.tensor_hom'_apply,
          tensor_product.map_tmul, to_int_linear_map_apply, id_apply, Module_to_Mod_obj_act_apply,
          tensor_product.lift.tmul, to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk] },
      { rw [map_add, ha, hb, map_add] }
    end },
  hom_inv_id' :=
  begin
    ext,
    simp only [comp_apply, add_monoid_hom.id_apply, id_apply, Mod.comp_hom', Mod.id_hom'],
  end,
  inv_hom_id' :=
  begin
    ext,
    simp only [comp_apply, add_monoid_hom.id_apply, id_apply, Mod.comp_hom', Mod.id_hom'],
  end }) $ λ M M' l,
begin
  ext,
  simp only [comp_apply, add_monoid_hom.id_apply, Mod.comp_hom', functor.id_map, functor.comp_map,
    Module_to_Mod_map_2, Module_to_Mod_map_hom, linear_map.to_add_monoid_hom_coe,
    Mod_to_Module_map_apply],
end

@[simps] def counit_iso : Module_to_Mod S ⋙ Mod_to_Module S ≅ 𝟭 (Module.{u} S) :=
nat_iso.of_components (λ M,
{ hom :=
  { to_fun := λ m, m,
    map_add' := λ _ _, rfl,
    map_smul' := λ r x,
    begin
      dsimp at *,
      erw Mod_to_Module_smul_def,
      simp only [Module_to_Mod_obj_act_2, Module_to_Mod_obj_act_apply, tensor_product.lift.tmul,
        to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk],
    end },
  inv :=
  { to_fun := λ m, m,
    map_add' := λ _ _, rfl,
    map_smul' := λ r x,
    begin
      dsimp at *,
      erw Mod_to_Module_smul_def,
      simp only [Module_to_Mod_obj_act_2, Module_to_Mod_obj_act_apply, tensor_product.lift.tmul,
        to_int_linear_map₂_apply_apply, add_monoid_hom.coe_mk],
    end },
  hom_inv_id' :=
  begin
    ext,
    simp only [Module.coe_comp, linear_map.coe_mk, Module.id_apply],
  end,
  inv_hom_id' :=
  begin
    ext,
    simp only [Module.coe_comp, linear_map.coe_mk, Module.id_apply],
  end }) $ λ M M' l,
begin
  ext,
  simp only [Module.coe_comp, linear_map.coe_mk, functor.comp_map, Module_to_Mod_map_2,
    function.comp_app, Mod_to_Module_map_apply, Module_to_Mod_map_hom,
    linear_map.to_add_monoid_hom_coe, functor.id_map],
end

end Mod_equiv_Module'

@[simps] def Mod_equiv_Module' (S : Ring.{u}) :  Mod (Ring_to_Mon_.obj S) ≌ Module.{u} S :=
{ functor := Mod_equiv_Module'.Mod_to_Module S,
  inverse := Mod_equiv_Module'.Module_to_Mod S,
  unit_iso := Mod_equiv_Module'.unit_iso S,
  counit_iso := Mod_equiv_Module'.counit_iso S,
  functor_unit_iso_comp' := λ M, rfl }

end Mod

end monoidal

end AddCommGroup
