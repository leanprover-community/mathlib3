import category_theory.monoidal.of_has_finite_products
import category_theory.monoidal.Mon_
import algebra.category.Group.limits
import algebra.category.Group.biproducts
import algebra.category.Group.abelian
import category_theory.elementwise

noncomputable theory

universes u

open category_theory category_theory.monoidal_category category_theory.limits
open_locale zero_object

namespace AddCommGroup

namespace Mon_

instance : category_theory.monoidal_category AddCommGroup.{u} :=
{ tensor_obj := λ X Y, of (X × Y),
  tensor_hom := λ _ _ _ _ f g,
  { to_fun := λ p, (f p.1, g p.2),
    map_zero' :=
    begin
      erw [map_zero, map_zero],
      refl,
    end,
    map_add' := λ ⟨a, b⟩ ⟨c, d⟩,
    begin
      erw [map_add, map_add],
      refl,
    end },
  tensor_id' := λ X Y, add_monoid_hom.ext $ λ ⟨a, b⟩,
  begin
    simp_rw [id_apply],
    refl,
  end,
  tensor_comp' := λ _ _ _ _ _ _ f₁ f₂ g₁ g₂, add_monoid_hom.ext $ λ ⟨a, b⟩,
  begin
    simp_rw [comp_apply],
    refl,
  end,
  tensor_unit := of punit,
  associator := λ X Y Z,
  { hom :=
    { to_fun := λ p, (p.1.1, p.1.2, p.2),
      map_zero' := rfl,
      map_add' := λ _ _, rfl },
    inv :=
    { to_fun := λ p, ((p.1, p.2.1), p.2.2),
      map_zero' := rfl,
      map_add' := λ _ _, rfl },
    hom_inv_id' := add_monoid_hom.ext $ λ ⟨⟨a, b⟩, c⟩,
    begin
      rw [comp_apply, id_apply],
      refl,
    end,
    inv_hom_id' := add_monoid_hom.ext $ λ ⟨a, b, c⟩,
    begin
      rw [comp_apply, id_apply],
      refl,
    end },
  associator_naturality' := λ _ _ _ _ _ _ f₁ f₂ f₃, add_monoid_hom.ext $ λ _, rfl,
  left_unitor := λ X,
  { hom :=
    { to_fun := λ p, p.2,
      map_zero' := rfl,
      map_add' := λ _ _, rfl },
    inv :=
    { to_fun := λ p, (0, p),
      map_zero' := rfl,
      map_add' := λ _ _, prod.ext (zero_add _).symm rfl },
    hom_inv_id' := add_monoid_hom.ext $ λ x,
    begin
      rw [comp_apply, id_apply, add_monoid_hom.coe_mk, add_monoid_hom.coe_mk],
      ext,
      refl,
    end,
    inv_hom_id' := add_monoid_hom.ext $ λ x, by rw [comp_apply, id_apply, add_monoid_hom.coe_mk,
      add_monoid_hom.coe_mk] },
  left_unitor_naturality' := λ _ _ f, add_monoid_hom.ext $ λ ⟨a, b⟩, by rw [comp_apply,
    add_monoid_hom.coe_mk, add_monoid_hom.coe_mk, id_apply, comp_apply, add_monoid_hom.coe_mk],
  right_unitor := λ X,
  { hom :=
    { to_fun := λ p, p.1,
      map_zero' := rfl,
      map_add' := λ _ _, rfl },
    inv :=
    { to_fun := λ p, (p, 0),
      map_zero' := rfl,
      map_add' := λ _ _, prod.ext rfl (add_zero _).symm },
    hom_inv_id' := add_monoid_hom.ext $ λ x,
    begin
      rw [comp_apply, id_apply, add_monoid_hom.coe_mk, add_monoid_hom.coe_mk],
      ext,
      refl,
    end,
    inv_hom_id' := add_monoid_hom.ext $ λ x, by rw [comp_apply, id_apply, add_monoid_hom.coe_mk,
      add_monoid_hom.coe_mk] },
  right_unitor_naturality' := λ _ _ f, add_monoid_hom.ext $ λ ⟨a, b⟩, by rw [comp_apply,
    add_monoid_hom.coe_mk, add_monoid_hom.coe_mk, id_apply, comp_apply, add_monoid_hom.coe_mk],
  pentagon' := λ _ _ _ _, add_monoid_hom.ext $ λ ⟨⟨⟨a, b⟩, c⟩, d⟩, by simp only [comp_apply,
    add_monoid_hom.coe_mk, id_apply],
  triangle' := λ _ _, add_monoid_hom.ext $ λ ⟨⟨a, ⟨⟩⟩, b⟩, by simp only [comp_apply,
    add_monoid_hom.coe_mk, id_apply] }

instance (R : Mon_ AddCommGroup.{u}) : has_one R.X :=
⟨R.one 0⟩

lemma one_def {R : Mon_ AddCommGroup.{u}} : 1 = R.one 0 := rfl

instance (R : Mon_ AddCommGroup.{u}) : has_mul R.X :=
⟨λ x y, R.mul (x, y)⟩

lemma mul_def {R : Mon_ AddCommGroup.{u}} (x y : R.X) : x * y = R.mul (x, y) := rfl

lemma one_mul {R : Mon_ AddCommGroup.{u}} (x : R.X) : (1 : R.X) * x = x :=
add_monoid_hom.congr_fun R.one_mul (0, x)

lemma mul_one {R : Mon_ AddCommGroup.{u}} (x : R.X) : x * (1 : R.X)= x :=
add_monoid_hom.congr_fun R.mul_one (x, 0)

lemma mul_assoc {R : Mon_ AddCommGroup.{u}} (x y z : R.X) :
  x * y * z = x * (y * z) :=
add_monoid_hom.congr_fun R.mul_assoc ((x, y), z)

instance (R : Mon_ AddCommGroup.{u}) : ring R.X :=
{ one := 1,
  mul := (*),
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  left_distrib := λ x y z, begin
    rw [mul_def, mul_def, mul_def],
    sorry
  end,
  right_distrib := sorry,
  ..(infer_instance : add_comm_group R.X) }

end Mon_

end AddCommGroup
