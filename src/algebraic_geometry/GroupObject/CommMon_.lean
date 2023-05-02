import category_theory.monoidal.CommMon_

universes v₁ v₂ u₁ u₂ u

open category_theory
open category_theory.monoidal_category

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C] [symmetric_category.{v₁} C]

namespace CommMon_

def iso_of_iso {M N : CommMon_ C}
  (f : M.X ≅ N.X)
  (one_f : M.one ≫ f.hom = N.one)
  (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul) :
  M ≅ N :=
{ hom := { hom := f.hom, one_hom' := one_f, mul_hom' := mul_f },
  inv :=
  { hom := f.inv,
    one_hom' := by { rw ←one_f, simp },
    mul_hom' :=
    begin
      rw ←(cancel_mono f.hom),
      slice_rhs 2 3 { rw mul_f },
      simp,
    end } }


variable {C}

-- The proofs that associators and unitors preserve monoid units don't require braiding.

lemma one_associator {M N P : CommMon_ C} :
    ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ P.one)) ≫ (α_ M.X N.X P.X).hom
  = (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ (λ_ (𝟙_ C)).inv ≫ (N.one ⊗ P.one)) :=
Mon_.one_associator

lemma one_left_unitor {M : CommMon_ C} :
  ((λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ M.one)) ≫ (λ_ M.X).hom = M.one :=
Mon_.one_left_unitor

lemma one_right_unitor {M : CommMon_ C} :
  ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ 𝟙 (𝟙_ C))) ≫ (ρ_ M.X).hom = M.one :=
Mon_.one_right_unitor

lemma CommMon_tensor_one_mul (M N : CommMon_ C) :
    ((λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) ⊗ 𝟙 (M.X ⊗ N.X)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
  = (λ_ (M.X ⊗ N.X)).hom :=
Mon_.Mon_tensor_one_mul _ _

lemma CommMon_tensor_mul_one (M N : CommMon_ C) :
    (𝟙 (M.X ⊗ N.X) ⊗ (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
  = (ρ_ (M.X ⊗ N.X)).hom :=
Mon_.Mon_tensor_mul_one _ _

lemma CommMon_tensor_mul_assoc (M N : CommMon_ C) :
    (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) ⊗ 𝟙 (M.X ⊗ N.X)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫
    (M.mul ⊗ N.mul)
  = (α_ (M.X ⊗ N.X) (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫
    (𝟙 (M.X ⊗ N.X) ⊗ tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)) ≫
    tensor_μ C (M.X, N.X) (M.X, N.X) ≫
    (M.mul ⊗ N.mul) :=
Mon_.Mon_tensor_mul_assoc _ _

lemma CommMon_tensor_mul_comm (M N : CommMon_ C) :
    (β_ (M.X ⊗ N.X) (M.X ⊗ N.X)).hom ≫ tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul)
  = tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) :=
begin
  rw [←M.mul_comm, ←N.mul_comm, tensor_comp, ←category.comp_id (β_ N.X N.X).hom,
     ←category.id_comp (β_ M.X M.X).hom, tensor_comp, ←tensor_id, tensor_μ],
  simp only [category.assoc],
  rw ←associator_inv_naturality_assoc,
  slice_lhs 3 6
  { dsimp,
    simp only [←tensor_comp],
    rw ←(iso.eq_inv_comp _).2 (braided_category.hexagon_forward _ _ _) },
  simp only [tensor_comp],
  slice_lhs 3 4
  { rw [(iso.hom_comp_eq_id (β_ (M.X ⊗ N.X) N.X)).1 (symmetric_category.symmetry _ _),
      ←iso.refl_inv, ←tensor_iso_inv] },
  slice_lhs 1 3
  { dsimp,
    rw (iso.eq_inv_comp _).2 (braided_category.hexagon_forward _ _ _) },
  slice_lhs 4 6
  { rw [←iso.refl_hom, ←tensor_iso_hom, iso.hom_inv_id] },
  slice_lhs 3 6
  { simp only [category.id_comp],
    rw (is_iso.eq_inv_comp _).2 (monoidal_category.pentagon M.X M.X N.X N.X) },
  slice_lhs 3 6
  { rw [iso.hom_inv_id, category.comp_id], },
  slice_lhs 4 5
  { rw [←tensor_id, ←associator_naturality] },
  slice_lhs 2 4
  { rw [inv_tensor, is_iso.iso.inv_hom, is_iso.inv_id],
    simp only [←tensor_comp]},
  slice_lhs 2 3
  { rw [←category.assoc, (iso.inv_comp_eq _).1 (braided_category.hexagon_reverse M.X N.X M.X)],
    simp only [category.assoc, ←tensor_comp, symmetric_category.symmetry,
      category.comp_id, tensor_id] },
  dsimp,
  sorry,
end

lemma mul_associator {M N P : CommMon_ C} :
    (tensor_μ C (M.X ⊗ N.X, P.X) (M.X ⊗ N.X, P.X) ≫
      (tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul) ⊗ P.mul)) ≫
    (α_ M.X N.X P.X).hom
  = ((α_ M.X N.X P.X).hom ⊗ (α_ M.X N.X P.X).hom) ≫
    tensor_μ C (M.X, N.X ⊗ P.X) (M.X, N.X ⊗ P.X) ≫
    (M.mul ⊗ tensor_μ C (N.X, P.X) (N.X, P.X) ≫ (N.mul ⊗ P.mul)) :=
Mon_.mul_associator

lemma mul_left_unitor {M : CommMon_ C}:
    (tensor_μ C (𝟙_ C, M.X) (𝟙_ C, M.X) ≫ ((λ_ (𝟙_ C)).hom ⊗ M.mul)) ≫ (λ_ M.X).hom
  = ((λ_ M.X).hom ⊗ (λ_ M.X).hom) ≫ M.mul :=
Mon_.mul_left_unitor

lemma mul_right_unitor {M : CommMon_ C} :
    (tensor_μ C (M.X, 𝟙_ C) (M.X, 𝟙_ C) ≫ (M.mul ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M.X).hom
  = ((ρ_ M.X).hom ⊗ (ρ_ M.X).hom) ≫ M.mul :=
Mon_.mul_right_unitor

instance CommMon_monoidal : monoidal_category (CommMon_ C) :=
{ tensor_obj := λ M N,
  { X := M.X ⊗ N.X,
    one := (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one),
    mul := tensor_μ C (M.X, N.X) (M.X, N.X) ≫ (M.mul ⊗ N.mul),
    one_mul' := CommMon_tensor_one_mul M N,
    mul_one' := CommMon_tensor_mul_one M N,
    mul_assoc' := CommMon_tensor_mul_assoc M N,
    mul_comm' := CommMon_tensor_mul_comm M N },
  tensor_hom := λ M N P Q f g,
  { hom := f.hom ⊗ g.hom,
    one_hom' :=
    begin
      dsimp,
      slice_lhs 2 3 { rw [←tensor_comp, f.one_hom, g.one_hom] },
    end,
    mul_hom' :=
    begin
      dsimp,
      slice_rhs 1 2 { rw [tensor_μ_natural] },
      slice_lhs 2 3 { rw [←tensor_comp, f.mul_hom, g.mul_hom, tensor_comp] },
      simp only [category.assoc],
    end },
  tensor_id' := by { intros, ext, apply tensor_id },
  tensor_comp' := by { intros, ext, apply tensor_comp },
  tensor_unit := trivial C,
  associator := λ M N P, iso_of_iso (α_ M.X N.X P.X) one_associator mul_associator,
  associator_naturality' := by { intros, ext, dsimp, apply associator_naturality },
  left_unitor := λ M, iso_of_iso (λ_ M.X) one_left_unitor mul_left_unitor,
  left_unitor_naturality' := by { intros, ext, dsimp, apply left_unitor_naturality },
  right_unitor := λ M, iso_of_iso (ρ_ M.X) one_right_unitor mul_right_unitor,
  right_unitor_naturality' := by { intros, ext, dsimp, apply right_unitor_naturality },
  pentagon' := by { intros, ext, dsimp, apply pentagon },
  triangle' := by { intros, ext, dsimp, apply triangle } }

lemma tensor_unit : (𝟙_ (CommMon_ C)) = CommMon_.trivial C := rfl
@[simp] lemma tensor_unit_one : (𝟙_ (CommMon_ C)).one = 𝟙 _ := rfl
@[simp] lemma tensor_unit_mul : (𝟙_ (CommMon_ C)).mul = (λ_ (𝟙_ C)).hom := rfl
@[simp] lemma tensor_one (X Y : CommMon_ C) :
  (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl
@[simp] lemma tensor_mul (X Y : CommMon_ C) :
  (X ⊗ Y).mul = tensor_μ C (X.X, Y.X) (X.X, Y.X) ≫ (X.mul ⊗ Y.mul) := rfl
lemma tensor_X (X Y : CommMon_ C) : (X ⊗ Y).X = X.X ⊗ Y.X := rfl
@[simp] lemma tensor_hom {M N P Q : CommMon_ C} (f : M ⟶ N) (g : P ⟶ Q) :
  (f ⊗ g).hom = f.hom ⊗ g.hom := rfl
@[simp] lemma associator (M N P : CommMon_ C) :
  α_ M N P = CommMon_.iso_of_iso (α_ M.X N.X P.X)
    CommMon_.one_associator CommMon_.mul_associator := rfl
@[simp] lemma left_unitor (M : CommMon_ C) :
  λ_ M = CommMon_.iso_of_iso (λ_ M.X) CommMon_.one_left_unitor CommMon_.mul_left_unitor := rfl
@[simp] lemma right_unitor (M : CommMon_ C) :
  ρ_ M = CommMon_.iso_of_iso (ρ_ M.X) CommMon_.one_right_unitor CommMon_.mul_right_unitor := rfl

end CommMon_
namespace monoidal_functor

def map_CommMon_

end monoidal_functor
