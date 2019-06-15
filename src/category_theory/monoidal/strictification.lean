import category_theory.monoidal.functor
import category_theory.full_subcategory
import category_theory.eq_to_hom
import category_theory.equivalence
import category_theory.monoidal.unitors

universes v₁ u₁

open category_theory
open category_theory.monoidal_category

namespace category_theory

namespace monoidal_strictification

variables {C : Type u₁} [𝒞 : monoidal_category.{v₁} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

def tensor : list C → C
| [] := 𝟙_ C
| (X :: w) := X ⊗ (tensor w)

@[simp] lemma tensor_nil : tensor [] = 𝟙_ C := rfl
@[simp] lemma tensor_cons {X : C} {w : list C} : tensor (X :: w) = X ⊗ tensor w := rfl

def tensorator : Π (w z : list C), (tensor w) ⊗ (tensor z) ≅ tensor (w ++ z)
| [] z := (λ_ _)
| (X :: w) z := (α_ _ _ _) ≪≫ (tensor_iso (iso.refl _) (tensorator w z))

@[simp] lemma tensorator_nil_left {z : list C} : tensorator [] z = (λ_ _) := rfl
@[simp] lemma tensorator_cons {X} {w z : list C} : tensorator (X :: w) z = (α_ _ _ _) ≪≫ (tensor_iso (iso.refl _) (tensorator w z)) := rfl

def tensorator_congr_left {w w' : list C} (h : w = w') (z : list C) :
  tensorator w z =
    (tensor_iso (eq_to_iso (by { cases h, refl })) (iso.refl _)) ≪≫
    tensorator w' z ≪≫ eq_to_iso (by { cases h, refl }) :=
by { cases h, simp }
def tensorator_congr_right (w : list C) {z z' : list C} (h : z = z') :
  tensorator w z =
    (tensor_iso (iso.refl _) (eq_to_iso (by { cases h, refl }))) ≪≫
    tensorator w z' ≪≫ eq_to_iso (by { cases h, refl }) :=
by { cases h, simp }

lemma id_tensor_eq_to_hom (X : C) {Y Z : C} (h : Y = Z) : 𝟙 X ⊗ eq_to_hom h = eq_to_hom (by { congr, exact h }) :=
by { cases h, simp, }
lemma eq_to_hom_tensor_id {X Y : C} (h : X = Y) (Z : C) : eq_to_hom h ⊗ 𝟙 Z = eq_to_hom (by { congr, exact h }) :=
by { cases h, simp, }

lemma tensorator_assoc (u v w : list C) :
  ((tensorator u v).hom ⊗ 𝟙 _) ≫ (tensorator (u ++ v) w).hom =
  (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (tensorator v w).hom) ≫ (tensorator u (v ++ w)).hom ≫ eq_to_hom (by rw list.append_assoc) :=
begin
  intros,
  induction u,
  { dsimp,
    simp,
    rw left_unitor_naturality,
    slice_rhs 1 2 { simp, }, },
  { dsimp,
    simp only [list.append, list.append_assoc, category.assoc],
    rw ←comp_tensor_id,
    slice_lhs 2 3 { erw associator_naturality, },
    slice_lhs 3 4 { rw id_tensor_comp, },
    rw u_ih,
    slice_rhs 2 3 { rw ←tensor_id, rw associator_naturality, },
    rw ←id_tensor_comp,
    slice_lhs 1 4 { rw pentagon, }, -- FIXME slice is getting the indexing wrong.
    simp only [list.append, list.append_assoc, cancel_epi, id_tensor_comp, category.assoc],
    conv { to_lhs, rw ←id_tensor_comp, rw ←id_tensor_comp, },
    conv { to_rhs, rw ←id_tensor_comp, rw category.assoc, },
    congr,
    apply id_tensor_eq_to_hom }
end

lemma tensorator_assoc' (u v w : list C) :
  (𝟙 _ ⊗ (tensorator v w).hom) ≫ (tensorator u (v ++ w)).hom =
  (α_ _ _ _).inv ≫ ((tensorator u v).hom ⊗ 𝟙 _) ≫ (tensorator (u ++ v) w).hom ≫ eq_to_hom (by rw list.append_assoc) :=
begin
  symmetry,
  apply is_iso.cancel_left_lhs,
  rw ←category.assoc,
  apply is_iso.cancel_right_lhs,
  rw tensorator_assoc,
  dsimp,
  simp only [list.append_assoc, category.assoc],
end

lemma tensorator_inv_assoc (u v w : list C) :
  (tensorator (u ++ v) w).inv ≫ ((tensorator u v).inv ⊗ 𝟙 _) =
  eq_to_hom (by rw list.append_assoc) ≫ (tensorator u (v ++ w)).inv ≫ (𝟙 _ ⊗ (tensorator v w).inv) ≫ (α_ _ _ _).inv :=
begin
  apply eq_of_inv_eq_inv,
  simp,
  apply tensorator_assoc,
end

lemma tensorator_inv_assoc' (u v w : list C) :
  (tensorator u (v ++ w)).inv ≫ (𝟙 _ ⊗ (tensorator v w).inv) =
  eq_to_hom (by rw list.append_assoc) ≫ (tensorator (u ++ v) w).inv ≫ ((tensorator u v).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom :=
begin
  apply eq_of_inv_eq_inv,
  simp,
  apply tensorator_assoc',
end

@[simp] lemma tensorator_nil_right (u : list C) : tensorator u [] = ρ_ (tensor u) ≪≫ eq_to_iso (by simp) :=
begin
  ext1,
  induction u,
  { simp only [iso.trans_refl, list.append_nil, tensorator_nil_left, eq_to_iso_refl],
    erw unitors_equal, refl, },
  { dsimp,
    rw u_ih,
    dsimp,
    rw [←id_tensor_comp, ←category.assoc],
    simp only [list.append, list.append_nil, cancel_epi, right_unitor_tensor],
    rw id_tensor_eq_to_hom,
    refl }
end

variables (C)

instance list_category : category.{v₁} (list C) :=
{ hom := λ X Y, (tensor X) ⟶ (tensor Y),
  id := λ X, 𝟙 (tensor X),
  comp := λ X Y Z f g, f ≫ g, }

open category monoidal_category

instance list_monoidal_category : monoidal_category.{v₁} (list C) :=
{ tensor_obj := λ X Y, X ++ Y,
  tensor_unit := [],
  tensor_hom := λ (W X Y Z) (f : tensor W ⟶ tensor X) (g : tensor Y ⟶ tensor Z),
  ((tensorator W Y).inv ≫ (f ⊗ g) ≫ (tensorator X Z).hom : tensor (W ++ Y) ⟶ tensor (X ++ Z)),
  associator   := λ X Y Z, eq_to_iso (list.append_assoc _ _ _),
  left_unitor  := λ X, iso.refl _,
  right_unitor := λ X, eq_to_iso (list.append_nil _),
  tensor_id' := λ X Y, by { erw [tensor_id, id_comp, iso.inv_hom_id], refl },
  tensor_comp' := λ U V W X Y Z f g h k,
  begin
    dsimp,
    erw [assoc, assoc],
    simp only [iso.hom_inv_id_assoc, cancel_epi],
    erw [tensor_comp, assoc],
  end,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃,
  begin
    dsimp,
    -- pull everything apart to get f₁ ⊗ f₂ ⊗ f₃ in the middle on both sides, then use tensorator_assoc above
    -- tidying up the left hand side:
    apply is_iso.cancel_right_lhs,
    erw inv_eq_to_hom,
    conv { to_lhs, rw [←tensor_id_comp_id_tensor, ←comp_tensor_id, ←comp_tensor_id], },
    slice_lhs 4 5 { rw tensor_id_comp_id_tensor },
    slice_lhs 4 4 { rw ←id_tensor_comp_tensor_id },
    slice_lhs 3 4 { rw tensor_id_comp_id_tensor, },
    -- tidying up the right hand side:
    symmetry,
    apply is_iso.cancel_right_lhs,
    apply is_iso.cancel_left_lhs,
    erw inv_eq_to_hom,
    erw inv_eq_to_hom,
    symmetry,
    conv { to_rhs, rw [←tensor_id_comp_id_tensor, ←id_tensor_comp, ←id_tensor_comp], },
    slice_rhs 2 3 { rw tensor_id_comp_id_tensor },
    slice_rhs 2 2 { rw ←id_tensor_comp_tensor_id },
    slice_rhs 3 4 { rw tensor_id_comp_id_tensor, },
    -- use tensorator[_inv]_assoc
    simp only [list.append_assoc, assoc, id_comp, comp_id],
    rw tensorator_assoc',
    conv { to_rhs, rw ←assoc, rw tensorator_inv_assoc' },
    -- now clean everything up
    simp only [list.append_assoc, assoc, id_comp, comp_id],
    apply is_iso.cancel_left_lhs,
    erw eq_to_hom_trans_assoc,
    simp only [list.append_assoc, assoc, id_comp, eq_to_hom_refl, comp_id],
    slice_rhs 3 5 { rw associator_conjugation', },
    simp only [list.append_assoc, assoc],
    apply is_iso.cancel_right_lhs,
    erw [inv_eq_to_hom, category.assoc, category.assoc, category.assoc, category.assoc, category.assoc, eq_to_hom_trans],
    simp only [list.append_assoc, cancel_epi, cancel_mono, eq_to_hom_refl, comp_id],
    -- and some final equalities:
    erw list.append_assoc,
    erw list.append_assoc,
  end,
  left_unitor_naturality' := λ X Y f,
  begin
    dsimp [tensorator],
    simp only [id_comp, comp_id],
    erw [left_unitor_naturality],
    simp,
  end,
  right_unitor_naturality' := λ X Y f,
  begin
    dsimp [tensorator],
    simp only [iso.trans_inv, eq_to_iso.inv, list.append_nil, tensorator_nil_right, assoc,
               id_comp, eq_to_iso.hom, comp_id, iso.trans_hom],
    erw [category.assoc, category.assoc, category.assoc, category.assoc, eq_to_hom_trans],
    simp only [list.append_nil, assoc, id_comp, eq_to_hom_refl, comp_id],
    erw right_unitor_conjugation,
    refl,
    { rw list.append_nil },
  end,
  pentagon' := λ W X Y Z,
  begin
    dsimp,
    rw tensorator_congr_left (list.append_assoc _ _ _) _,
    rw tensorator_congr_right _ (list.append_assoc _ _ _),
    dsimp,
    simp only [eq_to_hom_trans, list.append_assoc, assoc, id_comp, comp_id],
    slice_lhs 5 6 { erw id_tensor_comp },
    erw eq_to_hom_trans_assoc,
    erw eq_to_hom_trans,
    erw comp_tensor_id_assoc,
    erw eq_to_hom_trans,
    simp only [tensor_id, list.append_assoc, assoc, id_comp, eq_to_hom_refl, comp_id, iso.inv_hom_id],
    erw eq_to_hom_trans_assoc,
    simp only [list.append_assoc, assoc, id_comp, comp_id],
    erw comp_id,
    rw list.append_assoc W X Y,
    rw list.append_assoc W X Y,
    rw list.append_assoc X Y Z,
    rw list.append_assoc X Y Z,
  end,
  triangle' := λ X Y,
  begin
    dsimp,
    rw tensorator_congr_left (list.append_nil X),
    simp only [iso.trans_inv, tensor_iso_inv, eq_to_iso.inv, list.append_nil, iso.refl_inv,
               tensor_id, comp_tensor_id_assoc, list.append_assoc, assoc, id_comp, comp_id, iso.inv_hom_id],
    slice_rhs 3 4 { erw comp_tensor_id },
    erw eq_to_hom_trans,
    dsimp,
    simp only [tensor_id, list.append_nil, list.append_assoc, assoc, id_comp, comp_id, iso.inv_hom_id],
    erw tensor_id,
    simp only [list.append_nil, list.append_assoc, assoc, id_comp, comp_id, iso.inv_hom_id],
    erw comp_id,
    refl,
    rw list.append_nil,
  end
}.

@[simp] lemma tensor_unit : tensor (𝟙_ (list C)) = 𝟙_ C := rfl
@[simp] lemma left_unitor_singleton (X : C) : (λ_ [X]).hom = 𝟙 _ := rfl

section
omit 𝒞

class strictly_monoidal extends monoidal_category.{v₁} C :=
(left_unitor_trivial  : ∀ (X : C), { h : 𝟙_ C ⊗ X = X // λ_ X = eq_to_iso h })
(right_unitor_trivial : ∀ (X : C), { h : X ⊗ 𝟙_ C = X // ρ_ X = eq_to_iso h })
(associator_trivial   : ∀ (X Y Z : C), { h : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) // α_ X Y Z == eq_to_iso h })

include 𝒞

@[simp] lemma eq_to_iso_heq_refl (X Y : C) (h : Y = X) : eq_to_iso h == iso.refl X :=
begin
  induction h,
  simp,
end
@[simp] lemma eq_to_iso_heq_refl' (X Y : C) (h : X = Y) : eq_to_iso h == iso.refl X :=
begin
  induction h,
  simp,
end

instance : strictly_monoidal.{v₁} (list C) :=
{ left_unitor_trivial := λ X, begin fsplit, refl, refl end,
  right_unitor_trivial := λ X, begin dsimp [monoidal_strictification.list_monoidal_category], fsplit, simp, end,
  associator_trivial := λ X Y Z, begin dsimp [monoidal_strictification.list_monoidal_category], fsplit, simp, end,
  ..(monoidal_strictification.list_monoidal_category C) }
end

def inv_strictification : (list C) ⥤ C :=
{ obj := λ X, tensor X,
  map := λ X Y f, f }

namespace inv_strictification
instance : ess_surj (inv_strictification C) :=
{ obj_preimage := λ X, [X],
  iso' := λ X, ρ_ X }

instance : full (inv_strictification C) :=
{ preimage := λ X Y f, f }

instance : faithful (inv_strictification C) :=
{}

instance : is_equivalence (inv_strictification C) := equivalence.equivalence_of_fully_faithfully_ess_surj _
end inv_strictification

def strictification' : C ⥤ (list C) :=
{ obj := λ X, [X],
  map := λ X Y f, begin dsimp [monoidal_strictification.list_category], exact (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv end,
  map_comp' := λ X Y Z f g, begin dsimp, repeat { erw category.assoc }, rw iso.inv_hom_id_assoc, end }

namespace strictification'
instance : ess_surj (strictification' C) :=
{ obj_preimage := λ X, tensor X,
  iso' := λ X, { ..((ρ_ (tensor X))) } }

instance : full (strictification' C) :=
{ preimage := λ X Y f, sorry,
  witness' := sorry }

instance : faithful (strictification' C) :=
{ injectivity' := sorry, }

instance : is_equivalence (strictification' C) := equivalence.equivalence_of_fully_faithfully_ess_surj _
end strictification'


def strictification : C ⥤ (list C) := (inv_strictification C).inv

def monoidal_strictification : monoidal_functor.{v₁ v₁} C (list C) :=
{ ε := (λ_ _).inv,
  ε_is_iso := { .. (λ_ _).symm },
  μ := λ X Y, (α_ X Y (𝟙_ C)).inv,
  μ_is_iso := λ X Y, { .. (α_ X Y (𝟙_ C)).symm },
  μ_natural' := λ X Y X' Y' f g,
  by { dsimp [tensor_hom, strictification'], simp, sorry, },
  associativity' := λ X Y Z,
  begin
    dsimp [strictification'],
    sorry
  end,
  left_unitality' := λ X,
  begin
    dsimp [strictification'],
    slice_rhs 3 4 { rw ←right_unitor_naturality },
    simp,
    rw ← left_unitor_tensor,
    erw iso.inv_hom_id_assoc,
    simp,
    sorry
  end,
  right_unitality' := λ X,
  begin
    dsimp [strictification'],
    sorry
  end,
  ..(strictification' C) }

instance : faithful (monoidal_strictification C).to_functor := sorry

def monoidal_inv_strictification : monoidal_functor.{v₁ v₁} (list C) C :=
{ ε := 𝟙 _,
  μ := λ X Y, (tensorator X Y).hom,
  μ_is_iso := λ X Y, is_iso.of_iso _,
  μ_natural' := λ X Y X' Y' f g,
  by { dsimp [tensor_hom, inv_strictification], simp, },
  associativity' := λ X Y Z,
  begin
    dsimp [inv_strictification],
    erw [←category.assoc, tensorator_assoc],
    simp only [list.append_assoc, assoc, cancel_epi],
    dsimp [tensor_obj],
    erw eq_to_hom_trans,
    { simp only [list.append_assoc, eq_to_hom_refl, comp_id] },
    { rw list.append_assoc },
  end,
  left_unitality' := λ X,
  begin
    dsimp [inv_strictification],
    erw tensorator_nil_left,
    simp only [tensor_id, id_comp],
    erw comp_id,
  end,
  right_unitality' := λ X,
  begin
    dsimp [inv_strictification],
    rw [tensor_id, id_comp],
    erw tensorator_nil_right,
    dsimp,
    simp only [list.append_nil, assoc],
    erw eq_to_hom_trans,
    { simp, },
    { congr, exact list.append_nil X, },
  end,
  ..(inv_strictification C) }

-- Finally, we need to prove that a monoidal functor which is part of an equivalence is part of a monoidal equivalence.
-- err... and think about whether that's really the condition we want (3-categories, etc.)

end monoidal_strictification

end category_theory
