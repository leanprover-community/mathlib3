/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oleksandr Manzyuk
-/
import category_theory.bicategory.basic
import category_theory.monoidal.Mon_
import category_theory.limits.preserves.shapes.equalizers

/-!
# The category of bimodule objects over a pair of monoid objects.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]

section

open category_theory.limits

variables [has_coequalizers C]

section

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]

lemma id_tensor_π_preserves_coequalizer_inv_desc
  {W X Y Z : C} (f g : X ⟶ Y)
  (h : Z ⊗ Y ⟶ W) (wh : (𝟙 Z ⊗ f) ≫ h = (𝟙 Z ⊗ g) ≫ h) :
  (𝟙 Z ⊗ coequalizer.π f g) ≫ (preserves_coequalizer.iso (tensor_left Z) f g).inv ≫
    coequalizer.desc h wh = h :=
map_π_preserves_coequalizer_inv_desc (tensor_left Z) f g h wh

lemma id_tensor_π_preserves_coequalizer_inv_colim_map_desc
  {X Y Z X' Y' Z' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : Z ⊗ X ⟶ X') (q : Z ⊗ Y ⟶ Y')
  (wf : (𝟙 Z ⊗ f) ≫ q = p ≫ f') (wg : (𝟙 Z ⊗ g) ≫ q = p ≫ g')
  (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
  (𝟙 Z ⊗ coequalizer.π f g) ≫ (preserves_coequalizer.iso (tensor_left Z) f g).inv ≫
  colim_map (parallel_pair_hom (𝟙 Z ⊗ f) (𝟙 Z ⊗ g) f' g' p q wf wg) ≫
  coequalizer.desc h wh =
  q ≫ h :=
map_π_preserves_coequalizer_inv_colim_map_desc (tensor_left Z) f g f' g' p q wf wg h wh

end

section

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

lemma π_tensor_id_preserves_coequalizer_inv_desc
  {W X Y Z : C} (f g : X ⟶ Y)
  (h : Y ⊗ Z ⟶ W) (wh : (f ⊗ 𝟙 Z) ≫ h = (g ⊗ 𝟙 Z) ≫ h) :
  (coequalizer.π f g ⊗ 𝟙 Z) ≫ (preserves_coequalizer.iso (tensor_right Z) f g).inv ≫
    coequalizer.desc h wh = h :=
map_π_preserves_coequalizer_inv_desc (tensor_right Z) f g h wh

lemma π_tensor_id_preserves_coequalizer_inv_colim_map_desc
  {X Y Z X' Y' Z' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⊗ Z ⟶ X') (q : Y ⊗ Z ⟶ Y')
  (wf : (f ⊗ 𝟙 Z) ≫ q = p ≫ f') (wg : (g ⊗ 𝟙 Z) ≫ q = p ≫ g')
  (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
  (coequalizer.π f g ⊗ 𝟙 Z) ≫ (preserves_coequalizer.iso (tensor_right Z) f g).inv ≫
  colim_map (parallel_pair_hom (f ⊗ 𝟙 Z) (g ⊗ 𝟙 Z) f' g' p q wf wg) ≫
  coequalizer.desc h wh =
  q ≫ h :=
map_π_preserves_coequalizer_inv_colim_map_desc (tensor_right Z) f g f' g' p q wf wg h wh

end

end

/-- A bimodule object for a pair of monoid objects, all internal to some monoidal category. -/
structure Bimod (A B : Mon_ C) :=
(X : C)
(act_left : A.X ⊗ X ⟶ X)
(one_act_left' : (A.one ⊗ 𝟙 X) ≫ act_left = (λ_ X).hom . obviously)
(left_assoc' :
  (A.mul ⊗ 𝟙 X) ≫ act_left = (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ act_left) ≫ act_left . obviously)
(act_right : X ⊗ B.X ⟶ X)
(act_right_one' : (𝟙 X ⊗ B.one) ≫ act_right = (ρ_ X).hom . obviously)
(right_assoc' :
  (𝟙 X ⊗ B.mul) ≫ act_right = (α_ X B.X B.X).inv ≫ (act_right ⊗ 𝟙 B.X) ≫ act_right . obviously)
(middle_assoc' :
  (act_left ⊗ 𝟙 B.X) ≫ act_right = (α_ A.X X B.X).hom ≫ (𝟙 A.X ⊗ act_right) ≫ act_left . obviously)

restate_axiom Bimod.one_act_left'
restate_axiom Bimod.act_right_one'
restate_axiom Bimod.left_assoc'
restate_axiom Bimod.right_assoc'
restate_axiom Bimod.middle_assoc'
attribute [simp, reassoc]
Bimod.one_act_left Bimod.act_right_one Bimod.left_assoc Bimod.right_assoc Bimod.middle_assoc

namespace Bimod

variables {A B : Mon_ C} (M : Bimod A B)

/-- A morphism of bimodule objects. -/
@[ext]
structure hom (M N : Bimod A B) :=
(hom : M.X ⟶ N.X)
(left_act_hom' : M.act_left ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act_left . obviously)
(right_act_hom' : M.act_right ≫ hom = (hom ⊗ 𝟙 B.X) ≫ N.act_right . obviously)

restate_axiom hom.left_act_hom'
restate_axiom hom.right_act_hom'
attribute [simp, reassoc] hom.left_act_hom hom.right_act_hom

/-- The identity morphism on a bimodule object. -/
@[simps]
def id' (M : Bimod A B) : hom M M :=
{ hom := 𝟙 M.X, }

instance hom_inhabited (M : Bimod A B) : inhabited (hom M M) := ⟨id' M⟩

/-- Composition of bimodule object morphisms. -/
@[simps]
def comp {M N O : Bimod A B} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Bimod A B) :=
{ hom := λ M N, hom M N,
  id := id',
  comp := λ M N O f g, comp f g, }

@[simp] lemma id_hom' (M : Bimod A B) : (𝟙 M : hom M M).hom = 𝟙 M.X := rfl
@[simp] lemma comp_hom' {M N K : Bimod A B} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom := rfl

/--
Construct an isomorphism of bimodules by giving an isomorphism between the underlying objects
and checking compatibility with left and right actions only in the forward direction.
-/
@[simps]
def iso_of_iso {X Y : Mon_ C} {P Q : Bimod X Y}
  (f : P.X ≅ Q.X)
  (f_left_act_hom : P.act_left ≫ f.hom = (𝟙 X.X ⊗ f.hom) ≫ Q.act_left)
  (f_right_act_hom : P.act_right ≫ f.hom = (f.hom ⊗ 𝟙 Y.X) ≫ Q.act_right) :
  P ≅ Q :=
{ hom := ⟨f.hom⟩,
  inv :=
  { hom := f.inv,
    left_act_hom' := begin
      rw [←(cancel_mono f.hom), category.assoc, category.assoc, iso.inv_hom_id, category.comp_id,
          f_left_act_hom, ←category.assoc, ←id_tensor_comp, iso.inv_hom_id,
          monoidal_category.tensor_id, category.id_comp],
    end,
    right_act_hom' := begin
      rw [←(cancel_mono f.hom), category.assoc, category.assoc, iso.inv_hom_id, category.comp_id,
          f_right_act_hom, ←category.assoc, ←comp_tensor_id, iso.inv_hom_id,
          monoidal_category.tensor_id, category.id_comp],
    end },
  hom_inv_id' := begin
    ext, dsimp, rw iso.hom_inv_id,
  end,
  inv_hom_id' := begin
    ext, dsimp, rw iso.inv_hom_id,
  end }

variables (A)

/-- A monoid object as a bimodule over itself. -/
@[simps]
def regular : Bimod A A :=
{ X := A.X,
  act_left := A.mul,
  act_right := A.mul, }

instance : inhabited (Bimod A A) := ⟨regular A⟩

/-- The forgetful functor from bimodule objects to the ambient category. -/
def forget : Bimod A B ⥤ C :=
{ obj := λ A, A.X,
  map := λ A B f, f.hom, }

open category_theory.limits

variables [has_coequalizers C]

namespace tensor_Bimod
variables {R S T : Mon_ C} (P : Bimod R S) (Q : Bimod S T)

/-- The underlying object of the tensor product of two bimodules. -/
noncomputable
def X : C := coequalizer (P.act_right ⊗ 𝟙 Q.X) ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.act_left))

section

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]

/-- Left action for the tensor product of two bimodules. -/
noncomputable
def act_left : R.X ⊗ X P Q ⟶ X P Q :=
(preserves_coequalizer.iso (tensor_left R.X) _ _).inv ≫
colim_map
  (parallel_pair_hom _ _ _ _
    ((𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 S.X ⊗ 𝟙 Q.X) ≫ (α_ _ _ _).inv)
    ((α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 Q.X))
    begin
      dsimp,
      slice_lhs 1 2 { rw associator_inv_naturality },
      slice_rhs 3 4 { rw associator_inv_naturality },
      slice_rhs 4 5 { rw [←tensor_comp, middle_assoc, tensor_comp, comp_tensor_id] },
      coherence,
    end
    begin
      dsimp,
      slice_lhs 1 1 { rw id_tensor_comp },
      slice_lhs 2 3 { rw associator_inv_naturality },
      slice_lhs 3 4 { rw [tensor_id, id_tensor_comp_tensor_id] },
      slice_rhs 4 6 { rw iso.inv_hom_id_assoc },
      slice_rhs 3 4 { rw [tensor_id, tensor_id_comp_id_tensor] },
    end)

lemma id_tensor_π_act_left :
  (𝟙 R.X ⊗ coequalizer.π _ _) ≫ act_left P Q =
  (α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 Q.X) ≫ coequalizer.π _ _ :=
begin
  erw map_π_preserves_coequalizer_inv_colim_map (tensor_left _),
  simp only [category.assoc],
end

lemma one_act_left' : (R.one ⊗ 𝟙 _) ≫ act_left P Q = (λ_ _).hom :=
begin
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  dsimp [X],
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 2 3 { rw id_tensor_π_act_left },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←comp_tensor_id, one_act_left] },
  slice_rhs 1 2 { rw left_unitor_naturality },
  coherence,
end

lemma left_assoc' :
  (R.mul ⊗ 𝟙 _) ≫ act_left P Q =
  (α_ R.X R.X _).hom ≫ (𝟙 R.X ⊗ act_left P Q) ≫ act_left P Q :=
begin
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  dsimp [X],
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 2 3 { rw id_tensor_π_act_left },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←comp_tensor_id, left_assoc, comp_tensor_id, comp_tensor_id] },
  slice_rhs 1 2 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_rhs 2 3 { rw [←id_tensor_comp, id_tensor_π_act_left, id_tensor_comp, id_tensor_comp] },
  slice_rhs 4 5 { rw id_tensor_π_act_left },
  slice_rhs 3 4 { rw associator_inv_naturality },
  coherence,
end

end

section

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

/-- Right action for the tensor product of two bimodules. -/
noncomputable
def act_right : X P Q ⊗ T.X ⟶ X P Q :=
(preserves_coequalizer.iso (tensor_right T.X) _ _).inv ≫
colim_map
  (parallel_pair_hom _ _ _ _
    ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ 𝟙 S.X ⊗ Q.act_right) ≫ (α_ _ _ _).inv)
    ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.act_right))
    begin
      dsimp,
      slice_lhs 1 2 { rw associator_naturality },
      slice_lhs 2 3 { rw [tensor_id, tensor_id_comp_id_tensor] },
      slice_rhs 3 4 { rw associator_inv_naturality },
      slice_rhs 2 4 { rw iso.hom_inv_id_assoc },
      slice_rhs 2 3 { rw [tensor_id, id_tensor_comp_tensor_id] },
    end
    begin
      dsimp,
      slice_lhs 1 1 { rw comp_tensor_id },
      slice_lhs 2 3 { rw associator_naturality },
      slice_lhs 3 4 { rw [←id_tensor_comp, middle_assoc, id_tensor_comp] },
      slice_rhs 4 6 { rw iso.inv_hom_id_assoc },
      slice_rhs 3 4 { rw ←id_tensor_comp },
      coherence,
    end)

lemma π_tensor_id_act_right :
  (coequalizer.π _ _ ⊗ 𝟙 T.X) ≫ act_right P Q =
  (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.act_right) ≫ coequalizer.π _ _ :=
begin
  erw map_π_preserves_coequalizer_inv_colim_map (tensor_right _),
  simp only [category.assoc],
end

lemma act_right_one' : (𝟙 _ ⊗ T.one) ≫ act_right P Q = (ρ_ _).hom :=
begin
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp [X],
  slice_lhs 1 2 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 2 3 { rw π_tensor_id_act_right },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_lhs 2 3 { rw [←id_tensor_comp, act_right_one] },
  slice_rhs 1 2 { rw right_unitor_naturality },
  coherence,
end

lemma right_assoc' :
  (𝟙 _ ⊗ T.mul) ≫ act_right P Q =
  (α_ _ T.X T.X).inv ≫ (act_right P Q ⊗ 𝟙 T.X) ≫ act_right P Q :=
begin
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp [X],
  slice_lhs 1 2 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 2 3 { rw π_tensor_id_act_right },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_lhs 2 3 { rw [←id_tensor_comp, right_assoc, id_tensor_comp, id_tensor_comp] },
  slice_rhs 1 2 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_rhs 2 3 { rw [←comp_tensor_id, π_tensor_id_act_right, comp_tensor_id, comp_tensor_id] },
  slice_rhs 4 5 { rw π_tensor_id_act_right },
  slice_rhs 3 4 { rw associator_naturality },
  coherence,
end

end

section

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]
variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

lemma middle_assoc' :
  (act_left P Q ⊗ 𝟙 T.X) ≫ act_right P Q =
  (α_ R.X _ T.X).hom ≫ (𝟙 R.X ⊗ act_right P Q) ≫ act_left P Q :=
begin
  refine (cancel_epi ((tensor_left _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp [X],
  slice_lhs 1 2 { rw [←comp_tensor_id, id_tensor_π_act_left, comp_tensor_id, comp_tensor_id] },
  slice_lhs 3 4 { rw π_tensor_id_act_right },
  slice_lhs 2 3 { rw associator_naturality },
  slice_lhs 3 4 { rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor] },
  slice_rhs 1 2 { rw associator_naturality },
  slice_rhs 2 3 { rw [←id_tensor_comp, π_tensor_id_act_right, id_tensor_comp, id_tensor_comp] },
  slice_rhs 4 5 { rw id_tensor_π_act_left },
  slice_rhs 3 4 { rw associator_inv_naturality },
  slice_rhs 4 5 { rw [monoidal_category.tensor_id, id_tensor_comp_tensor_id] },
  coherence,
end

end

end tensor_Bimod

section

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]
variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

/-- Tensor product of two bimodule objects as a bimodule object. -/
@[simps]
noncomputable
def tensor_Bimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) : Bimod X Z :=
{ X := tensor_Bimod.X M N,
  act_left := tensor_Bimod.act_left M N,
  act_right := tensor_Bimod.act_right M N,
  one_act_left' := tensor_Bimod.one_act_left' M N,
  act_right_one' := tensor_Bimod.act_right_one' M N,
  left_assoc' := tensor_Bimod.left_assoc' M N,
  right_assoc' := tensor_Bimod.right_assoc' M N,
  middle_assoc' := tensor_Bimod.middle_assoc' M N, }

/-- Tensor product of two morphisms of bimodule objects. -/
@[simps]
noncomputable
def tensor_hom {X Y Z : Mon_ C} {M₁ M₂ : Bimod X Y} {N₁ N₂ : Bimod Y Z}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) : M₁.tensor_Bimod N₁ ⟶ M₂.tensor_Bimod N₂ :=
{ hom :=
    colim_map
      (parallel_pair_hom _ _ _ _ ((f.hom ⊗ 𝟙 Y.X) ⊗ g.hom) (f.hom ⊗ g.hom)
        (by rw [←tensor_comp, ←tensor_comp, hom.right_act_hom, category.id_comp, category.comp_id])
        begin
          slice_lhs 2 3 { rw [←tensor_comp, hom.left_act_hom, category.id_comp] },
          slice_rhs 1 2 { rw associator_naturality },
          slice_rhs 2 3 { rw [←tensor_comp, category.comp_id] },
        end),
  left_act_hom' := begin
    refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
    dsimp,
    slice_lhs 1 2 { rw tensor_Bimod.id_tensor_π_act_left },
    slice_lhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
    slice_lhs 2 3 { rw [←tensor_comp, hom.left_act_hom, category.id_comp] },
    slice_rhs 1 2 { rw [←id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one, id_tensor_comp] },
    slice_rhs 2 3 { rw tensor_Bimod.id_tensor_π_act_left },
    slice_rhs 1 2 { rw associator_inv_naturality },
    slice_rhs 2 3 { rw [←tensor_comp, category.comp_id] },
  end,
  right_act_hom' := begin
    refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
    dsimp,
    slice_lhs 1 2 { rw tensor_Bimod.π_tensor_id_act_right },
    slice_lhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
    slice_lhs 2 3 { rw [←tensor_comp, category.id_comp, hom.right_act_hom] },
    slice_rhs 1 2 { rw [←comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one, comp_tensor_id] },
    slice_rhs 2 3 { rw tensor_Bimod.π_tensor_id_act_right },
    slice_rhs 1 2 { rw associator_naturality },
    slice_rhs 2 3 { rw [←tensor_comp, category.comp_id] },
  end }

lemma tensor_id {X Y Z : Mon_ C} {M : Bimod X Y} {N : Bimod Y Z} :
  tensor_hom (𝟙 M) (𝟙 N) = 𝟙 (M.tensor_Bimod N) :=
begin
  ext,
  simp only [id_hom', tensor_id, tensor_hom_hom, ι_colim_map, parallel_pair_hom_app_one],
  dsimp, dunfold tensor_Bimod.X,
  simp only [category.id_comp, category.comp_id],
end

lemma tensor_comp {X Y Z : Mon_ C} {M₁ M₂ M₃ : Bimod X Y} {N₁ N₂ N₃ : Bimod Y Z}
  (f₁ : M₁ ⟶ M₂) (f₂ : M₂ ⟶ M₃) (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
  tensor_hom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensor_hom f₁ g₁ ≫ tensor_hom f₂ g₂ :=
begin
  ext,
  simp only [comp_hom', tensor_comp, tensor_hom_hom, ι_colim_map, parallel_pair_hom_app_one,
    category.assoc, ι_colim_map_assoc]
end

end

namespace associator_Bimod

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]
variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

variables {R S T U : Mon_ C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U)

/-- An auxiliary morphism for the definition of the underlying morphism of the forward component of
the associator isomorphism. -/
noncomputable
def hom_aux : (P.tensor_Bimod Q).X ⊗ L.X ⟶ (P.tensor_Bimod (Q.tensor_Bimod L)).X :=
(preserves_coequalizer.iso (tensor_right L.X) _ _).inv ≫
coequalizer.desc
  ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ (coequalizer.π _ _)) ≫ (coequalizer.π _ _))
  begin
    dsimp, dsimp [tensor_Bimod.X],
    slice_lhs 1 2 { rw associator_naturality },
    slice_lhs 2 3 { rw [monoidal_category.tensor_id,
                        tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
    slice_lhs 3 4 { rw coequalizer.condition },
    slice_lhs 2 3 { rw [←monoidal_category.tensor_id, associator_naturality] },
    slice_lhs 3 4 { rw [←id_tensor_comp, tensor_Bimod.id_tensor_π_act_left, id_tensor_comp] },
    slice_rhs 1 1 { rw comp_tensor_id },
    slice_rhs 2 3 { rw associator_naturality },
    slice_rhs 3 4 { rw ←id_tensor_comp },
    coherence,
  end

/-- The underlying morphism of the forward component of the associator isomorphism. -/
noncomputable
def hom : ((P.tensor_Bimod Q).tensor_Bimod L).X ⟶ (P.tensor_Bimod (Q.tensor_Bimod L)).X :=
coequalizer.desc
  (hom_aux P Q L)
  begin
    dsimp [hom_aux],
    refine (cancel_epi ((tensor_right _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _,
    dsimp [tensor_Bimod.X],
    slice_lhs 1 2 { rw [←comp_tensor_id,
                        tensor_Bimod.π_tensor_id_act_right,
                        comp_tensor_id, comp_tensor_id] },
    slice_lhs 3 5 { rw π_tensor_id_preserves_coequalizer_inv_desc },
    slice_lhs 2 3 { rw associator_naturality },
    slice_lhs 3 4 { rw [←id_tensor_comp, coequalizer.condition, id_tensor_comp, id_tensor_comp] },
    slice_rhs 1 2 { rw associator_naturality },
    slice_rhs 2 3 { rw [monoidal_category.tensor_id,
                        tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
    slice_rhs 3 5 { rw π_tensor_id_preserves_coequalizer_inv_desc },
    slice_rhs 2 3 { rw [←monoidal_category.tensor_id, associator_naturality] },
    coherence,
  end

lemma hom_left_act_hom' :
  ((P.tensor_Bimod Q).tensor_Bimod L).act_left ≫ hom P Q L =
  (𝟙 R.X ⊗ hom P Q L) ≫ (P.tensor_Bimod (Q.tensor_Bimod L)).act_left :=
begin
  dsimp, dsimp [hom, hom_aux],
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  rw tensor_left_map,
  slice_lhs 1 2 { rw tensor_Bimod.id_tensor_π_act_left },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc, id_tensor_comp] },
  refine (cancel_epi ((tensor_right _ ⋙ tensor_left _).map (coequalizer.π _ _))).1 _,
  dsimp, dsimp [tensor_Bimod.X],
  slice_lhs 1 2 { rw associator_inv_naturality },
  slice_lhs 2 3 { rw [←comp_tensor_id,
                      tensor_Bimod.id_tensor_π_act_left,
                      comp_tensor_id, comp_tensor_id] },
  slice_lhs 4 6 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_lhs 3 4 { rw associator_naturality },
  slice_lhs 4 5 { rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor] },
  slice_rhs 1 3 { rw [←id_tensor_comp, ←id_tensor_comp,
                      π_tensor_id_preserves_coequalizer_inv_desc,
                      id_tensor_comp, id_tensor_comp] },
  slice_rhs 3 4 { erw tensor_Bimod.id_tensor_π_act_left P (Q.tensor_Bimod L) },
  slice_rhs 2 3 { erw associator_inv_naturality },
  slice_rhs 3 4 { erw [monoidal_category.tensor_id, id_tensor_comp_tensor_id] },
  coherence,
end

lemma hom_right_act_hom' :
  ((P.tensor_Bimod Q).tensor_Bimod L).act_right ≫ hom P Q L =
  (hom P Q L ⊗ 𝟙 U.X) ≫ (P.tensor_Bimod (Q.tensor_Bimod L)).act_right :=
begin
  dsimp, dsimp [hom, hom_aux],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  rw tensor_right_map,
  slice_lhs 1 2 { rw tensor_Bimod.π_tensor_id_act_right },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc, comp_tensor_id] },
  refine (cancel_epi ((tensor_right _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp, dsimp [tensor_Bimod.X],
  slice_lhs 1 2 { rw associator_naturality },
  slice_lhs 2 3 { rw [monoidal_category.tensor_id,
                      tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 3 5 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_lhs 2 3 { rw [←monoidal_category.tensor_id,
                      associator_naturality] },
  slice_rhs 1 3 { rw [←comp_tensor_id, ←comp_tensor_id,
                      π_tensor_id_preserves_coequalizer_inv_desc,
                      comp_tensor_id, comp_tensor_id] },
  slice_rhs 3 4 { erw tensor_Bimod.π_tensor_id_act_right P (Q.tensor_Bimod L) },
  slice_rhs 2 3 { erw associator_naturality },
  dsimp,
  slice_rhs 3 4 { rw [←id_tensor_comp,
                      tensor_Bimod.π_tensor_id_act_right,
                      id_tensor_comp, id_tensor_comp] },
  coherence,
end

/-- An auxiliary morphism for the definition of the underlying morphism of the inverse component of
the associator isomorphism. -/
noncomputable
def inv_aux : P.X ⊗ (Q.tensor_Bimod L).X ⟶ ((P.tensor_Bimod Q).tensor_Bimod L).X :=
(preserves_coequalizer.iso (tensor_left P.X) _ _).inv ≫
coequalizer.desc
  ((α_ _ _ _).inv ≫ ((coequalizer.π _ _) ⊗ 𝟙 L.X) ≫ (coequalizer.π _ _))
  begin
    dsimp, dsimp [tensor_Bimod.X],
    slice_lhs 1 2 { rw associator_inv_naturality },
    rw [←(iso.inv_hom_id_assoc (α_ _ _ _) (𝟙 P.X ⊗ Q.act_right)), comp_tensor_id],
    slice_lhs 3 4 { rw [←comp_tensor_id, category.assoc, ←tensor_Bimod.π_tensor_id_act_right,
                        comp_tensor_id] },
    slice_lhs 4 5 { rw coequalizer.condition },
    slice_lhs 3 4 { rw associator_naturality },
    slice_lhs 4 5 { rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor] },
    slice_rhs 1 2 { rw id_tensor_comp },
    slice_rhs 2 3 { rw associator_inv_naturality },
    slice_rhs 3 4 { rw [monoidal_category.tensor_id, id_tensor_comp_tensor_id] },
    coherence,
  end

/-- The underlying morphism of the inverse component of the associator isomorphism. -/
noncomputable
def inv : (P.tensor_Bimod (Q.tensor_Bimod L)).X ⟶ ((P.tensor_Bimod Q).tensor_Bimod L).X :=
coequalizer.desc
  (inv_aux P Q L)
  begin
    dsimp [inv_aux],
    refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
    dsimp [tensor_Bimod.X],
    slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
    slice_lhs 2 4 { rw id_tensor_π_preserves_coequalizer_inv_desc },
    slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
    slice_lhs 2 3 { rw [←comp_tensor_id, coequalizer.condition, comp_tensor_id, comp_tensor_id] },
    slice_rhs 1 2 { rw [←monoidal_category.tensor_id, associator_naturality] },
    slice_rhs 2 3 { rw [←id_tensor_comp,
                        tensor_Bimod.id_tensor_π_act_left,
                        id_tensor_comp, id_tensor_comp] },
    slice_rhs 4 6 { rw id_tensor_π_preserves_coequalizer_inv_desc },
    slice_rhs 3 4 { rw associator_inv_naturality },
    coherence,
  end

lemma hom_inv_id : hom P Q L ≫ inv P Q L = 𝟙 _ :=
begin
  dsimp [hom, hom_aux, inv, inv_aux],
  ext,
  slice_lhs 1 2 { rw coequalizer.π_desc },
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  rw tensor_right_map,
  slice_lhs 1 3 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_lhs 2 4 { rw id_tensor_π_preserves_coequalizer_inv_desc },
  slice_lhs 1 3 { rw iso.hom_inv_id_assoc },
  dunfold tensor_Bimod.X,
  slice_rhs 2 3 { rw category.comp_id },
  refl,
end

lemma inv_hom_id : inv P Q L ≫ hom P Q L = 𝟙 _ :=
begin
  dsimp [hom, hom_aux, inv, inv_aux],
  ext,
  slice_lhs 1 2 { rw coequalizer.π_desc },
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  rw tensor_left_map,
  slice_lhs 1 3 { rw id_tensor_π_preserves_coequalizer_inv_desc },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_lhs 2 4 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_lhs 1 3 { rw iso.inv_hom_id_assoc },
  dunfold tensor_Bimod.X,
  slice_rhs 2 3 { rw category.comp_id },
  refl,
end

end associator_Bimod

namespace left_unitor_Bimod
variables {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the left unitor isomorphism. -/
noncomputable
def hom : tensor_Bimod.X (regular R) P ⟶ P.X :=
coequalizer.desc P.act_left (by { dsimp, rw [category.assoc, left_assoc] })

/-- The underlying morphism of the inverse component of the left unitor isomorphism. -/
noncomputable
def inv : P.X ⟶ tensor_Bimod.X (regular R) P :=
(λ_ P.X).inv ≫ (R.one ⊗ 𝟙 _) ≫ coequalizer.π _ _

lemma hom_inv_id : hom P ≫ inv P = 𝟙 _ :=
begin
  dunfold hom inv tensor_Bimod.X,
  ext, dsimp,
  slice_lhs 1 2 { rw coequalizer.π_desc },
  slice_lhs 1 2 { rw left_unitor_inv_naturality },
  slice_lhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 3 3 { rw ←(iso.inv_hom_id_assoc (α_ R.X R.X P.X) (𝟙 R.X ⊗ P.act_left)) },
  slice_lhs 4 6 { rw [←category.assoc, ←coequalizer.condition] },
  slice_lhs 2 3 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_lhs 3 4 { rw [←comp_tensor_id, Mon_.one_mul] },
  slice_rhs 1 2 { rw category.comp_id },
  coherence,
end

lemma inv_hom_id : inv P ≫ hom P = 𝟙 _ :=
begin
  dsimp [hom, inv],
  slice_lhs 3 4 { rw coequalizer.π_desc },
  rw [one_act_left, iso.inv_hom_id],
end

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]
variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

lemma hom_left_act_hom' :
  ((regular R).tensor_Bimod P).act_left ≫ hom P = (𝟙 R.X ⊗ hom P) ≫ P.act_left :=
begin
  dsimp, dsimp [hom, tensor_Bimod.act_left, regular],
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  dsimp,
  slice_lhs 1 4 { rw id_tensor_π_preserves_coequalizer_inv_colim_map_desc },
  slice_lhs 2 3 { rw left_assoc },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc] },
  rw iso.inv_hom_id_assoc,
end

lemma hom_right_act_hom' :
  ((regular R).tensor_Bimod P).act_right ≫ hom P = (hom P ⊗ 𝟙 S.X) ≫ P.act_right :=
begin
  dsimp, dsimp [hom, tensor_Bimod.act_right, regular],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp,
  slice_lhs 1 4 { rw π_tensor_id_preserves_coequalizer_inv_colim_map_desc },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc] },
  slice_rhs 1 2 { rw middle_assoc },
  simp only [category.assoc],
end

end left_unitor_Bimod

namespace right_unitor_Bimod
variables {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the right unitor isomorphism. -/
noncomputable
def hom : tensor_Bimod.X P (regular S) ⟶ P.X :=
coequalizer.desc P.act_right
  (by { dsimp, rw [category.assoc, right_assoc, iso.hom_inv_id_assoc] })

/-- The underlying morphism of the inverse component of the right unitor isomorphism. -/
noncomputable
def inv : P.X ⟶ tensor_Bimod.X P (regular S) :=
(ρ_ P.X).inv ≫ (𝟙 _ ⊗ S.one) ≫ coequalizer.π _ _

lemma hom_inv_id : hom P ≫ inv P = 𝟙 _ :=
begin
  dunfold hom inv tensor_Bimod.X,
  ext, dsimp,
  slice_lhs 1 2 { rw coequalizer.π_desc },
  slice_lhs 1 2 { rw right_unitor_inv_naturality },
  slice_lhs 2 3 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 3 4 { rw coequalizer.condition },
  slice_lhs 2 3 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_lhs 3 4 { rw [←id_tensor_comp, Mon_.mul_one] },
  slice_rhs 1 2 { rw category.comp_id },
  coherence,
end

lemma inv_hom_id : inv P ≫ hom P = 𝟙 _ :=
begin
  dsimp [hom, inv],
  slice_lhs 3 4 { rw coequalizer.π_desc },
  rw [act_right_one, iso.inv_hom_id],
end

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]
variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

lemma hom_left_act_hom' :
  (P.tensor_Bimod (regular S)).act_left ≫ hom P = (𝟙 R.X ⊗ hom P) ≫ P.act_left :=
begin
  dsimp, dsimp [hom, tensor_Bimod.act_left, regular],
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  dsimp,
  slice_lhs 1 4 { rw id_tensor_π_preserves_coequalizer_inv_colim_map_desc },
  slice_lhs 2 3 { rw middle_assoc },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc] },
  rw iso.inv_hom_id_assoc,
end

lemma hom_right_act_hom' :
  (P.tensor_Bimod (regular S)).act_right ≫ hom P = (hom P ⊗ 𝟙 S.X) ≫ P.act_right :=
begin
  dsimp, dsimp [hom, tensor_Bimod.act_right, regular],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp,
  slice_lhs 1 4 { rw π_tensor_id_preserves_coequalizer_inv_colim_map_desc },
  slice_lhs 2 3 { rw right_assoc },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc] },
  rw iso.hom_inv_id_assoc,
end

end right_unitor_Bimod

variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_left X)]
variables [∀ X : C, preserves_colimits_of_size.{0 0} (tensor_right X)]

/-- The associator as a bimodule isomorphism. -/
noncomputable
def associator_Bimod {W X Y Z : Mon_ C} (L : Bimod W X) (M : Bimod X Y) (N : Bimod Y Z) :
   (L.tensor_Bimod M).tensor_Bimod N ≅ L.tensor_Bimod (M.tensor_Bimod N) :=
iso_of_iso
  { hom := associator_Bimod.hom L M N,
    inv := associator_Bimod.inv L M N,
    hom_inv_id' := associator_Bimod.hom_inv_id L M N,
    inv_hom_id' := associator_Bimod.inv_hom_id L M N }
  (associator_Bimod.hom_left_act_hom' L M N)
  (associator_Bimod.hom_right_act_hom' L M N)

/-- The left unitor as a bimodule isomorphism. -/
noncomputable
def left_unitor_Bimod {X Y : Mon_ C} (M : Bimod X Y) : (regular X).tensor_Bimod M ≅ M :=
iso_of_iso
  { hom := left_unitor_Bimod.hom M,
    inv := left_unitor_Bimod.inv M,
    hom_inv_id' := left_unitor_Bimod.hom_inv_id M,
    inv_hom_id' := left_unitor_Bimod.inv_hom_id M }
  (left_unitor_Bimod.hom_left_act_hom' M)
  (left_unitor_Bimod.hom_right_act_hom' M)

/-- The right unitor as a bimodule isomorphism. -/
noncomputable
def right_unitor_Bimod {X Y : Mon_ C} (M : Bimod X Y) : M.tensor_Bimod (regular Y) ≅ M :=
iso_of_iso
  { hom := right_unitor_Bimod.hom M,
    inv := right_unitor_Bimod.inv M,
    hom_inv_id' := right_unitor_Bimod.hom_inv_id M,
    inv_hom_id' := right_unitor_Bimod.inv_hom_id M }
  (right_unitor_Bimod.hom_left_act_hom' M)
  (right_unitor_Bimod.hom_right_act_hom' M)

lemma whisker_left_comp_Bimod {X Y Z : Mon_ C}
  (M : Bimod X Y) {N P Q : Bimod Y Z} (f : N ⟶ P) (g : P ⟶ Q) :
  tensor_hom (𝟙 M) (f ≫ g) = tensor_hom (𝟙 M) f ≫ tensor_hom (𝟙 M) g :=
by rw [←tensor_comp, category.comp_id]

lemma id_whisker_left_Bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
  tensor_hom (𝟙 (regular X)) f = (left_unitor_Bimod M).hom ≫ f ≫ (left_unitor_Bimod N).inv :=
begin
  dsimp [tensor_hom, regular, left_unitor_Bimod],
  ext, dsimp,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [left_unitor_Bimod.hom],
  slice_rhs 1 2 { rw coequalizer.π_desc },
  dsimp [left_unitor_Bimod.inv],
  slice_rhs 1 2 { rw hom.left_act_hom },
  slice_rhs 2 3 { rw left_unitor_inv_naturality },
  slice_rhs 3 4 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_rhs 4 4 { rw ←(iso.inv_hom_id_assoc (α_ X.X X.X N.X) (𝟙 X.X ⊗ N.act_left)) },
  slice_rhs 5 7 { rw [←category.assoc, ←coequalizer.condition] },
  slice_rhs 3 4 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_rhs 4 5 { rw [←comp_tensor_id, Mon_.one_mul] },
  have :
    (λ_ (X.X ⊗ N.X)).inv ≫ (α_ (𝟙_ C) X.X N.X).inv ≫ ((λ_ X.X).hom ⊗ 𝟙 N.X) = 𝟙 _ :=
    by pure_coherence,
  slice_rhs 2 4 { rw this },
  slice_rhs 1 2 { rw category.comp_id },
end

lemma comp_whisker_left_Bimod {W X Y Z : Mon_ C}
  (M : Bimod W X) (N : Bimod X Y) {P P' : Bimod Y Z} (f : P ⟶ P') :
  tensor_hom (𝟙 (M.tensor_Bimod N)) f =
  (associator_Bimod M N P).hom ≫ tensor_hom (𝟙 M) (tensor_hom (𝟙 N) f) ≫
    (associator_Bimod M N P').inv :=
begin
  dsimp [tensor_hom, tensor_Bimod, associator_Bimod],
  ext, dsimp,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [tensor_Bimod.X, associator_Bimod.hom],
  slice_rhs 1 2 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.hom_aux, associator_Bimod.inv],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  rw tensor_right_map,
  slice_rhs 1 3 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_rhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 2 3 { rw [←id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 3 4 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.inv_aux],
  slice_rhs 2 2 { rw id_tensor_comp },
  slice_rhs 3 5 { rw id_tensor_π_preserves_coequalizer_inv_desc },
  slice_rhs 2 3 { rw associator_inv_naturality },
  slice_rhs 1 3 { rw [iso.hom_inv_id_assoc, monoidal_category.tensor_id] },
  slice_lhs 1 2 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  dunfold tensor_Bimod.X,
  simp only [category.assoc],
end

lemma comp_whisker_right_Bimod {X Y Z : Mon_ C}
  {M N P : Bimod X Y} (f : M ⟶ N) (g : N ⟶ P) (Q : Bimod Y Z) :
  tensor_hom (f ≫ g) (𝟙 Q) = tensor_hom f (𝟙 Q) ≫ tensor_hom g (𝟙 Q) :=
by rw [←tensor_comp, category.comp_id]

lemma whisker_right_id_Bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
  tensor_hom f (𝟙 (regular Y)) = (right_unitor_Bimod M).hom ≫ f ≫ (right_unitor_Bimod N).inv :=
begin
  dsimp [tensor_hom, regular, right_unitor_Bimod],
  ext, dsimp,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [right_unitor_Bimod.hom],
  slice_rhs 1 2 { rw coequalizer.π_desc },
  dsimp [right_unitor_Bimod.inv],
  slice_rhs 1 2 { rw hom.right_act_hom },
  slice_rhs 2 3 { rw right_unitor_inv_naturality },
  slice_rhs 3 4 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_rhs 4 5 { rw coequalizer.condition },
  slice_rhs 3 4 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_rhs 4 5 { rw [←id_tensor_comp, Mon_.mul_one] },
  have :
    (ρ_ (N.X ⊗ Y.X)).inv ≫ (α_ N.X Y.X (𝟙_ C)).hom ≫ (𝟙 N.X ⊗ (ρ_ Y.X).hom) = 𝟙 _ :=
    by pure_coherence,
  slice_rhs 2 4 { rw this },
  slice_rhs 1 2 { rw category.comp_id },
end

lemma whisker_right_comp_Bimod {W X Y Z : Mon_ C}
  {M M' : Bimod W X} (f : M ⟶ M') (N : Bimod X Y) (P : Bimod Y Z) :
  tensor_hom f (𝟙 (N.tensor_Bimod P)) =
  (associator_Bimod M N P).inv ≫ tensor_hom (tensor_hom f (𝟙 N)) (𝟙 P) ≫
    (associator_Bimod M' N P).hom :=
begin
  dsimp [tensor_hom, tensor_Bimod, associator_Bimod],
  ext, dsimp,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [tensor_Bimod.X, associator_Bimod.inv],
  slice_rhs 1 2 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.inv_aux, associator_Bimod.hom],
  refine (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _,
  rw tensor_left_map,
  slice_rhs 1 3 { rw id_tensor_π_preserves_coequalizer_inv_desc },
  slice_rhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 2 3 { rw [←comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 3 4 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.hom_aux],
  slice_rhs 2 2 { rw comp_tensor_id },
  slice_rhs 3 5 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_rhs 2 3 { rw associator_naturality },
  slice_rhs 1 3 { rw [iso.inv_hom_id_assoc, monoidal_category.tensor_id] },
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  dunfold tensor_Bimod.X,
  simp only [category.assoc],
end

lemma whisker_assoc_Bimod {W X Y Z : Mon_ C}
  (M : Bimod W X) {N N' : Bimod X Y} (f : N ⟶ N') (P : Bimod Y Z) :
  tensor_hom (tensor_hom (𝟙 M) f) (𝟙 P) =
  (associator_Bimod M N P).hom ≫ tensor_hom (𝟙 M) (tensor_hom f (𝟙 P)) ≫
    (associator_Bimod M N' P).inv :=
begin
  dsimp [tensor_hom, tensor_Bimod, associator_Bimod],
  ext, dsimp,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [associator_Bimod.hom],
  slice_rhs 1 2 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.hom_aux],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  rw tensor_right_map,
  slice_lhs 1 2 { rw [←comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 1 3 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_rhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 2 3 { rw [←id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [associator_Bimod.inv],
  slice_rhs 3 4 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.inv_aux],
  slice_rhs 2 2 { rw id_tensor_comp },
  slice_rhs 3 5 { rw id_tensor_π_preserves_coequalizer_inv_desc },
  slice_rhs 2 3 { rw associator_inv_naturality },
  slice_rhs 1 3 { rw iso.hom_inv_id_assoc },
  slice_lhs 1 1 { rw comp_tensor_id },
end

lemma whisker_exchange_Bimod {X Y Z : Mon_ C}
  {M N : Bimod X Y} {P Q : Bimod Y Z} (f : M ⟶ N) (g : P ⟶ Q) :
  tensor_hom (𝟙 M) g ≫ tensor_hom f (𝟙 Q) = tensor_hom f (𝟙 P) ≫ tensor_hom (𝟙 N) g :=
begin
  dsimp [tensor_hom],
  ext, dsimp,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 2 3 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 1 2 { rw id_tensor_comp_tensor_id },
  slice_rhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 2 3 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_rhs 1 2 { rw tensor_id_comp_id_tensor },
end

lemma pentagon_Bimod {V W X Y Z : Mon_ C}
  (M : Bimod V W) (N : Bimod W X) (P : Bimod X Y) (Q : Bimod Y Z) :
  tensor_hom (associator_Bimod M N P).hom (𝟙 Q) ≫ (associator_Bimod M (N.tensor_Bimod P) Q).hom ≫
    tensor_hom (𝟙 M) (associator_Bimod N P Q).hom =
  (associator_Bimod (M.tensor_Bimod N) P Q).hom ≫ (associator_Bimod M N (P.tensor_Bimod Q)).hom :=
begin
  dsimp [tensor_hom, associator_Bimod], ext, dsimp,
  dunfold associator_Bimod.hom,
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 2 3 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.hom_aux],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp,
  slice_lhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc] },
  slice_rhs 1 3 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_rhs 3 4 { rw coequalizer.π_desc },
  refine (cancel_epi ((tensor_right _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp,
  slice_lhs 1 2 { rw [←comp_tensor_id,
                      π_tensor_id_preserves_coequalizer_inv_desc,
                      comp_tensor_id, comp_tensor_id ]},
  slice_lhs 3 5 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  dunfold tensor_Bimod.X,
  slice_lhs 2 3 { rw associator_naturality },
  slice_lhs 5 6 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 4 5 { rw [←id_tensor_comp, coequalizer.π_desc] },
  slice_lhs 3 4 { rw [←id_tensor_comp,
                      π_tensor_id_preserves_coequalizer_inv_desc,
                      id_tensor_comp, id_tensor_comp] },
  slice_rhs 1 2 { rw associator_naturality },
  slice_rhs 2 3 { rw [monoidal_category.tensor_id,
                      tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_rhs 3 5 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_rhs 2 3 { rw [←monoidal_category.tensor_id, associator_naturality] },
  coherence,
end

lemma triangle_Bimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) :
  (associator_Bimod M (regular Y) N).hom ≫ tensor_hom (𝟙 M) (left_unitor_Bimod N).hom =
  tensor_hom (right_unitor_Bimod M).hom (𝟙 N) :=
begin
  dsimp [tensor_hom, associator_Bimod, left_unitor_Bimod, right_unitor_Bimod],
  ext, dsimp,
  dsimp [associator_Bimod.hom],
  slice_lhs 1 2 { rw coequalizer.π_desc },
  dsimp [associator_Bimod.hom_aux],
  slice_rhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [right_unitor_Bimod.hom],
  refine (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _,
  dsimp [regular],
  slice_lhs 1 3 { rw π_tensor_id_preserves_coequalizer_inv_desc },
  slice_lhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  dsimp [left_unitor_Bimod.hom],
  slice_lhs 2 3 { rw [←id_tensor_comp, coequalizer.π_desc] },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc] },
  slice_rhs 1 2 { rw coequalizer.condition },
  simp only [category.assoc],
end

/-- The bicategory of algebras (monoids) and bimodules, all internal to some monoidal category. -/
noncomputable
def Mon_bicategory : bicategory (Mon_ C) :=
{ hom := λ X Y, Bimod X Y,
  id := λ X, regular X,
  comp := λ _ _ _ M N, tensor_Bimod M N,
  whisker_left := λ _ _ _ L _ _ f, tensor_hom (𝟙 L) f,
  whisker_right := λ _ _ _ _ _ f N, tensor_hom f (𝟙 N),
  associator := λ _ _ _ _ L M N, associator_Bimod L M N,
  left_unitor := λ _ _ M, left_unitor_Bimod M,
  right_unitor := λ _ _ M, right_unitor_Bimod M,
  whisker_left_id' := λ _ _ _ _ _, tensor_id,
  whisker_left_comp' := λ _ _ _ M _ _ _ f g, whisker_left_comp_Bimod M f g,
  id_whisker_left' := λ _ _ _ _ f, id_whisker_left_Bimod f,
  comp_whisker_left' := λ _ _ _ _ M N _ _ f, comp_whisker_left_Bimod M N f,
  id_whisker_right' := λ _ _ _ _ _, tensor_id,
  comp_whisker_right' := λ _ _ _ _ _ _ f g Q, comp_whisker_right_Bimod f g Q,
  whisker_right_id' := λ _ _ _ _ f, whisker_right_id_Bimod f,
  whisker_right_comp' := λ _ _ _ _ _ _ f N P, whisker_right_comp_Bimod f N P,
  whisker_assoc' := λ _ _ _ _ M _ _ f P, whisker_assoc_Bimod M f P,
  whisker_exchange' := λ _ _ _ _ _ _ _ f g, whisker_exchange_Bimod f g,
  pentagon' := λ _ _ _ _ _ M N P Q, pentagon_Bimod M N P Q,
  triangle' := λ _ _ _ M N, triangle_Bimod M N }

end Bimod
