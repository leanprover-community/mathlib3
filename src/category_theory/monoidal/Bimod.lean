/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.Mon_
import category_theory.limits.preserves.shapes.equalizers

/-!
# The category of bimodule objects over a pair of monoid objects.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

variables {C}

/-- A bimodule object for a pair of monoid objects, all internal to some monoidal category. -/
structure Bimod (A B : Mon_ C) :=
(X : C)
(act_left : A.X ⊗ X ⟶ X)
(one_act_left' : (A.one ⊗ 𝟙 X) ≫ act_left = (λ_ X).hom . obviously)
(left_assoc' : (A.mul ⊗ 𝟙 X) ≫ act_left = (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ act_left) ≫ act_left . obviously)
(act_right : X ⊗ B.X ⟶ X)
(act_right_one' : (𝟙 X ⊗ B.one) ≫ act_right = (ρ_ X).hom . obviously)
(right_assoc' : (𝟙 X ⊗ B.mul) ≫ act_right = (α_ X B.X B.X).inv ≫ (act_right ⊗ 𝟙 B.X) ≫ act_right . obviously)
(middle_assoc' : (act_left ⊗ 𝟙 B.X) ≫ act_right = (α_ A.X X B.X).hom ≫ (𝟙 A.X ⊗ act_right) ≫ act_left . obviously)

restate_axiom Bimod.one_act_left'
restate_axiom Bimod.act_right_one'
restate_axiom Bimod.left_assoc'
restate_axiom Bimod.right_assoc'
restate_axiom Bimod.middle_assoc'
attribute [simp, reassoc] Bimod.one_act_left Bimod.act_right_one Bimod.left_assoc Bimod.right_assoc Bimod.middle_assoc

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
variables [∀ X : C, preserves_colimits (tensor_left X)]
variables [∀ X : C, preserves_colimits (tensor_right X)]

lemma id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map
  (X Y Z Y' Z' : C) (f g : Y ⟶ Z) (f' g' : Y' ⟶ Z') (p : X ⊗ Y ⟶ Y') (q : X ⊗ Z ⟶ Z')
  (wf : (𝟙 X ⊗ f) ≫ q = p ≫ f') (wg : (𝟙 X ⊗ g) ≫ q = p ≫ g') :
  (𝟙 X ⊗ coequalizer.π f g) ≫ (preserves_coequalizer.iso (tensor_left X) f g).inv ≫
  colim_map (parallel_pair_hom (𝟙 X ⊗ f) (𝟙 X ⊗ g) f' g' p q wf wg) =
  q ≫ coequalizer.π f' g' :=
begin
  rw [←tensor_left_map, ←ι_comp_coequalizer_comparison, ←preserves_coequalizer.iso_hom,
    category.assoc, iso.hom_inv_id_assoc, ι_colim_map, parallel_pair_hom_app_one],
end

lemma π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map
  (X Y Z Y' Z' : C) (f g : Y ⟶ Z) (f' g' : Y' ⟶ Z') (p : Y ⊗ X ⟶ Y') (q : Z ⊗ X ⟶ Z')
  (wf : (f ⊗ 𝟙 X) ≫ q = p ≫ f') (wg : (g ⊗ 𝟙 X) ≫ q = p ≫ g') :
  (coequalizer.π f g ⊗ 𝟙 X) ≫ (preserves_coequalizer.iso (tensor_right X) f g).inv ≫
  colim_map (parallel_pair_hom (f ⊗ 𝟙 X) (g ⊗ 𝟙 X) f' g' p q wf wg) =
  q ≫ coequalizer.π f' g' :=
begin
  rw [←tensor_right_map, ←ι_comp_coequalizer_comparison, ←preserves_coequalizer.iso_hom,
    category.assoc, iso.hom_inv_id_assoc, ι_colim_map, parallel_pair_hom_app_one],
end

namespace tensor_Bimod
variables {R S T : Mon_ C} (P : Bimod R S) (Q : Bimod S T)

noncomputable
def X : C := coequalizer (P.act_right ⊗ 𝟙 Q.X) ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.act_left))

noncomputable
def act_left : R.X ⊗ X P Q ⟶ X P Q :=
begin
  refine (preserves_coequalizer.iso (tensor_left R.X) _ _).inv ≫ _,
  apply colim_map,
  fapply parallel_pair_hom,
  dsimp,
  refine (𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 S.X ⊗ 𝟙 Q.X) ≫ (α_ _ _ _).inv,
  refine (α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 Q.X),
  { dsimp,
    slice_lhs 1 2 { rw associator_inv_naturality },
    slice_rhs 3 4 { rw associator_inv_naturality },
    slice_rhs 4 5 { rw [←tensor_comp, middle_assoc, tensor_comp, comp_tensor_id] },
    coherence, },
  { dsimp,
    slice_lhs 1 1 { rw id_tensor_comp },
    slice_lhs 2 3 { rw associator_inv_naturality },
    slice_lhs 3 4 { rw [tensor_id, id_tensor_comp_tensor_id] },
    slice_rhs 4 6 { rw iso.inv_hom_id_assoc },
    slice_rhs 3 4 { rw [tensor_id, tensor_id_comp_id_tensor] }, }
end

noncomputable
def act_right : X P Q ⊗ T.X ⟶ X P Q :=
begin
  refine (preserves_coequalizer.iso (tensor_right T.X) _ _).inv ≫ _,
  apply colim_map,
  fapply parallel_pair_hom,
  dsimp,
  refine (α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ 𝟙 S.X ⊗ Q.act_right) ≫ (α_ _ _ _).inv,
  refine (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.act_right),
  { dsimp,
    slice_lhs 1 2 { rw associator_naturality },
    slice_lhs 2 3 { rw [tensor_id, tensor_id_comp_id_tensor] },
    slice_rhs 3 4 { rw associator_inv_naturality },
    slice_rhs 2 4 { rw iso.hom_inv_id_assoc },
    slice_rhs 2 3 { rw [tensor_id, id_tensor_comp_tensor_id] }, },
  { dsimp,
    slice_lhs 1 1 { rw comp_tensor_id },
    slice_lhs 2 3 { rw associator_naturality },
    slice_lhs 3 4 { rw [←id_tensor_comp, middle_assoc, id_tensor_comp] },
    slice_rhs 4 6 { rw iso.inv_hom_id_assoc },
    slice_rhs 3 4 { rw ←id_tensor_comp },
    coherence, },
end

def one_act_left' : (R.one ⊗ 𝟙 _) ≫ act_left P Q = (λ_ _).hom :=
begin
  dunfold X act_left,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_left (𝟙_ C)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp,
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 2 4 { rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_lhs 1 2 { rw [←tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp, one_act_left, category.id_comp], },
  slice_rhs 1 2 { rw left_unitor_naturality },
  coherence,
end

def act_right_one' : (𝟙 _ ⊗ T.one) ≫ act_right P Q = (ρ_ _).hom :=
begin
  dunfold X act_right,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_right (𝟙_ C)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp,
  slice_lhs 1 2 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 2 4 { rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_lhs 1 2 { rw [←tensor_id, associator_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp, act_right_one, category.id_comp] },
  slice_rhs 1 2 { rw right_unitor_naturality },
  coherence,
end

def left_assoc' :
  (R.mul ⊗ 𝟙 _) ≫ act_left P Q =
  (α_ R.X R.X _).hom ≫ (𝟙 R.X ⊗ act_left P Q) ≫ act_left P Q :=
begin
  dunfold X act_left,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_left (R.X ⊗ R.X)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp,
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 2 4 { rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_rhs 1 2 { rw [←tensor_id, associator_naturality] },
  slice_rhs 2 3 { rw [←id_tensor_comp,
                      id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map,
                      id_tensor_comp] },
  slice_rhs 3 5 { rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_lhs 1 2 { rw [←tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←comp_tensor_id, left_assoc, comp_tensor_id, comp_tensor_id] },
  slice_rhs 2 2 { rw id_tensor_comp },
  slice_rhs 3 4 { rw associator_inv_naturality },
  coherence,
end

def right_assoc' :
  (𝟙 _ ⊗ T.mul) ≫ act_right P Q =
  (α_ _ T.X T.X).inv ≫ (act_right P Q ⊗ 𝟙 T.X) ≫ act_right P Q :=
begin
  dunfold X act_right,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_right (T.X ⊗ T.X)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp,
  slice_lhs 1 2 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 2 4 { rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_rhs 3 3 { rw comp_tensor_id },
  slice_rhs 1 2 { rw [←tensor_id, associator_inv_naturality] },
  slice_rhs 2 4 { rw [←comp_tensor_id, ←comp_tensor_id,
                      π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map,
                      comp_tensor_id] },
  slice_rhs 3 5 { rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_lhs 1 2 { rw [←tensor_id, associator_naturality] },
  slice_rhs 2 2 { rw comp_tensor_id },
  slice_rhs 3 4 { rw associator_naturality },
  slice_lhs 2 3 { rw [←id_tensor_comp, right_assoc, id_tensor_comp, id_tensor_comp] },
  coherence,
end

def middle_assoc' :
  (act_left P Q ⊗ 𝟙 T.X) ≫ act_right P Q =
  (α_ R.X _ T.X).hom ≫ (𝟙 R.X ⊗ act_right P Q) ≫ act_left P Q :=
begin
  dunfold X act_left act_right,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_left R.X ⋙ tensor_right T.X) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp,
  slice_lhs 1 2 { rw [←comp_tensor_id,
                      id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map,
                      comp_tensor_id, comp_tensor_id] },
  slice_lhs 3 5 { rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_rhs 1 2 { rw associator_naturality },
  slice_rhs 2 3 { rw [←id_tensor_comp,
                      π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map,
                      id_tensor_comp, id_tensor_comp] },
  slice_rhs 4 6 { rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map },
  slice_lhs 2 3 { rw associator_naturality },
  slice_lhs 3 4 { rw [tensor_id, tensor_id_comp_id_tensor] },
  slice_rhs 3 4 { rw associator_inv_naturality },
  slice_rhs 4 5 { rw [tensor_id, id_tensor_comp_tensor_id] },
  coherence,
end

end tensor_Bimod

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

@[simps]
noncomputable
def tensor_hom {X Y Z : Mon_ C} {M₁ M₂ : Bimod X Y} {N₁ N₂ : Bimod Y Z}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) : tensor_Bimod M₁ N₁ ⟶ tensor_Bimod M₂ N₂ :=
{ hom := begin
    refine colim_map (parallel_pair_hom _ _ _ _ ((f.hom ⊗ 𝟙 Y.X) ⊗ g.hom) (f.hom ⊗ g.hom) _ _),
    { rw [←tensor_comp, ←tensor_comp, hom.right_act_hom, category.id_comp, category.comp_id] },
    { slice_lhs 2 3 { rw [←tensor_comp, hom.left_act_hom, category.id_comp] },
      slice_rhs 1 2 { rw associator_naturality },
      slice_rhs 2 3 { rw [←tensor_comp, category.comp_id] } }
  end,
  left_act_hom' := begin
    dsimp, dunfold tensor_Bimod.act_left,
    refine (cancel_epi (preserves_coequalizer.iso (tensor_left X.X) _ _).hom).1 _,
    slice_lhs 1 3 { rw iso.hom_inv_id_assoc },
    ext,
    slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
    slice_lhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
    slice_lhs 2 3 { rw [←tensor_comp, hom.left_act_hom, category.id_comp] },
    slice_rhs 1 2 { rw [preserves_coequalizer.iso_hom,
                        ι_comp_coequalizer_comparison,
                        tensor_left_map] },
    slice_rhs 1 2 { rw [←id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one, id_tensor_comp] },
    dsimp,
    slice_rhs 2 4 { rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map },
    slice_rhs 1 2 { rw associator_inv_naturality },
    slice_rhs 2 3 { rw [←tensor_comp, category.comp_id] },
  end,
  right_act_hom' := begin
    dsimp, dunfold tensor_Bimod.act_right,
    refine (cancel_epi (preserves_coequalizer.iso (tensor_right Z.X) _ _).hom).1 _,
    slice_lhs 1 3 { rw iso.hom_inv_id_assoc },
    ext,
    slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
    slice_lhs 3 4 { rw [ι_colim_map, parallel_pair_hom_app_one] },
    slice_lhs 2 3 { rw [←tensor_comp, hom.right_act_hom, category.id_comp] },
    slice_rhs 1 2 { rw [preserves_coequalizer.iso_hom,
                        ι_comp_coequalizer_comparison,
                        tensor_right_map] },
    slice_rhs 1 2 { rw [←comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one, comp_tensor_id] },
    dsimp,
    slice_rhs 2 4 { rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map },
    slice_rhs 1 2 { rw associator_naturality },
    slice_rhs 2 3 { rw [←tensor_comp, category.comp_id] },
  end }

lemma tensor_id {X Y Z : Mon_ C} {M : Bimod X Y} {N : Bimod Y Z} :
  tensor_hom (𝟙 M) (𝟙 N) = 𝟙 (tensor_Bimod M N) :=
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

end Bimod
