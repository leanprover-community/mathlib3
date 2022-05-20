/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.bicategory.basic
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

def map_π_epi (G : C ⥤ C) [preserves_colimits G] {X Y : C} (f g : X ⟶ Y) :
  epi (G.map (coequalizer.π f g)) :=
{ left_cancellation := begin
    intros W h k H,
    rwa [←ι_comp_coequalizer_comparison, category.assoc, category.assoc,
         cancel_epi (coequalizer.π (G.map f) (G.map g)),
         ←preserves_coequalizer.iso_hom,
         cancel_epi ((preserves_coequalizer.iso G f g).hom)] at H,
  end }

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

lemma id_tensor_π_act_left :
  (𝟙 R.X ⊗ coequalizer.π _ _) ≫ act_left P Q =
  (α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 Q.X) ≫ coequalizer.π _ _ :=
begin
  dunfold act_left, dsimp,
  rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map,
  simp only [category.assoc],
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

lemma π_tensor_id_act_right :
  (coequalizer.π _ _ ⊗ 𝟙 T.X) ≫ act_right P Q =
  (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.act_right) ≫ coequalizer.π _ _ :=
begin
  dunfold act_right, dsimp,
  rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map,
  simp only [category.assoc],
end

def one_act_left' : (R.one ⊗ 𝟙 _) ≫ act_left P Q = (λ_ _).hom :=
begin
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _) (map_π_epi (tensor_left _) _ _) _ _).1 _,
  dunfold X,
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 2 3 { rw id_tensor_π_act_left },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←comp_tensor_id, one_act_left] },
  slice_rhs 1 2 { rw left_unitor_naturality },
  coherence,
end

def act_right_one' : (𝟙 _ ⊗ T.one) ≫ act_right P Q = (ρ_ _).hom :=
begin
  refine
    (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _) (map_π_epi (tensor_right _) _ _) _ _).1 _,
  dunfold X,
  slice_lhs 1 2 { rw [tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 2 3 { rw π_tensor_id_act_right },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_lhs 2 3 { rw [←id_tensor_comp, act_right_one] },
  slice_rhs 1 2 { rw right_unitor_naturality },
  coherence,
end

def left_assoc' :
  (R.mul ⊗ 𝟙 _) ≫ act_left P Q =
  (α_ R.X R.X _).hom ≫ (𝟙 R.X ⊗ act_left P Q) ≫ act_left P Q :=
begin
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _) (map_π_epi (tensor_left _) _ _) _ _).1 _,
  dunfold X,
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

def right_assoc' :
  (𝟙 _ ⊗ T.mul) ≫ act_right P Q =
  (α_ _ T.X T.X).inv ≫ (act_right P Q ⊗ 𝟙 T.X) ≫ act_right P Q :=
begin
  refine
    (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _) (map_π_epi (tensor_right _) _ _) _ _).1 _,
  dunfold X,
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

def middle_assoc' :
  (act_left P Q ⊗ 𝟙 T.X) ≫ act_right P Q =
  (α_ R.X _ T.X).hom ≫ (𝟙 R.X ⊗ act_right P Q) ≫ act_left P Q :=
begin
  refine
    (@cancel_epi _ _ _ _ _ ((𝟙 _ ⊗ coequalizer.π _ _) ⊗ 𝟙 _)
      (map_π_epi (tensor_left _ ⋙ tensor_right _) _ _) _ _).1 _,
  dunfold X,
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
    refine
      (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _) (map_π_epi (tensor_left _) _ _) _ _).1 _,
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
    refine
      (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _) (map_π_epi (tensor_right _) _ _) _ _).1 _,
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

lemma map_π_preserves_coequalizer_inv (G : C ⥤ C) [preserves_colimits G]
  {X Y : C} (f g : X ⟶ Y) :
  G.map (coequalizer.π f g) ≫ (preserves_coequalizer.iso G f g).inv =
  coequalizer.π (G.map f) (G.map g) :=
begin
  rw [←ι_comp_coequalizer_comparison, ←preserves_coequalizer.iso_hom, category.assoc,
    iso.hom_inv_id, category.comp_id],
end

def iso_of_iso {X Y : Mon_ C} {P Q : Bimod X Y}
  (f : P.X ≅ Q.X)
  (f_left_act_hom : P.act_left ≫ f.hom = (𝟙 X.X ⊗ f.hom) ≫ Q.act_left)
  (f_right_act_hom : P.act_right ≫ f.hom = (f.hom ⊗ 𝟙 Y.X) ≫ Q.act_right) :
  P ≅ Q :=
{ hom :=
  { hom := f.hom,
    left_act_hom' := f_left_act_hom,
    right_act_hom' := f_right_act_hom },
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

namespace associator_Bimod
variables {R S T U: Mon_ C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U)

noncomputable
def hom_hom_aux : (tensor_Bimod.X P Q) ⊗ L.X ⟶ tensor_Bimod.X P (tensor_Bimod Q L) :=
begin
  refine (preserves_coequalizer.iso (tensor_right L.X) _ _).inv ≫ coequalizer.desc _ _,
  exact (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ (coequalizer.π _ _)) ≫ (coequalizer.π _ _),
  dsimp, dunfold tensor_Bimod.X, dsimp,
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

noncomputable
def hom_hom : tensor_Bimod.X (tensor_Bimod P Q) L ⟶ tensor_Bimod.X P (tensor_Bimod Q L) :=
begin
  refine coequalizer.desc (hom_hom_aux P Q L) _,
  dunfold hom_hom_aux, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ ((coequalizer.π _ _ ⊗ 𝟙 _) ⊗ 𝟙 _)
      (map_π_epi (tensor_right _ ⋙ tensor_right _) _ _) _ _).1 _,
  dunfold tensor_Bimod.X, dsimp,
  slice_lhs 1 2 { rw [←comp_tensor_id,
                      tensor_Bimod.π_tensor_id_act_right,
                      comp_tensor_id, comp_tensor_id] },
  slice_lhs 3 4 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv (tensor_right L.X)] },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_lhs 2 3 { rw associator_naturality },
  slice_lhs 3 4 { rw [←id_tensor_comp, coequalizer.condition, id_tensor_comp, id_tensor_comp] },
  slice_rhs 1 2 { rw associator_naturality },
  slice_rhs 2 3 { rw [monoidal_category.tensor_id,
                      tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_rhs 3 4 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv (tensor_right L.X)] },
  slice_rhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 2 3 { rw [←monoidal_category.tensor_id, associator_naturality] },
  coherence,
end

def hom_left_act_hom' :
  ((P.tensor_Bimod Q).tensor_Bimod L).act_left ≫ hom_hom P Q L =
  (𝟙 R.X ⊗ hom_hom P Q L) ≫ (P.tensor_Bimod (Q.tensor_Bimod L)).act_left :=
begin
  dsimp, dunfold hom_hom hom_hom_aux, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _)
      (map_π_epi (tensor_left _) _ _) _ _).1 _,
  slice_lhs 1 2 { rw tensor_Bimod.id_tensor_π_act_left },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc, id_tensor_comp] },
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ (coequalizer.π _ _ ⊗ 𝟙 _))
      (map_π_epi (tensor_right _ ⋙ tensor_left _) _ _) _ _).1 _,
  dsimp, dunfold tensor_Bimod.X, dsimp,
  slice_lhs 1 2 { rw associator_inv_naturality },
  slice_lhs 2 3 { rw [←comp_tensor_id,
                      tensor_Bimod.id_tensor_π_act_left,
                      comp_tensor_id, comp_tensor_id] },
  slice_lhs 4 5 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv (tensor_right L.X)] },
  slice_lhs 4 5 { rw coequalizer.π_desc },
  slice_lhs 3 4 { rw associator_naturality },
  slice_lhs 4 5 { rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor] },
  slice_rhs 1 2 { rw [←id_tensor_comp,
                      ←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv (tensor_right L.X)] },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc, id_tensor_comp, id_tensor_comp] },
  -- Why do I need this explicit proof instead of applying tensor_Bimod.id_tensor_π_act_left?
  have :
    (𝟙 R.X ⊗
      coequalizer.π
        (P.act_right ⊗
          𝟙 (coequalizer (Q.act_right ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ L.act_left))))
        ((α_ P.X S.X
          (coequalizer (Q.act_right ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ L.act_left)))).hom ≫
            (𝟙 P.X ⊗ tensor_Bimod.act_left Q L))) ≫
    tensor_Bimod.act_left P (Q.tensor_Bimod L) =
    (α_ _ _ _).inv ≫ (P.act_left ⊗ 𝟙 _) ≫ coequalizer.π _ _,
  { dsimp,
    dunfold tensor_Bimod.act_left, dsimp,
    dunfold tensor_Bimod.act_left, dsimp,
    dunfold tensor_Bimod.X, dsimp,
    rw id_tensor_π_comp_preserves_coequalizer_inv_comp_colim_map,
    simp only [category.assoc] },
  slice_rhs 3 4 { rw this }, clear this,
  slice_rhs 2 3 { rw associator_inv_naturality },
  slice_rhs 3 4 { rw [monoidal_category.tensor_id, id_tensor_comp_tensor_id] },
  coherence,
end

def hom_right_act_hom' :
  ((P.tensor_Bimod Q).tensor_Bimod L).act_right ≫ hom_hom P Q L =
  (hom_hom P Q L ⊗ 𝟙 U.X) ≫ (P.tensor_Bimod (Q.tensor_Bimod L)).act_right :=
begin
  dsimp, dunfold hom_hom hom_hom_aux, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _)
      (map_π_epi (tensor_right _) _ _) _ _).1 _,
  slice_lhs 1 2 { rw tensor_Bimod.π_tensor_id_act_right },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc, comp_tensor_id] },
  refine
    (@cancel_epi _ _ _ _ _ ((coequalizer.π _ _ ⊗ 𝟙 _) ⊗ 𝟙 _)
      (map_π_epi (tensor_right _ ⋙ tensor_right _) _ _) _ _).1 _,
  dsimp, dunfold tensor_Bimod.X, dsimp,
  slice_lhs 1 2 { rw associator_naturality },
  slice_lhs 2 3 { rw [monoidal_category.tensor_id,
                      tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id] },
  slice_lhs 3 4 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv (tensor_right L.X)] },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_lhs 2 3 { rw [←monoidal_category.tensor_id,
                      associator_naturality] },
  slice_rhs 1 2 { rw [←comp_tensor_id,
                      ←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv (tensor_right L.X)] },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc, comp_tensor_id, comp_tensor_id] },
  have :
    (coequalizer.π
      (P.act_right ⊗
        𝟙 (coequalizer (Q.act_right ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ L.act_left))))
      ((α_ P.X S.X
        (coequalizer (Q.act_right ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ L.act_left)))).hom ≫
          (𝟙 P.X ⊗ tensor_Bimod.act_left Q L)) ⊗
        𝟙 U.X) ≫
    tensor_Bimod.act_right P (Q.tensor_Bimod L) =
    (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ (Q.tensor_Bimod L).act_right) ≫ coequalizer.π _ _,
  { dsimp,
    dunfold tensor_Bimod.act_right, dsimp,
    dunfold tensor_Bimod.act_right, dsimp,
    dunfold tensor_Bimod.X, dsimp,
    rw π_tensor_id_comp_preserves_coequalizer_inv_comp_colim_map,
    simp only [category.assoc] },
  slice_rhs 3 4 { rw this }, clear this,
  slice_rhs 2 3 { rw associator_naturality },
  dsimp,
  slice_rhs 3 4 { rw [←id_tensor_comp,
                      tensor_Bimod.π_tensor_id_act_right,
                      id_tensor_comp, id_tensor_comp] },
  coherence,
end

noncomputable
def inv_hom_aux : P.X ⊗ (tensor_Bimod.X Q L) ⟶ tensor_Bimod.X (tensor_Bimod P Q) L :=
begin
  refine (preserves_coequalizer.iso (tensor_left P.X) _ _).inv ≫ coequalizer.desc _ _,
  exact (α_ _ _ _).inv ≫ ((coequalizer.π _ _) ⊗ 𝟙 L.X) ≫ (coequalizer.π _ _),
  dsimp, dunfold tensor_Bimod.X, dsimp,
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

noncomputable
def inv_hom : tensor_Bimod.X P (tensor_Bimod Q L) ⟶ tensor_Bimod.X (tensor_Bimod P Q) L :=
begin
  refine coequalizer.desc (inv_hom_aux P Q L) _,
  dunfold inv_hom_aux, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _)
      (map_π_epi (tensor_left _) _ _) _ _).1 _,
  dunfold tensor_Bimod.X, dsimp,
  slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor] },
  slice_lhs 2 3 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 2 3 { rw coequalizer.π_desc },
  slice_lhs 1 2 { rw [←monoidal_category.tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←comp_tensor_id, coequalizer.condition, comp_tensor_id, comp_tensor_id] },
  slice_rhs 1 2 { rw [←monoidal_category.tensor_id, associator_naturality] },
  slice_rhs 2 3 { rw [←id_tensor_comp,
                      tensor_Bimod.id_tensor_π_act_left,
                      id_tensor_comp, id_tensor_comp] },
  slice_rhs 4 5 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_rhs 4 5 { rw coequalizer.π_desc },
  slice_rhs 3 4 { rw associator_inv_naturality },
  coherence,
end

lemma hom_hom_inv_hom_id : hom_hom P Q L ≫ inv_hom P Q L = 𝟙 _ :=
begin
  dunfold hom_hom hom_hom_aux inv_hom inv_hom_aux, dsimp,
  ext,
  slice_lhs 1 2 { rw coequalizer.π_desc },
  refine
    (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _)
      (map_π_epi (tensor_right _) _ _) _ _).1 _,
  slice_lhs 1 2 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 1 2 { rw coequalizer.π_desc },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_lhs 2 3 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 2 3 { rw coequalizer.π_desc },
  slice_lhs 1 3 { rw iso.hom_inv_id_assoc },
  dunfold tensor_Bimod.X,
  slice_rhs 2 3 { rw category.comp_id },
  refl,
end

lemma inv_hom_hom_hom_id : inv_hom P Q L ≫ hom_hom P Q L = 𝟙 _ :=
begin
  dunfold hom_hom hom_hom_aux inv_hom inv_hom_aux, dsimp,
  ext,
  slice_lhs 1 2 { rw coequalizer.π_desc },
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _)
      (map_π_epi (tensor_left _) _ _) _ _).1 _,
  slice_lhs 1 2 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 1 2 { rw coequalizer.π_desc },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_lhs 2 3 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 2 3 { rw coequalizer.π_desc },
  slice_lhs 1 3 { rw iso.inv_hom_id_assoc },
  dunfold tensor_Bimod.X,
  slice_rhs 2 3 { rw category.comp_id },
  refl,
end

end associator_Bimod

noncomputable
def associator_Bimod {W X Y Z : Mon_ C} (L : Bimod W X) (M : Bimod X Y) (N : Bimod Y Z) :
  tensor_Bimod (tensor_Bimod L M) N ≅ tensor_Bimod L (tensor_Bimod M N) :=
iso_of_iso
  { hom := associator_Bimod.hom_hom L M N,
    inv := associator_Bimod.inv_hom L M N,
    hom_inv_id' := associator_Bimod.hom_hom_inv_hom_id L M N,
    inv_hom_id' := associator_Bimod.inv_hom_hom_hom_id L M N }
  (associator_Bimod.hom_left_act_hom' L M N)
  (associator_Bimod.hom_right_act_hom' L M N)

namespace left_unitor_Bimod
variables {R S : Mon_ C} (P : Bimod R S)

noncomputable
def hom_hom : tensor_Bimod.X (regular R) P ⟶ P.X :=
begin
  dsimp, dunfold tensor_Bimod.X, dsimp,
  refine coequalizer.desc P.act_left _,
  rw [category.assoc, left_assoc],
end

lemma hom_left_act_hom' :
  ((regular R).tensor_Bimod P).act_left ≫ hom_hom P = (𝟙 R.X ⊗ hom_hom P) ≫ P.act_left :=
begin
  dsimp, dunfold hom_hom tensor_Bimod.act_left regular, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _)
      (map_π_epi (tensor_left _) _ _) _ _).1 _,
  dsimp,
  slice_lhs 1 2 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc] },
  rw [left_assoc, iso.inv_hom_id_assoc],
end

lemma hom_right_act_hom' :
  ((regular R).tensor_Bimod P).act_right ≫ hom_hom P = (hom_hom P ⊗ 𝟙 S.X) ≫ P.act_right :=
begin
  dsimp, dunfold hom_hom tensor_Bimod.act_right regular, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _)
      (map_π_epi (tensor_right _) _ _) _ _).1 _,
  dsimp,
  slice_lhs 1 2 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc] },
  rw middle_assoc,
end

noncomputable
def inv_hom : P.X ⟶ tensor_Bimod.X (regular R) P :=
(λ_ P.X).inv ≫ (R.one ⊗ 𝟙 _) ≫ coequalizer.π _ _

lemma hom_hom_inv_hom_id : hom_hom P ≫ inv_hom P = 𝟙 _ :=
begin
  dunfold hom_hom inv_hom tensor_Bimod.X,
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

lemma inv_hom_hom_hom_id : inv_hom P ≫ hom_hom P = 𝟙 _ :=
begin
  dunfold hom_hom inv_hom, dsimp,
  slice_lhs 3 4 { rw coequalizer.π_desc },
  rw [one_act_left, iso.inv_hom_id],
end

end left_unitor_Bimod

noncomputable
def left_unitor_Bimod {X Y : Mon_ C} (M : Bimod X Y) : tensor_Bimod (regular X) M ≅ M :=
iso_of_iso
  { hom := left_unitor_Bimod.hom_hom M,
    inv := left_unitor_Bimod.inv_hom M,
    hom_inv_id' := left_unitor_Bimod.hom_hom_inv_hom_id M,
    inv_hom_id' := left_unitor_Bimod.inv_hom_hom_hom_id M }
  (left_unitor_Bimod.hom_left_act_hom' M)
  (left_unitor_Bimod.hom_right_act_hom' M)

namespace right_unitor_Bimod
variables {R S : Mon_ C} (P : Bimod R S)

noncomputable
def hom_hom : tensor_Bimod.X P (regular S) ⟶ P.X :=
begin
  dsimp, dunfold tensor_Bimod.X, dsimp,
  refine coequalizer.desc P.act_right _,
  rw [category.assoc, right_assoc, iso.hom_inv_id_assoc],
end

lemma hom_left_act_hom' :
  (P.tensor_Bimod (regular S)).act_left ≫ hom_hom P = (𝟙 R.X ⊗ hom_hom P) ≫ P.act_left :=
begin
  dsimp, dunfold hom_hom tensor_Bimod.act_left regular, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (𝟙 _ ⊗ coequalizer.π _ _)
      (map_π_epi (tensor_left _) _ _) _ _).1 _,
  dsimp,
  slice_lhs 1 2 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←id_tensor_comp, coequalizer.π_desc] },
  rw [middle_assoc, iso.inv_hom_id_assoc],
end

lemma hom_right_act_hom' :
  (P.tensor_Bimod (regular S)).act_right ≫ hom_hom P = (hom_hom P ⊗ 𝟙 S.X) ≫ P.act_right :=
begin
  dsimp, dunfold hom_hom tensor_Bimod.act_right regular, dsimp,
  refine
    (@cancel_epi _ _ _ _ _ (coequalizer.π _ _ ⊗ 𝟙 _)
      (map_π_epi (tensor_right _) _ _) _ _).1 _,
  dsimp,
  slice_lhs 1 2 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      map_π_preserves_coequalizer_inv] },
  slice_lhs 1 2 { rw [ι_colim_map, parallel_pair_hom_app_one] },
  slice_lhs 3 4 { rw coequalizer.π_desc },
  slice_rhs 1 2 { rw [←comp_tensor_id, coequalizer.π_desc] },
  rw [right_assoc, iso.hom_inv_id_assoc],
end

noncomputable
def inv_hom : P.X ⟶ tensor_Bimod.X P (regular S) :=
(ρ_ P.X).inv ≫ (𝟙 _ ⊗ S.one) ≫ coequalizer.π _ _

lemma hom_hom_inv_hom_id : hom_hom P ≫ inv_hom P = 𝟙 _ :=
begin
  dunfold hom_hom inv_hom tensor_Bimod.X,
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

lemma inv_hom_hom_hom_id : inv_hom P ≫ hom_hom P = 𝟙 _ :=
begin
  dunfold hom_hom inv_hom, dsimp,
  slice_lhs 3 4 { rw coequalizer.π_desc },
  rw [act_right_one, iso.inv_hom_id],
end

end right_unitor_Bimod

noncomputable
def right_unitor_Bimod {X Y : Mon_ C} (M : Bimod X Y) : tensor_Bimod M (regular Y) ≅ M :=
iso_of_iso
  { hom := right_unitor_Bimod.hom_hom M,
    inv := right_unitor_Bimod.inv_hom M,
    hom_inv_id' := right_unitor_Bimod.hom_hom_inv_hom_id M,
    inv_hom_id' := right_unitor_Bimod.inv_hom_hom_hom_id M }
  (right_unitor_Bimod.hom_left_act_hom' M)
  (right_unitor_Bimod.hom_right_act_hom' M)

noncomputable
def Mon_bicategory : bicategory (Mon_ C) :=
{ hom := λ X Y, Bimod X Y,
  id := λ X, regular X,
  comp := λ X Y Z M N, tensor_Bimod M N,
  hom_category := λ X Y, infer_instance,
  whisker_left := λ X Y Z L M N f, tensor_hom (𝟙 L) f,
  whisker_right := λ X Y Z L M f N, tensor_hom f (𝟙 N),
  associator := sorry,
  left_unitor := λ X Y M, left_unitor_Bimod M,
  right_unitor := λ X Y M, right_unitor_Bimod M,
  whisker_left_id' := sorry,
  whisker_left_comp' := sorry,
  id_whisker_left' := sorry,
  comp_whisker_left' := sorry,
  id_whisker_right' := sorry,
  comp_whisker_right' := sorry,
  whisker_right_id' := sorry,
  whisker_right_comp' := sorry,
  whisker_assoc' := sorry,
  whisker_exchange' := sorry,
  pentagon' := sorry,
  triangle' := sorry }

end Bimod
