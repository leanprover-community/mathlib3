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
    slice_rhs 4 5 { rw [←tensor_comp,
                        middle_assoc,
                        ←category.id_comp (𝟙 Q.X ≫ 𝟙 Q.X), tensor_comp, tensor_comp] },
    coherence, },
  { dsimp,
    simp,
    slice_lhs 2 3 { rw associator_inv_naturality },
    simp, },
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
    simp,
    slice_lhs 1 2 { rw associator_naturality },
    slice_rhs 3 4 { rw associator_inv_naturality },
    simp, },
  { dsimp,
    simp,
    slice_lhs 2 3 { rw associator_naturality },
    slice_lhs 3 4 { rw [←tensor_comp,
                        middle_assoc,
                        ←category.id_comp (𝟙 P.X ≫ 𝟙 P.X), tensor_comp, tensor_comp]},
    coherence, },
end

def one_act_left' : (R.one ⊗ 𝟙 _) ≫ act_left P Q = (λ_ _).hom :=
begin
  dunfold X act_left,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_left (𝟙_ C)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp, simp, dsimp,
  slice_lhs 1 1 { rw ←tensor_id_comp_id_tensor },
  slice_lhs 2 2 { rw [←tensor_left_map, ←ι_comp_coequalizer_comparison] },
  slice_lhs 3 3 { rw [←preserves_coequalizer.iso_hom] },
  slice_lhs 3 4 { rw iso.hom_inv_id },
  simp,
  slice_lhs 1 2 { rw [←tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp, one_act_left], simp },
  slice_rhs 1 2 { rw left_unitor_naturality },
  dsimp, coherence,
end

def act_right_one' : (𝟙 _ ⊗ T.one) ≫ act_right P Q = (ρ_ _).hom :=
begin
  dunfold X act_right,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_right (𝟙_ C)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp, simp,
  slice_lhs 1 1 { rw ←id_tensor_comp_tensor_id, },
  slice_lhs 2 2 { rw [←tensor_right_map, ←ι_comp_coequalizer_comparison] },
  slice_lhs 3 3 { rw [←preserves_coequalizer.iso_hom] },
  slice_lhs 3 4 { rw iso.hom_inv_id },
  simp,
  slice_lhs 1 2 { rw [←tensor_id, associator_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp, act_right_one], simp },
  slice_rhs 1 2 { rw right_unitor_naturality },
  dsimp, coherence,
end

def left_assoc' :
  (R.mul ⊗ 𝟙 _) ≫ act_left P Q = (α_ R.X R.X _).hom ≫ (𝟙 R.X ⊗ act_left P Q) ≫ act_left P Q :=
begin
  dunfold X act_left,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_left (R.X ⊗ R.X)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp, simp,
  slice_lhs 1 1 { rw ←tensor_id_comp_id_tensor },
  slice_lhs 2 2 { rw [←tensor_left_map, ←ι_comp_coequalizer_comparison] },
  slice_lhs 3 3 { rw [←preserves_coequalizer.iso_hom] },
  slice_lhs 3 4 { rw iso.hom_inv_id },
  simp,
  slice_rhs 1 2 { rw [←tensor_id, associator_naturality] },
  simp,
  slice_rhs 2 3 { rw [←tensor_comp,
                      ←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      ←ι_comp_coequalizer_comparison,
                      ←preserves_coequalizer.iso_hom] },
  slice_rhs 2 3 { rw iso.hom_inv_id },
  simp,
  slice_rhs 2 3 { rw [←tensor_comp], simp },
  slice_rhs 4 5 { rw [←(tensor_left_map _ _ _ (coequalizer.π _ _)),
                      ←ι_comp_coequalizer_comparison,
                      ←preserves_coequalizer.iso_hom] },
  slice_rhs 5 6 { rw iso.hom_inv_id },
  simp,
  slice_lhs 1 2 { rw [←tensor_id, associator_inv_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp, left_assoc], simp },
  slice_rhs 3 4 { rw associator_inv_naturality },
  coherence,
end

def right_assoc' :
  (𝟙 _ ⊗ T.mul) ≫ act_right P Q = (α_ _ T.X T.X).inv ≫ (act_right P Q ⊗ 𝟙 T.X) ≫ act_right P Q :=
begin
  dunfold X act_right,
  refine (cancel_epi (preserves_coequalizer.iso (tensor_right (T.X ⊗ T.X)) _ _).hom).1 _,
  ext,
  erw ι_comp_coequalizer_comparison_assoc,
  erw ι_comp_coequalizer_comparison_assoc,
  dsimp, simp,
  slice_lhs 1 1 { rw ←id_tensor_comp_tensor_id },
  slice_lhs 2 2 { rw [←tensor_right_map, ←ι_comp_coequalizer_comparison] },
  slice_lhs 3 3 { rw [←preserves_coequalizer.iso_hom] },
  slice_lhs 3 4 { rw iso.hom_inv_id },
  simp,
  slice_rhs 1 2 { rw [←tensor_id, associator_inv_naturality] },
  simp,
  slice_rhs 2 3 { rw [←tensor_comp,
                      ←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      ←ι_comp_coequalizer_comparison,
                      ←preserves_coequalizer.iso_hom] },
  slice_rhs 2 3 { rw iso.hom_inv_id },
  simp,
  slice_rhs 2 3 { rw [←tensor_comp], simp },
  slice_rhs 4 5 { rw [←(tensor_right_map _ _ _ (coequalizer.π _ _)),
                      ←ι_comp_coequalizer_comparison,
                      ←preserves_coequalizer.iso_hom] },
  slice_rhs 5 6 { rw iso.hom_inv_id },
  simp,
  slice_lhs 1 2 { rw [←tensor_id, associator_naturality] },
  slice_lhs 2 3 { rw [←tensor_comp, right_assoc], simp },
  slice_rhs 3 4 { rw associator_naturality },
  coherence,
end

end tensor_Bimod

noncomputable
def tensor_Bimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) : Bimod X Z :=
{ X := tensor_Bimod.X M N,
  act_left := tensor_Bimod.act_left M N,
  act_right := tensor_Bimod.act_right M N,
  one_act_left' := tensor_Bimod.one_act_left' M N,
  act_right_one' := tensor_Bimod.act_right_one' M N,
  left_assoc' := tensor_Bimod.left_assoc' M N,
  right_assoc' := tensor_Bimod.right_assoc' M N,
  middle_assoc' := sorry, }

end Bimod
