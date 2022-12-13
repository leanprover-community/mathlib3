/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston
-/

import category_theory.preadditive.opposite
import algebra.homology.additive

/-!
# Opposite categories of complexes
Given an appropriate category `C`, the opposite of its category of chain complexes,
`Ch(C)ᵒᵖ` is the category of cochain complexes `CoCh(Cᵒᵖ)`. We define this equivalence
(and the other analogous equivalences).
Likewise, something something natural transformation with the homology functor.
## Implementation notes
We work in terms of homological complexes, a generalisation of both chain and cochain complexes.
See the file blah for an explanation.
## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/

noncomputable theory

open opposite category_theory category_theory.limits

namespace homological_complex

variables {C : Type*} [category C] [preadditive C]
variables {ι : Type*} {c : complex_shape ι}

@[simps]
protected def op (X : homological_complex C c) : homological_complex Cᵒᵖ c.symm :=
{ X := λ i, op (X.X i),
  d := λ i j, (X.d j i).op,
  shape' := λ i j hij, by { rw [X.shape j i hij, op_zero], },
  d_comp_d' := by { intros, rw [← op_comp, X.d_comp_d, op_zero], } }

@[simps]
protected def unop (X : homological_complex Cᵒᵖ c) : homological_complex C c.symm :=
{ X := λ i, unop (X.X i),
  d := λ i j, (X.d j i).unop,
  shape' := λ i j hij, by { rw [X.shape j i hij, unop_zero], },
  d_comp_d' := by { intros, rw [← unop_comp, X.d_comp_d, unop_zero], } }

@[simps]
def op_functor : (homological_complex C c)ᵒᵖ ⥤ homological_complex Cᵒᵖ c.symm :=
{ obj := λ X, (unop X).op,
  map := λ X Y f,
  { f := λ i, (f.unop.f i).op,
    comm' := λ i j hij, by simp only [op_d, ← op_comp, f.unop.comm] }, }

@[simps]
def unop_functor : (homological_complex Cᵒᵖ c)ᵒᵖ ⥤ homological_complex C c.symm :=
{ obj := λ X, (unop X).unop,
  map := λ X Y f,
  { f := λ i, (f.unop.f i).unop,
    comm' := λ i j hij, by simp only [unop_d, ← unop_comp, f.unop.comm] }, }

instance op_functor_additive : (@op_functor C _ _ _ c).additive := {}

instance unop_functor_additive : (@unop_functor C _ _ _ c).additive := {}

end homological_complex

-- need to fix because c.symm.symm isn't defeq to c
/-def op_unop_obj (C : homological_complex V c) :
  (op V c ⋙ unop V c).obj C ≅ C :=
{ hom := { f := λ i, 𝟙 _,
    comm' := λ i j hij, by { rw [category.id_comp, category.comp_id], refl }},
  inv := { f := λ i, 𝟙 _,
  comm' := λ i j hij, by { rw [category.id_comp, category.comp_id], refl }},
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
def op_unop_map (C D : homological_complex V c) (f : C ⟶ D) :
  (op V c ⋙ unop V c).map f ≫ (op_unop_obj V c D).hom =
      (op_unop_obj V c C).hom ≫ (𝟭 (homological_complex V c)).map f :=
begin
  ext i,
  rw [functor.id_map, functor.comp_map, comp_f],
  show _ ≫ 𝟙 _ = 𝟙 _ ≫ _,
  rw [category.id_comp, category.comp_id],
  refl,
end
def op_unop : op V c ⋙ unop V c ≅ functor.id _ :=
nat_iso.of_components (op_unop_obj V c) (λ _ _, op_unop_map V c _ _)-/

#exit
namespace complex_shape

variables (c)

lemma symm_prev (i : ι) : c.symm.prev i = c.next i := rfl

lemma symm_next (i : ι) : c.symm.next i = c.prev i := rfl
end complex_shape

variables {W : Type*} [category W] [abelian W]
  (C : homological_complex W c) (i : ι)
open_locale zero_object
--move

def homology_of_prev_none {j : ι} (h : c.prev j = none) :
  C.homology j ≅ kernel_subobject (C.d_from j) :=
(homology.congr (C.d_to_comp_d_from j) zero_comp (C.d_to_eq_zero h) rfl).trans
  (homology_of_zero_left (C.d_from j))

def homology_of_next_none {j : ι} (h : c.next j = none) :
  C.homology j ≅ cokernel (C.d_to j) :=
(homology.congr (C.d_to_comp_d_from j) comp_zero rfl (C.d_from_eq_zero h)).trans
  (homology_of_zero_right (C.d_to j))

namespace homological_complex

variables (W)
--move
def op_zero_iso : opposite.op (0 : W) ≅ (0 : Wᵒᵖ) :=
{ hom := 0,
  inv := 0,
  hom_inv_id' := by { rw [zero_comp, ←op_id, ←op_zero], congr },
  inv_hom_id' := by { rw [zero_comp, id_zero] }}

def unop_zero_iso : opposite.unop (0 : Wᵒᵖ) ≅ 0 :=
(op_zero_iso W).unop

variables {W}

def X_op_prev_none {i : ι} (h : c.next i = none) :
  opposite.unop (C.op_obj.X_prev i) ≅ C.X_next i :=
((eq_to_iso (by { dsimp [X_prev], rw [c.symm_prev, h], refl })).trans $
  unop_zero_iso W).trans (C.X_next_iso_zero h).symm

def X_op_prev_rel {i j : ι} (h : c.rel i j) :
  opposite.unop (C.op_obj.X_prev i) ≅ C.X_next i :=
eq_to_iso (begin
  dsimp [X_prev, X_next],
  rw [c.symm_prev, c.next_eq_some h],
  refl
end)

lemma op_d_to_of_none {i : ι} (h : c.next i = none) :
  (C.op_obj.d_to i).unop ≫ (C.X_op_prev_none h).hom = C.d_from i :=
begin
  dsimp [d_from, d_to, X_op_prev_none],
  rw [c.symm_prev, h],
  show quiver.hom.unop (0 : _ ⟶ opposite.op (C.X i)) ≫ _ ≫ _ = (0 : C.X i ⟶ C.X_next i),
  rw [unop_zero, zero_comp],
end

lemma op_d_to_op_of_none {i : ι} (h : c.next i = none) :
  (C.X_op_prev_none h).hom.op ≫ (C.op_obj.d_to i) = (C.d_from i).op :=
begin
  rw ←C.op_d_to_of_none h,
  refl,
end

lemma op_d_to_of_rel {i j : ι} (h : c.rel i j) :
  (C.op_obj.d_to i).unop ≫ (C.X_op_prev_rel h).hom = C.d_from i :=
begin
  dsimp [d_from, d_to, X_op_prev_rel],
  rw [c.symm_prev, c.next_eq_some h],
  show _ = _ ≫ _,
  erw unop_comp,
  show (C.d i j ≫ _) ≫ _ = _,
  dsimp [X_next_iso, X_prev_iso],
  simp only [eq_to_hom_trans, eq_to_hom_unop, category.assoc],
end

lemma op_d_to_op_of_rel {i j : ι} (h : c.rel i j) :
  (C.X_op_prev_rel h).hom.op ≫ (C.op_obj.d_to i) = (C.d_from i).op :=
begin
  rw ←C.op_d_to_of_rel h,
  refl,
end

def X_op_next_none {i : ι} (h : c.prev i = none) :
  opposite.unop (C.op_obj.X_next i) ≅ C.X_prev i :=
((eq_to_iso (by { dsimp [X_next], rw [c.symm_next, h], refl })).trans $
  unop_zero_iso W).trans (C.X_prev_iso_zero h).symm

def X_op_next_rel {i j : ι} (h : c.rel i j) :
  opposite.unop (C.op_obj.X_next j) ≅ C.X_prev j :=
eq_to_iso (begin
  dsimp [X_prev, X_next],
  rw [c.symm_next, c.prev_eq_some h],
  refl
end)

lemma op_d_from_of_none {i : ι} (h : c.prev i = none) :
  (C.X_op_next_none h).inv ≫ (C.op_obj.d_from i).unop = C.d_to i :=
begin
  dsimp [d_from, d_to, X_op_next_none],
  rw [c.symm_next, h],
  show _ ≫ quiver.hom.unop (0 : opposite.op (C.X i) ⟶ _) = (0 : C.X_prev i ⟶ C.X i),
  rw [unop_zero, comp_zero],
end

lemma op_d_from_op_of_none {i : ι} (h : c.prev i = none) :
  C.op_obj.d_from i ≫ (C.X_op_next_none h).inv.op = (C.d_to i).op :=
begin
  rw ←C.op_d_from_of_none h,
  refl,
end

lemma op_d_from_of_rel {i j : ι} (h : c.rel i j) :
  (C.X_op_next_rel h).inv ≫ (C.op_obj.d_from j).unop = C.d_to j :=
begin
  dsimp [d_from, d_to, X_op_next_rel],
  rw [c.symm_next, c.prev_eq_some h],
  show _ = _ ≫ _,
  erw unop_comp,
  show _ ≫ _ ≫ C.d i j = _,
  dsimp [X_next_iso, X_prev_iso],
  simp only [eq_to_iso.inv, eq_to_hom_trans_assoc, eq_to_hom_unop],
end

lemma op_d_from_op_of_rel {i j : ι} (h : c.rel i j) :
  C.op_obj.d_from j ≫ (C.X_op_next_rel h).inv.op = (C.d_to j).op :=
begin
  rw ←C.op_d_from_of_rel h,
  refl,
end

variables (D : homological_complex Wᵒᵖ c)
-- haven't really thought about whether all this duplication is necessary
def X_unop_prev_none {i : ι} (h : c.next i = none) :
  opposite.op (D.unop_obj.X_prev i) ≅ D.X_next i :=
((eq_to_iso $ by { dsimp [X_prev], rw [c.symm_prev, h], refl }).trans
  (op_zero_iso W)).trans (D.X_next_iso_zero h).symm

def X_unop_prev_rel {i j : ι} (h : c.rel i j) :
  opposite.op (D.unop_obj.X_prev i) ≅ D.X_next i :=
eq_to_iso (begin
  dsimp [X_prev, X_next],
  rw [c.symm_prev, c.next_eq_some h],
  refl
end)

lemma unop_d_to_of_none {i : ι} (h : c.next i = none) :
  (D.unop_obj.d_to i).op ≫ (D.X_unop_prev_none h).hom = D.d_from i :=
begin
  dsimp [d_from, d_to, X_unop_prev_none],
  rw [c.symm_prev, h],
  show quiver.hom.op (0 : _ ⟶ opposite.unop (D.X i)) ≫ _ ≫ _ = (0 : D.X i ⟶ D.X_next i),
  rw [op_zero, zero_comp],
end

lemma unop_d_to_unop_of_none {i : ι} (h : c.next i = none) :
  (D.X_unop_prev_none h).hom.unop ≫ (D.unop_obj.d_to i) = (D.d_from i).unop :=
begin
  rw ←D.unop_d_to_of_none h,
  refl,
end

lemma unop_d_to_of_rel {i j : ι} (h : c.rel i j) :
  (D.unop_obj.d_to i).op ≫ (D.X_unop_prev_rel h).hom = D.d_from i :=
begin
  dsimp [d_from, d_to, X_unop_prev_rel],
  rw [c.symm_prev, c.next_eq_some h],
  show _ = _ ≫ _,
  erw op_comp,
  show (D.d i j ≫ _) ≫ _ = _,
  dsimp [X_next_iso, X_prev_iso],
  simp only [eq_to_hom_trans, eq_to_hom_op, category.assoc],
end

lemma unop_d_to_unop_of_rel {i j : ι} (h : c.rel i j) :
  (D.X_unop_prev_rel h).hom.unop ≫ (D.unop_obj.d_to i) = (D.d_from i).unop :=
begin
  rw ←D.unop_d_to_of_rel h,
  refl,
end

def X_unop_next_none {i : ι} (h : c.prev i = none) :
  opposite.op (D.unop_obj.X_next i) ≅ D.X_prev i :=
((eq_to_iso (by { dsimp [X_next], rw [c.symm_next, h], refl })).trans $
  op_zero_iso W).trans (D.X_prev_iso_zero h).symm

def X_unop_next_rel {i j : ι} (h : c.rel i j) :
  opposite.op (D.unop_obj.X_next j) ≅ D.X_prev j :=
eq_to_iso (begin
  dsimp [X_prev, X_next],
  rw [c.symm_next, c.prev_eq_some h],
  refl
end)

lemma unop_d_from_of_none {i : ι} (h : c.prev i = none) :
  (D.X_unop_next_none h).inv ≫ (D.unop_obj.d_from i).op = D.d_to i :=
begin
  dsimp [d_from, d_to, X_unop_next_none],
  rw [c.symm_next, h],
  show _ ≫ quiver.hom.op (0 : opposite.unop (D.X i) ⟶ _) = (0 : D.X_prev i ⟶ D.X i),
  rw [op_zero, comp_zero],
end

lemma unop_d_from_unop_of_none {i : ι} (h : c.prev i = none) :
  D.unop_obj.d_from i ≫ (D.X_unop_next_none h).inv.unop = (D.d_to i).unop :=
begin
  rw ←D.unop_d_from_of_none h,
  refl,
end

lemma unop_d_from_of_rel {i j : ι} (h : c.rel i j) :
  (D.X_unop_next_rel h).inv ≫ (D.unop_obj.d_from j).op = D.d_to j :=
begin
  dsimp [d_from, d_to, X_unop_next_rel],
  rw [c.symm_next, c.prev_eq_some h],
  show _ = _ ≫ _,
  erw op_comp,
  show _ ≫ _ ≫ D.d i j = _,
  dsimp [X_next_iso, X_prev_iso],
  simp only [eq_to_iso.inv, eq_to_hom_trans_assoc, eq_to_hom_op],
end

lemma unop_d_from_unop_of_rel {i j : ι} (h : c.rel i j) :
  D.unop_obj.d_from j ≫ (D.X_unop_next_rel h).inv.unop = (D.d_to j).unop :=
begin
  rw ←D.unop_d_from_of_rel h,
  refl,
end

variables {j : ι}

def kernel_op_to_kernel_op_of_rel {i j : ι} (hij : c.rel i j) :
  ↑(kernel_subobject (C.op_obj.d_from j)) ⟶ kernel (C.d_to j).op :=
(((kernel_subobject_iso (C.op_obj.d_from j)).hom ≫ (kernel_comp_mono
  (C.op_obj.d_from j) (C.X_op_next_rel hij).inv.op).inv) ≫ (@kernel_iso_of_eq _ _ _ _ _
  (((op_obj C).d_from j) ≫ (C.X_op_next_rel hij).inv.op) (C.d_to j).op
  _ _ (C.op_d_from_op_of_rel hij)).hom)

def homology_op_of_rel {i j : ι} (hij : c.rel i j) :
  C.homology j ⟶ opposite.unop (C.op_obj.homology j) :=
homology.desc _ _ _ (kernel.lift _ ((limits.kernel_subobject _).arrow ≫ cokernel.π (C.d_to j)
  ≫ (kernel_op_unop _).inv ≫ (C.kernel_op_to_kernel_op_of_rel hij).unop)
  sorry ≫ (kernel_unop_unop _).hom) sorry

instance {i j : ι} (hij : c.rel i j) : is_iso (C.homology_op_of_rel hij) :=
sorry --@abelian.is_iso_of_mono_of_epi _ _ _ _ _ (C.homology_op_of_rel hij) sorry sorry

-- there's two cases here. don't want to do them rn
def homology_op_of_none {j : ι} (h : c.prev j = none) :
  C.homology j ≅ opposite.unop (C.op_obj.homology j) :=
sorry

def kernel_unop_to_kernel_unop_of_rel {i j : ι} (hij : c.rel i j) :
  ↑(kernel_subobject (D.unop_obj.d_from j)) ⟶ kernel (D.d_to j).unop :=
(((kernel_subobject_iso (D.unop_obj.d_from j)).hom ≫ (kernel_comp_mono
  (D.unop_obj.d_from j) (D.X_unop_next_rel hij).inv.unop).inv) ≫ (@kernel_iso_of_eq _ _ _ _ _
  ((D.unop_obj.d_from j) ≫ (D.X_unop_next_rel hij).inv.unop) (D.d_to j).unop
  _ _ (D.unop_d_from_unop_of_rel hij)).hom)

def homology_unop_of_rel {i j : ι} (hij : c.rel i j) :
  D.homology j ⟶ opposite.op (D.unop_obj.homology j) :=
homology.desc _ _ _ (kernel.lift _ ((limits.kernel_subobject _).arrow ≫ cokernel.π (D.d_to j)
  ≫ (kernel_unop_op _).inv ≫ (D.kernel_unop_to_kernel_unop_of_rel hij).op)
  sorry ≫ (kernel_op_op _).hom) sorry

instance {i j : ι} (hij : c.rel i j) : is_iso (D.homology_unop_of_rel hij) :=
sorry --@abelian.is_iso_of_mono_of_epi _ _ _ _ _ (D.homology_unop_of_rel hij) sorry sorry

end homological_complex

namespace chain_complex

def homology_op (X : chain_complex W ℕ) (n : ℕ) :
  opposite.unop (X.op_obj.homology n) ≅ X.homology n :=
(as_iso (X.homology_op_of_rel rfl)).symm

def homology_unop (X : chain_complex Wᵒᵖ ℕ) (n : ℕ) :
  opposite.op (X.unop_obj.homology n) ≅ X.homology n :=
(as_iso (X.homology_unop_of_rel rfl)).symm

end chain_complex
namespace cochain_complex

def homology_op_zero (X : cochain_complex W ℕ) :
  opposite.unop (X.op_obj.homology 0) ≅ X.homology 0 :=
((homology_of_prev_none X cochain_complex.prev_nat_zero).trans $
  (kernel_subobject_iso _).trans $ (cokernel_op_unop _).symm.trans $
  (iso.trans (homology_of_next_none _ chain_complex.next_nat_zero) $
  ((cokernel_iso_of_eq (X.op_d_to_op_of_rel rfl).symm).trans
  (cokernel_epi_comp _ _)).symm).unop).symm

def homology_op_succ (X : cochain_complex W ℕ) (n : ℕ) :
  opposite.unop (X.op_obj.homology (n + 1)) ≅ X.homology (n + 1) :=
(as_iso (X.homology_op_of_rel rfl)).symm

def homology_op (X : cochain_complex W ℕ) : Π n : ℕ,
  opposite.unop (X.op_obj.homology n) ≅ X.homology n
| 0 := homology_op_zero X
| (n+1) := homology_op_succ X n

def homology_unop_zero (X : cochain_complex Wᵒᵖ ℕ) :
  opposite.op (X.unop_obj.homology 0) ≅ X.homology 0 :=
((homology_of_prev_none X cochain_complex.prev_nat_zero).trans $
  (kernel_subobject_iso _).trans $ (cokernel_unop_op _).symm.trans $
  (iso.trans (homology_of_next_none _ chain_complex.next_nat_zero) $
  ((cokernel_iso_of_eq (X.unop_d_to_unop_of_rel rfl).symm).trans
  (cokernel_epi_comp _ _)).symm).op).symm

def homology_unop_succ (X : cochain_complex Wᵒᵖ ℕ) (n : ℕ) :
  opposite.op (X.unop_obj.homology (n + 1)) ≅ X.homology (n + 1) :=
(as_iso (X.homology_unop_of_rel rfl)).symm

def homology_unop (X : cochain_complex Wᵒᵖ ℕ) : Π n : ℕ,
  opposite.op (X.unop_obj.homology n) ≅ X.homology n
| 0 := homology_unop_zero X
| (n+1) := homology_unop_succ X n

end cochain_complex

/-
def homology_op_obj (i : ι) (C : homological_complex W c) :
  (op W c ⋙ (homology_functor _ _ i).op ⋙ op_op _).obj C ≅ (homology_functor W c i).obj C :=
{ hom := _,
  inv := _,
  hom_inv_id' := _,
  inv_hom_id' := _ }
def homology_op (i : ι) :
  op W c ⋙ (homology_functor _ _ i).op ⋙ op_op _ ≅ homology_functor W c i :=
nat_iso.of_components _ _-/
Footer
© 2022 GitHub, Inc.
Footer navigation
Terms
Privacy
Security
Status
Docs
Contact GitHub
Pricing
API
Training
Blog
About
mathlib/op_complex.lean at group-cohomology · leanprover-community/mathlib
