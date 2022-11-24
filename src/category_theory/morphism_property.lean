/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.diagonal
import category_theory.arrow
import category_theory.limits.shapes.comm_sq
import category_theory.concrete_category.basic

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `stable_under_base_change`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.
* `stable_under_cobase_change`: `P` is stable under cobase change if in all pushout
  squares, the right map satisfies `P` if the left map satisfies it.

-/

universes v u

open category_theory category_theory.limits opposite

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C] {D : Type*} [category D]

/-- A `morphism_property C` is a class of morphisms between objects in `C`. -/
@[derive complete_lattice]
def morphism_property := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Prop

instance : inhabited (morphism_property C) := ⟨⊤⟩

variable {C}

namespace morphism_property

instance : has_subset (morphism_property C) :=
⟨λ P₁ P₂, ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P₁ f), P₂ f⟩
instance : has_inter (morphism_property C) :=
⟨λ P₁ P₂ X Y f, P₁ f ∧ P₂ f⟩

/-- The morphism property in `Cᵒᵖ` associated to a morphism property in `C` -/
@[simp] def op (P : morphism_property C) : morphism_property Cᵒᵖ := λ X Y f, P f.unop

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp] def unop (P : morphism_property Cᵒᵖ) : morphism_property C := λ X Y f, P f.op

lemma unop_op (P : morphism_property C) : P.op.unop = P := rfl
lemma op_unop (P : morphism_property Cᵒᵖ) : P.unop.op = P := rfl

/-- The inverse image of a `morphism_property D` by a functor `C ⥤ D` -/
def inverse_image (P : morphism_property D) (F : C ⥤ D) : morphism_property C :=
λ X Y f, P (F.map f)

/-- A morphism property `respects_iso` if it still holds when composed with an isomorphism -/
def respects_iso (P : morphism_property C) : Prop :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f)) ∧
  (∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.hom))

lemma respects_iso.op {P : morphism_property C} (h : respects_iso P) : respects_iso P.op :=
⟨λ X Y Z e f hf, h.2 e.unop f.unop hf, λ X Y Z e f hf, h.1 e.unop f.unop hf⟩

lemma respects_iso.unop {P : morphism_property Cᵒᵖ} (h : respects_iso P) : respects_iso P.unop :=
⟨λ X Y Z e f hf, h.2 e.op f.op hf, λ X Y Z e f hf, h.1 e.op f.op hf⟩

/-- A morphism property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def stable_under_composition (P : morphism_property C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)

lemma stable_under_composition.op {P : morphism_property C} (h : stable_under_composition P) :
  stable_under_composition P.op := λ X Y Z f g hf hg, h g.unop f.unop hg hf

lemma stable_under_composition.unop {P : morphism_property Cᵒᵖ} (h : stable_under_composition P) :
  stable_under_composition P.unop := λ X Y Z f g hf hg, h g.op f.op hg hf

/-- A morphism property is `stable_under_inverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def stable_under_inverse (P : morphism_property C) : Prop :=
∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv

lemma stable_under_inverse.op {P : morphism_property C} (h : stable_under_inverse P) :
  stable_under_inverse P.op := λ X Y e he, h e.unop he

lemma stable_under_inverse.unop {P : morphism_property Cᵒᵖ} (h : stable_under_inverse P) :
  stable_under_inverse P.unop := λ X Y e he, h e.op he

/-- A morphism property is `stable_under_base_change` if the base change of such a morphism
still falls in the class. -/
def stable_under_base_change (P : morphism_property C) : Prop :=
∀ ⦃X Y Y' S : C⦄ ⦃f : X ⟶ S⦄ ⦃g : Y ⟶ S⦄ ⦃f' : Y' ⟶ Y⦄ ⦃g' : Y' ⟶ X⦄
  (sq : is_pullback f' g' g f) (hg : P g), P g'

/-- A morphism property is `stable_under_cobase_change` if the cobase change of such a morphism
still falls in the class. -/
def stable_under_cobase_change (P : morphism_property C) : Prop :=
∀ ⦃A A' B B' : C⦄ ⦃f : A ⟶ A'⦄ ⦃g : A ⟶ B⦄ ⦃f' : B ⟶ B'⦄ ⦃g' : A' ⟶ B'⦄
  (sq : is_pushout g f f' g') (hf : P f), P f'

lemma stable_under_composition.respects_iso {P : morphism_property C}
  (hP : stable_under_composition P) (hP' : ∀ {X Y} (e : X ≅ Y), P e.hom) : respects_iso P :=
⟨λ X Y Z e f hf, hP _ _ (hP' e) hf, λ X Y Z e f hf, hP _ _ hf (hP' e)⟩

lemma respects_iso.cancel_left_is_iso {P : morphism_property C}
  (hP : respects_iso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] :
    P (f ≫ g) ↔ P g :=
⟨λ h, by simpa using hP.1 (as_iso f).symm (f ≫ g) h, hP.1 (as_iso f) g⟩

lemma respects_iso.cancel_right_is_iso {P : morphism_property C}
  (hP : respects_iso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
    P (f ≫ g) ↔ P f :=
⟨λ h, by simpa using hP.2 (as_iso g).symm (f ≫ g) h, hP.2 (as_iso g) f⟩

lemma respects_iso.arrow_iso_iff {P : morphism_property C}
  (hP : respects_iso P) {f g : arrow C} (e : f ≅ g) : P f.hom ↔ P g.hom :=
by { rw [← arrow.inv_left_hom_right e.hom, hP.cancel_left_is_iso, hP.cancel_right_is_iso], refl }

lemma respects_iso.arrow_mk_iso_iff {P : morphism_property C}
  (hP : respects_iso P) {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : arrow.mk f ≅ arrow.mk g) :
    P f ↔ P g :=
hP.arrow_iso_iff e

lemma respects_iso.of_respects_arrow_iso (P : morphism_property C)
  (hP : ∀ (f g : arrow C) (e : f ≅ g) (hf : P f.hom), P g.hom) : respects_iso P :=
begin
  split,
  { intros X Y Z e f hf,
    refine hP (arrow.mk f) (arrow.mk (e.hom ≫ f)) (arrow.iso_mk e.symm (iso.refl _) _) hf,
    dsimp,
    simp only [iso.inv_hom_id_assoc, category.comp_id], },
  { intros X Y Z e f hf,
    refine hP (arrow.mk f) (arrow.mk (f ≫ e.hom)) (arrow.iso_mk (iso.refl _) e _) hf,
    dsimp,
    simp only [category.id_comp], },
end

lemma stable_under_base_change.mk {P : morphism_property C} [has_pullbacks C]
  (hP₁ : respects_iso P)
  (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) (hg : P g), P (pullback.fst : pullback f g ⟶ X)) :
  stable_under_base_change P := λ X Y Y' S f g f' g' sq hg,
begin
  let e := sq.flip.iso_pullback,
  rw [← hP₁.cancel_left_is_iso e.inv, sq.flip.iso_pullback_inv_fst],
  exact hP₂ _ _ _ f g hg,
end

lemma stable_under_base_change.respects_iso {P : morphism_property C}
  (hP : stable_under_base_change P) : respects_iso P :=
begin
  apply respects_iso.of_respects_arrow_iso,
  intros f g e,
  exact hP (is_pullback.of_horiz_is_iso (comm_sq.mk e.inv.w)),
end

lemma stable_under_base_change.fst {P : morphism_property C}
  (hP : stable_under_base_change P) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [has_pullback f g]
  (H : P g) : P (pullback.fst : pullback f g ⟶ X) :=
hP (is_pullback.of_has_pullback f g).flip H

lemma stable_under_base_change.snd {P : morphism_property C}
  (hP : stable_under_base_change P) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [has_pullback f g]
  (H : P f) : P (pullback.snd : pullback f g ⟶ Y) :=
hP (is_pullback.of_has_pullback f g) H

lemma stable_under_base_change.base_change_obj [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) {S S' : C} (f : S' ⟶ S)
  (X : over S) (H : P X.hom) : P ((base_change f).obj X).hom :=
hP.snd X.hom f H

lemma stable_under_base_change.base_change_map [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) {S S' : C} (f : S' ⟶ S)
  {X Y : over S} (g : X ⟶ Y) (H : P g.left) : P ((base_change f).map g).left :=
begin
  let e := pullback_right_pullback_fst_iso Y.hom f g.left ≪≫
    pullback.congr_hom (g.w.trans (category.comp_id _)) rfl,
  have : e.inv ≫ pullback.snd = ((base_change f).map g).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw [← this, hP.respects_iso.cancel_left_is_iso],
  exact hP.snd _ _ H,
end

lemma stable_under_base_change.pullback_map [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : stable_under_composition P) {S X X' Y Y' : C}
  {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'}
  (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _)
      ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂)) :=
begin
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _)
    ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂) =
      ((pullback_symmetry _ _).hom ≫
      ((base_change _).map (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g')).left) ≫
      (pullback_symmetry _ _).hom ≫
      ((base_change g').map (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f')).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw this,
  apply hP'; rw hP.respects_iso.cancel_left_is_iso,
  exacts [hP.base_change_map _ (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g') h₂,
    hP.base_change_map _ (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f') h₁],
end

lemma stable_under_cobase_change.mk {P : morphism_property C} [has_pushouts C]
  (hP₁ : respects_iso P)
  (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) (hf : P f), P (pushout.inr : B ⟶ pushout f g)) :
  stable_under_cobase_change P := λ A A' B B' f g f' g' sq hf,
begin
  let e := sq.flip.iso_pushout,
  rw [← hP₁.cancel_right_is_iso _ e.hom, sq.flip.inr_iso_pushout_hom],
  exact hP₂ _ _ _ f g hf,
end

lemma stable_under_cobase_change.respects_iso {P : morphism_property C}
  (hP : stable_under_cobase_change P) : respects_iso P :=
respects_iso.of_respects_arrow_iso _ (λ f g e, hP (is_pushout.of_horiz_is_iso (comm_sq.mk e.hom.w)))

lemma stable_under_cobase_change.inl {P : morphism_property C}
  (hP : stable_under_cobase_change P) {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [has_pushout f g]
  (H : P g) : P (pushout.inl : A' ⟶ pushout f g) :=
hP (is_pushout.of_has_pushout f g) H

lemma stable_under_cobase_change.inr {P : morphism_property C}
  (hP : stable_under_cobase_change P) {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [has_pushout f g]
  (H : P f) : P (pushout.inr : B ⟶ pushout f g) :=
hP (is_pushout.of_has_pushout f g).flip H

lemma stable_under_cobase_change.op {P : morphism_property C}
  (hP : stable_under_cobase_change P) : stable_under_base_change P.op :=
λ X Y Y' S f g f' g' sq hg, hP sq.unop hg

lemma stable_under_cobase_change.unop {P : morphism_property Cᵒᵖ}
  (hP : stable_under_cobase_change P) : stable_under_base_change P.unop :=
λ X Y Y' S f g f' g' sq hg, hP sq.op hg

lemma stable_under_base_change.op {P : morphism_property C}
  (hP : stable_under_base_change P) : stable_under_cobase_change P.op :=
λ A A' B B' f g f' g' sq hf, hP sq.unop hf

lemma stable_under_base_change.unop {P : morphism_property Cᵒᵖ}
  (hP : stable_under_base_change P) : stable_under_cobase_change P.unop :=
λ A A' B B' f g f' g' sq hf, hP sq.op hf

/-- If `P : morphism_property C` and `F : C ⥤ D`, then
`P.is_inverted_by F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
def is_inverted_by (P : morphism_property C) (F : C ⥤ D) : Prop :=
∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P f), is_iso (F.map f)

namespace is_inverted_by

lemma of_comp {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃]
  (W : morphism_property C₁) (F : C₁ ⥤ C₂) (hF : W.is_inverted_by F) (G : C₂ ⥤ C₃) :
  W.is_inverted_by (F ⋙ G) :=
λ X Y f hf, by { haveI := hF f hf, dsimp, apply_instance, }

lemma op {W : morphism_property C} {L : C ⥤ D} (h : W.is_inverted_by L) :
  W.op.is_inverted_by L.op :=
λ X Y f hf, by { haveI := h f.unop hf, dsimp, apply_instance, }

lemma right_op {W : morphism_property C} {L : Cᵒᵖ ⥤ D} (h : W.op.is_inverted_by L) :
  W.is_inverted_by L.right_op :=
λ X Y f hf, by { haveI := h f.op hf, dsimp, apply_instance, }

lemma left_op {W : morphism_property C} {L : C ⥤ Dᵒᵖ} (h : W.is_inverted_by L) :
  W.op.is_inverted_by L.left_op :=
λ X Y f hf, by { haveI := h f.unop hf, dsimp, apply_instance, }

lemma unop {W : morphism_property C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.is_inverted_by L) :
  W.is_inverted_by L.unop :=
λ X Y f hf, by { haveI := h f.op hf, dsimp, apply_instance, }

end is_inverted_by

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def naturality_property {F₁ F₂ : C ⥤ D} (app : Π X, F₁.obj X ⟶ F₂.obj X) :
  morphism_property C := λ X Y f, F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturality_property

lemma is_stable_under_composition {F₁ F₂ : C ⥤ D} (app : Π X, F₁.obj X ⟶ F₂.obj X) :
  (naturality_property app).stable_under_composition := λ X Y Z f g hf hg,
begin
  simp only [naturality_property] at ⊢ hf hg,
  simp only [functor.map_comp, category.assoc, hg],
  slice_lhs 1 2 { rw hf },
  rw category.assoc,
end

lemma is_stable_under_inverse {F₁ F₂ : C ⥤ D} (app : Π X, F₁.obj X ⟶ F₂.obj X) :
  (naturality_property app).stable_under_inverse := λ X Y e he,
begin
  simp only [naturality_property] at ⊢ he,
  rw ← cancel_epi (F₁.map e.hom),
  slice_rhs 1 2 { rw he },
  simp only [category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp,
    e.hom_inv_id, functor.map_id, category.id_comp, category.comp_id],
end

end naturality_property

lemma respects_iso.inverse_image {P : morphism_property D} (h : respects_iso P) (F : C ⥤ D) :
  respects_iso (P.inverse_image F) :=
begin
  split,
  all_goals
  { intros X Y Z e f hf,
    dsimp [inverse_image],
    rw F.map_comp, },
  exacts [h.1 (F.map_iso e) (F.map f) hf, h.2 (F.map_iso e) (F.map f) hf],
end

lemma stable_under_composition.inverse_image {P : morphism_property D}
  (h : stable_under_composition P) (F : C ⥤ D) : stable_under_composition (P.inverse_image F) :=
λ X Y Z f g hf hg, by simpa only [← F.map_comp] using h (F.map f) (F.map g) hf hg

variable (C)

/-- The `morphism_property C` satisfied by isomorphisms in `C`. -/
def isomorphisms : morphism_property C := λ X Y f, is_iso f

/-- The `morphism_property C` satisfied by monomorphisms in `C`. -/
def monomorphisms : morphism_property C := λ X Y f, mono f

/-- The `morphism_property C` satisfied by epimorphisms in `C`. -/
def epimorphisms : morphism_property C := λ X Y f, epi f

section

variables {C} {X Y : C} (f : X ⟶ Y)

@[simp] lemma isomorphisms.iff : (isomorphisms C) f ↔ is_iso f := by refl
@[simp] lemma monomorphisms.iff : (monomorphisms C) f ↔ mono f := by refl
@[simp] lemma epimorphisms.iff : (epimorphisms C) f ↔ epi f := by refl

lemma isomorphisms.infer_property [hf : is_iso f] : (isomorphisms C) f := hf
lemma monomorphisms.infer_property [hf : mono f] : (monomorphisms C) f := hf
lemma epimorphisms.infer_property [hf : epi f] : (epimorphisms C) f := hf

end

lemma respects_iso.monomorphisms : respects_iso (monomorphisms C) :=
by { split; { intros X Y Z e f, simp only [monomorphisms.iff], introI, apply mono_comp, }, }

lemma respects_iso.epimorphisms : respects_iso (epimorphisms C) :=
by { split; { intros X Y Z e f, simp only [epimorphisms.iff], introI, apply epi_comp, }, }

lemma respects_iso.isomorphisms : respects_iso (isomorphisms C) :=
by { split; { intros X Y Z e f, simp only [isomorphisms.iff], introI, apply_instance, }, }

lemma stable_under_composition.isomorphisms : stable_under_composition (isomorphisms C) :=
λ X Y Z f g hf hg, begin
  rw isomorphisms.iff at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply_instance,
end

lemma stable_under_composition.monomorphisms : stable_under_composition (monomorphisms C) :=
λ X Y Z f g hf hg, begin
  rw monomorphisms.iff at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply mono_comp,
end

lemma stable_under_composition.epimorphisms : stable_under_composition (epimorphisms C) :=
λ X Y Z f g hf hg, begin
  rw epimorphisms.iff at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply epi_comp,
end

variable {C}

/-- The full subcategory of `C ⥤ D` consisting of functors inverting morphisms in `W` -/
@[derive category, nolint has_nonempty_instance]
def functors_inverting (W : morphism_property C) (D : Type*) [category D] :=
full_subcategory (λ (F : C ⥤ D), W.is_inverted_by F)

/-- A constructor for `W.functors_inverting D` -/
def functors_inverting.mk {W : morphism_property C} {D : Type*} [category D]
(F : C ⥤ D) (hF : W.is_inverted_by F) : W.functors_inverting D := ⟨F, hF⟩

lemma is_inverted_by.iff_of_iso (W : morphism_property C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) :
  W.is_inverted_by F₁ ↔ W.is_inverted_by F₂ :=
begin
  suffices : ∀ (X Y : C) (f : X ⟶ Y), is_iso (F₁.map f) ↔ is_iso (F₂.map f),
  { split,
    exact λ h X Y f hf, by { rw ← this, exact h f hf, },
    exact λ h X Y f hf, by { rw this, exact h f hf, }, },
  intros X Y f,
  exact (respects_iso.isomorphisms D).arrow_mk_iso_iff
    (arrow.iso_mk (e.app X) (e.app Y) (by simp)),
end

section diagonal

variables [has_pullbacks C] {P : morphism_property C}

/-- For `P : morphism_property C`, `P.diagonal` is a morphism property that holds for `f : X ⟶ Y`
whenever `P` holds for `X ⟶ Y xₓ Y`. -/
def diagonal (P : morphism_property C) : morphism_property C :=
λ X Y f, P (pullback.diagonal f)

lemma diagonal_iff {X Y : C} {f : X ⟶ Y} : P.diagonal f ↔ P (pullback.diagonal f) := iff.rfl

lemma respects_iso.diagonal (hP : P.respects_iso) : P.diagonal.respects_iso :=
begin
  split,
  { introv H,
    rwa [diagonal_iff, pullback.diagonal_comp, hP.cancel_left_is_iso, hP.cancel_left_is_iso,
      ← hP.cancel_right_is_iso _ _, ← pullback.condition, hP.cancel_left_is_iso],
    apply_instance },
  { introv H,
    delta diagonal,
    rwa [pullback.diagonal_comp, hP.cancel_right_is_iso] }
end

lemma stable_under_composition.diagonal
  (hP : stable_under_composition P) (hP' : respects_iso P) (hP'' : stable_under_base_change P) :
  P.diagonal.stable_under_composition :=
begin
  introv X h₁ h₂,
  rw [diagonal_iff, pullback.diagonal_comp],
  apply hP, { assumption },
  rw hP'.cancel_left_is_iso,
  apply hP''.snd,
  assumption
end

lemma stable_under_base_change.diagonal
  (hP : stable_under_base_change P) (hP' : respects_iso P) :
  P.diagonal.stable_under_base_change :=
stable_under_base_change.mk hP'.diagonal
begin
  introv h,
  rw [diagonal_iff, diagonal_pullback_fst, hP'.cancel_left_is_iso, hP'.cancel_right_is_iso],
  convert hP.base_change_map f _ _; simp; assumption
end

end diagonal

section universally

/-- `P.universally` holds for a morphism `f : X ⟶ Y` iff `P` holds for all `X ×[Y] Y' ⟶ Y'`. -/
def universally (P : morphism_property C) : morphism_property C :=
λ X Y f, ∀ ⦃X' Y' : C⦄ (i₁ : X' ⟶ X) (i₂ : Y' ⟶ Y) (f' : X' ⟶ Y')
  (h : is_pullback f' i₁ i₂ f), P f'

lemma universally_respects_iso (P : morphism_property C) :
  P.universally.respects_iso :=
begin
  constructor,
  { intros X Y Z e f hf X' Z' i₁ i₂ f' H,
    have : is_pullback (𝟙 _) (i₁ ≫ e.hom) i₁ e.inv := is_pullback.of_horiz_is_iso
      ⟨by rw [category.id_comp, category.assoc, e.hom_inv_id, category.comp_id]⟩,
    replace this := this.paste_horiz H,
    rw [iso.inv_hom_id_assoc, category.id_comp] at this,
    exact hf _ _ _ this },
  { intros X Y Z e f hf X' Z' i₁ i₂ f' H,
    have : is_pullback (𝟙 _) i₂ (i₂ ≫ e.inv) e.inv :=
      is_pullback.of_horiz_is_iso ⟨category.id_comp _⟩,
    replace this := H.paste_horiz this,
    rw [category.assoc, iso.hom_inv_id, category.comp_id, category.comp_id] at this,
    exact hf _ _ _ this },
end

lemma universally_stable_under_base_change (P : morphism_property C) :
  P.universally.stable_under_base_change :=
λ X Y Y' S f g f' g' H h₁ Y'' X'' i₁ i₂ f'' H', h₁ _ _ _ (H'.paste_vert H.flip)

lemma stable_under_composition.universally [has_pullbacks C]
  {P : morphism_property C} (hP : P.stable_under_composition) :
  P.universally.stable_under_composition :=
begin
  intros X Y Z f g hf hg X' Z' i₁ i₂ f' H,
  have := pullback.lift_fst _ _ (H.w.trans (category.assoc _ _ _).symm),
  rw ← this at H ⊢,
  apply hP _ _ _ (hg _ _ _ $ is_pullback.of_has_pullback _ _),
  exact hf _ _ _ (H.of_right (pullback.lift_snd _ _ _) (is_pullback.of_has_pullback i₂ g))
end

lemma universally_le (P : morphism_property C) :
  P.universally ≤ P :=
begin
  intros X Y f hf,
  exact hf (𝟙 _) (𝟙 _) _ (is_pullback.of_vert_is_iso ⟨by rw [category.comp_id, category.id_comp]⟩)
end

lemma stable_under_base_change.universally_eq
  {P : morphism_property C} (hP : P.stable_under_base_change) :
  P.universally = P :=
P.universally_le.antisymm $ λ X Y f hf X' Y' i₁ i₂ f' H, hP H.flip hf

lemma universally_mono : monotone (universally : morphism_property C → morphism_property C) :=
λ P₁ P₂ h X Y f h₁ X' Y' i₁ i₂ f' H, h _ _ _ (h₁ _ _ _ H)

end universally

section bijective

variables [concrete_category C]

open function

local attribute [instance] concrete_category.has_coe_to_fun concrete_category.has_coe_to_sort

variable (C)

/-- Injectiveness (in a concrete category) as a `morphism_property` -/
protected def injective : morphism_property C := λ X Y f, injective f

/-- Surjectiveness (in a concrete category) as a `morphism_property` -/
protected def surjective : morphism_property C := λ X Y f, surjective f

/-- Bijectiveness (in a concrete category) as a `morphism_property` -/
protected def bijective : morphism_property C := λ X Y f, bijective f

lemma bijective_eq_sup : morphism_property.bijective C =
  morphism_property.injective C ⊓ morphism_property.surjective C :=
rfl

lemma injective_stable_under_composition :
  (morphism_property.injective C).stable_under_composition :=
λ X Y Z f g hf hg, by { delta morphism_property.injective, rw coe_comp, exact hg.comp hf }

lemma surjective_stable_under_composition :
  (morphism_property.surjective C).stable_under_composition :=
λ X Y Z f g hf hg, by { delta morphism_property.surjective, rw coe_comp, exact hg.comp hf }

lemma bijective_stable_under_composition :
  (morphism_property.bijective C).stable_under_composition :=
λ X Y Z f g hf hg, by { delta morphism_property.bijective, rw coe_comp, exact hg.comp hf }

lemma injective_respects_iso :
  (morphism_property.injective C).respects_iso :=
(injective_stable_under_composition C).respects_iso
  (λ X Y e, ((forget C).map_iso e).to_equiv.injective)

lemma surjective_respects_iso :
  (morphism_property.surjective C).respects_iso :=
(surjective_stable_under_composition C).respects_iso
  (λ X Y e, ((forget C).map_iso e).to_equiv.surjective)

lemma bijective_respects_iso :
  (morphism_property.bijective C).respects_iso :=
(bijective_stable_under_composition C).respects_iso
  (λ X Y e, ((forget C).map_iso e).to_equiv.bijective)

end bijective

end morphism_property

end category_theory
