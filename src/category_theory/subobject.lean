/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.over
import category_theory.thin
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.zero
import category_theory.isomorphism_classes

/-!
## Subobjects in a category.

We define `subobject X` as the (isomorphism classes of) monomorphisms into `X`.
This is naturally a preorder.

When the ambient category has pullbacks, `subobject X` has an intersection operation,
and becomes a `semilattice_inf`.
-/

universes v u

noncomputable theory

namespace category_theory

variables {C : Type u} [category.{v} C]

/-- The category of monomorphisms into `X` is "thin", i.e. a preorder. -/
instance {X : C} (A B : { f : over X // mono f.hom }) : subsingleton (A ⟶ B) :=
begin
  fsplit,
  rintros ⟨f, _, wf⟩ ⟨g, _, wg⟩,
  dsimp at *, simp at wf wg, ext, dsimp,
  exact (@cancel_mono _ _ _ _ _ _ B.property _ _).mp (wf.trans (wg.symm)),
end

/--
We define the subobjects of `X` simply to be the isomorphism classes of monomorphisms into `X`.
See https://ncatlab.org/nlab/show/subobject

One could instead just take the monomorphisms directly: not much changes!
See https://mathoverflow.net/questions/184196/concise-definition-of-subobjects
However if we follow this route we only get a preorder, not a partial order,
which is less convenient for describing lattice properties.
-/
def subobject (X : C) := isomorphism_classes.obj (Cat.of { f : over X // mono f.hom })

namespace subobject

/-- Construct a subobject from an explicit monomorphism. -/
def mk {X Y : C} (f : X ⟶ Y) [w : mono f] : subobject Y :=
quot.mk _ ⟨over.mk f, w⟩

instance (X : C) : inhabited (subobject X) := ⟨mk (𝟙 _)⟩

/-- The underlying object of a subobject. -/
def X {X : C} (A : subobject X) : C :=
(isomorphism_classes.representative A).val.left

/-- The inclusion of a subobject into the ambient object. -/
def ι {X : C} (A : subobject X) : A.X ⟶ X :=
(isomorphism_classes.representative A).val.hom

instance {X : C} (A : subobject X) : mono (ι A) :=
(isomorphism_classes.representative A).property

/-- The underlying object of the subobject constructed from an explicit monomorphism is isomorphic
to the original source object. -/
def mk_X_iso {X Y : C} (f : X ⟶ Y) [w : mono f] : (mk f).X ≅ X :=
(over.forget Y).map_iso
  ((full_subcategory_inclusion _).map_iso
  (@isomorphism_classes.mk_representative_iso (Cat.of { f : over Y // mono f.hom }) ⟨over.mk f, w⟩))

@[simp]
lemma mk_X_iso_hom_comm {X Y : C} (f : X ⟶ Y) [w : mono f] :
  (mk_X_iso f).hom ≫ f = (mk f).ι :=
begin
  have h := ((full_subcategory_inclusion _).map_iso
    (@isomorphism_classes.mk_representative_iso (Cat.of { f : over Y // mono f.hom })
      ⟨over.mk f, w⟩)).hom.w,
  dsimp at h,
  simpa only [category.comp_id] using h,
end

@[simp]
lemma mk_X_iso_id_hom {X : C} : (mk_X_iso (𝟙 X)).hom = (mk (𝟙 X)).ι :=
by rw [←mk_X_iso_hom_comm, category.comp_id]

@[simp]
lemma mk_X_iso_inv_comm {X Y : C} (f : X ⟶ Y) [w : mono f] :
  (mk_X_iso f).inv ≫ (mk f).ι = f :=
by simp [iso.inv_comp_eq]

/--
The preorder on subobjects of `X` is `(A,f) ≤ (B,g)`
if there exists a morphism `h : A ⟶ B` so `h ≫ g = f`.
(Such a morphism is unique if it exists; in a moment we upgrade this to a `partial_order`.)
-/
instance (X : C) : preorder (subobject X) :=
{ le := λ A B,
  nonempty (isomorphism_classes.representative A ⟶ isomorphism_classes.representative B),
  le_refl := λ A, ⟨𝟙 _⟩,
  le_trans := λ A B C, by { rintro ⟨f⟩, rintro ⟨g⟩, exact ⟨f ≫ g⟩, }, }

/--
Construct an inequality in the preorder on subobjects from an explicit morphism.
-/
lemma le_of_hom {X : C} {A B : subobject X} (f : A.X ⟶ B.X) (w : f ≫ B.ι = A.ι) : A ≤ B :=
nonempty.intro (over.hom_mk f w)

/-- Construct a morphism between the underlying objects from an inequality between subobjects. -/
def hom_of_le {X : C} {A B : subobject X} (h : A ≤ B) : A.X ⟶ B.X :=
comma_morphism.left (nonempty.some h)

@[simp]
lemma hom_of_le_comm {X : C} {A B : subobject X} (h : A ≤ B) :
  subobject.hom_of_le h ≫ B.ι = A.ι :=
begin
  have := (nonempty.some h).w,
  simp only [functor.id_map, functor.const.obj_map] at this,
  dsimp at this,
  simp only [category.comp_id] at this,
  exact this,
end

instance (X : C) : partial_order (subobject X) :=
{ le_antisymm := λ A B h₁ h₂,
  begin
    induction A,
    swap, refl,
    rcases A with ⟨⟨A, ⟨⟩, f⟩, w₁⟩,
    induction B,
    swap, refl,
    rcases B with ⟨⟨B, ⟨⟩, g⟩, w₂⟩,
    dsimp at A f w₁ B g w₂,
    resetI,
    apply quot.sound,
    fsplit,
    apply iso_of_both_ways,
    { fsplit,
      { exact (mk_X_iso f).inv ≫ hom_of_le h₁ ≫ (mk_X_iso g).hom, },
      { exact ⟨⟨rfl⟩⟩ },
      { dsimp,
        rw [category.comp_id, category.assoc, (mk_X_iso f).inv_comp_eq, category.assoc],
        erw [mk_X_iso_hom_comm, mk_X_iso_hom_comm, hom_of_le_comm], }, },
    { fsplit,
      { exact (mk_X_iso g).inv ≫ hom_of_le h₂ ≫ (mk_X_iso f).hom, },
      { exact ⟨⟨rfl⟩⟩ },
      { dsimp,
        rw [category.comp_id, category.assoc, (mk_X_iso g).inv_comp_eq, category.assoc],
        erw [mk_X_iso_hom_comm, mk_X_iso_hom_comm, hom_of_le_comm], }, },
  end,
  ..(by apply_instance : preorder (subobject X)) }

open category_theory.limits

section has_top
variables (W : C)

instance : has_top (subobject W) :=
{ top := mk (𝟙 W), }

@[simp] lemma top_ι : (⊤ : subobject W).ι = (mk_X_iso (𝟙 W)).hom :=
by { simp, refl, }

variables {W}

lemma le_top (X : subobject W) : X ≤ ⊤ :=
le_of_hom (X.ι ≫ (mk_X_iso (𝟙 W)).inv) (by simp)

end has_top

section has_bot
variables (W : C)
variables [has_zero_object C] [has_zero_morphisms C]
local attribute [instance] has_zero_object.has_zero

instance : has_bot (subobject W) :=
{ bot := mk (0 : 0 ⟶ W) }

@[simp] lemma bot_ι : (⊥ : subobject W).ι = 0 :=
by { erw [←mk_X_iso_hom_comm, comp_zero], }

variables {W}

lemma bot_le (X : subobject W) : ⊥ ≤ X :=
le_of_hom 0 (by simp)

end has_bot

section semilattice_inf
variables [has_pullbacks C] (W : C)

instance : has_inf (subobject W) :=
{ inf := λ A B,
  @mk _ _ _ W (@pullback.fst _ _ _ _ _ A.ι B.ι _ ≫ A.ι) (mono_comp _ _) }

local attribute [instance] mono_comp

lemma le_inf (X Y Z : subobject W) (f : X ≤ Y) (g : X ≤ Z) : X ≤ Y ⊓ Z :=
le_of_hom (pullback.lift (hom_of_le f) (hom_of_le g) (by simp) ≫ (mk_X_iso _).inv)
  (by { slice_lhs 2 3 { erw mk_X_iso_inv_comm _, }, simp })

lemma inf_le_left (X Y : subobject W) : X ⊓ Y ≤ X :=
le_of_hom ((mk_X_iso _).hom ≫ pullback.fst) (by { simp, refl, })

lemma inf_le_right (X Y : subobject W) : X ⊓ Y ≤ Y :=
le_of_hom ((mk_X_iso _).hom ≫ pullback.snd)
  (by { rw [category.assoc, ←pullback.condition], simp, refl, })

instance : semilattice_inf (subobject W) :=
{ le_inf := le_inf W,
  inf_le_left := inf_le_left W,
  inf_le_right := inf_le_right W,
  ..(by apply_instance : partial_order (subobject W)),
  ..(by apply_instance : has_inf (subobject W)) }

end semilattice_inf

section
variables [has_coproducts C] [has_images C] (W : C)

instance : has_sup (subobject W) :=
{ sup := λ A B, mk (image.ι (coprod.desc A.ι B.ι)), }

variables [has_image_maps C]

lemma le_sup_left (X Y : subobject W) : X ≤ X ⊔ Y :=
le_of_hom
  ((factor_thru_image coprod.inl ≫ image.map_composable coprod.inl (coprod.desc X.ι Y.ι)) ≫
    (mk_X_iso (image.ι _)).inv)
  (by { slice_lhs 3 4 { erw mk_X_iso_inv_comm, }, simp, })

lemma le_sup_right (X Y : subobject W) : Y ≤ X ⊔ Y :=
le_of_hom
  ((factor_thru_image coprod.inr ≫ image.map_composable coprod.inr (coprod.desc X.ι Y.ι)) ≫
    (mk_X_iso (image.ι _)).inv)
  (by { slice_lhs 3 4 { erw mk_X_iso_inv_comm, }, simp, })

variables [has_equalizers C]

lemma sup_le (X Y Z : subobject W) (f : X ≤ Z) (g : Y ≤ Z) : X ⊔ Y ≤ Z :=
le_of_hom
((mk_X_iso _).hom ≫
  image.eq_to_hom
    (show coprod.desc X.ι Y.ι = coprod.desc (hom_of_le f) (hom_of_le g) ≫ Z.ι, by simp) ≫
  image.lift { I := Z.X, m := Z.ι, e := coprod.desc (hom_of_le f) (hom_of_le g) })
(begin
  dsimp,
  rw [category.assoc, category.assoc, image.lift_fac, ←(mk_X_iso _).eq_inv_comp],
  erw [mk_X_iso_inv_comm, ←image.eq_fac],
end)

instance : semilattice_sup (subobject W) :=
{ sup_le := sup_le W,
  le_sup_left := le_sup_left W,
  le_sup_right := le_sup_right W,
  ..(by apply_instance : partial_order (subobject W)),
  ..(by apply_instance : has_sup (subobject W)) }

end

-- PROJECT: Further lattice structures on `subobject W`.
-- What conditions are required to get a distributive lattice?
--   https://ncatlab.org/nlab/show/poset+of+subobjects
--   says any "coherent category" (including any pretopos)
-- What about in the abelian direction?

end subobject

end category_theory
