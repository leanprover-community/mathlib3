/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.over
import category_theory.currying

universes v u u₂

namespace category_theory
namespace limits

open category

variables {C : Type u} [category.{v} C] [has_binary_coproducts C]

@[simps]
noncomputable def over_coproduct (A B : C) :
  over A × over B ⥤ over (A ⨿ B) :=
{ obj := λ t, over.mk (coprod.map t.1.hom t.2.hom),
  map := λ t₁ t₂ k, over.hom_mk (coprod.map k.1.left k.2.left) }

class extensive (C : Type u) [category.{v} C] [has_binary_coproducts C] :=
(coprod_equiv (A B : C) : is_equivalence (over_coproduct A B))

attribute [instance] extensive.coprod_equiv

/-- The flip of a coproduct diagram is a coproduct diagram. -/
def flip_is_colimit {A₁ A₂ B : C} {pA₁ : A₁ ⟶ B} {pA₂ : A₂ ⟶ B}
  (t : is_colimit (binary_cofan.mk pA₁ pA₂)) :
  is_colimit (binary_cofan.mk pA₂ pA₁) :=
{ desc := λ (s : binary_cofan _ _), t.desc (binary_cofan.mk s.inr s.inl),
  fac' := λ (s : binary_cofan _ _) j,
  begin
    rcases j with _ | _,
    { apply t.fac _ walking_pair.right },
    { apply t.fac _ walking_pair.left },
  end,
  uniq' := λ (s : binary_cofan _ _) m w,
  begin
    refine t.uniq (binary_cofan.mk _ _) _ _,
    rintro (_ | _),
    { apply w walking_pair.right },
    { apply w walking_pair.left },
  end }

variables {X₁ X₂ X A₁ A₂ A : C}

/--
  A₁  → A ←  A₂
  ↓     ↓    ↓
  X₁  → X ←  X₂

In an extensive category, if both rows are coproducts then both squares are pullbacks.
-/
noncomputable def left_pullback_of_coproduct_of_coproduct [extensive C]
  {pA₁ : A₁ ⟶ A} {pA₂ : A₂ ⟶ A} (cA : is_colimit (binary_cofan.mk pA₁ pA₂))
  {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} (cX : is_colimit (binary_cofan.mk pX₁ pX₂))
  (f₁ : A₁ ⟶ X₁) (f₂ : A₂ ⟶ X₂) (f : A ⟶ X)
  (c₁ : f₁ ≫ pX₁ = pA₁ ≫ f)
  (c₂ : f₂ ≫ pX₂ = pA₂ ≫ f) :
  is_limit (pullback_cone.mk _ _ c₁) :=
pullback_cone.is_limit_aux' _ $ λ s,
begin
  dsimp,
  let f' : over X₁ × over X₂ := (over.mk f₁, over.mk f₂),
  let g : over X₁ × over X₂ := (over.mk s.fst, over.mk f₂),
  let iA : A ≅ _ ⨿ _ := cA.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  let iX : X ≅ _ ⨿ _ := cX.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  have iA₁ : pA₁ ≫ iA.hom = coprod.inl :=
    cA.comp_cocone_point_unique_up_to_iso_hom _ walking_pair.left,
  have iA₂ : pA₂ ≫ iA.hom = coprod.inr :=
    cA.comp_cocone_point_unique_up_to_iso_hom _ walking_pair.right,
  have iX₁ : pX₁ ≫ iX.hom = coprod.inl :=
    cX.comp_cocone_point_unique_up_to_iso_hom _ walking_pair.left,
  have iX₂ : pX₂ ≫ iX.hom = coprod.inr :=
    cX.comp_cocone_point_unique_up_to_iso_hom _ walking_pair.right,
  have : iA.hom ≫ coprod.map f₁ f₂ = f ≫ iX.hom,
  { apply binary_cofan.is_colimit.hom_ext cA,
    { change pA₁ ≫ _ ≫ _ = pA₁ ≫ _ ≫ _,
      rw [reassoc_of iA₁, coprod.inl_map, ←reassoc_of c₁, iX₁] },
    { change pA₂ ≫ _ ≫ _ = pA₂ ≫ _ ≫ _,
      rw [reassoc_of iA₂, coprod.inr_map, ←reassoc_of c₂, iX₂] } },
  let z : (over_coproduct _ _).obj g ⟶ (over_coproduct _ _).obj f',
  { apply over.hom_mk _ _,
    apply coprod.desc (s.snd ≫ iA.hom) coprod.inr,
    change coprod.desc (s.snd ≫ iA.hom) coprod.inr ≫ coprod.map f₁ f₂ = coprod.map s.fst f₂,
    simp [this, ←s.condition_assoc, iX₁] },
  let t := functor.preimage _ z,
  have ht₁ : t.1.left ≫ f₁ = s.fst := over.w t.1,
  have ht : coprod.map _ _ = coprod.desc (s.snd ≫ iA.hom) coprod.inr :=
    congr_arg comma_morphism.left (functor.image_preimage _ z),
  have ht₃ := coprod.inl ≫= ht,
  dsimp at ht₃,
  simp only [coprod.map_map, coprod.inr_desc, coprod.inl_desc, coprod.inl_map, coprod.inr_map,
    assoc, id_comp, comp_id] at ht₃,
  refine ⟨t.1.left, ht₁, by simpa [←iA₁, ←iA.comp_inv_eq] using ht₃, _⟩,
  intros m m₁ m₂,
  let m' : g ⟶ f' := ⟨over.hom_mk m m₁, 𝟙 _⟩,
  suffices : m' = t,
  { rw ←this,
    refl },
  apply functor.map_injective (over_coproduct X₁ X₂),
  rw functor.image_preimage _ z,
  ext : 1,
  dsimp,
  rw [←m₂, assoc, iA₁],
  ext;
  simp
end

/--
  A₁  → A ←  A₂
  ↓     ↓    ↓
  X₁  → X ←  X₂

In an extensive category, if both rows are coproducts then both squares are pullbacks.
-/
noncomputable def right_pullback_of_coproduct_of_coproduct [extensive C]
  {pA₁ : A₁ ⟶ A} {pA₂ : A₂ ⟶ A} (cA : is_colimit (binary_cofan.mk pA₁ pA₂))
  {pX₁ : X₁ ⟶ X} {pX₂ : X₂ ⟶ X} (cX : is_colimit (binary_cofan.mk pX₁ pX₂))
  (f₁ : A₁ ⟶ X₁) (f₂ : A₂ ⟶ X₂) (f : A ⟶ X)
  (c₁ : f₁ ≫ pX₁ = pA₁ ≫ f)
  (c₂ : f₂ ≫ pX₂ = pA₂ ≫ f) :
  is_limit (pullback_cone.mk _ _ c₂) :=
left_pullback_of_coproduct_of_coproduct (flip_is_colimit cA) (flip_is_colimit cX) f₂ f₁ f c₂ c₁

def ess_surj_over_coproduct [extensive C] : ess_surj (over_coproduct X₁ X₂) :=
equivalence.ess_surj_of_equivalence _

local attribute [instance] ess_surj_over_coproduct

namespace extensive_internal

noncomputable def over_isomorphism [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  over X₁ × over X₂ :=
(over_coproduct X₁ X₂).obj_preimage
  (over.mk (f ≫ (cX.cocone_point_unique_up_to_iso (colimit.is_colimit _)).hom))

noncomputable def pullback_along_inl [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) : C :=
(over_isomorphism cX f).1.left

noncomputable def pullback_along_inr [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) : C :=
(over_isomorphism cX f).2.left

noncomputable def pullback_fst_along_inl [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) : pullback_along_inl cX f ⟶ X₁ :=
(over_isomorphism cX f).1.hom

noncomputable def pullback_fst_along_inr [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) : pullback_along_inr cX f ⟶ X₂ :=
(over_isomorphism cX f).2.hom

noncomputable def pullback_coprod_pullback_iso [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  pullback_along_inl cX f ⨿ pullback_along_inr cX f ≅ A :=
(over.forget _).map_iso ((over_coproduct X₁ X₂).obj_obj_preimage_iso (over.mk _))

noncomputable def pullback_snd_along_inl [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) : pullback_along_inl cX f ⟶ A :=
coprod.inl ≫ (pullback_coprod_pullback_iso cX f).hom

noncomputable def pullback_snd_along_inr [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) : pullback_along_inr cX f ⟶ A :=
coprod.inr ≫ (pullback_coprod_pullback_iso cX f).hom

noncomputable def is_coproduct_snd_snd [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  is_colimit (binary_cofan.mk (pullback_snd_along_inl cX f) (pullback_snd_along_inr cX f)) :=
(colimit.is_colimit _).of_iso_colimit
  (cocones.ext (pullback_coprod_pullback_iso cX f) (by rintro (_ | _); refl))

lemma pullback_condition_along_inl [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  pullback_fst_along_inl cX f ≫ x₁ = pullback_snd_along_inl cX f ≫ f :=
begin
  let iX := cX.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  have iX₁ : x₁ ≫ iX.hom = coprod.inl :=
    cX.comp_cocone_point_unique_up_to_iso_hom _ walking_pair.left,
  have hiA :
    (pullback_coprod_pullback_iso cX f).hom ≫ _ ≫ iX.hom =
      coprod.map (pullback_fst_along_inl _ _) (pullback_fst_along_inr _ _) :=
    over.w ((over_coproduct X₁ X₂).obj_obj_preimage_iso (over.mk _)).hom,
  have : _ ≫ _ ≫ _ ≫ _ = _ := coprod.inl ≫= hiA,
  simp only [coprod.inl_map, ←iX₁] at this,
  rw [←iX.cancel_iso_hom_right _ _, assoc, ←this, assoc, pullback_snd_along_inl, assoc],
end

lemma pullback_condition_along_inr [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  pullback_fst_along_inr cX f ≫ x₂ = pullback_snd_along_inr cX f ≫ f :=
begin
  let iX := cX.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  have iX₂ : x₂ ≫ iX.hom = coprod.inr :=
    cX.comp_cocone_point_unique_up_to_iso_hom _ walking_pair.right,
  have hiA :
    (pullback_coprod_pullback_iso cX f).hom ≫ _ ≫ iX.hom =
      coprod.map (pullback_fst_along_inl _ _) (pullback_fst_along_inr _ _) :=
    over.w ((over_coproduct X₁ X₂).obj_obj_preimage_iso (over.mk _)).hom,
  have : _ ≫ _ ≫ _ ≫ _ = _ := coprod.inr ≫= hiA,
  simp only [coprod.inr_map, ←iX₂] at this,
  rw [←iX.cancel_iso_hom_right _ _, assoc, ←this, assoc, pullback_snd_along_inr, assoc],
end

noncomputable def is_pullback_along_inl [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  is_limit (pullback_cone.mk _ _ (pullback_condition_along_inl cX f)) :=
left_pullback_of_coproduct_of_coproduct
  (is_coproduct_snd_snd cX f) cX _ _ _ _ (pullback_condition_along_inr cX f)

noncomputable def is_pullback_along_inr [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  is_limit (pullback_cone.mk _ _ (pullback_condition_along_inr cX f)) :=
right_pullback_of_coproduct_of_coproduct
  (is_coproduct_snd_snd cX f) cX _ _ _ (pullback_condition_along_inl cX f) _

end extensive_internal

open extensive_internal

def has_pullback_along_is_inl [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  has_pullback x₁ f :=
has_limit.mk ⟨_, is_pullback_along_inl cX f⟩

def has_pullback_along_is_inr [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  has_pullback x₂ f :=
has_limit.mk ⟨_, is_pullback_along_inr cX f⟩

def has_pullback_along_is_inl' [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  has_pullback f x₁ :=
has_limit.mk ⟨pullback_cone.mk _ _ (pullback_condition_along_inl cX f).symm,
  pullback_cone.flip_is_limit (is_pullback_along_inl cX f)⟩

def has_pullback_along_is_inr' [extensive C] {x₁ : X₁ ⟶ X} {x₂ : X₂ ⟶ X}
  (cX : is_colimit (binary_cofan.mk x₁ x₂)) (f : A ⟶ X) :
  has_pullback f x₂ :=
has_limit.mk ⟨pullback_cone.mk _ _ (pullback_condition_along_inr cX f).symm,
  pullback_cone.flip_is_limit (is_pullback_along_inr cX f)⟩

instance has_pullback_along_inl [extensive C] (f : A ⟶ X₁ ⨿ X₂) : has_pullback coprod.inl f :=
has_pullback_along_is_inl (coprod_is_coprod _ _) f
instance has_pullback_along_inr [extensive C] (f : A ⟶ X₁ ⨿ X₂) : has_pullback coprod.inr f :=
has_pullback_along_is_inr (coprod_is_coprod _ _) f
instance has_pullback_along_inl' [extensive C] (f : A ⟶ X₁ ⨿ X₂) : has_pullback f coprod.inl :=
has_pullback_along_is_inl' (coprod_is_coprod _ _) f
instance has_pullback_along_inr' [extensive C] (f : A ⟶ X₁ ⨿ X₂) : has_pullback f coprod.inr :=
has_pullback_along_is_inr' (coprod_is_coprod _ _) f

noncomputable def coproduct_of_both_pullback [extensive C]
  (a₁ : A₁ ⟶ A) (a₂ : A₂ ⟶ A)
  (x₁ : X₁ ⟶ X) (x₂ : X₂ ⟶ X) (cX : is_colimit (binary_cofan.mk x₁ x₂))
  (f₁ : A₁ ⟶ X₁) (f₂ : A₂ ⟶ X₂) (f : A ⟶ X)
  (c₁ : f₁ ≫ x₁ = a₁ ≫ f) (c₂ : f₂ ≫ x₂ = a₂ ≫ f)
  (hc₁ : is_limit (pullback_cone.mk _ _ c₁)) (hc₂ : is_limit (pullback_cone.mk _ _ c₂)) :
  is_colimit (binary_cofan.mk a₁ a₂) :=
begin
  let iA₁ : A₁ ≅ pullback_along_inl _ _ :=
    hc₁.cone_point_unique_up_to_iso (is_pullback_along_inl cX _),
  let iA₂ : A₂ ≅ pullback_along_inr _ _ :=
    hc₂.cone_point_unique_up_to_iso (is_pullback_along_inr cX _),
  have ha₁ : iA₁.hom ≫ pullback_snd_along_inl cX f = a₁ :=
    hc₁.cone_point_unique_up_to_iso_hom_comp _ walking_cospan.right,
  have ha₂ : iA₂.hom ≫ pullback_snd_along_inr cX f = a₂ :=
    hc₂.cone_point_unique_up_to_iso_hom_comp _ walking_cospan.right,
  refine ⟨λ (s : binary_cofan _ _),
            (is_coproduct_snd_snd cX f).desc
              (binary_cofan.mk (iA₁.inv ≫ s.inl) (iA₂.inv ≫ s.inr)), _, _⟩,
  { rintro (s : binary_cofan _ _) (_ | _),
    { change a₁ ≫ _ = s.inl,
      have : pullback_snd_along_inl cX f ≫ _ = _ ≫ _ :=
        (is_coproduct_snd_snd cX f).fac (binary_cofan.mk (iA₁.inv ≫ s.inl) _) walking_pair.left,
      rw [←ha₁, assoc, this, iso.hom_inv_id_assoc] },
    { change a₂ ≫ _ = s.inr,
      have : pullback_snd_along_inr cX f ≫ _ = _ ≫ _ :=
        (is_coproduct_snd_snd cX f).fac (binary_cofan.mk _ (iA₂.inv ≫ s.inr)) walking_pair.right,
      rw [←ha₂, assoc, this, iso.hom_inv_id_assoc] } },
  { rintro (s : binary_cofan _ _) m w,
    refine (is_coproduct_snd_snd cX f).uniq
        (binary_cofan.mk (iA₁.inv ≫ s.inl) (iA₂.inv ≫ s.inr)) _ _,
    rintro (_ | _),
    { change pullback_snd_along_inl cX f ≫ m = _ ≫ _,
      rw [iA₁.eq_inv_comp, ←assoc, ha₁],
      exact w walking_pair.left },
    { change pullback_snd_along_inr cX f ≫ m = _ ≫ _,
      rw [iA₂.eq_inv_comp, ←assoc, ha₂],
      exact w walking_pair.right } }
end

noncomputable def extensive_of_pullbacks_equiv_coproduct
  (i : ∀ (A X₁ X₂ : C) (f : A ⟶ X₁ ⨿ X₂), has_pullback coprod.inl f)
  (h : ∀ (A₁ A₂ A X₁ X₂ : C)
    (pA₁ : A₁ ⟶ A) (pA₂ : A₂ ⟶ A) (f₁ : A₁ ⟶ X₁) (f₂ : A₂ ⟶ X₂) (f : A ⟶ X₁ ⨿ X₂)
    (c₁ : f₁ ≫ coprod.inl = pA₁ ≫ f) (c₂ : f₂ ≫ coprod.inr = pA₂ ≫ f),
    is_colimit (binary_cofan.mk pA₁ pA₂) ≃
      is_limit (pullback_cone.mk _ _ c₁) × is_limit (pullback_cone.mk _ _ c₂)) :
  extensive C :=
begin
  constructor,
  have : ∀ (A X₁ X₂ : C) (f : A ⟶ X₁ ⨿ X₂), has_pullback coprod.inr f,
  { intros A X₁ X₂ f,
    let P := pullback coprod.inl (f ≫ (coprod.braiding _ _).hom),
    refine has_limit.mk ⟨pullback_cone.mk (pullback.fst : P ⟶ _) pullback.snd _, _⟩,
    { rw [←(coprod.braiding _ _).cancel_iso_hom_right _ _, assoc, assoc, ←pullback.condition],
      simp },
    refine pullback_cone.is_limit.mk _ (λ s, pullback.lift s.fst s.snd _)
      (λ s, pullback.lift_fst _ _ _) (λ s, pullback.lift_snd _ _ _) _,
    { intro s,
      rw ←s.condition_assoc,
      simp },
    { intros s m m₁ m₂,
      apply pullback.hom_ext;
      simp [m₁, m₂] } },
  introsI X₁ X₂,
  apply equivalence.of_fully_faithfully_ess_surj _,
  { refine ⟨λ f g t, _, _⟩,
    let c :=
      h g.1.left g.2.left _ X₁ X₂ coprod.inl coprod.inr g.1.hom g.2.hom (coprod.map g.1.hom g.2.hom)
        (by simp) (by simp) (coprod_is_coprod _ _),
    have : t.left ≫ coprod.map _ _ = coprod.map _ _ := over.w t,
    refine
      ⟨over.hom_mk _
        (pullback_cone.is_limit.lift' c.1 f.1.hom (coprod.inl ≫ t.left) (by simp [this])).2.1,
       over.hom_mk _
        (pullback_cone.is_limit.lift' c.2 f.2.hom (coprod.inr ≫ t.left) (by simp [this])).2.1⟩,
    intros f g t,
    ext : 2,
    { dsimp,
      simp only [coprod.inl_map],
      exact (pullback_cone.is_limit.lift' _ f.1.hom (coprod.inl ≫ t.left) _).2.2 },
    { dsimp,
      simp only [coprod.inr_map],
      exact (pullback_cone.is_limit.lift' _ f.2.hom (coprod.inr ≫ t.left) _).2.2 } },
  { refine ⟨_⟩,
    rintro ⟨g₁, g₂⟩ ⟨f₁, f₂⟩ ⟨k₁ : g₁ ⟶ f₁, k₂ : g₂ ⟶ f₂⟩ ⟨l₁ : g₁ ⟶ f₁, l₂ : g₂ ⟶ f₂⟩ t,
    replace t := congr_arg comma_morphism.left t,
    simp only [over_coproduct_map, over.hom_mk_left] at t,
    simp only [prod.mk.inj_iff],
    obtain ⟨c₁, c₂⟩ :=
      h f₁.left f₂.left _ X₁ X₂ coprod.inl coprod.inr f₁.hom f₂.hom (coprod.map f₁.hom f₂.hom)
        (by simp) (by simp) (coprod_is_coprod _ _),
    split,
    { ext,
      apply pullback_cone.is_limit.hom_ext c₁,
      { rw [pullback_cone.mk_fst, over.w k₁, over.w l₁] },
      { rw [pullback_cone.mk_snd, ←coprod.inl_map, t, coprod.inl_map] } },
    { ext,
      apply pullback_cone.is_limit.hom_ext c₂,
      { rw [pullback_cone.mk_fst, over.w k₂, over.w l₂] },
      { rw [pullback_cone.mk_snd, ←coprod.inr_map, t, coprod.inr_map] } } },
  { refine ⟨λ Y, ⟨⟨_, _⟩, ⟨_⟩⟩⟩,
    { apply over.mk (pullback.fst : pullback coprod.inl Y.hom ⟶ X₁) },
    { apply over.mk (pullback.fst : pullback coprod.inr Y.hom ⟶ X₂) },
    let c := (h _ _ _ _ _ _ _ _ _ Y.hom _ _).symm
                ⟨pullback_is_pullback _ _, pullback_is_pullback _ _⟩,
    let j : Y.left ≅ _ ⨿ _ := c.cocone_point_unique_up_to_iso (colimit.is_colimit _),
    refine over.iso_mk _ _,
    refine j.symm,
    ext,
    { dsimp,
      rw [colimit.comp_cocone_point_unique_up_to_iso_inv_assoc, coprod.inl_map, pullback.condition],
      refl },
    { dsimp,
      rw [colimit.comp_cocone_point_unique_up_to_iso_inv_assoc, coprod.inr_map, pullback.condition],
      refl } }
end

end limits
end category_theory
