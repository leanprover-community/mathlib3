import category_theory.adjunction
import category_theory.opposites
import category_theory.types
import category_theory.yoneda
import category_theory.limits
import category_theory.limits.functor_category
import category_theory.limits.types
import data.equiv.basic

import category_theory.sheafy_preamble

namespace category_theory
open category_theory.limits

universes u v

-- TODO: How much of this should be generalized to a possibly large category?
variables (C : Type v) [𝒞 : small_category.{v} C]
include 𝒞

def presheaf := Cᵒᵖ ⥤ Type v
variables {C}

namespace presheaf

section simp
variable (F : presheaf C)

@[simp] lemma map_id {c : C} : F.map (𝟙 c) = 𝟙 (F.obj c) := F.map_id c

@[simp] lemma map_id' {c : C} :
F.map (@category.id C 𝒞 c) = 𝟙 (F.obj c) := functor.map_id F c

@[simp] lemma map_comp {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
F.map (g ≫ f) = (F.map g) ≫ (F.map f) := F.map_comp g f

@[simp] lemma map_comp' {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
F.map (@category.comp C 𝒞 _ _ _ f g) = (F.map g) ≫ (F.map f) := functor.map_comp F g f

end simp

instance : category.{(v+1) v} (presheaf C) := by dunfold presheaf; apply_instance
instance : has_limits.{(v+1) v} (presheaf C) := limits.functor_category_has_limits
instance : has_pullbacks.{(v+1) v} (presheaf C) := limits.functor_category_has_pullbacks
instance : has_colimits.{(v+1) v} (presheaf C) := limits.functor_category_has_colimits
instance : has_coproducts.{(v+1) v} (presheaf C) := limits.functor_category_has_coproducts
instance : has_coequalizers.{(v+1) v} (presheaf C) := limits.functor_category_has_coequalizers

section extension
variables {D : Type u} [𝒟 : category.{u v} D] (F : C ⥤ D)
include 𝒟

def restricted_yoneda : D ⥤ presheaf C :=
{ obj := λ d, F.op ⋙ yoneda.obj d,
  map := λ d₁ d₂ g, whisker_left _ $ yoneda.map g }

variables [has_colimits.{u v} D]

def yoneda_extension : presheaf C ⥤ D :=
-- @adjunction.left_adjoint_of_equiv _ _ _ _
-- (λ X, colimit (comma.fst.{v v v v} yoneda (functor.of_obj X) ⋙ F))
-- (restricted_yoneda F)
-- (λ X d, _) _
{ obj := λ X, colimit (comma.fst.{v v v v} yoneda (functor.of_obj X) ⋙ F),
  map := λ X Y f, colimit.pre (comma.fst.{v v v v} yoneda (functor.of_obj Y) ⋙ F) (comma.map_right yoneda $ functor.of_map f),
  map_id' := λ X,
  begin
    erw functor.of_map_id,
    erw colimit.pre_map
      (comma.fst.{v v v v} yoneda (functor.of_obj X) ⋙ F)
      (comma.map_right_id'.{v v v} yoneda (functor.of_obj X)).hom,
  end }

end extension

section category_of_elements

variables (X : presheaf C)

-- TODO: Implement this as the comma category of `yoneda` over X?
structure category_of_elements :=
(c : C)
(e : yoneda.obj c ⟹ X)

instance category_of_elements.category : category (category_of_elements X) :=
{ hom := λ a b, {f : a.c ⟶ b.c // a.e = (yoneda.map f).vcomp b.e },
  id := λ a, ⟨𝟙 _, by tidy⟩,
  comp := λ a b c f g,
    ⟨f.1 ≫ g.1, begin
       cases f with f hf, cases g with g hg,
       dsimp { iota := tt },
       rw [hf, hg],
       tidy
     end⟩ }

def category_of_elements.forget : category_of_elements X ⥤ C :=
{ obj := λ a, a.c, map := λ a b f, f.1 }

variables {X} {Y : presheaf C}
def category_of_elements.map (g : X ⟶ Y) : category_of_elements X ⥤ category_of_elements Y :=
{ obj := λ a, ⟨a.c, a.e ⊟ g⟩,
  map := λ a b f, ⟨f, by cases f with f₁ f₂; dsimp; rw f₂; simp⟩ }

end category_of_elements

section extension
variables {D : Type u} [𝒟 : category.{u v} D] (F : C ⥤ D)
include 𝒟

def restricted_yoneda : D ⥤ Cᵒᵖ ⥤ Type v :=
{ obj := λ d,
  { obj := λ c, F.obj c ⟶ d,
    map := λ c c' f h, F.map f ≫ h,
    map_id' := λ c, by ext h; erw [F.map_id, category.id_comp]; refl,
    map_comp' := λ c c' c'' f f', by ext h; erw [F.map_comp, category.assoc]; refl },
  map := λ d d' g, { app := λ c h, h ≫ g } }

variables [has_colimits.{u v} D]

def yoneda_extension_obj : presheaf C → D :=
λ X, colimit ((category_of_elements.forget X).comp F)

def yoneda_extension_e (X Y) :
  (yoneda_extension_obj F X ⟶ Y) ≃ (X ⟶ (restricted_yoneda F).obj Y) :=
calc
  (colimit _ ⟶ Y)
    ≃ ((category_of_elements.forget X).comp F ⟹ (functor.const _).obj Y)
    : (colimit.universal_property _).equiv
... ≃ { t : Π (c : C) (e : yoneda.obj c ⟹ X), F.obj c ⟶ Y //
        ∀ (c c' : C) (f : c' ⟶ c) (e : yoneda.obj c ⟹ X),
          t c' ((yoneda.map f).vcomp e) = F.map f ≫ t c e }
    : ⟨λ t,
         ⟨λ c e, t.app ⟨c, e⟩,
          λ c d f e, begin
            erw @nat_trans.naturality _ _ _ _ _ _ t ⟨d, yoneda.map f ⊟ e⟩ ⟨c, e⟩ ⟨f, rfl⟩,
            erw category.comp_id
          end⟩,
       λ t,
         { app := λ a, t.1 a.1 a.2,
           naturality' := λ a b f, by erw [f.2, ←t.2 b.1 a.1 f.1 b.2, category.comp_id] },
       λ t, by cases t; ext1 ce; cases ce; refl,
       λ t, by cases t; refl⟩
... ≃ { t : Π (c : C) (e : X.obj c), F.obj c ⟶ Y // _ }
    : equiv.subtype_equiv_of_subtype $ equiv.Pi_congr_right $ λ c,
        equiv.arrow_congr (yoneda_equiv X) (equiv.refl _)
... ≃ { t : Π (c : C) (e : X.obj c), F.obj c ⟶ Y //
        ∀ c c' (f : c ⟶ c'), X.map f ≫ t c' = t c ≫ ((restricted_yoneda F).obj Y).map f }
    : begin
        apply equiv.subtype_equiv_subtype,
        ext t,
        apply forall_congr, intro c,
        apply forall_congr, intro c',
        apply forall_congr, intro f,
        dsimp [equiv.Pi_congr_right, equiv.arrow_congr, equiv.refl, yoneda_equiv],
        split; intro H,
        { ext e,
          have : e = (yoneda_equiv X).to_fun ((yoneda_equiv X).inv_fun e),
            by rw (yoneda_equiv X).right_inv,
          rw this,
          convert H ((yoneda_equiv X).inv_fun e),
          rw ←this,
          simp [yoneda_equiv] },
        { intro e,
          convert congr_fun H ((yoneda_equiv X).to_fun e),
          dsimp [yoneda_equiv],
          convert functor_to_types.naturality _ _ e f (𝟙 c) using 2,
          simp }
      end
... ≃ (X ⟶ (restricted_yoneda F).obj Y)
    : ⟨λ t, { app := t.1, naturality' := λ c c' f, by apply t.2 },
       λ t, ⟨t.app, λ c c' f, by apply t.naturality⟩,
       λ t, by cases t; refl,
       λ t, by cases t; refl⟩

local attribute [elab_simple] colimit.ι
lemma yoneda_extension_eq {X Y} {j : category_of_elements X} (h : yoneda_extension_obj F X ⟶ Y) :
  (yoneda_equiv _).to_fun (j.e ⊟ (yoneda_extension_e F X Y).to_fun h) =
  colimit.ι ((category_of_elements.forget X).comp F) j ≫ h :=
begin
  cases j with jc je,
  change colimit.ι ((category_of_elements.forget X).comp F) {c := jc, e := nat_trans.mk _ _} ≫ h = _,
  congr,
  ext c' e', dsimp,
  rw ←functor_to_types.naturality,
  congr,
  apply category.comp_id
end

lemma yoneda_extension_e_natural (X Y Y') (g : Y ⟶ Y') (h) :
  (yoneda_extension_e F X Y').to_fun (h ≫ g) =
  (yoneda_extension_e F X Y).to_fun h ≫ (restricted_yoneda F).map g :=
by ext c e; symmetry; apply category.assoc

def yoneda_extension : presheaf C ⥤ D :=
adjunction.left_adjoint_of_equiv (yoneda_extension_e F) (yoneda_extension_e_natural F)

def yoneda_extension_adj : adjunction (yoneda_extension F) (restricted_yoneda F) :=
by apply adjunction.adjunction_of_equiv_left

def yoneda_extension_map {X Y} (g : X ⟶ Y) : yoneda_extension_obj F X ⟶ yoneda_extension_obj F Y :=
colimit.pre ((category_of_elements.forget Y).comp F) (category_of_elements.map g)

lemma yoneda_extension_e_natural' (X Y Z) (g : X ⟶ Y) (h) :
  (yoneda_extension_e F X Z).to_fun (yoneda_extension_map F g ≫ h) =
  g ≫ (yoneda_extension_e F Y Z).to_fun h :=
begin
  ext c' f,
  dsimp [yoneda_extension_e, equiv.trans, equiv.subtype_equiv_subtype, equiv.subtype_equiv_of_subtype,
    equiv.Pi_congr_right, equiv.arrow_congr, is_colimit.equiv],
  dsimp [yoneda_extension_map], rw ←category.assoc,
  erw colimit.ι_pre (category_of_elements.forget Y ⋙ F) (category_of_elements.map g),
  dsimp [category_of_elements.map],
  congr,
  rw equiv.eq_symm_apply,
  convert ←yoneda_equiv_nat' _ _,
  exact (yoneda_equiv X).right_inv f
end

lemma yoneda_extension_map_eq {X Y} {g : X ⟶ Y} :
  (yoneda_extension F).map g = yoneda_extension_map F g :=
begin
  dsimp [yoneda_extension, adjunction.left_adjoint_of_equiv],
  rw equiv.symm_apply_eq, symmetry,
  convert yoneda_extension_e_natural' F X Y _ g _,
  simp, refl
end

local attribute [elab_simple] yoneda_extension -- to infer universe parameters
def yoneda_extension_is_extension : yoneda ⋙ yoneda_extension F ≅ F :=
nat_iso.of_components
  (λ c, coext_equiv
     (λ Z, calc
         (F.obj c ⟶ Z)
           ≃ ((restricted_yoneda F).obj Z).obj c           : equiv.refl _
       ... ≃ (yoneda.obj c ⟹ (restricted_yoneda F).obj Z)  : (yoneda_equiv _).symm
       ... ≃ ((yoneda ⋙ yoneda_extension F).obj c ⟶ Z)
           : (yoneda_extension_adj F).hom_equiv.symm)
     begin
       intros d d' f g,
       dsimp [equiv.trans, equiv.symm, equiv.refl],
       rw ←adjunction.hom_equiv_symm_naturality', congr,
       dsimp [yoneda_equiv], ext c', dsimp [restricted_yoneda], simp
     end)
  begin
    intros c c' f,
    dsimp [equiv.trans, equiv.symm, equiv.refl],
    rw [coext_equiv_hom, coext_equiv_hom_comp],
    dsimp, rw ←adjunction.hom_equiv_symm_naturality, congr,
    convert yoneda_equiv_symm_nat f _,
    dsimp [restricted_yoneda], simp
  end

end extension


section canonical_diagram

def restricted_yoneda_yoneda_iso_id : restricted_yoneda yoneda ≅ functor.id (presheaf C) :=
nat_iso.of_components
  (λ X, begin
     fapply nat_iso.of_components,
     { exact λ c, iso_of_equiv (yoneda_equiv X : _ ≃ X.obj c) },
     { intros c c' f, ext t,
       dsimp [iso_of_equiv],
       erw yoneda_equiv_nat, refl }
   end)
  (by intros X Y f; ext c e; refl)

lemma restricted_yoneda_yoneda_iso_id_yoneda {c : C} {Y}
  (h : yoneda.obj c ⟶ (restricted_yoneda yoneda).obj Y) :
  (yoneda_equiv _).to_fun h = (h ⊟ restricted_yoneda_yoneda_iso_id.hom.app Y) :=
begin
  ext c' f,
  have := (congr_fun (h.naturality f) (𝟙 c)).symm,
  dsimp [restricted_yoneda_yoneda_iso_id, restricted_yoneda, yoneda_equiv,
    nat_iso.of_components] at ⊢ this,
  rw category.comp_id at this,
  rw ←this,
  dsimp, simp
end

def id_iso_yoneda_extension_yoneda : functor.id (presheaf C) ≅ yoneda_extension yoneda :=
(adjunction.nat_iso_equiv (yoneda_extension_adj _) adjunction.id).inv_fun
  restricted_yoneda_yoneda_iso_id

-- So, we showed that the colimit of the canonical diagram is isomorphic to X, *somehow*!
-- Can we identify the colimit cone as the obvious one?

variables (X : presheaf C)

def canonical_diagram : category_of_elements X ⥤ presheaf C :=
(category_of_elements.forget X).comp yoneda

def canonical_diagram.cocone : cocone (canonical_diagram X) :=
{ X := X,
  ι :=
  { app := λ a, a.e,
    naturality' := λ a b f, by rw f.2; refl } }

def canonical_diagram.colimit_cocone : cocone (canonical_diagram X) :=
colimit.cocone (canonical_diagram X)

def canonical_diagram.cocone_equiv_colimit :
  canonical_diagram.cocone X ≅ canonical_diagram.colimit_cocone X :=
cocones.ext _ _ (nat_iso.app id_iso_yoneda_extension_yoneda X)
  begin
    intro j,
    dsimp [canonical_diagram.cocone],
    suffices : ∀ {Y} (h : (yoneda_extension yoneda).obj X ⟶ Y),
      colimit.ι _ j ≫ h = (j.e ≫ (id_iso_yoneda_extension_yoneda.hom).app X) ≫ h,
    { exact (this (𝟙 _)).symm },
    { intros Y h,
      rw ←(yoneda_extension_adj yoneda).hom_equiv.left_inv h,
      generalize : (adjunction.hom_equiv (yoneda_extension_adj yoneda)).to_fun h = h',

      rw category.assoc,
      dsimp [id_iso_yoneda_extension_yoneda, adjunction.nat_iso_equiv],
      erw (adjunction.nat_trans_iff' (yoneda_extension_adj yoneda) adjunction.id).mp _,
      swap 3, { simp },
      rw [adjunction.id.hom_equiv_inv, ←category.assoc],

      rw ←yoneda_extension_eq,
      dsimp [yoneda_extension_adj],
      rw adjunction.adjunction_of_equiv_left_equiv,
      rw (yoneda_extension_e yoneda X Y).right_inv,

      apply restricted_yoneda_yoneda_iso_id_yoneda }
  end
/-
-- This proof is ridiculous
  begin
    intro j,
    ext c e,
/-
    dsimp [canonical_diagram.cocone, canonical_diagram,
      canonical_diagram.colimit_cocone, id_iso_yoneda_extension_yoneda,
      adjunction.nat_iso_equiv, adjunction.nat_trans_equiv,
      equiv.refl, equiv.symm, equiv.trans, iso.hom_equiv_of_isos,
      adjunction.mate, adjunction.nat_equiv, adjunction.nat_equiv',
      adjunction.hom_equiv, adjunction.id, adjunction.adjunction_of_equiv_left,
      adjunction.adjunction_of_equiv, adjunction.left_adjoint_of_equiv,
      yoneda_extension_adj, yoneda_extension_e,
      equiv.subtype_equiv_subtype, equiv.subtype_equiv_of_subtype, equiv.Pi_congr_right,
      equiv.arrow_congr,
      is_colimit.equiv,
      restricted_yoneda, yoneda_extension, yoneda_extension_obj,
      restricted_yoneda_yoneda_iso_id,
      nat_iso.of_components, iso_of_equiv, yoneda_equiv], -/
    change
      (colimit.ι (category_of_elements.forget X ⋙ yoneda)
          {c := c, e := {app := λ (Y : Cᵒᵖ) (f : Y ⟶ c), X.map f ((j.e).app c e), naturality' := _}}).app
        c
        (𝟙 c) =
      (colimit.ι (category_of_elements.forget X ⋙ yoneda) j).app c e,
    dsimp [canonical_diagram, category_of_elements.forget] at e,
    let f : category_of_elements.mk c (_) ⟶ j, { refine ⟨e, _⟩, swap, dsimp, refl },
    have := colimit.w (category_of_elements.forget X ⋙ yoneda) f,
    have := congr_arg nat_trans.app this,
    convert congr_fun (congr_fun this.symm c) (𝟙 c),
    { ext c' g, rw ←functor_to_types.naturality, refl },
    { exact (category.id_comp _ _).symm }
  end
-/

def canonical_diagram.is_colimit : is_colimit (canonical_diagram.cocone X) :=
is_colimit_invariance _ _ (canonical_diagram.cocone_equiv_colimit X).symm
  (colimit.universal_property _)

end canonical_diagram

section colimit_preserving
variables {D : Type u} [𝒟 : category.{u v} D] [has_colimits.{u v} D]
include 𝒟
variables (F : presheaf C ⥤ D) [preserves_colimits F]

def colimit_preserving_is_extension : F ≅ yoneda_extension (yoneda.comp F) :=
nat_iso.of_components
  (λ X, cocones.vertex.on_iso $ colimit_cocone.ext
     (preserves_colimits.preserves F (canonical_diagram.is_colimit X))
     (colimit.universal_property _))
  begin
    intros X Y f,
    dsimp [colimit_cocone.ext, cocones.vertex],
    apply is_colimit.hom_ext
      (preserves_colimits.preserves F (canonical_diagram.is_colimit X)),
    intro j,
    rw [←category.assoc, ←category.assoc, is_colimit.fac],
    dsimp [canonical_diagram],
    have :
      (canonical_diagram.cocone X).ι.app j ≫ f =
      (canonical_diagram.cocone Y).ι.app ⟨j.c, _ ⊟ _⟩, { refl },
    rw [←F.map_comp, this, ←functor.map_cocone_ι, is_colimit.fac],
    change colimit.ι _ _ = _,
    rw yoneda_extension_map_eq,
    symmetry,
    exact colimit.ι_pre (category_of_elements.forget Y ⋙ yoneda ⋙ F) (category_of_elements.map f) _
  end

end colimit_preserving

end category_theory
