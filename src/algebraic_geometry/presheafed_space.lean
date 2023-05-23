/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.adjunction.fully_faithful

/-!
# Presheafed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

universes w v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

variables (C : Type u) [category.{v} C]

local attribute [tidy] tactic.op_induction' tactic.auto_cases_opens

namespace algebraic_geometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace :=
(carrier : Top.{w})
(presheaf : carrier.presheaf C)

variables {C}

namespace PresheafedSpace

attribute [protected] presheaf

instance coe_carrier : has_coe (PresheafedSpace.{w v u} C) Top.{w} :=
{ coe := λ X, X.carrier }

@[simp] lemma as_coe (X : PresheafedSpace.{w v u} C) : X.carrier = (X : Top.{w}) := rfl
@[simp] lemma mk_coe (carrier) (presheaf) : (({ carrier := carrier, presheaf := presheaf } :
  PresheafedSpace.{v} C) : Top.{v}) = carrier := rfl

instance (X : PresheafedSpace.{v} C) : topological_space X := X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : Top) (Z : C) : PresheafedSpace C :=
{ carrier := X,
  presheaf :=
  { obj := λ U, Z,
    map := λ U V f, 𝟙 Z, } }

instance [inhabited C] : inhabited (PresheafedSpace C) := ⟨const (Top.of pempty) default⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom (X Y : PresheafedSpace.{w v u} C) :=
(base : (X : Top.{w}) ⟶ (Y : Top.{w}))
(c : Y.presheaf ⟶ base _* X.presheaf)

@[ext] lemma ext {X Y : PresheafedSpace C} (α β : hom X Y)
  (w : α.base = β.base)
  (h : α.c ≫ (whisker_right (eq_to_hom (by rw w)) _) = β.c) :
  α = β :=
begin
  cases α, cases β,
  dsimp [presheaf.pushforward_obj] at *,
  tidy, -- TODO including `injections` would make tidy work earlier.
end

lemma hext {X Y : PresheafedSpace C} (α β : hom X Y)
  (w : α.base = β.base)
  (h : α.c == β.c) :
  α = β :=
by { cases α, cases β, congr, exacts [w,h] }

.

/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace.{w v u} C) : hom X X :=
{ base := 𝟙 (X : Top.{w}),
  c := eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm }

instance hom_inhabited (X : PresheafedSpace C) : inhabited (hom X X) := ⟨id X⟩

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) : hom X Z :=
{ base := α.base ≫ β.base,
  c := β.c ≫ (presheaf.pushforward _ β.base).map α.c }

lemma comp_c {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) :
  (comp α β).c = β.c ≫ (presheaf.pushforward _ β.base).map α.c := rfl


variables (C)

section
local attribute [simp] id comp

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance category_of_PresheafedSpaces : category (PresheafedSpace.{v v u} C) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g,
  id_comp' := λ X Y f, begin
    ext1,
    { rw comp_c,
      erw eq_to_hom_map,
      simp only [eq_to_hom_refl, assoc, whisker_right_id'],
      erw [comp_id, comp_id] },
    apply id_comp
  end,
  comp_id' := λ X Y f, begin
    ext1,
    { rw comp_c,
      erw congr_hom (presheaf.id_pushforward _) f.c,
      simp only [comp_id, functor.id_map, eq_to_hom_refl, assoc, whisker_right_id'],
      erw eq_to_hom_trans_assoc,
      simp only [id_comp, eq_to_hom_refl],
      erw comp_id },
    apply comp_id
  end,
  assoc' := λ W X Y Z f g h, begin
    ext1,
    repeat {rw comp_c},
    simp only [eq_to_hom_refl, assoc, functor.map_comp, whisker_right_id'],
    erw comp_id,
    congr,
    refl
  end }

end

variables {C}
local attribute [simp] eq_to_hom_map

@[simp] lemma id_base (X : PresheafedSpace.{v v u} C) :
  ((𝟙 X) : X ⟶ X).base = 𝟙 (X : Top.{v}) := rfl

lemma id_c (X : PresheafedSpace.{v v u} C) :
  ((𝟙 X) : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm := rfl

@[simp] lemma id_c_app (X : PresheafedSpace.{v v u} C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = X.presheaf.map
    (eq_to_hom (by { induction U using opposite.rec, cases U, refl })) :=
by { induction U using opposite.rec, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : PresheafedSpace.{v v u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

instance (X Y : PresheafedSpace.{v v u} C) : has_coe_to_fun (X ⟶ Y) (λ _, X → Y) :=
⟨λ f, f.base⟩

lemma coe_to_fun_eq {X Y : PresheafedSpace.{v v u} C} (f : X ⟶ Y) : (f : X → Y) = f.base := rfl

-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp] lemma comp_c_app {X Y Z : PresheafedSpace.{v v u} C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U))) := rfl

lemma congr_app {X Y : PresheafedSpace.{v v u} C} {α β : X ⟶ Y} (h : α = β) (U) :
  α.c.app U = β.c.app U ≫ X.presheaf.map (eq_to_hom (by subst h)) :=
by { subst h, dsimp, simp, }

section
variables (C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace.{v v u} C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f.base }

end

section iso

variables {X Y : PresheafedSpace.{v v u} C}

/--
An isomorphism of PresheafedSpaces is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps hom inv]
def iso_of_components (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y :=
{ hom := { base := H.hom, c := α.inv },
  inv := { base := H.inv,
    c := presheaf.to_pushforward_of_iso H α.hom },
  hom_inv_id' := by { ext, { simp, erw category.id_comp, simpa }, simp },
  inv_hom_id' :=
  begin
    ext x,
    induction x using opposite.rec,
    simp only [comp_c_app, whisker_right_app, presheaf.to_pushforward_of_iso_app,
      nat_trans.comp_app, eq_to_hom_app, id_c_app, category.assoc],
    erw [← α.hom.naturality],
    have := nat_trans.congr_app (α.inv_hom_id) (op x),
    cases x,
    rw nat_trans.comp_app at this,
    convert this,
    { dsimp, simp },
    { simp },
    { simp }
  end }

/-- Isomorphic PresheafedSpaces have natural isomorphic presheaves. -/
@[simps]
def sheaf_iso_of_iso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 :=
{ hom := H.hom.c,
  inv := presheaf.pushforward_to_of_iso ((forget _).map_iso H).symm H.inv.c,
  hom_inv_id' :=
  begin
    ext U,
    have := congr_app H.inv_hom_id U,
    simp only [comp_c_app, id_c_app,
      eq_to_hom_map, eq_to_hom_trans] at this,
    generalize_proofs h at this,
    simpa using congr_arg (λ f, f ≫ eq_to_hom h.symm) this,
  end,
  inv_hom_id' :=
  begin
    ext U,
    simp only [presheaf.pushforward_to_of_iso_app, nat_trans.comp_app, category.assoc,
      nat_trans.id_app, H.hom.c.naturality],
    have := congr_app H.hom_inv_id ((opens.map H.hom.base).op.obj U),
    generalize_proofs h at this,
    simpa using congr_arg (λ f, f ≫ X.presheaf.map (eq_to_hom h.symm)) this
  end }

instance base_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.base :=
is_iso.of_iso ((forget _).map_iso (as_iso f))

instance c_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.c :=
is_iso.of_iso (sheaf_iso_of_iso (as_iso f))

/-- This could be used in conjunction with `category_theory.nat_iso.is_iso_of_is_iso_app`. -/
lemma is_iso_of_components (f : X ⟶ Y) [is_iso f.base] [is_iso f.c] : is_iso f :=
begin
  convert is_iso.of_iso (iso_of_components (as_iso f.base) (as_iso f.c).symm),
  ext, { simpa }, { simp },
end

end iso

section restrict

/--
The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : Top} (X : PresheafedSpace.{v v u} C)
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) : PresheafedSpace C :=
{ carrier := U,
  presheaf := h.is_open_map.functor.op ⋙ X.presheaf }

/--
The map from the restriction of a presheafed space.
-/
@[simps]
def of_restrict {U : Top} (X : PresheafedSpace.{v v u} C)
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) :
  X.restrict h ⟶ X :=
{ base := f,
  c := { app := λ V, X.presheaf.map (h.is_open_map.adjunction.counit.app V.unop).op,
    naturality' := λ U V f, show _ = _ ≫ X.presheaf.map _,
      by { rw [← map_comp, ← map_comp], refl } } }

instance of_restrict_mono {U : Top} (X : PresheafedSpace C) (f : U ⟶ X.1)
   (hf : open_embedding f) : mono (X.of_restrict hf) :=
 begin
   haveI : mono f := (Top.mono_iff_injective _).mpr hf.inj,
   constructor,
   intros Z g₁ g₂ eq,
   ext V,
   { induction V using opposite.rec,
     have hV : (opens.map (X.of_restrict hf).base).obj (hf.is_open_map.functor.obj V) = V,
     { ext1, exact set.preimage_image_eq _ hf.inj },
     haveI : is_iso (hf.is_open_map.adjunction.counit.app
               (unop (op (hf.is_open_map.functor.obj V)))) :=
       (nat_iso.is_iso_app_of_is_iso (whisker_left
         hf.is_open_map.functor hf.is_open_map.adjunction.counit) V : _),
     have := PresheafedSpace.congr_app eq (op (hf.is_open_map.functor.obj V)),
     simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, category.assoc,
       cancel_epi] at this,
     have h : _ ≫ _ = _ ≫ _ ≫ _ :=
       congr_arg (λ f, (X.restrict hf).presheaf.map (eq_to_hom hV).op ≫ f) this,
     erw [g₁.c.naturality, g₂.c.naturality_assoc] at h,
     simp only [presheaf.pushforward_obj_map, eq_to_hom_op,
       category.assoc, eq_to_hom_map, eq_to_hom_trans] at h,
     rw ←is_iso.comp_inv_eq at h,
     simpa using h },
   { have := congr_arg PresheafedSpace.hom.base eq,
     simp only [PresheafedSpace.comp_base, PresheafedSpace.of_restrict_base] at this,
     rw cancel_mono at this,
     exact this }
 end

lemma restrict_top_presheaf (X : PresheafedSpace C) :
  (X.restrict (opens.open_embedding ⊤)).presheaf =
  (opens.inclusion_top_iso X.carrier).inv _* X.presheaf :=
by { dsimp, rw opens.inclusion_top_functor X.carrier, refl }

lemma of_restrict_top_c (X : PresheafedSpace C) :
  (X.of_restrict (opens.open_embedding ⊤)).c = eq_to_hom
    (by { rw [restrict_top_presheaf, ←presheaf.pushforward.comp_eq],
          erw iso.inv_hom_id, rw presheaf.pushforward.id_eq }) :=
  /- another approach would be to prove the left hand side
     is a natural isoomorphism, but I encountered a universe
     issue when `apply nat_iso.is_iso_of_is_iso_app`. -/
begin
  ext U, change X.presheaf.map _ = _, convert eq_to_hom_map _ _ using 1,
  congr, simpa,
  { induction U using opposite.rec, dsimp, congr, ext,
    exact ⟨ λ h, ⟨⟨x,trivial⟩,h,rfl⟩, λ ⟨⟨_,_⟩,h,rfl⟩, h ⟩ },
  /- or `rw [opens.inclusion_top_functor, ←comp_obj, ←opens.map_comp_eq],
         erw iso.inv_hom_id, cases U, refl` after `dsimp` -/
end

/--
The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def to_restrict_top (X : PresheafedSpace C) :
  X ⟶ X.restrict (opens.open_embedding ⊤) :=
{ base := (opens.inclusion_top_iso X.carrier).inv,
  c := eq_to_hom (restrict_top_presheaf X) }

/--
The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrict_top_iso (X : PresheafedSpace C) :
  X.restrict (opens.open_embedding ⊤) ≅ X :=
{ hom := X.of_restrict _,
  inv := X.to_restrict_top,
  hom_inv_id' := ext _ _ (concrete_category.hom_ext _ _ $ λ ⟨x, _⟩, rfl) $
    by { erw comp_c, rw X.of_restrict_top_c, ext, simp },
  inv_hom_id' := ext _ _ rfl $
    by { erw comp_c, rw X.of_restrict_top_c, ext, simpa [-eq_to_hom_refl] } }

end restrict

/--
The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace.{v v u} C)ᵒᵖ ⥤ C :=
{ obj := λ X, (unop X).presheaf.obj (op ⊤),
  map := λ X Y f, f.unop.c.app (op ⊤) }

lemma Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

lemma Γ_map_op {X Y : PresheafedSpace.{v v u} C} (f : X ⟶ Y) :
  Γ.map f.op = f.c.app (op ⊤) := rfl

end PresheafedSpace

end algebraic_geometry

open algebraic_geometry algebraic_geometry.PresheafedSpace

variables {C}

namespace category_theory

variables {D : Type u} [category.{v} D]

local attribute [simp] presheaf.pushforward_obj

namespace functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def map_presheaf (F : C ⥤ D) : PresheafedSpace.{v v u} C ⥤ PresheafedSpace.{v v u} D :=
{ obj := λ X, { carrier := X.carrier, presheaf := X.presheaf ⋙ F },
  map := λ X Y f, { base := f.base, c := whisker_right f.c F }, }

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
  ((F.map_presheaf.obj X) : Top.{v}) = (X : Top.{v}) := rfl
@[simp] lemma map_presheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
  (F.map_presheaf.obj X).presheaf = X.presheaf ⋙ F := rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace.{v v u} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).base = f.base := rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace.{v v u} C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F := rfl

end functor

namespace nat_trans

/--
A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
{ app := λ X,
  { base := 𝟙 _,
    c := whisker_left X.presheaf α ≫ eq_to_hom (presheaf.pushforward.id_eq _).symm } }

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end nat_trans

end category_theory
