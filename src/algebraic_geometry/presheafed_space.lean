/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Andrew Yang
-/
import topology.sheaves.presheaf
import category_theory.adjunction.fully_faithful

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

universes v u

open category_theory
open Top
open topological_space
open opposite
open category_theory.category category_theory.functor

variables (C : Type u) [category.{v} C]

local attribute [tidy] tactic.op_induction'

namespace algebraic_geometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace :=
(carrier : Top)
(presheaf : carrier.presheaf C)

variables {C}

namespace PresheafedSpace

attribute [protected] presheaf

instance coe_carrier : has_coe (PresheafedSpace C) Top :=
{ coe := λ X, X.carrier }

@[simp] lemma as_coe (X : PresheafedSpace C) : X.carrier = (X : Top.{v}) := rfl
@[simp] lemma mk_coe (carrier) (presheaf) : (({ carrier := carrier, presheaf := presheaf } :
  PresheafedSpace.{v} C) : Top.{v}) = carrier := rfl

instance (X : PresheafedSpace.{v} C) : topological_space X := X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : Top) (Z : C) : PresheafedSpace C :=
{ carrier := X,
  presheaf :=
  { obj := λ U, Z,
    map := λ U V f, 𝟙 Z, } }

instance [inhabited C] : inhabited (PresheafedSpace C) := ⟨const (Top.of pempty) (default C)⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom (X Y : PresheafedSpace C) :=
(base : (X : Top.{v}) ⟶ (Y : Top.{v}))
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
def id (X : PresheafedSpace C) : hom X X :=
{ base := 𝟙 (X : Top.{v}),
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
instance category_of_PresheafedSpaces : category (PresheafedSpace C) :=
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

@[simp] lemma id_base (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).base = 𝟙 (X : Top.{v}) := rfl

lemma id_c (X : PresheafedSpace C) :
  ((𝟙 X) : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm := rfl

@[simp] lemma id_c_app (X : PresheafedSpace C) (U) :
  ((𝟙 X) : X ⟶ X).c.app U = X.presheaf.map
    (eq_to_hom (by { induction U using opposite.rec, cases U, refl })) :=
by { induction U using opposite.rec, cases U, simp only [id_c], dsimp, simp, }

@[simp] lemma comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).base = f.base ≫ g.base := rfl

@[simp] lemma comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
  (α ≫ β).c.app U = (β.c).app U ≫ (α.c).app (op ((opens.map (β.base)).obj (unop U))) := rfl

lemma congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
  α.c.app U = β.c.app U ≫ X.presheaf.map (eq_to_hom (by subst h)) :=
by { subst h, dsimp, simp, }

section
variables (C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace C ⥤ Top :=
{ obj := λ X, (X : Top.{v}),
  map := λ X Y f, f.base }

end

section iso

variables {X Y : PresheafedSpace C}

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
    erw [←α.hom.naturality],
    have := nat_trans.congr_app (α.inv_hom_id) (op x),
    cases x,
    rw nat_trans.comp_app at this,
    convert this,
    { dsimp, simp },
    { simp },
    { simp }
  end }

-- /-- Isomorphic PresheafedSpaces have homeomorphic topological spaces. -/
-- def base_iso_of_iso (H : X ≅ Y) : X.1 ≅ Y.1 :=
-- { hom := H.hom.base,
--   inv := H.inv.base,
--   hom_inv_id' := congr_arg hom.base H.hom_inv_id,
--   inv_hom_id' := congr_arg hom.base H.inv_hom_id }

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
    simpa using congr_arg (λ f, f ≫X.presheaf.map (eq_to_hom h.symm)) this
  end }

instance base_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.base :=
is_iso.of_iso ((forget _).map_iso (as_iso f))

instance c_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.c :=
is_iso.of_iso (sheaf_iso_of_iso (as_iso f))

end iso

section restrict

/--
The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : Top} (X : PresheafedSpace C)
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) : PresheafedSpace C :=
{ carrier := U,
  presheaf := h.is_open_map.functor.op ⋙ X.presheaf }

/--
The map from the restriction of a presheafed space.
-/
@[simps]
def of_restrict {U : Top} (X : PresheafedSpace C)
  {f : U ⟶ (X : Top.{v})} (h : open_embedding f) :
  X.restrict h ⟶ X :=
{ base := f,
  c := { app := λ V, X.presheaf.map (h.is_open_map.adjunction.counit.app V.unop).op,
    naturality' := λ U V f, show _ = _ ≫ X.presheaf.map _,
      by { rw [← map_comp, ← map_comp], refl } } }

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
    by { erw comp_c, rw X.of_restrict_top_c, ext, simp, erw comp_id, refl } }

instance of_restrict_mono {U : Top} (X : PresheafedSpace C) (f : U ⟶ X.1)
  (hf : open_embedding f) : mono (X.of_restrict hf) :=
begin
  haveI : mono f := (Top.mono_iff_injective _).mpr hf.inj,
  constructor,
  intros Z g₁ g₂ eq,
  ext V,
  { induction V using opposite.rec,
    have hV : (opens.map (X.of_restrict hf).base).obj (hf.is_open_map.functor.obj V) = V,
    { cases V, simp[opens.map, set.preimage_image_eq _ hf.inj] },
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

local attribute[-simp] eq_to_hom_map

-- /--
-- Equal open embeddings give rise to isomorphic structured spaces.

-- The simp lemmas are provided below,
-- and the lemmas generated by `simps` are merely used to prove them.
-- -/
-- @[simps hom_base inv_base, simps hom_c_app inv_c_app (lemmas_only)]
-- def restrict_eq {X : Top} (Y : PresheafedSpace C) {f : X ⟶ Y.1}
--   (hf : open_embedding f) {g : X ⟶ Y.1} (hg : open_embedding g) (eq : f = g) :
--   Y.restrict hf ≅ Y.restrict hg :=
-- PresheafedSpace.iso_of_components (iso.refl X)
-- begin
--   change (opens.map (iso.refl X).hom ⋙ is_open_map.functor _).op ⋙ Y.presheaf ≅ _,
--   refine iso_whisker_right _ Y.presheaf,
--   change (opens.map _ ⋙ is_open_map.functor _).op ≅ _,
--   apply nat_iso.op,
--   fapply nat_iso.of_components,
--   { intro U,
--     apply eq_to_iso,
--     cases U,
--     ext,
--     simp only [is_open_map.functor_obj_coe, opens.map, functor.comp_obj, subtype.coe_mk, eq],
--     erw iso.refl_hom,
--     simp },
--   { intros _ _ _,
--     simp[is_open_map.functor] },
-- end

-- @[simp] lemma restrict_eq_hom_c_app' {X : Top} (Y : PresheafedSpace C) {f : X ⟶ Y.1}
--   (hf : open_embedding f) {g : X ⟶ Y.1} (hg : open_embedding g) (eq : f = g)
--   (U : (opens (Y.restrict hg))ᵒᵖ) :
--   (Y.restrict_eq hf hg eq).hom.c.app U = Y.presheaf.map
--     (eq_to_hom (begin
--       tactic.op_induction',
--       cases U,
--       cases eq,
--       dsimp only [is_open_map.functor, opens.map, functor.op],
--       congr
--     end)) := by simpa [restrict_eq_hom_c_app]

-- @[simp] lemma restrict_eq_inv_c_app' {X : Top} (Y : PresheafedSpace C) (f : X ⟶ Y.1)
--   (hf : open_embedding f) (g : X ⟶ Y.1) (hg : open_embedding g) (eq : f = g)
--   (U : (opens (Y.restrict hg))ᵒᵖ) :
--   (Y.restrict_eq hf hg eq).inv.c.app U = Y.presheaf.map
--     (eq_to_hom (begin
--       tactic.op_induction',
--       cases U,
--       cases eq,
--       dsimp only [is_open_map.functor, opens.map, functor.op],
--       congr
--     end)) := by { rw restrict_eq_inv_c_app, exact category.id_comp _ }

-- @[simp] lemma restrict_eq_hom_comp_of_restrict {X : Top} (Y : PresheafedSpace C) (f : X ⟶ Y.1)
--   (hf : open_embedding f) (g : X ⟶ Y.1) (hg : open_embedding g) (eq : f = g) :
--   (Y.restrict_eq hf hg eq).hom ≫ Y.of_restrict _ = Y.of_restrict _ :=
-- begin
--   ext,
--   { dsimp only [restrict],
--     simp only [of_restrict_c_app, eq_to_hom_app, whisker_right_app, assoc, restrict_eq_hom_c_app',
--       comp_c_app, nat_trans.comp_app, ←Y.presheaf.map_comp, functor.comp_map],
--     congr },
--   { simp[eq] }
-- end

-- @[simp] lemma restrict_eq_inv_comp_of_restrict {X : Top} (Y : PresheafedSpace C) (f : X ⟶ Y.1)
--   (hf : open_embedding f) (g : X ⟶ Y.1) (hg : open_embedding g) (eq : f = g) :
--   (Y.restrict_eq hf hg eq).inv ≫ Y.of_restrict _ = Y.of_restrict _ :=
-- by rw [iso.inv_comp_eq, restrict_eq_hom_comp_of_restrict]

-- /--
-- If `X ≅ Y` are isomorphic PresheafedSpaces, then there restriction along an open embedding is
-- also isomorphic.
-- -/
-- @[simps hom_base inv_base hom_c_app inv_c_app]
-- def restrict_map_iso {X Y : PresheafedSpace C} {T : Top.{v}} (f : T ⟶ X) (hf : open_embedding f)
--   (g : X ≅ Y) :
-- X.restrict hf ≅ @restrict _ _ T Y (f ≫ g.hom.base)
--   ((homeo_of_iso ((forget _).map_iso g)).open_embedding.comp hf) :=
-- iso_of_components (iso.refl _) $ nat_iso.of_components
--   (λ U, X.presheaf.map_iso (eq_to_iso
--     (begin
--       induction U using opposite.rec,
--       cases U,
--       dsimp only [opens.map, is_open_map.functor, coe_comp, functor.op, unop_op],
--       congr,
--       rw coe_comp,
--       conv_rhs { rw ←set.image_image },
--       erw set.preimage_image_eq _ (homeo_of_iso ((forget _).map_iso g)).injective,
--       simpa
--     end)) ≪≫ ((sheaf_iso_of_iso g).app _).symm)
--   (λ U V i,
--   begin
--     simp only [iso.symm_hom, iso.app_inv, map_iso_hom, assoc, presheaf.pushforward_obj_map,
--       eq_to_iso.hom, op_map, iso.trans_hom],
--     erw ←(sheaf_iso_of_iso g).inv.naturality,
--     erw ←X.presheaf.map_comp_assoc,
--     erw ←X.presheaf.map_comp_assoc,
--     congr
--   end)

-- /--
-- If `f : Y ≅ X.carrier` is an homeomorphism, then `X` is isomorphic to the restriction onto `Y`.
-- -/
-- def iso_restrict_iso (X : PresheafedSpace C) {Y : Top} (H : Y ≅ X.1) :
--   X ≅ X.restrict (homeo_of_iso H).open_embedding :=
-- PresheafedSpace.iso_of_components H.symm
-- begin
--   refine iso_whisker_right _ X.presheaf,
--   fapply nat_iso.of_components,
--   { intro U,
--     fapply eq_to_iso,
--     induction U using opposite.rec,
--     cases U,
--     dsimp only [functor.op, opens.map, is_open_map.functor],
--     congr' 2,
--     refine (set.preimage_eq_preimage ((homeo_of_iso H).surjective)).mp _,
--     erw set.preimage_image_eq _ ((homeo_of_iso H).injective),
--     { ext, simp [set.preimage_preimage, ←Top.comp_app] } },
--   { intros U V i, simp }
-- end

-- @[simp] lemma iso_restrict_iso_inv (X : PresheafedSpace C) {Y : Top} (H : Y ≅ X.1) :
--   (X.iso_restrict_iso H).inv = X.of_restrict _ :=
-- begin
--   ext,
--   rw nat_trans.comp_app,
--   erw to_pushforward_of_iso_app,
--   erw ←X.presheaf.map_comp,
--   erw ←X.presheaf.map_comp,
--   exact congr_arg (λ f, X.presheaf.map f) (subsingleton.elim _ _),
--   simp [iso_restrict_iso]
-- end

-- @[simp] lemma iso_restrict_iso_hom_comp_restrict (X : PresheafedSpace C) {Y : Top} (H : Y ≅ X.1) :
--   (X.iso_restrict_iso H).hom ≫ X.of_restrict _ = 𝟙 _ :=
-- by rw [←iso_restrict_iso_inv, iso.hom_inv_id]

-- @[simp] lemma restrict_comp_iso_restrict_iso_hom (X : PresheafedSpace C) {Y : Top} (H : Y ≅ X.1) :
--   X.of_restrict _ ≫ (X.iso_restrict_iso H).hom = 𝟙 _ :=
-- by rw [←iso_restrict_iso_inv, iso.inv_hom_id]

variables {X Y : Top.{v}} (Z : PresheafedSpace C) (f : X ⟶ Y) (hf : open_embedding f)
variables (g : Y ⟶ Z.1) (hg : open_embedding g) (h : X ⟶ Z.1) (feq : h = f ≫ g)

include feq

-- /--
-- Equal open embeddings give rise to isomorphic structured spaces.

-- The simp lemmas are provided below,
-- and the lemmas generated by `simps` are merely used to prove them.
-- -/
-- @[simps hom_base inv_base, simps hom_c_app inv_c_app (lemmas_only)]
-- def restrict_comp :
--   Z.restrict (show open_embedding h, by simpa[feq] using hg.comp hf) ≅
--     ((Z.restrict hg).restrict hf) :=
-- PresheafedSpace.iso_of_components (iso.refl X)
-- begin
--   change (opens.map (iso.refl X).hom ⋙ is_open_map.functor _).op ⋙ Z.presheaf ≅
--     (is_open_map.functor _ ⋙ is_open_map.functor _).op ⋙ Z.presheaf,
--   refine iso_whisker_right _ Z.presheaf,
--   apply nat_iso.op,
--   fapply nat_iso.of_components,
--   intro U,
--   apply eq_to_iso,
--   ext1,
--   simp only [set.image_congr, is_open_map.functor, Top.comp_app,
--     functor.comp_obj, subtype.coe_mk, feq, ←set.image_comp],
--   congr,
--   intros _ _ _,
--   simp[is_open_map.functor],
-- end

-- @[simp] lemma restrict_comp_hom_c_app' (U : (opens ((Z.restrict hg).restrict hf))ᵒᵖ) :
--   (restrict_comp Z f hf g hg h feq).hom.c.app U = Z.presheaf.map
--     (eq_to_hom (begin
--       tactic.op_induction',
--       cases U,
--       cases feq,
--       dsimp only [is_open_map.functor, opens.map, functor.op],
--       congr' 2,
--       erw set.image_image,
--       congr
--     end)) := by simpa [restrict_comp_hom_c_app]

-- @[simp] lemma restrict_comp_inv_c_app' (U : (opens ((Z.restrict hg).restrict hf))ᵒᵖ) :
--   (restrict_comp Z f hf g hg h feq).inv.c.app U = Z.presheaf.map
--     (eq_to_hom (begin
--       tactic.op_induction',
--       cases U,
--       cases feq,
--       dsimp only [is_open_map.functor, opens.map, functor.op],
--       congr' 2,
--       erw set.image_image,
--       congr
--     end)) := by { rw restrict_comp_inv_c_app, exact category.id_comp _ }

-- @[simp] lemma restrict_comp_hom_of_restrict_of_restrict :
--   (restrict_comp Z f hf g hg h feq).hom ≫ (Z.restrict hg).of_restrict hf ≫ Z.of_restrict hg =
--   Z.of_restrict (show open_embedding h, by simpa[feq] using hg.comp hf) :=
-- begin
--   ext,
--   { change ((_ ≫ _) ≫ _) ≫ _ = _,
--     iterate 3 { erw ← Z.presheaf.map_comp },
--     congr },
--   simp[PresheafedSpace.of_restrict, ←feq],
-- end

end restrict

/--
The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C :=
{ obj := λ X, (unop X).presheaf.obj (op ⊤),
  map := λ X Y f, f.unop.c.app (op ⊤) }

lemma Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

lemma Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) :
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
def map_presheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D :=
{ obj := λ X, { carrier := X.carrier, presheaf := X.presheaf ⋙ F },
  map := λ X Y f, { base := f.base, c := whisker_right f.c F }, }

@[simp] lemma map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
  ((F.map_presheaf.obj X) : Top.{v}) = (X : Top.{v}) := rfl
@[simp] lemma map_presheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
  (F.map_presheaf.obj X).presheaf = X.presheaf ⋙ F := rfl
@[simp] lemma map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).base = f.base := rfl
@[simp] lemma map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
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
