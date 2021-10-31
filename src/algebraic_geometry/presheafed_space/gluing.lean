/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.gluing
import algebraic_geometry.presheafed_space.has_colimits
import category_theory.limits.shapes.binary_products
import algebraic_geometry.stalks
import category_theory.adjunction.fully_faithful

/-!
# Gluing Topological spaces

Given a family of gluing data, consisting of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.

THe construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.gluing_data`: A structure containing the family of gluing data.
* `Top.gluing_data.glued`: The glued topological space.
    This is defined as the coequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API can
    be used.
* `Top.gluing_data.imm`: The immersion `imm i : U i ⟶ glued` for each `i : ι`.
* `Top.gluing_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `f i j x = y`. See `Top.gluing_data.imm_eq_iff_rel`.

## Main results

* `Top.gluing_data.is_open_iff`: A set in `glued` is open iff its preimage along each `imm i` is
    open.
* `Top.gluing_data.imm_jointly_surjective`: The `imm i`s are jointly surjective.
* `Top.gluing_data.glue_condition` : `f i j ≫ imm j = imm i`.
* `Top.gluing_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.gluing_data.imm_eq_iff_rel`: `imm i x = imm j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.gluing_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.gluing_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.gluing_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.gluing_data.imm_open_embedding`: Each of the `imm i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory
open category_theory.limits
namespace algebraic_geometry

universes v u

variables {C : Type u} [category.{v} C]

-- @[simps]
-- def _root_.topological_space.opens.map_map_iso {X Y : Top.{v}} (H : X ≅ Y) : opens Y ≌ opens X :=
-- { functor := opens.map H.hom,
--   inverse := opens.map H.inv,
--   unit_iso := nat_iso.of_components (λ U, eq_to_iso (by simp[opens.map, set.preimage_preimage]))
--     (by { intros _ _ _, simp }),
--   counit_iso := nat_iso.of_components (λ U, eq_to_iso (by simp[opens.map, set.preimage_preimage]))
--     (by { intros _ _ _, simp }) }

open topological_space

-- def is_open_map.functor_comp {X Y Z: Top.{u}} (f : X ⟶ Y)
--   (hf : is_open_map f) (g : Y ⟶ Z) (hg : is_open_map g) :
--   hf.functor ⋙ hg.functor = @is_open_map.functor _ _ (f ≫ g) (hg.comp hf) :=
-- begin
--   fapply category_theory.functor.ext,
--   intro U, ext, simp,
--   intros U V i, delta is_open_map.functor, simp
-- end

section end

attribute[simps] Top.presheaf.pushforward
open opposite Top.presheaf

-- local attribute [reducible] equivalence.to_adjunction

section iso
/-- A homeomorphism of spaces gives an equivalence of categories of presheaves. -/
@[simps] def iso_pushforward_equiv {X Y : Top} (H : X ≅ Y) :
  X.presheaf C ≌ Y.presheaf C :=
equivalence.congr_left (opens.map_map_iso H).symm.op

/--
If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def to_pushforward_of_iso {X Y : Top} (H : X ≅ Y) {ℱ : X.presheaf C} {𝒢 : Y.presheaf C}
  (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
(iso_pushforward_equiv H).to_adjunction.hom_equiv ℱ 𝒢 α

@[simp]
lemma to_pushforward_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : X.presheaf C} {𝒢 : Y.presheaf C}
  (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : (opens X)ᵒᵖ) :
(to_pushforward_of_iso H₁ H₂).app U =
  ℱ.map (eq_to_hom (by simp[opens.map, set.preimage_preimage])) ≫
  H₂.app (op ((opens.map H₁.inv).obj (unop U))) :=
begin
  delta to_pushforward_of_iso,
  simp only [equiv.to_fun_as_coe, nat_trans.comp_app, equivalence.equivalence_mk'_unit,
    eq_to_hom_map, iso_pushforward_equiv_unit_iso_hom_app_app, equivalence.to_adjunction,
    equivalence.equivalence_mk'_counit, iso_pushforward_equiv_inverse_map_app,
    adjunction.mk_of_unit_counit_hom_equiv_apply],
  congr
end

/--
If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforward_to_of_iso {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.presheaf C} {𝒢 : X.presheaf C}
  (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
((iso_pushforward_equiv H₁.symm).to_adjunction.hom_equiv ℱ 𝒢).symm H₂

@[simp]
lemma pushforward_to_of_iso_app {X Y : Top} (H₁ : X ≅ Y) {ℱ : Y.presheaf C} {𝒢 : X.presheaf C}
  (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : (opens X)ᵒᵖ) :
(pushforward_to_of_iso H₁ H₂).app U =
  H₂.app (op ((opens.map H₁.inv).obj (unop U))) ≫
  𝒢.map (eq_to_hom (by simp[opens.map, set.preimage_preimage])) :=
begin
  delta pushforward_to_of_iso,
  simp only [adjunction.mk_of_unit_counit_hom_equiv_symm_apply, nat_trans.comp_app,
    iso_pushforward_equiv_counit_iso_hom_app_app, equivalence.equivalence_mk'_unit,
    equivalence.to_adjunction, equivalence.equivalence_mk'_counit,
    eq_to_hom_map, iso_pushforward_equiv_functor_map_app, equiv.inv_fun_as_coe],
  congr
end

variables {X Y : PresheafedSpace C}

/--
An isomorphism of PresheafedSpaces is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps hom inv]
def PresheafedSpace.iso_of_components (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y :=
{ hom := { base := H.hom, c := α.inv },
  inv := { base := H.inv,
    c := to_pushforward_of_iso H α.hom },
  hom_inv_id' := by { ext, { simp, erw category.id_comp, simpa }, simp },
  inv_hom_id' :=
  begin
    ext x,
    induction x using opposite.rec,
    simp only [PresheafedSpace.comp_c_app, whisker_right_app, to_pushforward_of_iso_app,
      nat_trans.comp_app, eq_to_hom_app, PresheafedSpace.id_c_app, category.assoc],
    erw [←H₂.hom.naturality],
    have := congr_app (H₂.inv_hom_id) (op x),
    cases x,
    rw nat_trans.comp_app at this,
    convert this,
    { dsimp, simp },
    { simp },
    { simp }
  end }

/-- Isomorphic PresheafedSpaces have homeomorphic topological spaces. -/
def PresheafedSpace.base_iso_of_iso (H : X ≅ Y) : X.1 ≅ Y.1 :=
{ hom := H.hom.base,
  inv := H.inv.base,
  hom_inv_id' := congr_arg PresheafedSpace.hom.base H.hom_inv_id,
  inv_hom_id' := congr_arg PresheafedSpace.hom.base H.inv_hom_id }

/-- Isomorphic PresheafedSpaces have natural isomorphic presheaves. -/
def PresheafedSpace.sheaf_iso_of_iso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 :=
{ hom := H.hom.c,
  inv := pushforward_to_of_iso (PresheafedSpace.base_iso_of_iso H).symm H.inv.c,
  hom_inv_id' :=
  begin
    ext U,
    have := PresheafedSpace.congr_app H.inv_hom_id U,
    simp only [PresheafedSpace.comp_c_app, PresheafedSpace.id_c_app,
      eq_to_hom_map, eq_to_hom_trans] at this,
    generalize_proofs h at this,
    simpa using congr_arg (λ f, f ≫ eq_to_hom h.symm) this,
  end,
  inv_hom_id' :=
  begin
    ext U,
    simp only [pushforward_to_of_iso_app, nat_trans.comp_app, category.assoc,
      nat_trans.id_app, H.hom.c.naturality],
    have := PresheafedSpace.congr_app H.hom_inv_id ((opens.map H.hom.base).op.obj U),
    generalize_proofs h at this,
    simpa using congr_arg (λ f, f ≫X.presheaf.map (eq_to_hom h.symm)) this
  end }

instance PresheafedSpace.base_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.base :=
is_iso.of_iso (PresheafedSpace.base_iso_of_iso (as_iso f))

instance PresheafedSpace.c_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.c :=
is_iso.of_iso (PresheafedSpace.sheaf_iso_of_iso (as_iso f))

end iso

section end

@[simps hom_base inv_base hom_c_app inv_c_app { attrs := [] }]
def restrict_eq {X : Top} (Y : PresheafedSpace C) (f g : X ⟶ Y.1)
  (hf : open_embedding f) (hg : open_embedding g) (eq : f = g) :
  Y.restrict hf ≅ Y.restrict hg :=
PresheafedSpace.iso_of_components (iso.refl X)
begin
  refine (functor.associator _ _ _).symm.trans _,
  refine iso_whisker_right _ Y.presheaf,
  change (opens.map _ ⋙ is_open_map.functor _).op ≅ _,
  apply nat_iso.op,
  fapply nat_iso.of_components,
  { intro U,
    apply eq_to_iso,
    cases U,
    ext,
    simp only [is_open_map.functor_obj_coe, opens.map, functor.comp_obj, subtype.coe_mk, eq],
    erw iso.refl_hom,
    simp },
  { intros _ _ _,
    simp[is_open_map.functor] },
end

@[simps hom_base inv_base hom_c_app inv_c_app { attrs := [] }]
def restrict_comp {X Y : Top} (Z : PresheafedSpace C) (f : X ⟶ Y)
  (hf : open_embedding f) (g : Y ⟶ Z.1) (hg : open_embedding g) (h : X ⟶ Z.1) (eq : h = f ≫ g) :
  Z.restrict (show open_embedding h, by simpa[eq] using hg.comp hf) ≅
    ((Z.restrict hg).restrict hf) :=
PresheafedSpace.iso_of_components (iso.refl X)
begin
  refine (functor.associator _ _ _).symm.trans
  ((iso_whisker_right _ Z.presheaf).trans (functor.associator _ _ _)),
  change (opens.map _ ⋙ is_open_map.functor _).op ≅
    (is_open_map.functor _ ⋙ is_open_map.functor _).op,
  apply nat_iso.op,
  fapply nat_iso.of_components,
  intro U,
  apply eq_to_iso,
  ext1,
  simp only [set.image_congr, is_open_map.functor, Top.comp_app,
    functor.comp_obj, subtype.coe_mk, eq, ←set.image_comp],
  congr,
  intros _ _ _,
  simp[is_open_map.functor],
end

attribute [simp]  algebraic_geometry.restrict_eq_hom_base
                  algebraic_geometry.restrict_eq_inv_base
                  algebraic_geometry.restrict_comp_hom_base
                  algebraic_geometry.restrict_comp_inv_base

@[simp]
lemma restrict_eq_hom_c_app' {X : Top} (Y : PresheafedSpace C) (f g : X ⟶ Y.1)
  (hf : open_embedding f) (hg : open_embedding g) (eq : f = g) (U) :
  (restrict_eq Y f g hf hg eq).hom.c.app U = Y.presheaf.map
    (eq_to_hom (begin
      tactic.op_induction',
      cases U,
      cases eq,
      dsimp only [is_open_map.functor, opens.map, functor.op],
      congr
    end)) := by simpa [restrict_eq_hom_c_app]

@[simp]
lemma restrict_comp_hom_c_app' {X Y : Top} (Z : PresheafedSpace C) (f : X ⟶ Y) (hf : open_embedding f)
  (g : Y ⟶ Z.1) (hg : open_embedding g) (h : X ⟶ Z.1) (feq : h = f ≫ g) (U) :
  (restrict_comp Z f hf g hg h feq).hom.c.app U = Z.presheaf.map
    (eq_to_hom (begin
      tactic.op_induction',
      cases U,
      cases feq,
      dsimp only [is_open_map.functor, opens.map, functor.op],
      congr' 2,
      erw set.image_image,
      congr
    end)) := by simpa [restrict_comp_hom_c_app]

@[simp] lemma restrict_comp_hom_of_restrict_of_restrict {X Y : Top} (Z : PresheafedSpace C)
  (f : X ⟶ Y) (hf : open_embedding f) (g : Y ⟶ Z.1) (hg : open_embedding g) (h : X ⟶ Z.1)
  (eq : h = f ≫ g) :
  (restrict_comp Z f hf g hg h eq).hom ≫ (Z.restrict hg).of_restrict hf ≫ Z.of_restrict hg =
  Z.of_restrict (show open_embedding h, by simpa[eq] using hg.comp hf) :=
begin
  ext,
  { change ((_ ≫ _) ≫ (_ ≫ _) ≫ _) ≫ _ = Z.presheaf.map _,
    erw category.comp_id,
    erw category.id_comp,
    erw ←Z.presheaf.map_comp,
    erw ←Z.presheaf.map_comp,
    erw ←Z.presheaf.map_comp,
    congr },
  simp[PresheafedSpace.of_restrict, ←eq],
end


section end

variables {X Y : PresheafedSpace C} (f : X ⟶ Y)

structure open_immersion :=
(base_open : open_embedding f.base)
(iso_restrict : X ≅ Y.restrict base_open)
(fac : iso_restrict.hom ≫ Y.of_restrict _ = f)

attribute [simp] open_immersion.fac


@[simp] lemma open_immersion.inv_fac {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
  (H : open_immersion f) : H.iso_restrict.inv ≫ f = Y.of_restrict _ := by { rw iso.inv_comp_eq, simp }

@[simp, elementwise] lemma open_immersion.fac_base {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
  (H : open_immersion f) : H.iso_restrict.hom.base ≫ (Y.of_restrict _).base = f.base :=
congr_arg PresheafedSpace.hom.base H.fac

@[simp] lemma open_immersion.inv_fac_base {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
  (H : open_immersion f) : H.iso_restrict.inv.base ≫ f.base = (Y.of_restrict _).base :=
congr_arg PresheafedSpace.hom.base H.inv_fac

@[simp, elementwise]
lemma open_immersion.iso_restrict_hom_base {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
  (H : open_immersion f) : H.iso_restrict.hom.base = 𝟙 _ :=
begin
  haveI := (Top.mono_iff_injective f.base).mpr H.base_open.inj,
  rw ←cancel_mono f.base,
  refine (congr_arg PresheafedSpace.hom.base H.fac).trans (category.id_comp _).symm,
end

@[simp, elementwise]
lemma open_immersion.iso_restrict_inv_base {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
  (H : open_immersion f) : H.iso_restrict.inv.base = 𝟙 _ :=
begin
  convert congr_arg PresheafedSpace.hom.base H.iso_restrict.hom_inv_id using 1,
  simp only [PresheafedSpace.comp_base, open_immersion.iso_restrict_hom_base, category.id_comp]
end


def open_immersion.c_iso (H : open_immersion f) : X.presheaf ≅ (Y.restrict H.base_open).presheaf :=
PresheafedSpace.sheaf_iso_of_iso H.iso_restrict.symm ≪≫
iso_whisker_right (eq_to_iso
  (by { rw [open_immersion.iso_restrict_inv_base], apply functor.hext; simp }) :
    (opens.map H.iso_restrict.inv.base).op ⋙
      (is_open_map.functor _).op ≅ (is_open_map.functor _).op) (Y.presheaf)

@[simp, elementwise, reassoc]
lemma open_immersion.map_iso_restrict_hom_c_app {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
(H : open_immersion f) (U : opens (X.carrier)) :
  H.iso_restrict.hom.c.app (op U) =
  f.c.app (op (H.base_open.is_open_map.functor.obj U)) ≫ X.presheaf.map
    (eq_to_hom (by { dsimp only [opens.map, functor.op], congr' 2,
      erw set.preimage_image_eq _ H.base_open.inj, simpa })) :=
begin
  have := PresheafedSpace.congr_app H.fac (op (H.base_open.is_open_map.functor.obj U)),
  generalize_proofs _ _ h at this,
  have := congr_arg (λ x, x ≫ X.presheaf.map (eq_to_hom h.symm)) this,
  simp only [eq_to_hom_refl, category.assoc, ← X.presheaf.map_comp,
    eq_to_hom_trans, X.presheaf.map_id] at this,
  erw category.comp_id at this,
  rw [←this, category.assoc, ←functor.map_comp, eq_to_hom_trans, ←is_iso.comp_inv_eq],
  simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, inv_eq_to_hom,
    ←functor.map_inv],
  have h' := H.iso_restrict.hom.c.naturality,
  dsimp [-forall_3_true_iff] at h',
  convert (h' _).symm using 2,
  swap 4,
  { dsimp only [functor.op],
    apply quiver.hom.op, apply hom_of_le,
    rintros _ ⟨_, hx, eq⟩,
    cases H.base_open.inj eq,
    exact hx },
  { congr },
  { congr },
  { congr, simp }
end

@[simp, elementwise, reassoc]
lemma open_immersion_map_iso_restrict_inv_c_app {C : Type*} [category C] {X Y : PresheafedSpace C} {f : X ⟶ Y}
(H : open_immersion f) (U : opens (Y.carrier)) :
f.c.app (op U) ≫ H.iso_restrict.inv.c.app (op ((opens.map f.base).obj (unop (op U)))) =
  Y.presheaf.map ((@hom_of_le (opens Y.1) _ ⟨_, _⟩ U
  (by { rintros _ ⟨x, hx₂, rfl⟩, simpa using hx₂ })).op) :=
begin
have := PresheafedSpace.congr_app H.inv_fac (op U),
-- unfold PresheafedSpace.restrict at this,
simp only [PresheafedSpace.restrict, PresheafedSpace.comp_c_app,
  PresheafedSpace.of_restrict_c_app] at this,
erw ←functor.map_comp at this,
convert this,
end

section end

lemma eq_to_hom_heq_id {C : Type*} [category C] {X Y Z : C} (H : X = Y) (H' : Y = Z) :
  eq_to_hom H == 𝟙 Z := by { cases H, cases H', refl }

lemma heq_of_subsingleton (α β : Type*) [subsingleton α] (x : α) (y : β)
   (H : α = β) : x == y := by { cases H, simp, }

lemma open_immersion_map_iso_restrict_inv_c_app'
(H : open_immersion f) (U : opens X) :
  f.c.app (op (H.base_open.is_open_map.functor.obj U)) ≫
  X.presheaf.map
    (eq_to_hom (by { cases U, simp [opens.map, set.preimage_image_eq U_val H.base_open.inj] })) ≫
  H.iso_restrict.inv.c.app (op U) =
  Y.presheaf.map ((@eq_to_hom (opens Y.1) _ ⟨_, _⟩ (H.base_open.is_open_map.functor.obj U)
  (by simpa)).op) :=
begin
  have : op U = (opens.map f.base).op.obj (op (H.base_open.is_open_map.functor.obj U)),
  { cases U, simp [opens.map, set.preimage_image_eq U_val H.base_open.inj] },
  convert open_immersion_map_iso_restrict_inv_c_app H (H.base_open.is_open_map.functor.obj U),
  rw H.iso_restrict.inv.c.naturality (eq_to_hom _),
  refine heq.trans _ (heq_iff_eq.mpr (category.comp_id _)),
  congr,
  exact this,
  { rw eq_to_hom_map, apply eq_to_hom_heq_id, simp[this] },
  { apply heq_of_subsingleton, simp[this] }
end

variable {f}

lemma open_immersion.app_is_iso (H : open_immersion f) (U : opens X) :
  is_iso (f.c.app (op (H.base_open.is_open_map.functor.obj U))) :=
begin
  have :=  open_immersion_map_iso_restrict_inv_c_app' f H U,
  rw [←is_iso.eq_comp_inv] at this,
  rw this,
  apply_instance
end

abbreviation open_immersion.inv_c_app (H : open_immersion f) (U : opens X) :=
@@inv _ (f.c.app (op (H.base_open.is_open_map.functor.obj U))) (H.app_is_iso U)

lemma open_immersion.iso_restrict_inv_c_app_eq_inv_f_app
(H : open_immersion f) (U : opens X) :
  H.iso_restrict.inv.c.app (op U) =
  X.presheaf.map
    (eq_to_hom (by { cases U, simp [opens.map, set.preimage_image_eq U_val H.base_open.inj] })) ≫
  H.inv_c_app U ≫
  Y.presheaf.map ((@eq_to_hom (opens Y.1) _ ⟨_, _⟩ (H.base_open.is_open_map.functor.obj U)
  (by simpa)).op) :=
begin
  rw ← open_immersion_map_iso_restrict_inv_c_app' f H U,
  simp,
end

section end

@[simp, reassoc]
lemma open_immersion.iso_restrict_inv_comp_c_app
(H : open_immersion f) (U : opens X) :
  H.iso_restrict.inv.c.app (op U) ≫ f.c.app _ =
  X.presheaf.map
    (eq_to_hom (by { cases U, simpa [opens.map, set.preimage_image_eq _ H.base_open.inj] })) :=
begin
  rw open_immersion.iso_restrict_inv_c_app_eq_inv_f_app H U,
  simp only [category.assoc],
  rw f.c.naturality,
  simpa
end

section end

instance is_open_map.functor_full_of_mono {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f)
  [H : mono f] : full hf.functor :=
{ preimage := λ U V i, hom_of_le (λ x hx, by
  { obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩, exact (Top.mono_iff_injective f).mp H eq ▸ hy }) }

instance is_open_map.functor_faithful {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) :
  faithful hf.functor := { }

lemma is_open_map.functor_faithfuly {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f)
[H : mono f] : is_iso (hf.adjunction.unit) := infer_instance

instance whisker_left_counit_iso {C D : Type*} [category C] [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [full F] [faithful F] : is_iso (whisker_left F adj.counit) :=
begin
  have := adj.left_triangle,
  rw ←is_iso.eq_inv_comp at this,
  rw this,
  apply_instance
end

instance of_restrict_mono {U : Top} {f : U ⟶ X.1} (hf : open_embedding f) :
  mono (X.of_restrict hf) :=
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
    simp only [pushforward_obj_map, eq_to_hom_op,
      category.assoc, eq_to_hom_map, eq_to_hom_trans] at h,
    rw ←is_iso.comp_inv_eq at h,
    simpa using h },
  { have := congr_arg PresheafedSpace.hom.base eq,
    simp only [PresheafedSpace.comp_base, PresheafedSpace.of_restrict_base] at this,
    rw cancel_mono at this,
    exact this }
end

lemma open_immersion.mono (H : open_immersion f) : mono f :=
by { rw ← H.fac, apply mono_comp }


def pullback_cone_of_open_immersion {C : Type*} [category C] {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) : pullback_cone f g :=
begin
 fapply pullback_cone.mk,
 exact Z.restrict (Top.open_embedding_of_pullback_open_embeddings hf.base_open hg.base_open),
 exact (restrict_comp Z _
  (Top.fst_open_embedding_of_right_open_embedding f.base hg.base_open) f.base hf.base_open
  (limit.π (cospan f.base g.base) walking_cospan.one) (limit.w _ walking_cospan.hom.inl).symm).hom
    ≫ PresheafedSpace.of_restrict _ _ ≫ (hf.iso_restrict).inv,
 exact (restrict_comp Z _
  (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base) g.base hg.base_open
  (limit.π (cospan f.base g.base) walking_cospan.one) (limit.w _ walking_cospan.hom.inr).symm).hom
    ≫ PresheafedSpace.of_restrict _ _ ≫ (hg.iso_restrict).inv,
  simp,
end

def pullback_cone_of_open_immersion_lift {C : Type u} [category.{v} C] {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g)
  (s : pullback_cone f g) : s.X ⟶ (pullback_cone_of_open_immersion hf hg).X :=
{ base := pullback.lift s.fst.base s.snd.base
  (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition),
  c := whisker_left _ (s.π.app walking_cospan.one).c ≫
    (whisker_right (nat_trans.op
    { app := λ U, hom_of_le
      (λ x (hx : x ∈ (opens.map (pullback.lift s.fst.base s.snd.base _)).obj U),
        ⟨pullback.lift s.fst.base s.snd.base
            (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition) x, hx,
          show limit.π (cospan f.base g.base) walking_cospan.one
            (pullback.lift s.fst.base s.snd.base _ x) = (s.π.app walking_cospan.one).base x,
          by  { have := s.π.naturality walking_cospan.hom.inl,
                erw category.id_comp at this,
                simp [this] } ⟩),
      naturality' := λ _ _ _, refl _ }) s.X.presheaf
      : (is_open_map.functor _ ⋙ opens.map _).op ⋙ s.X.presheaf ⟶ _ ⋙ s.X.presheaf)}

section end

lemma pullback_cone_of_open_immersion_lift_comp_fst {C : Type u} [category.{v} C]
  {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g)
  (s : pullback_cone f g) :
pullback_cone_of_open_immersion_lift hf hg s ≫ (pullback_cone_of_open_immersion hf hg).fst = s.fst :=
begin
  delta pullback_cone_of_open_immersion_lift pullback_cone_of_open_immersion,
  ext x,
  { induction x using opposite.rec,
    let fx : ((opens.map f.base).op.obj
      (op (hf.base_open.is_open_map.functor.obj ((opens.map hf.iso_restrict.inv.base).obj x)))) ⟶
        op x,
    { apply eq_to_hom, cases x, simpa[opens.map, set.preimage_image_eq _ hf.base_open.inj] },
    have := λ x, PresheafedSpace.congr_app
      ((category.id_comp _).symm.trans (s.π.naturality walking_cospan.hom.inl : _)) x,
    dsimp only [PresheafedSpace.comp_c_app, whisker_right_app,
      nat_trans.comp_app],
    erw this,
    dsimp only [pullback_cone.mk_fst, PresheafedSpace.comp_c_app],
    erw restrict_comp_hom_c_app',
    simp only [category.assoc],
    erw ←Z.presheaf.map_comp_assoc,
    erw f.c.naturality_assoc,
    erw s.fst.c.naturality_assoc,
    rw [pushforward_obj_map],
    iterate 3 { erw [←s.X.presheaf.map_comp] },
    erw ← s.fst.c.naturality fx,
    erw hf.iso_restrict_inv_comp_c_app_assoc,
    rw [←functor.map_comp_assoc, eq_to_hom_trans, eq_to_hom_refl,
      X.presheaf.map_id, category.id_comp] },
  { change pullback.lift _ _ _ ≫ 𝟙 _ ≫ pullback.fst ≫ hf.iso_restrict.inv.base = _,
    simp only [category.comp_id, hf.iso_restrict_inv_base, category.id_comp,
      pullback.lift_fst] }
end

section end

-- set_option trace.dsimplify true
-- #help options

lemma pullback_cone_of_open_immersion_lift_comp_snd {C : Type u} [category.{v} C]
  {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g)
  (s : pullback_cone f g) :
pullback_cone_of_open_immersion_lift hf hg s ≫
  (pullback_cone_of_open_immersion hf hg).snd = s.snd :=
begin
  delta pullback_cone_of_open_immersion_lift pullback_cone_of_open_immersion,
  ext x,
  { induction x using opposite.rec,
    let gx : ((opens.map g.base).op.obj
      (op (hg.base_open.is_open_map.functor.obj ((opens.map hg.iso_restrict.inv.base).obj x)))) ⟶
        op x,
    { apply eq_to_hom, cases x, simpa[opens.map, set.preimage_image_eq _ hg.base_open.inj] },
    have := λ x, PresheafedSpace.congr_app
      ((category.id_comp _).symm.trans (s.π.naturality walking_cospan.hom.inr : _)) x,
    dsimp only [PresheafedSpace.comp_c_app, whisker_right_app,
      nat_trans.comp_app],
    erw this,
    dsimp only [pullback_cone.mk_snd, PresheafedSpace.comp_c_app],
    erw restrict_comp_hom_c_app',
    simp only [category.assoc],
    erw ←Z.presheaf.map_comp_assoc,
    erw g.c.naturality_assoc,
    erw s.snd.c.naturality_assoc,
    rw [pushforward_obj_map],
    iterate 3 { erw [←s.X.presheaf.map_comp] },
    erw ← s.snd.c.naturality gx,
    erw hg.iso_restrict_inv_comp_c_app_assoc,
    rw [←functor.map_comp_assoc, eq_to_hom_trans, eq_to_hom_refl,
      Y.presheaf.map_id, category.id_comp] },
  { change pullback.lift _ _ _ ≫ 𝟙 _ ≫ pullback.snd ≫ hg.iso_restrict.inv.base = _,
    simp only [category.comp_id, hg.iso_restrict_inv_base, category.id_comp,
      pullback.lift_snd] }
end

section end

lemma pullback_cone_π_app_one_base {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) :
  ((pullback_cone_of_open_immersion hf hg).π.app walking_cospan.one).base =
    limit.π (cospan f.base g.base) walking_cospan.one :=
begin
  delta pullback_cone_of_open_immersion,
  simp only [open_immersion.inv_fac, restrict_comp_hom_base, cospan_map_inl,
    category.assoc, PresheafedSpace.comp_base, pullback_cone.mk_π_app_one,
    PresheafedSpace.of_restrict_base, ← limit.w (cospan f.base g.base) walking_cospan.hom.inl],
  erw category.id_comp
end

def pullback_cone_open_immersion {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) :
  open_immersion ((pullback_cone_of_open_immersion hf hg).π.app walking_cospan.one) :=
{ base_open :=
  begin
    convert Top.open_embedding_of_pullback_open_embeddings hf.base_open hg.base_open,
    apply pullback_cone_π_app_one_base
  end,
  iso_restrict :=
  begin
    refine restrict_eq Z _ _ _ _ _,
    symmetry,
    apply pullback_cone_π_app_one_base,
  end,
  fac :=
  begin
    ext U,
    { dsimp only [nat_trans.comp_app, PresheafedSpace.comp_c_app, whisker_right_app],
      rw restrict_eq_hom_c_app',
      erw category_theory.functor.map_id,
      erw category.comp_id,
      dsimp only [pullback_cone_of_open_immersion, pullback_cone.mk_π_app_one,
        PresheafedSpace.comp_c_app],
      simp only [category.assoc],
      induction U using opposite.rec,
      rw open_immersion_map_iso_restrict_inv_c_app_assoc,
      rw restrict_comp_hom_c_app',
      dsimp only [PresheafedSpace.of_restrict_c_app, cospan_one, PresheafedSpace.restrict_presheaf,
        functor.comp_map],
      simp only [←functor.map_comp],
      congr },
    { simp only [restrict_eq_hom_base, PresheafedSpace.comp_base,
        PresheafedSpace.of_restrict_base],
      erw category.id_comp },
  end }

lemma pullback_cone_of_open_immersion_is_limit {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) :
  is_limit (pullback_cone_of_open_immersion hf hg) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  split,
  swap,
  exact pullback_cone_of_open_immersion_lift hf hg s,
  split,
  apply pullback_cone_of_open_immersion_lift_comp_fst,
  split,
  apply pullback_cone_of_open_immersion_lift_comp_snd,
  intros m h₁ h₂,
  haveI := (pullback_cone_open_immersion hf hg).mono,
  have := congr_arg (λ i, i ≫ f)
    (h₁.trans (pullback_cone_of_open_immersion_lift_comp_fst hf hg s).symm),
  simp only [category.assoc] at this,
  erw ← (pullback_cone_of_open_immersion hf hg).π.naturality walking_cospan.hom.inl at this,
  simp only [←category.assoc] at this,
  rw cancel_mono at this,
  erw cancel_mono (𝟙 _) at this,
  exact this,
  apply_instance
end



/--
A family of gluing data consists of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.
-/
@[nolint has_inhabited_instance]
structure glue_data : Type (max u v + 1) :=
  (ι : Type u)
  (U : ι → PresheafedSpace C)
  (V : ι × ι → PresheafedSpace C)
  (f : Π i j, V (i, j) ⟶ U i)
  (f_open : ∀ i j, open_immersion (f i j))
  (f_id : ∀ i, is_iso (f i i))
  (t : Π i j, V (i, j) ⟶ V (j, i))
  (t_id : ∀ i, t i i = 𝟙 _)
  (t' : Π i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i))
  (t_fac : ∀ i j k, t' i j k ≫ pullback.snd = pullback.fst ≫ t i j)
  (cocycle : ∀ i j k , t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _)

attribute [simp] glue_data.V_id glue_data.f_id

namespace glue_data

variable (D : glue_data.{u})

-- @[simp, reassoc, elementwise] lemma inv (i j : D.ι) :
--   D.f i j ≫ D.f j i = 𝟙 _ :=
-- begin
--   ext x,
--   change ↑(D.f j i (D.f i j x)) = ↑x,
--   have := D.cocycle i j i x (by simp),
--   rw f_id at this,
--   convert this,
--   ext, refl,
-- end

-- /-- (Implementation) The disjoint union of `U i`. -/
-- def sigma_opens : Top := ∐ D.U

-- /-- (Implementation) The family of `V i j` as topological spaces indexed by `ι × ι`. -/
-- def inters : D.ι × D.ι → Top := (λ p : D.ι × D.ι, (opens.to_Top _).obj (D.V p.1 p.2))

-- /-- (Implementation) The disjoint union of `V i j`. -/
-- def sigma_inters : Top := ∐ D.inters

-- /-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via left projection. -/
-- def left_imm : D.sigma_inters ⟶ D.sigma_opens :=
-- sigma.desc (λ p : D.ι × D.ι, opens.inclusion _ ≫ sigma.ι _ p.1)

-- /-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via right projection. -/
-- def right_imm : D.sigma_inters ⟶ D.sigma_opens :=
-- sigma.desc (λ p : D.ι × D.ι, D.f p.1 p.2 ≫ opens.inclusion _ ≫ sigma.ι _ p.2)

-- /-- (Implementation) The diagram to take colimit of. -/
-- def diagram := parallel_pair D.left_imm D.right_imm

-- /-- The glued topological space given a family of gluing data. -/
-- def glued : Top :=
-- coequalizer D.left_imm D.right_imm

-- /-- (Implementation) The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
-- def π : D.sigma_opens ⟶ D.glued :=
-- coequalizer.π _ _

-- instance π_epi : epi D.π :=
-- coequalizer.π_epi

-- lemma π_surjective : function.surjective D.π :=
-- (Top.epi_iff_surjective D.π).mp infer_instance

-- /-- The open immersion `D.U i ⟶ D.glued` for each `i`. -/
-- def imm (i : D.ι) : D.U i ⟶ D.glued :=
-- sigma.ι _ _ ≫ D.π

-- lemma is_open_iff (U : set D.glued) : is_open U ↔ ∀ i, is_open (D.imm i ⁻¹' U) :=
-- by { rw [coequalizer_is_open_iff, colimit_is_open_iff], refl }


-- lemma imm_jointly_surjective (x : D.glued) : ∃ i (y : D.U i), D.imm i y = x :=
-- begin
--   rcases D.π_surjective x with ⟨x', rfl⟩,
--   rw ← (show (coprod_iso_sigma _).inv _ = x', from congr_fun (coprod_iso_sigma _).hom_inv_id x'),
--   rcases (coprod_iso_sigma _).hom x' with ⟨i, y⟩,
--   exact ⟨i, y, by simpa⟩
-- end

-- @[simp]
-- lemma glue_condition (i j : D.ι) :
--   D.f i j ≫ opens.inclusion _ ≫ D.imm j = opens.inclusion _ ≫ D.imm i :=
-- begin
--   ext x,
--   symmetry,
--   simpa [π, left_imm, right_imm] using
--     continuous_map.congr_fun (coequalizer.condition D.left_imm D.right_imm)
--       ((sigma.ι D.inters (i, j) : _) x),
-- end

-- @[simp] lemma glue_condition_apply (i j : D.ι) (x) :
--   D.imm j ↑(D.f i j x) = D.imm i ↑x :=
-- continuous_map.congr_fun (D.glue_condition i j) x

-- /--
-- An equivalence relation on `Σ i, D.U i` that holds iff `D.imm i x = D.imm j x`.
-- See `Top.gluing_data.imm_eq_iff_rel`.
-- -/
-- inductive rel : (Σ i, D.U i) → (Σ i, D.U i) → Prop
-- | refl (x : Σ i, D.U i) : rel x x
-- | eq {i j : D.ι} (x : D.V i j) (y : D.V j i) (h : D.f i j x = y) : rel ⟨i, x⟩ ⟨j, y⟩

-- lemma rel_equiv : equivalence D.rel :=
-- ⟨ rel.refl,
--   λ x y h, by { cases h, exact h, apply rel.eq, simp [←h_h] },
--   λ _ _ _ h₁ h₂, by
--   { cases h₁ with _ i j x y, exact h₂,
--     cases x with x hx, cases y with y hy,
--     cases h₂ with _ _ k z _, exact h₁,
--     cases h₂_h,
--     cases z with z hz,
--     dsimp at *,
--     have eq : x = ↑(D.f j i ⟨z, hy⟩) := by simp [←h₁_h],
--     refine rel.eq ⟨x, _⟩ ⟨(↑(D.f j k ⟨z, _⟩) : D.U k), _⟩ _; cases eq,
--     { apply D.f_inter, exact hz },
--     { apply D.f_inter, exact hy },
--     { ext, apply D.cocycle } } ⟩

-- open category_theory.limits.walking_parallel_pair

-- lemma eqv_gen_of_π_eq {x y : ∐ D.U} (h : D.π x = D.π y) :
--   eqv_gen (types.coequalizer_rel (D.left_imm) (D.right_imm)) x y :=
-- begin
--   change colimit.ι D.diagram one x = colimit.ι D.diagram one y at h,
--   have : colimit.ι (D.diagram ⋙ forget _) one x = colimit.ι (D.diagram ⋙ forget _) one y,
--   { rw ←ι_preserves_colimits_iso_hom,
--     simp[h] },
--   have :
--     (colimit.ι (D.diagram ⋙ forget _) _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ =
--     (colimit.ι (D.diagram ⋙ forget _) _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ :=
--     (congr_arg (colim.map (diagram_iso_parallel_pair (D.diagram ⋙ forget _)).hom
--     ≫ (colimit.iso_colimit_cocone (types.coequalizer_limit _ _)).hom) this : _),
--   simp only [eq_to_hom_refl, types_comp_apply, colimit.ι_map_assoc,
--     diagram_iso_parallel_pair_hom_app, colimit.iso_colimit_cocone_ι_hom, types_id_apply] at this,
--   exact quot.eq.1 this,
-- end

-- lemma inv_image.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
--   (h : equivalence r) : equivalence (inv_image r f) :=
-- ⟨λ _, h.1 _, λ _ _ x, h.2.1 x, inv_image.trans r f h.2.2⟩

-- lemma imm_eq_iff_rel (i j : D.ι) (x : D.U i) (y : D.U j) :
--   D.imm i x = D.imm j y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
-- begin
--   split,
--   { intro h,
--     rw ← (show _ = sigma.mk i x, from congr_fun (coprod_iso_sigma D.U).inv_hom_id _),
--     rw ← (show _ = sigma.mk j y, from congr_fun (coprod_iso_sigma D.U).inv_hom_id _),
--     change inv_image D.rel (coprod_iso_sigma D.U).hom _ _,
--     simp only [Top.coprod_iso_sigma_inv_app],
--     rw ←relation.eqv_gen_iff_of_equivalence (inv_image.equivalence _ _ D.rel_equiv),
--     refine relation.eqv_gen_mono _ (D.eqv_gen_of_π_eq h : _),
--     rintros _ _ ⟨x⟩,
--     rw ← (show (coprod_iso_sigma _).inv _ = x, from congr_fun (coprod_iso_sigma _).hom_inv_id x),
--     generalize : (coprod_iso_sigma D.inters).hom x = x',
--     cases x',
--     unfold inv_image left_imm right_imm,
--     simp only [opens.inclusion_to_fun, Top.comp_app, coprod_iso_sigma_inv_app,
--       category_theory.limits.colimit.ι_desc_apply, cofan.mk_ι_app,
--       coprod_iso_sigma_hom_app, continuous_map.to_fun_eq_coe],
--     apply rel.eq,
--     simp },
--   { rintro (⟨⟩ | ⟨_, _, x,_,rfl⟩),
--     refl, simp }
-- end

-- lemma imm_injective (i : D.ι) : function.injective (D.imm i) :=
-- begin
--   intros x y h,
--   rcases (D.imm_eq_iff_rel _ _ _ _).mp h with (_ | ⟨_,_,_,_,rfl⟩); simp,
-- end

-- instance imm_mono (i : D.ι) : mono (D.imm i) :=
-- (Top.mono_iff_injective _).mpr (D.imm_injective _)

-- lemma image_inter (i j : D.ι) :
--   set.range (D.imm i) ∩ set.range (D.imm j) = D.imm i '' D.V i j :=
-- begin
--   ext x,
--   split,
--   { rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩,
--   have := (D.imm_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm),
--   cases this with _ _ _ x y h,
--   exact ⟨x₁, by simp, eq₁⟩,
--   exact ⟨x, x.property, eq₁⟩ },
--   { rintro ⟨x, hx, rfl⟩,
--     split, simp,
--     exact ⟨↑(D.f i j ⟨x, hx⟩), continuous_map.congr_fun (D.glue_condition i j) ⟨x, hx⟩⟩ }
-- end

-- lemma preimage_range (i j : D.ι) :
--   D.imm j ⁻¹' (set.range (D.imm i)) = D.V j i :=
-- by rw [←set.preimage_image_eq ↑(D.V j i) (D.imm_injective j),
--        ←image_inter, set.preimage_range_inter]

-- lemma preimage_image_eq_preimage_f (i j : D.ι) (U : set (D.U i)) :
-- D.imm j ⁻¹' (D.imm i '' U) = opens.inclusion _ '' ((D.f j i ≫ opens.inclusion _) ⁻¹' U) :=
-- begin
--   have : coe ⁻¹' (D.imm j ⁻¹' (D.imm i '' U)) = (D.f j i ≫ opens.inclusion _) ⁻¹' U,
--   { ext x,
--     conv_rhs { rw ← set.preimage_image_eq U (D.imm_injective _) },
--     generalize : D.imm i '' U = U',
--     simp },
--   change _ = coe '' _,
--   rw [←this, subtype.image_preimage_coe, subtype.val_eq_coe],
--   symmetry,
--   apply set.inter_eq_self_of_subset_left,
--   rw ← D.preimage_range i j,
--   exact set.preimage_mono (set.image_subset_range _ _),
-- end

-- lemma open_image_open (i : D.ι) (U : opens (D.U i)) : is_open (D.imm i '' U) :=
-- begin
--   rw is_open_iff,
--   intro j,
--   rw preimage_image_eq_preimage_f,
--   apply (opens.open_embedding _).is_open_map,
--   apply (D.f j i ≫ (D.V i j).inclusion).continuous_to_fun.is_open_preimage,
--   exact U.property
-- end

-- lemma imm_open_embedding (i : D.ι) : open_embedding (D.imm i) :=
-- open_embedding_of_continuous_injective_open
--   (D.imm i).continuous_to_fun (D.imm_injective i) (λ U h, D.open_image_open i ⟨U, h⟩)

end glue_data

end algebraic_geometry
