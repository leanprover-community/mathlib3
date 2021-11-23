/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.presheafed_space.has_colimits
import category_theory.limits.shapes.binary_products
import topology.sheaves.functors
import category_theory.limits.preserves.shapes.pullbacks
import algebraic_geometry.Scheme

/-!
# Open immersions of presheafed spaces

We say that a morphism of presheaved spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

## Main definitions

* `algebraic_geometry.PresheafedSpace.is_open_immersion`: the `Prop`-valued typeclass asserting
  that `f` is an open_immersion
* `algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left`: An explicit limit
  cocone of the pullback of `f, g` if `f` is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.lift`: If `f : X ⟶ U ⊆ Z` is an
  open immersion, then for each `Y ⟶ Z` whose image falls in `U`, we may lift it into a unique
  `Y ⟶ X` that commutes with them.

## Main results

* `algebraic_geometry.PresheafedSpace.is_open_immersion.comp`: The composition of two open
  immersions is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso`: An iso is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`: An epic open immersion is iso.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`: An epic open immersion is iso.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left`: If `f` is an
  open immersion, then the pullback of `f, g` exists. There is also `has_pullback_of_right`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left`: Open immersions
  are stable under pullback. There is also `pullback_fst_of_right`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_one_is_open_immersion`:
  The pullback of two open immersions is an open immersion.


We also proves that the pullback of two presheaved spaces exists, and is also an open immersion.
-/

open topological_space category_theory opposite
open category_theory.limits
namespace algebraic_geometry

universes v u

variables {C : Type u} [category.{v} C]

/--
An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.is_open_immersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop :=
(base_open : open_embedding f.base)
(c_iso : ∀ U : opens X, is_iso (f.c.app (op (base_open.is_open_map.functor.obj U))))

/--
A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbreviation SheafedSpace.is_open_immersion [has_products C] {X Y : SheafedSpace C} (f : X ⟶ Y) :
  Prop := PresheafedSpace.is_open_immersion f

/--
A morphism of LocallyRingedSpace is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbreviation LocallyRingedSpace.is_open_immersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) :
  Prop := SheafedSpace.is_open_immersion f.1

namespace PresheafedSpace.is_open_immersion

open PresheafedSpace

attribute [instance] is_open_immersion.c_iso

section

variables {X Y : PresheafedSpace C} {f : X ⟶ Y} (H : is_open_immersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbreviation open_functor := H.base_open.is_open_map.functor

local attribute [-simp] eq_to_hom_map eq_to_iso_map

/-- An open immersion `f : X ⟶ Y` induces an isomorphsm `X ≅ Y|_{f(X)}`. -/
@[simps] noncomputable
def iso_restrict : X ≅ Y.restrict H.base_open :=
PresheafedSpace.iso_of_components (iso.refl _)
begin
  symmetry,
  fapply nat_iso.of_components,
  intro U,
  refine as_iso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eq_to_iso _),
  { induction U using opposite.rec,
    cases U,
    dsimp only [is_open_map.functor, functor.op, opens.map],
    congr' 2,
    erw set.preimage_image_eq _ H.base_open.inj,
    refl },
  { intros U V i,
    simp only [category_theory.eq_to_iso.hom, Top.presheaf.pushforward_obj_map, category.assoc,
      functor.op_map, iso.trans_hom, as_iso_hom, functor.map_iso_hom, ←X.presheaf.map_comp],
    erw [f.c.naturality_assoc, ←X.presheaf.map_comp],
    congr }
end

@[simp] lemma iso_restrict_hom_of_restrict : H.iso_restrict.hom ≫ Y.of_restrict _ = f :=
begin
  ext,
  { simp only [comp_c_app, iso_restrict_hom_c_app, nat_trans.comp_app,
      eq_to_hom_refl, of_restrict_c_app, category.assoc, whisker_right_id'],
    erw [category.comp_id, f.c.naturality_assoc, ←X.presheaf.map_comp],
    transitivity f.c.app x ≫ X.presheaf.map (𝟙 _),
    { congr },
    { erw [X.presheaf.map_id, category.comp_id] } },
  { simp }
end

@[simp] lemma iso_restrict_inv_of_restrict : H.iso_restrict.inv ≫ f = Y.of_restrict _ :=
by { rw iso.inv_comp_eq, simp }

instance mono [H : is_open_immersion f] : mono f :=
by { rw ← H.iso_restrict_hom_of_restrict, apply mono_comp }

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : is_open_immersion f] (g : Y ⟶ Z)
  [hg : is_open_immersion g] :
  is_open_immersion (f ≫ g) :=
{ base_open := hg.base_open.comp hf.base_open,
  c_iso := λ U,
  begin
    generalize_proofs h,
    dsimp only [algebraic_geometry.PresheafedSpace.comp_c_app, unop_op, functor.op, comp_base,
      Top.presheaf.pushforward_obj_obj, opens.map_comp_obj],
    apply_with is_iso.comp_is_iso { instances := ff },
    swap,
    { have : (opens.map g.base).obj (h.functor.obj U) = hf.open_functor.obj U,
      { dsimp only [opens.map, is_open_map.functor, PresheafedSpace.comp_base],
        congr' 1,
        rw [coe_comp, ←set.image_image, set.preimage_image_eq _ hg.base_open.inj] },
      rw this,
      apply_instance },
    { have : h.functor.obj U = hg.open_functor.obj (hf.open_functor.obj U),
      { dsimp only [is_open_map.functor],
        congr' 1,
        rw [comp_base, coe_comp, ←set.image_image],
        congr },
      rw this,
      apply_instance }
  end
}

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable
def inv_app (U : opens X) : X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (H.open_functor.obj U)) :=
X.presheaf.map (eq_to_hom (by simp [opens.map, set.preimage_image_eq _ H.base_open.inj])) ≫
  inv (f.c.app (op (H.open_functor.obj U)))

@[simp, reassoc] lemma inv_naturality {U V : (opens X)ᵒᵖ} (i : U ⟶ V) :
  X.presheaf.map i ≫ H.inv_app (unop V) = H.inv_app (unop U) ≫
    Y.presheaf.map (H.open_functor.op.map i) :=
begin
  simp only [inv_app, ←category.assoc],
  rw [is_iso.comp_inv_eq],
  simp only [category.assoc, f.c.naturality, is_iso.inv_hom_id_assoc, ← X.presheaf.map_comp],
  erw ← X.presheaf.map_comp,
  congr
end

instance (U : opens X) : is_iso (H.inv_app U) := by { delta inv_app, apply_instance }

lemma inv_inv_app (U : opens X) :
  inv (H.inv_app U) = f.c.app (op (H.open_functor.obj U)) ≫
    X.presheaf.map (eq_to_hom (by simp [opens.map, set.preimage_image_eq _ H.base_open.inj])) :=
begin
  rw ← cancel_epi (H.inv_app U),
  rw is_iso.hom_inv_id,
  delta inv_app,
  simp [← functor.map_comp]
end

@[simp, reassoc] lemma inv_app_app (U : opens X) :
  H.inv_app U ≫ f.c.app (op (H.open_functor.obj U)) =
    X.presheaf.map (eq_to_hom (by simp [opens.map, set.preimage_image_eq _ H.base_open.inj])) :=
by rw [inv_app, category.assoc, is_iso.inv_hom_id, category.comp_id]

@[simp, reassoc] lemma app_inv_app (U : opens Y) :
  f.c.app (op U) ≫ H.inv_app ((opens.map f.base).obj U) =
  Y.presheaf.map ((hom_of_le (by exact set.image_preimage_subset f.base U)).op :
    op U ⟶ op (H.open_functor.obj ((opens.map f.base).obj U))) :=
by { erw ← category.assoc, rw [is_iso.comp_inv_eq, f.c.naturality], congr }

/-- A variant of `app_inv_app` that gives an `eq_to_hom` instead of `hom_of_le`. -/
@[reassoc] lemma app_inv_app' (U : opens Y) (hU : (U : set Y) ⊆ set.range f.base) :
  f.c.app (op U) ≫ H.inv_app ((opens.map f.base).obj U) =
  Y.presheaf.map (eq_to_hom (by
    { apply has_le.le.antisymm,
      { exact set.image_preimage_subset f.base U.1 },
      { change U ⊆ _,
        refine has_le.le.trans_eq _ (@set.image_preimage_eq_inter_range _ _ f.base U.1).symm,
        exact set.subset_inter_iff.mpr ⟨λ _ h, h, hU⟩ } })).op :=
by { erw ← category.assoc, rw [is_iso.comp_inv_eq, f.c.naturality], congr }

/-- An isomorphism is an open immersion. -/
instance of_iso {X Y : PresheafedSpace C} (H : X ≅ Y) : is_open_immersion H.hom :=
{ base_open := (Top.homeo_of_iso ((forget C).map_iso H)).open_embedding,
  c_iso := λ _, infer_instance }

@[priority 100]
instance of_is_iso {X Y : PresheafedSpace C} (f : X ⟶ Y) [is_iso f] : is_open_immersion f :=
algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso (as_iso f)

instance of_restrict {X : Top} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
  (hf : open_embedding f) : is_open_immersion (Y.of_restrict hf) :=
{ base_open := hf,
  c_iso := λ U,
  begin
    dsimp,
    have : (opens.map f).obj (hf.is_open_map.functor.obj U) = U,
    { cases U,
      dsimp only [opens.map, is_open_map.functor],
      congr' 1,
      rw set.preimage_image_eq _ hf.inj,
      refl },
    convert (show is_iso (Y.presheaf.map (𝟙 _)), from infer_instance),
    { apply subsingleton.helim,
      rw this },
    { rw Y.presheaf.map_id,
      apply_instance }
  end }

/-- This could be used in conjunction with `category_theory.nat_iso.is_iso_of_is_iso_app`. -/
lemma is_iso_of_components (f : X ⟶ Y) [is_iso f.base] [is_iso f.c] : is_iso f :=
begin
  convert is_iso.of_iso (iso_of_components (as_iso f.base) (as_iso f.c).symm),
  ext, { simpa }, { simp },
end

lemma to_iso (f : X ⟶ Y) [h : is_open_immersion f] [h' : epi f.base] : is_iso f :=
begin
  apply_with is_iso_of_components { instances := ff },
  { let : X ≃ₜ Y := (homeomorph.of_embedding _ h.base_open.to_embedding).trans
    { to_fun := subtype.val, inv_fun := λ x, ⟨x,
      by { rw set.range_iff_surjective.mpr ((Top.epi_iff_surjective _).mp h'), trivial }⟩,
      left_inv := λ ⟨_,_⟩, rfl, right_inv := λ _, rfl },
    convert is_iso.of_iso (Top.iso_of_homeo this),
    { ext, refl } },
  { apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
    intro U,
    have : U = op (h.open_functor.obj ((opens.map f.base).obj (unop U))),
    { induction U using opposite.rec,
      cases U,
      dsimp only [functor.op, opens.map],
      congr,
      exact (set.image_preimage_eq _ ((Top.epi_iff_surjective _).mp h')).symm },
    convert @@is_open_immersion.c_iso _ h ((opens.map f.base).obj (unop U)) }
end

instance stalk_iso [has_colimits C] [H : is_open_immersion f] (x : X) : is_iso (stalk_map f x) :=
begin
  rw ← H.iso_restrict_hom_of_restrict,
  rw PresheafedSpace.stalk_map.comp,
  apply_instance
end

end

section pullback
noncomputable theory

variables {X Y Z : PresheafedSpace C} (f : X ⟶ Z) [hf : is_open_immersion f] (g : Y ⟶ Z)

include hf

/--
  (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullback_cone_of_left_fst :
  Y.restrict (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base) ⟶ X :=
{ base := pullback.fst,
  c :=
  { app := λ U, hf.inv_app (unop U) ≫
      g.c.app (op (hf.base_open.is_open_map.functor.obj (unop U))) ≫
      Y.presheaf.map (eq_to_hom
      (begin
        simp only [is_open_map.functor, subtype.mk_eq_mk, unop_op, op_inj_iff, opens.map,
        subtype.coe_mk, functor.op_obj, subtype.val_eq_coe],
        apply has_le.le.antisymm,
          { rintros _ ⟨_, h₁, h₂⟩,
            use (Top.pullback_iso_prod_subtype _ _).inv ⟨⟨_, _⟩, h₂⟩,
            simpa using h₁ },
          { rintros _ ⟨x, h₁, rfl⟩,
            exact ⟨_, h₁, concrete_category.congr_hom pullback.condition x⟩ }
      end)),
    naturality' :=
    begin
      intros U V i,
      induction U using opposite.rec,
      induction V using opposite.rec,
      simp only [quiver.hom.unop_op, Top.presheaf.pushforward_obj_map, category.assoc,
        nat_trans.naturality_assoc, functor.op_map, inv_naturality_assoc, ← Y.presheaf.map_comp],
      erw ← Y.presheaf.map_comp,
      congr
    end } }

lemma pullback_cone_of_left_condition :
  pullback_cone_of_left_fst f g ≫ f = Y.of_restrict _ ≫ g :=
begin
  ext U,
  { induction U using opposite.rec,
    dsimp only [comp_c_app, nat_trans.comp_app, unop_op,
      whisker_right_app, pullback_cone_of_left_fst],
    simp only [quiver.hom.unop_op, Top.presheaf.pushforward_obj_map, app_inv_app_assoc,
      eq_to_hom_app, eq_to_hom_unop, category.assoc, nat_trans.naturality_assoc, functor.op_map],
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp],
    congr },
  { simpa using pullback.condition }
end

/--
We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullback_cone_of_left : pullback_cone f g :=
pullback_cone.mk (pullback_cone_of_left_fst f g) (Y.of_restrict _)
  (pullback_cone_of_left_condition f g)

variable (s : pullback_cone f g)

/--
  (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullback_cone_of_left_lift : s.X ⟶ (pullback_cone_of_left f g).X :=
{ base := pullback.lift s.fst.base s.snd.base
  (congr_arg (λ x, PresheafedSpace.hom.base x) s.condition),
  c :=
  { app := λ U, s.snd.c.app _ ≫ s.X.presheaf.map (eq_to_hom (begin
      dsimp only [opens.map, is_open_map.functor, functor.op],
      congr' 2,
      let s' : pullback_cone f.base g.base := pullback_cone.mk s.fst.base s.snd.base _,
      have : _ = s.snd.base := limit.lift_π s' walking_cospan.right,
      conv_lhs { erw ← this, rw coe_comp, erw ← set.preimage_preimage },
      erw set.preimage_image_eq _
        (Top.snd_open_embedding_of_left_open_embedding hf.base_open g.base).inj,
      simp,
    end)),
    naturality' := λ U V i,
    begin
      erw s.snd.c.naturality_assoc,
      rw category.assoc,
      erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp],
      congr
    end } }

lemma pullback_cone_of_left_lift_fst :
  pullback_cone_of_left_lift f g s ≫
    (pullback_cone_of_left f g).fst = s.fst :=
begin
  ext x,
  { induction x using opposite.rec,
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _,
    simp_rw [category.assoc],
    erw ← s.X.presheaf.map_comp,
    erw s.snd.c.naturality_assoc,
    have := congr_app s.condition (op (hf.open_functor.obj x)),
    dsimp only [comp_c_app, unop_op] at this,
    rw ← is_iso.comp_inv_eq at this,
    reassoc! this,
    erw [← this, hf.inv_app_app_assoc, s.fst.c.naturality_assoc],
    simpa },
  { change pullback.lift _ _ _ ≫ pullback.fst = _,
    simp }
end

lemma pullback_cone_of_left_lift_snd :
  pullback_cone_of_left_lift f g s ≫
    (pullback_cone_of_left f g).snd = s.snd :=
begin
  ext x,
  { change (_ ≫ _ ≫ _) ≫ _ = _,
    simp_rw category.assoc,
    erw s.snd.c.naturality_assoc,
    erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp],
    transitivity s.snd.c.app x ≫ s.X.presheaf.map (𝟙 _),
    { congr },
    { rw s.X.presheaf.map_id, erw category.comp_id } },
  { change pullback.lift _ _ _ ≫ pullback.snd = _,
    simp }
end

instance pullback_cone_snd_is_open_immersion :
  is_open_immersion (pullback_cone_of_left f g).snd :=
begin
  erw category_theory.limits.pullback_cone.mk_snd,
  apply_instance
end

/-- The constructed pullback cone is indeed the pullback. -/
def pullback_cone_of_left_is_limit :
  is_limit (pullback_cone_of_left f g) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  split,
  swap,
  exact pullback_cone_of_left_lift f g s,
  split,
  apply pullback_cone_of_left_lift_fst,
  split,
  apply pullback_cone_of_left_lift_snd,
  intros m h₁ h₂,
  rw ← cancel_mono (pullback_cone_of_left f g).snd,
  exact (h₂.trans (pullback_cone_of_left_lift_snd f g s).symm)
end

instance has_pullback_of_left :
  has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_left_is_limit f g⟩⟩⟩

instance has_pullback_of_right :
  has_pullback g f := has_pullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
  is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
begin
  delta pullback.snd,
  rw ← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right,
  apply_instance
end

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
  is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
begin
  rw ← pullback_symmetry_hom_comp_snd,
  apply_instance
end

instance pullback_one_is_open_immersion [is_open_immersion g] :
  is_open_immersion (limit.π (cospan f g) walking_cospan.one) :=
begin
  rw [←limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl],
  apply_instance
end

instance forget_preserves_limits_of_left : preserves_limit (cospan f g) (forget C) :=
preserves_limit_of_preserves_limit_cone (pullback_cone_of_left_is_limit f g)
begin
  apply (is_limit.postcompose_hom_equiv (diagram_iso_cospan _) _).to_fun,
  refine (is_limit.equiv_iso_limit _).to_fun (limit.is_limit (cospan f.base g.base)),
  fapply cones.ext,
  exact (iso.refl _),
  change ∀ j, _ = 𝟙 _ ≫ _ ≫ _,
  simp_rw category.id_comp,
  rintros (_|_|_); symmetry,
  { erw category.comp_id,
    exact limit.w (cospan f.base g.base) walking_cospan.hom.inl },
  { exact category.comp_id _ },
  { exact category.comp_id _ },
end

instance forget_preserves_limits_of_right : preserves_limit (cospan g f) (forget C) :=
preserves_pullback_symmetry (forget C) f g

lemma pullback_snd_is_iso_of_range_subset (H : set.range g.base ⊆ set.range f.base) :
  is_iso (pullback.snd : pullback f g ⟶ _) :=
begin
  haveI := Top.snd_iso_of_left_embedding_range_subset hf.base_open.to_embedding g.base H,
  haveI : is_iso (pullback.snd : pullback f g ⟶ _).base,
  { delta pullback.snd,
    rw ← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right,
    change is_iso (_ ≫ pullback.snd),
    apply_instance },
  apply to_iso
end

/--
The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : set.range g.base ⊆ set.range f.base) : Y ⟶ X :=
begin
  haveI := pullback_snd_is_iso_of_range_subset f g H,
  exact inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst,
end

@[simp, reassoc] lemma lift_fac (H : set.range g.base ⊆ set.range f.base) :
  lift f g H ≫ f = g :=
by { erw category.assoc, rw is_iso.inv_comp_eq, exact pullback.condition }

lemma lift_uniq (H : set.range g.base ⊆ set.range f.base) (l : Y ⟶ X)
  (hl : l ≫ f = g) : l = lift f g H :=
by rw [← cancel_mono f, hl, lift_fac]

def iso_of_range_eq [is_open_immersion g] (e : set.range f.base = set.range g.base) :
  X ≅ Y :=
{ hom := lift g f (le_of_eq e),
  inv := lift f g (le_of_eq e.symm),
  hom_inv_id' := by { rw ← cancel_mono f, simp },
  inv_hom_id' := by { rw ← cancel_mono g, simp } }

end pullback

open category_theory.limits.walking_cospan

section to_SheafedSpace

variables [has_products C] {X : PresheafedSpace C} (Y : SheafedSpace C)
variables (f : X ⟶ Y.to_PresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def to_SheafedSpace : SheafedSpace C :=
{ is_sheaf :=
  begin
    apply Top.presheaf.is_sheaf_of_iso (sheaf_iso_of_iso H.iso_restrict.symm).symm,
    apply Top.sheaf.pushforward_sheaf_of_sheaf,
    exact (Y.restrict H.base_open).is_sheaf
  end,
to_PresheafedSpace := X }

@[simp] lemma to_SheafedSpace_to_PresheafedSpace : (to_SheafedSpace Y f).to_PresheafedSpace = X :=
rfl

/--
If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def to_SheafedSpace_hom : to_SheafedSpace Y f ⟶ Y := f

@[simp] lemma to_SheafedSpace_hom_base : (to_SheafedSpace_hom Y f).base = f.base := rfl

@[simp] lemma to_SheafedSpace_hom_c : (to_SheafedSpace_hom Y f).c = f.c := rfl

instance to_SheafedSpace_hom_forget_is_open_immersion :
  SheafedSpace.is_open_immersion (to_SheafedSpace_hom Y f) := H

omit H

@[simp] lemma SheafedSpace_to_SheafedSpace {X Y : SheafedSpace C} (f : X ⟶ Y)
  [is_open_immersion f] : to_SheafedSpace Y f = X := by unfreezingI { cases X, refl }

end to_SheafedSpace

section to_LocallyRingedSpace

variables {X : PresheafedSpace CommRing.{u}} (Y : LocallyRingedSpace.{u})
variables (f : X ⟶ Y.to_PresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def to_LocallyRingedSpace : LocallyRingedSpace :=
{ to_SheafedSpace := to_SheafedSpace Y.to_SheafedSpace f,
  local_ring := λ x, begin
    haveI : local_ring (Y.to_SheafedSpace.to_PresheafedSpace.stalk (f.base x)) := Y.local_ring _,
    exact (as_iso (stalk_map f x)).CommRing_iso_to_ring_equiv.local_ring
  end }

@[simp] lemma to_LocallyRingedSpace_to_SheafedSpace :
  (to_LocallyRingedSpace Y f).to_SheafedSpace = (to_SheafedSpace Y.1 f) := rfl

/--
If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def to_LocallyRingedSpace_hom : to_LocallyRingedSpace Y f ⟶ Y := ⟨f, λ x, infer_instance⟩

@[simp] lemma to_LocallyRingedSpace_hom_val :
  (to_LocallyRingedSpace_hom Y f).val = f := rfl

instance to_LocallyRingedSpace_hom_hom_forget_is_open_immersion :
  LocallyRingedSpace.is_open_immersion (to_LocallyRingedSpace_hom Y f) := H

omit H

@[simp] lemma LocallyRingedSpace_to_LocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  [LocallyRingedSpace.is_open_immersion f] :
  @to_LocallyRingedSpace X.to_PresheafedSpace Y (@@coe (@@coe_to_lift (@@coe_base coe_subtype)) f)
    (show is_open_immersion f.val, by apply_instance) = X :=
by unfreezingI { cases X, delta to_LocallyRingedSpace, simp }

end to_LocallyRingedSpace

end PresheafedSpace.is_open_immersion

namespace SheafedSpace.is_open_immersion

variables [has_products C]

section pullback

variables {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : SheafedSpace.is_open_immersion f]

include H

local notation `forget` := SheafedSpace.forget_to_PresheafedSpace
open category_theory.limits.walking_cospan

instance : mono f := faithful_reflects_mono forget
  (show @mono (PresheafedSpace C) _ _ _ f, by apply_instance)

instance forget_map_is_open_immersion :
  PresheafedSpace.is_open_immersion (forget .map f) := ⟨H.base_open, H.c_iso⟩

instance has_limit_cospan_forget_of_left : has_limit (cospan f g ⋙ forget) :=
begin
  apply has_limit_of_iso (diagram_iso_cospan _).symm,
  change has_limit (cospan (forget .map f) (forget .map g)),
  apply_instance
end

instance has_limit_cospan_forget_of_left' : has_limit (cospan ((cospan f g ⋙ forget).map hom.inl)
  ((cospan f g ⋙ forget).map hom.inr)) :=
show has_limit (cospan (forget .map f) (forget .map g)), from infer_instance

instance has_limit_cospan_forget_of_right : has_limit (cospan g f ⋙ forget) :=
begin
  apply has_limit_of_iso (diagram_iso_cospan _).symm,
  change has_limit (cospan (forget .map g) (forget .map f)),
  apply_instance
end

instance has_limit_cospan_forget_of_right' : has_limit (cospan ((cospan g f ⋙ forget).map hom.inl)
  ((cospan g f ⋙ forget).map hom.inr)) :=
show has_limit (cospan (forget .map g) (forget .map f)), from infer_instance


instance forget_creates_pullback_of_left : creates_limit (cospan f g) forget :=
creates_limit_of_fully_faithful_of_iso
  (PresheafedSpace.is_open_immersion.to_SheafedSpace Y
    (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
  (eq_to_iso (show pullback _ _ = pullback _ _, by congr)
    ≪≫ has_limit.iso_of_nat_iso (diagram_iso_cospan _).symm)

instance forget_creates_pullback_of_right : creates_limit (cospan g f) forget :=
creates_limit_of_fully_faithful_of_iso
  (PresheafedSpace.is_open_immersion.to_SheafedSpace Y
    (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
  (eq_to_iso (show pullback _ _ = pullback _ _, by congr)
    ≪≫ has_limit.iso_of_nat_iso (diagram_iso_cospan _).symm)

instance SheafedSpace_forget_preserves_of_left :
  preserves_limit (cospan f g) (SheafedSpace.forget C) :=
@@limits.comp_preserves_limit _ _ _ _ forget (PresheafedSpace.forget C) _
begin
  apply_with (preserves_limit_of_iso_diagram _ (diagram_iso_cospan _).symm) { instances := tt },
  dsimp,
  apply_instance
end

instance SheafedSpace_forget_preserves_of_right :
  preserves_limit (cospan g f) (SheafedSpace.forget C) :=
preserves_pullback_symmetry _ _ _

instance SheafedSpace_has_pullback_of_left : has_pullback f g :=
  has_limit_of_created (cospan f g) forget

instance SheafedSpace_has_pullback_of_right : has_pullback g f :=
  has_limit_of_created (cospan g f) forget

/-- Open immersions are stable under base-change. -/
instance SheafedSpace_pullback_snd_of_left :
  SheafedSpace.is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
begin
  delta pullback.snd,
  have : _ = limit.π (cospan f g) right := preserves_limits_iso_hom_π
      forget (cospan f g) right,
  rw ← this,
  have := has_limit.iso_of_nat_iso_hom_π
    (diagram_iso_cospan (cospan f g ⋙ forget))
    right,
  erw category.comp_id at this,
  rw ← this,
  dsimp,
  apply_instance
end

instance SheafedSpace_pullback_fst_of_right :
  SheafedSpace.is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
begin
  delta pullback.fst,
  have : _ = limit.π (cospan g f) left := preserves_limits_iso_hom_π
      forget (cospan g f) left,
  rw ← this,
  have := has_limit.iso_of_nat_iso_hom_π
    (diagram_iso_cospan (cospan g f ⋙ forget)) left,
  erw category.comp_id at this,
  rw ← this,
  dsimp,
  apply_instance
end

instance SheafedSpace_pullback_one_is_open_immersion [SheafedSpace.is_open_immersion g] :
  SheafedSpace.is_open_immersion (limit.π (cospan f g) one : pullback f g ⟶ Z) :=
begin
  rw [←limit.w (cospan f g) hom.inl, cospan_map_inl],
  apply_instance
end

end pullback

variables [has_limits C] [has_colimits C] [concrete_category.{v} C]
variables [reflects_isomorphisms (forget C)] [preserves_limits (forget C)]
variables [preserves_filtered_colimits (forget C)]

/--
Suppose `C` is a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then an (topological) open embedding is an open immersion
iff every stalk map is an iso.
-/
lemma of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y)
  (hf : open_embedding f.base) [H : ∀ x : X, is_iso (PresheafedSpace.stalk_map f x)] :
  SheafedSpace.is_open_immersion f :=
{ base_open := hf,
  c_iso := λ U, begin
    apply_with (Top.presheaf.app_is_iso_of_stalk_functor_map_iso
      (show Y.sheaf ⟶ (Top.sheaf.pushforward f.base).obj X.sheaf, from f.c)) { instances := ff },
    rintros ⟨_, y, hy, rfl⟩,
    specialize H y,
    delta PresheafedSpace.stalk_map at H,
    haveI H' := Top.presheaf.stalk_pushforward.stalk_pushforward_iso_of_open_embedding
      C hf X.presheaf y,
    have := @@is_iso.comp_is_iso _ H (@@is_iso.inv_is_iso _ H'),
    rw [category.assoc, is_iso.hom_inv_id, category.comp_id] at this,
    exact this
  end }

end SheafedSpace.is_open_immersion

namespace LocallyRingedSpace.is_open_immersion

section pullback

instance is_local_ring_hom_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) [is_local_ring_hom f]
  [is_local_ring_hom g] : is_local_ring_hom (f ≫ g) := is_local_ring_hom_comp _ _

variables {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : LocallyRingedSpace.is_open_immersion f]

@[priority 100]
instance of_is_iso [is_iso g] :
  LocallyRingedSpace.is_open_immersion g :=
@@PresheafedSpace.is_open_immersion.of_is_iso _ g.1 ⟨⟨(inv g).1,
  by { erw ← LocallyRingedSpace.comp_val, rw is_iso.hom_inv_id,
    erw ← LocallyRingedSpace.comp_val, rw is_iso.inv_hom_id, split; simpa }⟩⟩

include H

instance comp (g : Z ⟶ Y) [LocallyRingedSpace.is_open_immersion g] :
  LocallyRingedSpace.is_open_immersion (f ≫ g) := PresheafedSpace.is_open_immersion.comp f.1 g.1

instance mono : mono f :=
faithful_reflects_mono (LocallyRingedSpace.forget_to_SheafedSpace)
  (show mono f.1, by apply_instance)

instance : SheafedSpace.is_open_immersion (LocallyRingedSpace.forget_to_SheafedSpace.map f) := H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullback_cone_of_left : pullback_cone f g :=
begin
  refine pullback_cone.mk _
    (Y.of_restrict (Top.snd_open_embedding_of_left_open_embedding H.base_open g.1.base)) _,
  { use PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst f.1 g.1,
    intro x,
    have := PresheafedSpace.stalk_map.congr_hom _ _
      (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition f.1 g.1) x,
    rw [PresheafedSpace.stalk_map.comp, PresheafedSpace.stalk_map.comp] at this,
    rw ← is_iso.eq_inv_comp at this,
    rw this,
    apply_instance },
  { exact subtype.eq (PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition _ _) },
end

instance : LocallyRingedSpace.is_open_immersion (pullback_cone_of_left f g).snd :=
show PresheafedSpace.is_open_immersion (Y.to_PresheafedSpace.of_restrict _), by apply_instance

/-- The constructed `pullback_cone_of_left` is indeed limiting. -/
def pullback_cone_of_left_is_limit : is_limit (pullback_cone_of_left f g) :=
pullback_cone.is_limit_aux' _ $ λ s,
begin
  use PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift f.1 g.1
    (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg subtype.val s.condition)),
  { intro x,
    have := PresheafedSpace.stalk_map.congr_hom _ _
      (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
        (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg subtype.val s.condition))) x,
    change _ = _ ≫ PresheafedSpace.stalk_map s.snd.1 x at this,
    rw [PresheafedSpace.stalk_map.comp, ← is_iso.eq_inv_comp] at this,
    rw this,
    apply_instance },
  split,
  exact subtype.eq (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst f.1 g.1 _),
  split,
  exact subtype.eq (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1 _),
  intros m h₁ h₂,
  rw ← cancel_mono (pullback_cone_of_left f g).snd,
  exact (h₂.trans (subtype.eq
    (PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd f.1 g.1
      (pullback_cone.mk s.fst.1 s.snd.1 (congr_arg subtype.val s.condition))).symm))
end

instance has_pullback_of_left :
  has_pullback f g :=
⟨⟨⟨_, pullback_cone_of_left_is_limit f g⟩⟩⟩

instance has_pullback_of_right :
  has_pullback g f := has_pullback_symmetry f g

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
  LocallyRingedSpace.is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
begin
  delta pullback.snd,
  rw ← limit.iso_limit_cone_hom_π ⟨_, pullback_cone_of_left_is_limit f g⟩ walking_cospan.right,
  apply_instance
end

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
 LocallyRingedSpace.is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
begin
  rw ← pullback_symmetry_hom_comp_snd,
  apply_instance
end

instance pullback_one_is_open_immersion [LocallyRingedSpace.is_open_immersion g] :
  LocallyRingedSpace.is_open_immersion (limit.π (cospan f g) walking_cospan.one) :=
begin
  rw [←limit.w (cospan f g) walking_cospan.hom.inl, cospan_map_inl],
  apply_instance
end

instance forget_preserves_pullback_of_left :
  preserves_limit (cospan f g) LocallyRingedSpace.forget_to_SheafedSpace :=
preserves_limit_of_preserves_limit_cone (pullback_cone_of_left_is_limit f g)
begin
  apply (is_limit_map_cone_pullback_cone_equiv _ _).symm.to_fun,
  apply is_limit_of_is_limit_pullback_cone_map SheafedSpace.forget_to_PresheafedSpace,
  exact PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit f.1 g.1
end

instance forget_reflects_pullback_of_left :
  reflects_limit (cospan f g) LocallyRingedSpace.forget_to_SheafedSpace :=
reflects_limit_of_reflects_isomorphisms _ _

instance forget_preserves_pullback_of_right :
  preserves_limit (cospan g f) LocallyRingedSpace.forget_to_SheafedSpace :=
preserves_pullback_symmetry _ _ _

instance forget_reflects_pullback_of_right :
  reflects_limit (cospan g f) LocallyRingedSpace.forget_to_SheafedSpace :=
reflects_limit_of_reflects_isomorphisms _ _

end pullback

def iso_restrict {X Y : LocallyRingedSpace} {f : X ⟶ Y}
  (H : LocallyRingedSpace.is_open_immersion f) : X ≅ Y.restrict H.base_open :=
begin
  apply LocallyRingedSpace.iso_of_SheafedSpace_iso,
  apply @preimage_iso _ _ _ _ SheafedSpace.forget_to_PresheafedSpace,
  exact H.iso_restrict,
end

def Scheme (X : LocallyRingedSpace)
  (c : Π (x : X), costructured_arrow Spec.to_LocallyRingedSpace X)
  (hc : ∀ (x : X), x ∈ set.range (c x).hom.1.base)
  [H : ∀ (x : X), LocallyRingedSpace.is_open_immersion (c x).hom] : Scheme :=
{ local_affine := λ x, ⟨⟨⟨_, (H x).base_open.open_range⟩, hc x⟩,unop (c x).left,⟨by {
  apply LocallyRingedSpace.iso_of_SheafedSpace_iso,
  apply @preimage_iso _ _ _ _ SheafedSpace.forget_to_PresheafedSpace,
  apply PresheafedSpace.is_open_immersion.iso_of_range_eq
    (PresheafedSpace.of_restrict _ _) (c x).hom.1,
  exact subtype.range_coe_subtype,
  apply_instance }⟩⟩,
  ..X }

end LocallyRingedSpace.is_open_immersion

/--
A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpace
-/
abbreviation is_open_immersion {X Y : Scheme} (f : X ⟶ Y) :
  Prop := LocallyRingedSpace.is_open_immersion f

namespace is_open_immersion

variables {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [H : is_open_immersion f]

@[priority 100]
instance of_is_iso [is_iso g] :
  is_open_immersion g := @@LocallyRingedSpace.is_open_immersion.of_is_iso _
(show is_iso ((induced_functor _).map g), by apply_instance)

include H

instance mono : mono f :=
faithful_reflects_mono (induced_functor _)
(show @mono LocallyRingedSpace _ _ _ f, by apply_instance)

instance forget_creates_pullback_of_left : creates_limit (cospan f g) Scheme.forget :=
creates_limit_of_fully_faithful_of_iso
  (PresheafedSpace.is_open_immersion.to_SheafedSpace Y
    (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
  (eq_to_iso (show pullback _ _ = pullback _ _, by congr)
    ≪≫ has_limit.iso_of_nat_iso (diagram_iso_cospan _).symm)

instance forget_creates_pullback_of_right : creates_limit (cospan g f) forget :=
creates_limit_of_fully_faithful_of_iso
  (PresheafedSpace.is_open_immersion.to_SheafedSpace Y
    (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
  (eq_to_iso (show pullback _ _ = pullback _ _, by congr)
    ≪≫ has_limit.iso_of_nat_iso (diagram_iso_cospan _).symm)

instance SheafedSpace_forget_preserves_of_left :
  preserves_limit (cospan f g) (SheafedSpace.forget C) :=
@@limits.comp_preserves_limit _ _ _ _ forget (PresheafedSpace.forget C) _
begin
  apply_with (preserves_limit_of_iso_diagram _ (diagram_iso_cospan _).symm) { instances := tt },
  dsimp,
  apply_instance
end

instance SheafedSpace_forget_preserves_of_right :
  preserves_limit (cospan g f) (SheafedSpace.forget C) :=
preserves_pullback_symmetry _ _ _

instance SheafedSpace_has_pullback_of_left : has_pullback f g :=
  has_limit_of_created (cospan f g) forget

instance SheafedSpace_has_pullback_of_right : has_pullback g f :=
  has_limit_of_created (cospan g f) forget

end is_open_immersion

end algebraic_geometry
