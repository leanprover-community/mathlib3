/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.preserves.basic

/-!
# Preserving pullbacks

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullback_comparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/

noncomputable theory

universes v₁ v₂ u₁ u₂

open category_theory category_theory.category category_theory.limits

namespace category_theory.limits

section pullback

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables (G : C ⥤ D)
variables {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

/-- The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a
limit. This essentially lets us commute `pullback_cone.mk` with `functor.map_cone`. -/
def is_limit_map_cone_pullback_cone_equiv :
  is_limit (G.map_cone (pullback_cone.mk h k comm)) ≃
    is_limit (pullback_cone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm])
      : pullback_cone (G.map f) (G.map g)) :=
(is_limit.postcompose_hom_equiv (diagram_iso_cospan.{v₂} _) _).symm.trans $
is_limit.equiv_iso_limit $ cones.ext (iso.refl _) $
  (by rintro (_|_|_); dsimp; simp only [comp_id, id_comp, G.map_comp])

/-- The property of preserving pullbacks expressed in terms of binary fans. -/
def is_limit_pullback_cone_map_of_is_limit [preserves_limit (cospan f g) G]
  (l : is_limit (pullback_cone.mk h k comm)) :
  is_limit (pullback_cone.mk (G.map h) (G.map k) _) :=
is_limit_map_cone_pullback_cone_equiv G comm (preserves_limit.preserves l)

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
def is_limit_of_is_limit_pullback_cone_map [reflects_limit (cospan f g) G]
  (l : is_limit (pullback_cone.mk (G.map h) (G.map k) _)) :
  is_limit (pullback_cone.mk h k comm) :=
reflects_limit.reflects ((is_limit_map_cone_pullback_cone_equiv G comm).symm l)

variables (f g) [preserves_limit (cospan f g) G]

/-- If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit. -/
def is_limit_of_has_pullback_of_preserves_limit [has_pullback f g] :
  is_limit (pullback_cone.mk (G.map pullback.fst) (G.map pullback.snd) _) :=
is_limit_pullback_cone_map_of_is_limit G _ (pullback_is_pullback f g)

/-- If `F` preserves the pullback of `f, g`, it also preserves the pullback of `g, f`. -/
def preserves_pullback_symmetry : preserves_limit (cospan g f) G :=
{ preserves := λ c hc,
  begin
    apply (is_limit.postcompose_hom_equiv (diagram_iso_cospan.{v₂} _) _).to_fun,
    apply is_limit.of_iso_limit _ (pullback_cone.iso_mk _).symm,
    apply pullback_cone.flip_is_limit,
    apply (is_limit_map_cone_pullback_cone_equiv _ _).to_fun,
    { apply_with preserves_limit.preserves { instances := ff },
      { dsimp, apply_instance },
      apply pullback_cone.flip_is_limit,
      apply is_limit.of_iso_limit _ (pullback_cone.iso_mk _),
      exact (is_limit.postcompose_hom_equiv (diagram_iso_cospan.{v₁} _) _).inv_fun hc },
    { exact (c.π.naturality walking_cospan.hom.inr).symm.trans
      (c.π.naturality walking_cospan.hom.inl : _) }
  end }

lemma has_pullback_of_preserves_pullback [has_pullback f g] :
  has_pullback (G.map f) (G.map g) :=
⟨⟨⟨_, is_limit_pullback_cone_map_of_is_limit G _ (pullback_is_pullback _ _)⟩⟩⟩

variables [has_pullback f g] [has_pullback (G.map f) (G.map g)]

/-- If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism. -/
def preserves_pullback.iso :
  G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_pullback_of_preserves_limit G f g)
  (limit.is_limit _)

@[reassoc] lemma preserves_pullback.iso_hom_fst :
  (preserves_pullback.iso G f g).hom ≫ pullback.fst = G.map pullback.fst :=
by simp [preserves_pullback.iso]

@[reassoc] lemma preserves_pullback.iso_hom_snd :
  (preserves_pullback.iso G f g).hom ≫ pullback.snd = G.map pullback.snd :=
by simp [preserves_pullback.iso]

@[simp, reassoc] lemma preserves_pullback.iso_inv_fst :
  (preserves_pullback.iso G f g).inv ≫ G.map pullback.fst = pullback.fst :=
by simp [preserves_pullback.iso, iso.inv_comp_eq]

@[simp, reassoc] lemma preserves_pullback.iso_inv_snd :
  (preserves_pullback.iso G f g).inv ≫ G.map pullback.snd = pullback.snd :=
by simp [preserves_pullback.iso, iso.inv_comp_eq]

end pullback

section pushout

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]
variables (G : C ⥤ D)
variables {W X Y Z : C} {h : X ⟶ Z} {k : Y ⟶ Z} {f : W ⟶ X} {g : W ⟶ Y} (comm : f ≫ h = g ≫ k)

/-- The map of a pushout cocone is a colimit iff the cofork consisting of the mapped morphisms is a
colimit. This essentially lets us commute `pushout_cocone.mk` with `functor.map_cocone`. -/
def is_colimit_map_cocone_pushout_cocone_equiv :
  is_colimit (G.map_cocone (pushout_cocone.mk h k comm)) ≃
    is_colimit (pushout_cocone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm])
      : pushout_cocone (G.map f) (G.map g)) :=
(is_colimit.precompose_hom_equiv (diagram_iso_span.{v₂} _).symm _).symm.trans $
is_colimit.equiv_iso_colimit $ cocones.ext (iso.refl _) $
  (by rintro (_|_|_); dsimp; simp only [category.comp_id, category.id_comp, ← G.map_comp])

/-- The property of preserving pushouts expressed in terms of binary cofans. -/
def is_colimit_pushout_cocone_map_of_is_colimit [preserves_colimit (span f g) G]
  (l : is_colimit (pushout_cocone.mk h k comm)) :
  is_colimit (pushout_cocone.mk (G.map h) (G.map k) _) :=
is_colimit_map_cocone_pushout_cocone_equiv G comm (preserves_colimit.preserves l)

/-- The property of reflecting pushouts expressed in terms of binary cofans. -/
def is_colimit_of_is_colimit_pushout_cocone_map [reflects_colimit (span f g) G]
  (l : is_colimit (pushout_cocone.mk (G.map h) (G.map k) _)) :
  is_colimit (pushout_cocone.mk h k comm) :=
reflects_colimit.reflects ((is_colimit_map_cocone_pushout_cocone_equiv G comm).symm l)

variables (f g) [preserves_colimit (span f g) G]

/-- If `G` preserves pushouts and `C` has them, then the pushout cocone constructed of the mapped
morphisms of the pushout cocone is a colimit. -/
def is_colimit_of_has_pushout_of_preserves_colimit [has_pushout f g] :
  is_colimit (pushout_cocone.mk (G.map pushout.inl) (G.map pushout.inr) _) :=
is_colimit_pushout_cocone_map_of_is_colimit G _ (pushout_is_pushout f g)

/-- If `F` preserves the pushout of `f, g`, it also preserves the pushout of `g, f`. -/
def preserves_pushout_symmetry : preserves_colimit (span g f) G :=
{ preserves := λ c hc,
  begin
    apply (is_colimit.precompose_hom_equiv (diagram_iso_span.{v₂} _).symm _).to_fun,
    apply is_colimit.of_iso_colimit _ (pushout_cocone.iso_mk _).symm,
    apply pushout_cocone.flip_is_colimit,
    apply (is_colimit_map_cocone_pushout_cocone_equiv _ _).to_fun,
    { apply_with preserves_colimit.preserves { instances := ff },
      { dsimp, apply_instance },
      apply pushout_cocone.flip_is_colimit,
      apply is_colimit.of_iso_colimit _ (pushout_cocone.iso_mk _),
      exact (is_colimit.precompose_hom_equiv (diagram_iso_span.{v₁} _) _).inv_fun hc },
    { exact (c.ι.naturality walking_span.hom.snd).trans
      (c.ι.naturality walking_span.hom.fst).symm }
  end }

lemma has_pushout_of_preserves_pushout [has_pushout f g] :
  has_pushout (G.map f) (G.map g) :=
⟨⟨⟨_, is_colimit_pushout_cocone_map_of_is_colimit G _ (pushout_is_pushout _ _)⟩⟩⟩

variables [has_pushout f g]  [has_pushout (G.map f) (G.map g)]

/-- If `G` preserves the pushout of `(f,g)`, then the pushout comparison map for `G` at `(f,g)` is
an isomorphism. -/
def preserves_pushout.iso :
  pushout (G.map f) (G.map g) ≅ G.obj (pushout f g) :=
is_colimit.cocone_point_unique_up_to_iso
  (colimit.is_colimit _)
  (is_colimit_of_has_pushout_of_preserves_colimit G f g)

@[reassoc] lemma preserves_pushout.inl_iso_hom :
  pushout.inl ≫ (preserves_pushout.iso G f g).hom = G.map pushout.inl :=
by { delta preserves_pushout.iso, simp }

@[reassoc] lemma preserves_pushout.inr_iso_hom :
  pushout.inr ≫ (preserves_pushout.iso G f g).hom = G.map pushout.inr :=
by { delta preserves_pushout.iso, simp }

@[simp, reassoc] lemma preserves_pushout.inl_iso_inv :
  G.map pushout.inl ≫ (preserves_pushout.iso G f g).inv = pushout.inl :=
by simp [preserves_pushout.iso, iso.comp_inv_eq]

@[simp, reassoc] lemma preserves_pushout.inr_iso_inv :
  G.map pushout.inr ≫ (preserves_pushout.iso G f g).inv = pushout.inr :=
by simp [preserves_pushout.iso, iso.comp_inv_eq]

end pushout

section

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₁} D]
variables (G : C ⥤ D)

section pullback

variables {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
variables [has_pullback f g] [has_pullback (G.map f) (G.map g)]

/-- If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`. -/
def preserves_pullback.of_iso_comparison [i : is_iso (pullback_comparison G f g)] :
  preserves_limit (cospan f g) G :=
begin
  apply preserves_limit_of_preserves_limit_cone (pullback_is_pullback f g),
  apply (is_limit_map_cone_pullback_cone_equiv _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (cospan (G.map f) (G.map g))),
  apply i,
end

variable [preserves_limit (cospan f g) G]

@[simp]
lemma preserves_pullback.iso_hom :
  (preserves_pullback.iso G f g).hom = pullback_comparison G f g := rfl

instance : is_iso (pullback_comparison G f g) :=
begin
  rw ← preserves_pullback.iso_hom,
  apply_instance
end

end pullback

section pushout

variables {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
variables [has_pushout f g] [has_pushout (G.map f) (G.map g)]

/-- If the pushout comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pushout of `(f,g)`. -/
def preserves_pushout.of_iso_comparison [i : is_iso (pushout_comparison G f g)] :
  preserves_colimit (span f g) G :=
begin
  apply preserves_colimit_of_preserves_colimit_cocone (pushout_is_pushout f g),
  apply (is_colimit_map_cocone_pushout_cocone_equiv _ _).symm _,
  apply is_colimit.of_point_iso (colimit.is_colimit (span (G.map f) (G.map g))),
  apply i,
end

variable [preserves_colimit (span f g) G]

@[simp]
lemma preserves_pushout.iso_hom :
  (preserves_pushout.iso G f g).hom = pushout_comparison G f g := rfl

instance : is_iso (pushout_comparison G f g) :=
begin
  rw ← preserves_pushout.iso_hom,
  apply_instance
end

end pushout

end

end category_theory.limits
