/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Scott Morrison, Floris van Doorn
-/
import category_theory.limits.is_limit
import category_theory.category.ulift

/-!
# Existence of limits and colimits

In `category_theory.limits.is_limit` we defined `is_limit c`,
the data showing that a cone `c` is a limit cone.

The two main structures defined in this file are:
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

`has_limit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).

While `has_limit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `has_limit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.X ⟶ limit F`, the universal morphism from any other `c : cone F`, etc.

Key to using the `has_limit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `has_limits_of_shape J C` and `has_limits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `is_limit`,
and then a result in terms of `has_limit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `has_limit`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

noncomputable theory

open category_theory category_theory.category category_theory.functor opposite

namespace category_theory.limits

-- morphism levels before object levels. See note [category_theory universes].
universes v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variables {J : Type u₁} [category.{v₁} J] {K : Type u₂} [category.{v₂} K]
variables {C : Type u} [category.{v} C]

variables {F : J ⥤ C}

section limit

/-- `limit_cone F` contains a cone over `F` together with the information that it is a limit. -/
@[nolint has_inhabited_instance]
structure limit_cone (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

/-- `has_limit F` represents the mere existence of a limit for `F`. -/
class has_limit (F : J ⥤ C) : Prop :=
mk' :: (exists_limit : nonempty (limit_cone F))

lemma has_limit.mk {F : J ⥤ C} (d : limit_cone F) : has_limit F :=
⟨nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `limit_cone F` from `has_limit F`. -/
def get_limit_cone (F : J ⥤ C) [has_limit F] : limit_cone F :=
classical.choice $ has_limit.exists_limit

variables (J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class has_limits_of_shape : Prop :=
(has_limit : Π F : J ⥤ C, has_limit F . tactic.apply_instance)

/--
`C` has all limits of size `v₁ u₁` (`has_limits_of_size.{v₁ u₁} C`)
if it has limits of every shape `J : Type u₁` with `[category.{v₁} J]`.
-/
class has_limits_of_size (C : Type u) [category.{v} C] : Prop :=
(has_limits_of_shape :
  Π (J : Type u₁) [𝒥 : category.{v₁} J], has_limits_of_shape J C . tactic.apply_instance)

/-- `C` has all (small) limits if it has limits of every shape that is as big as its hom-sets. -/
abbreviation has_limits (C : Type u) [category.{v} C] : Prop := has_limits_of_size.{v v} C

lemma has_limits.has_limits_of_shape {C : Type u} [category.{v} C] [has_limits C]
  (J : Type v) [category.{v} J] :
  has_limits_of_shape J C := has_limits_of_size.has_limits_of_shape J

variables {J C}

@[priority 100] -- see Note [lower instance priority]
instance has_limit_of_has_limits_of_shape
  {J : Type u₁} [category.{v₁} J] [H : has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
has_limits_of_shape.has_limit F

@[priority 100] -- see Note [lower instance priority]
instance has_limits_of_shape_of_has_limits
  {J : Type u₁} [category.{v₁} J] [H : has_limits_of_size.{v₁ u₁} C] : has_limits_of_shape J C :=
has_limits_of_size.has_limits_of_shape J

/- Interface to the `has_limit` class. -/

/-- An arbitrary choice of limit cone for a functor. -/
def limit.cone (F : J ⥤ C) [has_limit F] : cone F := (get_limit_cone F).cone

/-- An arbitrary choice of limit object of a functor. -/
def limit (F : J ⥤ C) [has_limit F] := (limit.cone F).X

/-- The projection from the limit object to a value of the functor. -/
def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F.obj j :=
(limit.cone F).π.app j

@[simp] lemma limit.cone_X {F : J ⥤ C} [has_limit F] :
  (limit.cone F).X = limit F := rfl

@[simp] lemma limit.cone_π {F : J ⥤ C} [has_limit F] :
  (limit.cone F).π.app = limit.π _ := rfl

@[simp, reassoc] lemma limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') :
  limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provied by `limit.cone F` is a limit cone. -/
def limit.is_limit (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
(get_limit_cone F).is_limit

/-- The morphism from the cone point of any other cone to the limit object. -/
def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F :=
(limit.is_limit F).lift c

@[simp] lemma limit.is_limit_lift {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.is_limit F).lift c = limit.lift F c := rfl

@[simp, reassoc] lemma limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  limit.lift F c ≫ limit.π F j = c.π.app j :=
is_limit.fac _ c j

/--
Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def lim_map {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) : limit F ⟶ limit G :=
is_limit.map _ (limit.is_limit G) α

@[simp, reassoc] lemma lim_map_π {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) (j : J) :
  lim_map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) :
  c ⟶ limit.cone F :=
(limit.is_limit F).lift_cone_morphism c

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.cone_morphism c).hom = limit.lift F c := rfl
lemma limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).hom ≫ limit.π F j = c.π.app j :=
by simp

@[simp, reassoc] lemma limit.cone_point_unique_up_to_iso_hom_comp {F : J ⥤ C} [has_limit F]
  {c : cone F} (hc : is_limit c) (j : J) :
  (is_limit.cone_point_unique_up_to_iso hc (limit.is_limit _)).hom ≫ limit.π F j = c.π.app j :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ _

@[simp, reassoc] lemma limit.cone_point_unique_up_to_iso_inv_comp {F : J ⥤ C} [has_limit F]
  {c : cone F} (hc : is_limit c) (j : J) :
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) hc).inv ≫ limit.π F j = c.π.app j :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ _

/--
Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point.
-/
def limit.iso_limit_cone {F : J ⥤ C} [has_limit F] (t : limit_cone F) :
  limit F ≅ t.cone.X :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit F) t.is_limit

@[simp, reassoc] lemma limit.iso_limit_cone_hom_π
  {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) :
  (limit.iso_limit_cone t).hom ≫ t.cone.π.app j = limit.π F j :=
by { dsimp [limit.iso_limit_cone, is_limit.cone_point_unique_up_to_iso], tidy, }

@[simp, reassoc] lemma limit.iso_limit_cone_inv_π
  {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) :
  (limit.iso_limit_cone t).inv ≫ limit.π F j = t.cone.π.app j :=
by { dsimp [limit.iso_limit_cone, is_limit.cone_point_unique_up_to_iso], tidy, }

@[ext] lemma limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C} {f f' : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
(limit.is_limit F).hom_ext w

@[simp] lemma limit.lift_map {F G : J ⥤ C} [has_limit F] [has_limit G] (c : cone F) (α : F ⟶ G) :
  limit.lift F c ≫ lim_map α = limit.lift G ((cones.postcompose α).obj c) :=
by { ext, rw [assoc, lim_map_π, limit.lift_π_assoc, limit.lift_π], refl }

@[simp] lemma limit.lift_cone {F : J ⥤ C} [has_limit F] :
  limit.lift F (limit.cone F) = 𝟙 (limit F) :=
(limit.is_limit _).lift_self

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.hom_iso (F : J ⥤ C) [has_limit F] (W : C) :
  ulift.{u₁} (W ⟶ limit F : Type v) ≅ (F.cones.obj (op W)) :=
(limit.is_limit F).hom_iso W

@[simp] lemma limit.hom_iso_hom (F : J ⥤ C) [has_limit F] {W : C} (f : ulift (W ⟶ limit F)) :
  (limit.hom_iso F W).hom f = (const J).map f.down ≫ (limit.cone F).π :=
(limit.is_limit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.hom_iso' (F : J ⥤ C) [has_limit F] (W : C) :
  ulift.{u₁} ((W ⟶ limit F) : Type v) ≅
    { p : Π j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
(limit.is_limit F).hom_iso' W

lemma limit.lift_extend {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
by obviously

/--
If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
lemma has_limit_of_iso {F G : J ⥤ C} [has_limit F] (α : F ≅ G) : has_limit G :=
has_limit.mk
{ cone := (cones.postcompose α.hom).obj (limit.cone F),
  is_limit :=
  { lift := λ s, limit.lift F ((cones.postcompose α.inv).obj s),
    fac' := λ s j,
    begin
      rw [cones.postcompose_obj_π, nat_trans.comp_app, limit.cone_π, ←category.assoc, limit.lift_π],
      simp
    end,
    uniq' := λ s m w,
    begin
      apply limit.hom_ext, intro j,
      rw [limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app, ←nat_iso.app_inv,
        iso.eq_comp_inv],
      simpa using w j
    end } }

/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
-- See the construction of limits from products and equalizers
-- for an example usage.
lemma has_limit.of_cones_iso {J K : Type u₁} [category.{v₁} J] [category.{v₂} K] (F : J ⥤ C)
  (G : K ⥤ C) (h : F.cones ≅ G.cones) [has_limit F] : has_limit G :=
has_limit.mk ⟨_, is_limit.of_nat_iso ((is_limit.nat_iso (limit.is_limit F)) ≪≫ h)⟩

/--
The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_limit.iso_of_nat_iso {F G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) :
  limit F ≅ limit G :=
is_limit.cone_points_iso_of_nat_iso (limit.is_limit F) (limit.is_limit G) w

@[simp, reassoc]
lemma has_limit.iso_of_nat_iso_hom_π {F G : J ⥤ C} [has_limit F] [has_limit G]
  (w : F ≅ G) (j : J) :
  (has_limit.iso_of_nat_iso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
is_limit.cone_points_iso_of_nat_iso_hom_comp _ _ _ _

@[simp, reassoc]
lemma has_limit.lift_iso_of_nat_iso_hom {F G : J ⥤ C} [has_limit F] [has_limit G] (t : cone F)
  (w : F ≅ G) :
  limit.lift F t ≫ (has_limit.iso_of_nat_iso w).hom =
    limit.lift G ((cones.postcompose w.hom).obj _) :=
is_limit.lift_comp_cone_points_iso_of_nat_iso_hom _ _ _

/--
The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_limit.iso_of_equivalence {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
is_limit.cone_points_iso_of_equivalence (limit.is_limit F) (limit.is_limit G) e w

@[simp]
lemma has_limit.iso_of_equivalence_hom_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
  (has_limit.iso_of_equivalence e w).hom ≫ limit.π G k =
    limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) :=
begin
  simp only [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom],
  dsimp,
  simp,
end

@[simp]
lemma has_limit.iso_of_equivalence_inv_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
  (has_limit.iso_of_equivalence e w).inv ≫ limit.π F j =
    limit.π G (e.functor.obj j) ≫ w.hom.app j :=
begin
  simp only [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom],
  dsimp,
  simp,
end

section pre
variables (F) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)]

/--
The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[simp, reassoc] lemma limit.pre_π (k : K) :
  limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) :=
by { erw is_limit.fac, refl }

@[simp] lemma limit.lift_pre (c : cone F) :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
by ext; simp

variables {L : Type u₃} [category.{v₃} L]
variables (D : L ⥤ K) [has_limit (D ⋙ E ⋙ F)]

@[simp] lemma limit.pre_pre : limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
by ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; refl

variables {E F}

/---
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
lemma limit.pre_eq (s : limit_cone (E ⋙ F)) (t : limit_cone F) :
  limit.pre F E =
    (limit.iso_limit_cone t).hom ≫ s.is_limit.lift ((t.cone).whisker E) ≫
      (limit.iso_limit_cone s).inv :=
by tidy

end pre

section post
variables {D : Type u'} [category.{v'} D]

variables (F) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)]

/--
The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
limit.lift (F ⋙ G) (G.map_cone (limit.cone F))

@[simp, reassoc] lemma limit.post_π (j : J) :
  limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
by { erw is_limit.fac, refl }

@[simp] lemma limit.lift_post (c : cone F) :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
by { ext, rw [assoc, limit.post_π, ←G.map_comp, limit.lift_π, limit.lift_π], refl }

@[simp] lemma limit.post_post
  {E : Type u''} [category.{v''} E] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] :
/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals -/
/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) -/
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
by ext; erw [assoc, limit.post_π, ←H.map_comp, limit.post_π, limit.post_π]; refl

end post

lemma limit.pre_post {D : Type u'} [category.{v'} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_limit F] [has_limit (E ⋙ F)] [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)] :
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
by ext; erw [assoc, limit.post_π, ←G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]; refl

open category_theory.equivalence
instance has_limit_equivalence_comp (e : K ≌ J) [has_limit F] : has_limit (e.functor ⋙ F) :=
has_limit.mk { cone := cone.whisker e.functor (limit.cone F),
  is_limit := is_limit.whisker_equivalence (limit.is_limit F) e, }

local attribute [elab_simple] inv_fun_id_assoc -- not entirely sure why this is needed

/--
If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
lemma has_limit_of_equivalence_comp (e : K ≌ J) [has_limit (e.functor ⋙ F)] : has_limit F :=
begin
  haveI : has_limit (e.inverse ⋙ e.functor ⋙ F) := limits.has_limit_equivalence_comp e.symm,
  apply has_limit_of_iso (e.inv_fun_id_assoc F),
end

-- `has_limit_comp_equivalence` and `has_limit_of_comp_equivalence`
-- are proved in `category_theory/adjunction/limits.lean`.

section lim_functor


variables [has_limits_of_shape J C]

section

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[simps obj]
def lim : (J ⥤ C) ⥤ C :=
{ obj := λ F, limit F,
  map := λ F G α, lim_map α,
  map_id' := λ F, by { ext, erw [lim_map_π, category.id_comp, category.comp_id] },
  map_comp' := λ F G H α β,
    by ext; erw [assoc, is_limit.fac, is_limit.fac, ←assoc, is_limit.fac, assoc]; refl }
end

variables {F} {G : J ⥤ C} (α : F ⟶ G)

-- We generate this manually since `simps` gives it a weird name.
@[simp] lemma lim_map_eq_lim_map : lim.map α = lim_map α := rfl

lemma limit.map_pre [has_limits_of_shape K C] (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
by { ext, simp }

lemma limit.map_pre' [has_limits_of_shape K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whisker_right α F) :=
by ext1; simp [← category.assoc]

lemma limit.id_pre (F : J ⥤ C) :
limit.pre F (𝟭 _) = lim.map (functor.left_unitor F).inv := by tidy

lemma limit.map_post {D : Type u'} [category.{v'} D] [has_limits_of_shape J D] (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim_map α) ≫ limit.post G H = limit.post F H ≫ lim_map (whisker_right α H) :=
begin
  ext,
  simp only [whisker_right_app, lim_map_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp],
end

/--
The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def lim_yoneda : lim ⋙ yoneda ⋙ (whiskering_right _ _ _).obj ulift_functor.{u₁}
  ≅ category_theory.cones J C :=
nat_iso.of_components (λ F, nat_iso.of_components (λ W, limit.hom_iso F (unop W)) (by tidy))
  (by tidy)

end lim_functor

/--
We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
lemma has_limits_of_shape_of_equivalence {J' : Type u₂} [category.{v₂} J']
  (e : J ≌ J') [has_limits_of_shape J C] : has_limits_of_shape J' C :=
by { constructor, intro F, apply has_limit_of_equivalence_comp e, apply_instance }

variable (C)

/--
`has_limits_of_size.{v u} C` tries to obtain `has_limits_of_size.{v u} C`
from some other `has_limits_of_size C`.
-/
lemma has_limits_of_size_shrink [has_limits_of_size.{(max v₁ v₂) (max u₁ u₂)} C] :
  has_limits_of_size.{v₁ u₁} C :=
⟨λ J hJ, by exactI has_limits_of_shape_of_equivalence
  (ulift_hom_ulift_category.equiv.{v₂ u₂} J).symm⟩

lemma has_smallest_limits_of_has_limits [has_limits C] :
  has_limits_of_size.{0 0} C := has_limits_of_size_shrink.{0 0} C

end limit


section colimit

/-- `colimit_cocone F` contains a cocone over `F` together with the information that it is a
    colimit. -/
@[nolint has_inhabited_instance]
structure colimit_cocone (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

/-- `has_colimit F` represents the mere existence of a colimit for `F`. -/
class has_colimit (F : J ⥤ C) : Prop :=
mk' :: (exists_colimit : nonempty (colimit_cocone F))

lemma has_colimit.mk {F : J ⥤ C} (d : colimit_cocone F) : has_colimit F :=
⟨nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `colimit_cocone F` from `has_colimit F`. -/
def get_colimit_cocone (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
classical.choice $ has_colimit.exists_colimit

variables (J C)

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
class has_colimits_of_shape : Prop :=
(has_colimit : Π F : J ⥤ C, has_colimit F . tactic.apply_instance)

/--
`C` has all colimits of size `v₁ u₁` (`has_colimits_of_size.{v₁ u₁} C`)
if it has colimits of every shape `J : Type u₁` with `[category.{v₁} J]`.
-/
class has_colimits_of_size (C : Type u) [category.{v} C] : Prop :=
(has_colimits_of_shape :
  Π (J : Type u₁) [𝒥 : category.{v₁} J], has_colimits_of_shape J C . tactic.apply_instance)

/--
`C` has all (small) colimits if it has colimits of every shape that is as big as its hom-sets.
-/
abbreviation has_colimits (C : Type u) [category.{v} C] : Prop := has_colimits_of_size.{v v} C

lemma has_colimits.has_colimits_of_shape {C : Type u} [category.{v} C] [has_colimits C]
  (J : Type v) [category.{v} J] :
  has_colimits_of_shape J C := has_colimits_of_size.has_colimits_of_shape J

variables {J C}

@[priority 100] -- see Note [lower instance priority]
instance has_colimit_of_has_colimits_of_shape
  {J : Type u₁} [category.{v₁} J] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
has_colimits_of_shape.has_colimit F

@[priority 100] -- see Note [lower instance priority]
instance has_colimits_of_shape_of_has_colimits_of_size {J : Type u₁} [category.{v₁} J]
  [H : has_colimits_of_size.{v₁ u₁} C] : has_colimits_of_shape J C :=
has_colimits_of_size.has_colimits_of_shape J

/- Interface to the `has_colimit` class. -/

/-- An arbitrary choice of colimit cocone of a functor. -/
def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F := (get_colimit_cocone F).cocone

/-- An arbitrary choice of colimit object of a functor. -/
def colimit (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X

/-- The coprojection from a value of the functor to the colimit object. -/
def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F.obj j ⟶ colimit F :=
(colimit.cocone F).ι.app j

@[simp] lemma colimit.cocone_ι {F : J ⥤ C} [has_colimit F] (j : J) :
  (colimit.cocone F).ι.app j = colimit.ι _ j := rfl

@[simp] lemma colimit.cocone_X {F : J ⥤ C} [has_colimit F] :
  (colimit.cocone F).X = colimit F := rfl

@[simp, reassoc] lemma colimit.w (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') :
  F.map f ≫ colimit.ι F j' = colimit.ι F j := (colimit.cocone F).w f

/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/
def colimit.is_colimit (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
(get_colimit_cocone F).is_colimit

/-- The morphism from the colimit object to the cone point of any other cocone. -/
def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X :=
(colimit.is_colimit F).desc c

@[simp] lemma colimit.is_colimit_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.is_colimit F).desc c = colimit.desc F c := rfl

/--
We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `tactic/reassoc_axiom.lean`)
 -/
@[simp, reassoc] lemma colimit.ι_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
is_colimit.fac _ c j

/--
Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
is_colimit.map (colimit.is_colimit F) _ α

@[simp, reassoc]
lemma ι_colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) (j : J) :
  colimit.ι F j ≫ colim_map α = α.app j ≫ colimit.ι G j :=
colimit.ι_desc _ j

/-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/
def colimit.cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone F) ⟶ c :=
(colimit.is_colimit F).desc_cocone_morphism c

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism c).hom = colimit.desc F c := rfl
lemma colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.cocone_morphism c).hom = c.ι.app j :=
by simp

@[simp, reassoc] lemma colimit.comp_cocone_point_unique_up_to_iso_hom {F : J ⥤ C} [has_colimit F]
  {c : cocone F} (hc : is_colimit c) (j : J) :
  colimit.ι F j ≫ (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hc).hom =
    c.ι.app j :=
is_colimit.comp_cocone_point_unique_up_to_iso_hom _ _ _

@[simp, reassoc] lemma colimit.comp_cocone_point_unique_up_to_iso_inv {F : J ⥤ C} [has_colimit F]
  {c : cocone F} (hc : is_colimit c) (j : J) :
  colimit.ι F j ≫ (is_colimit.cocone_point_unique_up_to_iso hc (colimit.is_colimit _)).inv =
    c.ι.app j :=
is_colimit.comp_cocone_point_unique_up_to_iso_inv _ _ _

/--
Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone point.
-/
def colimit.iso_colimit_cocone {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) :
  colimit F ≅ t.cocone.X :=
is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) t.is_colimit

@[simp, reassoc] lemma colimit.iso_colimit_cocone_ι_hom
  {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.iso_colimit_cocone t).hom = t.cocone.ι.app j :=
by { dsimp [colimit.iso_colimit_cocone, is_colimit.cocone_point_unique_up_to_iso], tidy, }

@[simp, reassoc] lemma colimit.iso_colimit_cocone_ι_inv
  {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) :
  t.cocone.ι.app j ≫ (colimit.iso_colimit_cocone t).inv = colimit.ι F j :=
by { dsimp [colimit.iso_colimit_cocone, is_colimit.cocone_point_unique_up_to_iso], tidy, }

@[ext] lemma colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C} {f f' : colimit F ⟶ X}
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
(colimit.is_colimit F).hom_ext w

@[simp] lemma colimit.desc_cocone {F : J ⥤ C} [has_colimit F] :
  colimit.desc F (colimit.cocone F) = 𝟙 (colimit F) :=
(colimit.is_colimit _).desc_self

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.hom_iso (F : J ⥤ C) [has_colimit F] (W : C) :
  ulift.{u₁} (colimit F ⟶ W : Type v) ≅ (F.cocones.obj W) :=
(colimit.is_colimit F).hom_iso W

@[simp] lemma colimit.hom_iso_hom (F : J ⥤ C) [has_colimit F] {W : C} (f : ulift (colimit F ⟶ W)) :
  (colimit.hom_iso F W).hom f = (colimit.cocone F).ι ≫ (const J).map f.down :=
(colimit.is_colimit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.hom_iso' (F : J ⥤ C) [has_colimit F] (W : C) :
  ulift.{u₁} ((colimit F ⟶ W) : Type v) ≅
    { p : Π j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
(colimit.is_colimit F).hom_iso' W

lemma colimit.desc_extend (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
begin
  ext1, rw [←category.assoc], simp
end

/--
If `F` has a colimit, so does any naturally isomorphic functor.
-/
-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
lemma has_colimit_of_iso {F G : J ⥤ C} [has_colimit F] (α : G ≅ F) : has_colimit G :=
has_colimit.mk
{ cocone := (cocones.precompose α.hom).obj (colimit.cocone F),
  is_colimit :=
  { desc := λ s, colimit.desc F ((cocones.precompose α.inv).obj s),
    fac' := λ s j,
    begin
      rw [cocones.precompose_obj_ι, nat_trans.comp_app, colimit.cocone_ι],
      rw [category.assoc, colimit.ι_desc, ←nat_iso.app_hom, ←iso.eq_inv_comp], refl
    end,
    uniq' := λ s m w,
    begin
      apply colimit.hom_ext, intro j,
      rw [colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app, ←nat_iso.app_inv,
        iso.eq_inv_comp],
      simpa using w j
    end } }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
lemma has_colimit.of_cocones_iso {K : Type u₁} [category.{v₂} K] (F : J ⥤ C)
  (G : K ⥤ C) (h : F.cocones ≅ G.cocones)
    [has_colimit F] : has_colimit G :=
has_colimit.mk ⟨_, is_colimit.of_nat_iso (is_colimit.nat_iso (colimit.is_colimit F) ≪≫ h)⟩

/--
The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_colimit.iso_of_nat_iso {F G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) :
  colimit F ≅ colimit G :=
is_colimit.cocone_points_iso_of_nat_iso (colimit.is_colimit F) (colimit.is_colimit G) w

@[simp, reassoc]
lemma has_colimit.iso_of_nat_iso_ι_hom {F G : J ⥤ C} [has_colimit F] [has_colimit G]
  (w : F ≅ G) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_nat_iso w).hom = w.hom.app j ≫ colimit.ι G j :=
is_colimit.comp_cocone_points_iso_of_nat_iso_hom _ _ _ _

@[simp, reassoc]
lemma has_colimit.iso_of_nat_iso_hom_desc {F G : J ⥤ C} [has_colimit F] [has_colimit G]
  (t : cocone G) (w : F ≅ G) :
  (has_colimit.iso_of_nat_iso w).hom ≫ colimit.desc G t =
    colimit.desc F ((cocones.precompose w.hom).obj _) :=
is_colimit.cocone_points_iso_of_nat_iso_hom_desc _ _ _

/--
The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_colimit.iso_of_equivalence {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
is_colimit.cocone_points_iso_of_equivalence (colimit.is_colimit F) (colimit.is_colimit G) e w

@[simp]
lemma has_colimit.iso_of_equivalence_hom_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_equivalence e w).hom =
     F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ :=
begin
  simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv],
  dsimp,
  simp,
end

@[simp]
lemma has_colimit.iso_of_equivalence_inv_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
  colimit.ι G k ≫ (has_colimit.iso_of_equivalence e w).inv =
     G.map (e.counit_inv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) :=
begin
  simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv],
  dsimp,
  simp,
end

section pre
variables (F) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)]

/--
The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[simp, reassoc] lemma colimit.ι_pre (k : K) :
  colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) :=
by { erw is_colimit.fac, refl, }

@[simp, reassoc] lemma colimit.pre_desc (c : cocone F) :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
by ext; rw [←assoc, colimit.ι_pre]; simp

variables {L : Type u₃} [category.{v₃} L]
variables (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)]

@[simp] lemma colimit.pre_pre : colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) :=
begin
  ext j,
  rw [←assoc, colimit.ι_pre, colimit.ι_pre],
  letI : has_colimit ((D ⋙ E) ⋙ F) := show has_colimit (D ⋙ E ⋙ F), by apply_instance,
  exact (colimit.ι_pre F (D ⋙ E) j).symm
end

variables {E F}

/---
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
lemma colimit.pre_eq (s : colimit_cocone (E ⋙ F)) (t : colimit_cocone F) :
  colimit.pre F E =
    (colimit.iso_colimit_cocone s).hom ≫ s.is_colimit.desc ((t.cocone).whisker E) ≫
      (colimit.iso_colimit_cocone t).inv :=
by tidy

end pre

section post
variables {D : Type u'} [category.{v'} D]

variables (F) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)]

/--
The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
colimit.desc (F ⋙ G) (G.map_cocone (colimit.cocone F))

@[simp, reassoc] lemma colimit.ι_post (j : J) :
  colimit.ι (F ⋙ G) j ≫ colimit.post F G  = G.map (colimit.ι F j) :=
by { erw is_colimit.fac, refl, }

@[simp] lemma colimit.post_desc (c : cocone F) :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
by { ext, rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_desc, colimit.ι_desc], refl }

@[simp] lemma colimit.post_post
  {E : Type u''} [category.{v''} E] (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] :
/- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals -/
/- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H)) -/
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_post],
  exact (colimit.ι_post F (G ⋙ H) j).symm
end

end post

lemma colimit.pre_post {D : Type u'} [category.{v'} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_colimit F] [has_colimit (E ⋙ F)] [has_colimit (F ⋙ G)] [H : has_colimit ((E ⋙ F) ⋙ G)] :
/- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs -/
/- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or -/
  colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
    (@@colimit.pre _ _ _ (F ⋙ G) _ E H ≫ colimit.post F G : _) :=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_pre, ←assoc],
  letI : has_colimit (E ⋙ F ⋙ G) := show has_colimit ((E ⋙ F) ⋙ G), by apply_instance,
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
end

open category_theory.equivalence
instance has_colimit_equivalence_comp (e : K ≌ J) [has_colimit F] : has_colimit (e.functor ⋙ F) :=
has_colimit.mk { cocone := cocone.whisker e.functor (colimit.cocone F),
  is_colimit := is_colimit.whisker_equivalence (colimit.is_colimit F) e, }

/--
If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
lemma has_colimit_of_equivalence_comp (e : K ≌ J) [has_colimit (e.functor ⋙ F)] : has_colimit F :=
begin
  haveI : has_colimit (e.inverse ⋙ e.functor ⋙ F) := limits.has_colimit_equivalence_comp e.symm,
  apply has_colimit_of_iso (e.inv_fun_id_assoc F).symm,
end

section colim_functor


variables [has_colimits_of_shape J C]

section
local attribute [simp] colim_map

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps obj]
def colim : (J ⥤ C) ⥤ C :=
{ obj := λ F, colimit F,
  map := λ F G α, colim_map α,
  map_id' := λ F, by { ext, erw [ι_colim_map, id_comp, comp_id] },
  map_comp' := λ F G H α β,
    by { ext, erw [←assoc, is_colimit.fac, is_colimit.fac, assoc, is_colimit.fac, ←assoc], refl } }

end

variables {F} {G : J ⥤ C} (α : F ⟶ G)

@[simp, reassoc] lemma colimit.ι_map (j : J) :
  colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j :=
by apply is_colimit.fac

@[simp] lemma colimit.map_desc (c : cocone G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F ((cocones.precompose α).obj c) :=
by ext; rw [←assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]; refl

lemma colimit.pre_map [has_colimits_of_shape K C] (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
by ext; rw [←assoc, colimit.ι_pre, colimit.ι_map, ←assoc, colimit.ι_map, assoc, colimit.ι_pre]; refl

lemma colimit.pre_map' [has_colimits_of_shape K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  colimit.pre F E₁ = colim.map (whisker_right α F) ≫ colimit.pre F E₂ :=
by ext1; simp [← category.assoc]

lemma colimit.pre_id (F : J ⥤ C) :
colimit.pre F (𝟭 _) = colim.map (functor.left_unitor F).hom := by tidy

lemma colimit.map_post {D : Type u'} [category.{v'} D] [has_colimits_of_shape J D] (H : C ⥤ D) :
/- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
   H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H:=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_map, H.map_comp],
  rw [←assoc, colimit.ι_map, assoc, colimit.ι_post],
  refl
end

/--
The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colim_coyoneda : colim.op ⋙ coyoneda ⋙ (whiskering_right _ _ _).obj ulift_functor.{u₁} ≅
  category_theory.cocones J C :=
nat_iso.of_components (λ F, nat_iso.of_components (colimit.hom_iso (unop F)) (by tidy))
  (by tidy)

end colim_functor

/--
We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
lemma has_colimits_of_shape_of_equivalence {J' : Type u₂} [category.{v₂} J']
  (e : J ≌ J') [has_colimits_of_shape J C] : has_colimits_of_shape J' C :=
by { constructor, intro F, apply has_colimit_of_equivalence_comp e, apply_instance }

variable (C)

/--
`has_colimits_of_size.{v u} C` tries to obtain `has_colimits_of_size.{v u} C`
from some other `has_colimits_of_size C`.
-/
lemma has_colimits_of_size_shrink [has_colimits_of_size.{(max v₁ v₂) (max u₁ u₂)} C] :
  has_colimits_of_size.{v₁ u₁} C :=
⟨λ J hJ, by exactI has_colimits_of_shape_of_equivalence
  (ulift_hom_ulift_category.equiv.{v₂ u₂} J).symm⟩

lemma has_smallest_colimits_of_has_colimits [has_colimits C] :
  has_colimits_of_size.{0 0} C := has_colimits_of_size_shrink.{0 0} C

end colimit

section opposite

/--
If `t : cone F` is a limit cone, then `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit.op {t : cone F} (P : is_limit t) : is_colimit t.op :=
{ desc := λ s, (P.lift s.unop).op,
  fac' := λ s j, congr_arg quiver.hom.op (P.fac s.unop (unop j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.unop m.unop,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
If `t : cocone F` is a colimit cocone, then `t.op : cone F.op` is a limit cone.
-/
def is_colimit.op {t : cocone F} (P : is_colimit t) : is_limit t.op :=
{ lift := λ s, (P.desc s.unop).op,
  fac' := λ s j, congr_arg quiver.hom.op (P.fac s.unop (unop j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.unop m.unop,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
If `t : cone F.op` is a limit cone, then `t.unop : cocone F` is a colimit cocone.
-/
def is_limit.unop {t : cone F.op} (P : is_limit t) : is_colimit t.unop :=
{ desc := λ s, (P.lift s.op).unop,
  fac' := λ s j, congr_arg quiver.hom.unop (P.fac s.op (op j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.op m.op,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
If `t : cocone F.op` is a colimit cocone, then `t.unop : cone F.` is a limit cone.
-/
def is_colimit.unop {t : cocone F.op} (P : is_colimit t) : is_limit t.unop :=
{ lift := λ s, (P.desc s.op).unop,
  fac' := λ s j, congr_arg quiver.hom.unop (P.fac s.op (op j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.op m.op,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
`t : cone F` is a limit cone if and only is `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit_equiv_is_colimit_op {t : cone F} : is_limit t ≃ is_colimit t.op :=
equiv_of_subsingleton_of_subsingleton
  is_limit.op (λ P, P.unop.of_iso_limit (cones.ext (iso.refl _) (by tidy)))

/--
`t : cocone F` is a colimit cocone if and only is `t.op : cone F.op` is a limit cone.
-/
def is_colimit_equiv_is_limit_op {t : cocone F} : is_colimit t ≃ is_limit t.op :=
equiv_of_subsingleton_of_subsingleton
  is_colimit.op (λ P, P.unop.of_iso_colimit (cocones.ext (iso.refl _) (by tidy)))

end opposite

end category_theory.limits
