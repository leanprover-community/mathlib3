/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.kan_extension
import category_theory.limits.filtered_colimit_commutes_finite_limit
import category_theory.limits.preserves.functor_category
import category_theory.limits.preserves.shapes.equalizers
import category_theory.limits.shapes.bicones
import category_theory.limits.presheaf
import category_theory.limits.yoneda
import category_theory.limits.comma
import category_theory.sites.sheaf_of_types

/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also knows as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to differentiate
this concept from other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limit`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
limits, then `F` is flat.
* `preserves_finite_limit_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `Lan_preserves_finite_limit_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `preserves_limit_of_Lan_preserves_limit`: If the functor `Lan F.op` between presheaves of sets
preserves limits of shape `J`, then so will `F`.
* `family_of_elements_compatible_of_flat`: If `F : C ⥤ D` is a flat functor, and a
`family_of_elements` over a sieve in `C` that factors through `u.op` is compatible,
then the family of elements viewed as a family over the image sieve in `D` is also compatible.

-/

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory
open category_theory.limits
open opposite

namespace category_theory


namespace structured_arrow_cone
open structured_arrow
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]
variables {J : Type v₁} [small_category J]
variables {K : J ⥤ C} (F : C ⥤ D) (c : cone K)

/--
Given a cone `c : cone K` and a map `f : X ⟶ c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point. This is the underlying diagram.
-/
@[simps]
def to_diagram : J ⥤ structured_arrow c.X K :=
{ obj := λ j, structured_arrow.mk (c.π.app j),
  map := λ j k g, structured_arrow.hom_mk g (by simpa),
  map_id' := λ X, by simpa,
  map_comp' := λ X Y Z g h, by { ext, simp } }

/-- Given a diagram of `structured_arrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps]
def diagram_to_cone {X : D} (G : J ⥤ structured_arrow X F) : cone (G ⋙ proj X F ⋙ F) := {
  X := X, π := { app := λ j, (G.obj j).hom } }

/--
Given a cone `c : cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def to_cone {X : D} (f : X ⟶ F.obj c.X) :
  cone (to_diagram (F.map_cone c) ⋙ map f ⋙ pre _ K F) :=
{ X := mk f, π := { app := λ j, hom_mk (c.π.app j) rfl,
                    naturality' := λ j k g, by { ext, dsimp, simp } } }

lemma eq_to_hom_right {A : Type*} [category A] {B : Type*} [category B] {T : Type*} [category T]
  {L : A ⥤ T} {R : B ⥤ T} (X Y : comma L R) (H : X = Y) :
  comma_morphism.right (eq_to_hom H) = eq_to_hom (by { cases H, refl }) := by { cases H, refl }

local attribute[simp] eq_to_hom_right

/--
If a cone `s₁` factors through another cone `s₂`, then the two constructed diagrams are actually
the same.
-/
lemma to_diagram_comp_map (s₁ s₂ : cone K)
  (f : s₁.X ⟶ s₂.X) (H : ∀ (j : J), f ≫ s₂.π.app j = s₁.π.app j) :
    to_diagram s₂ ⋙ structured_arrow.map f = to_diagram s₁ := by { apply functor.ext, tidy, }

end structured_arrow_cone

section representably_flat
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/--
A functor `F : C ⥤ D` is representably flat if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class representably_flat (F : C ⥤ D) : Prop :=
(cofiltered : ∀ (X : D), is_cofiltered (structured_arrow X F))

instance functor.flat_cofiltered (F : C ⥤ D) [representably_flat F] (X : D) :
 is_cofiltered (structured_arrow X F) := representably_flat.cofiltered X

end representably_flat

section has_limit
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

@[priority 100]
instance cofiltered_of_has_finite_limit [has_finite_limits C] : is_cofiltered C :=
{ cocone_objs := λ A B, ⟨limits.prod A B, limits.prod.fst, limits.prod.snd, trivial⟩,
  cocone_maps :=  λ A B f g, ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩,
  nonempty := ⟨⊤_ C⟩ }

lemma flat_of_preserves_finite_limit [has_limits C] (F : C ⥤ D)
  (H : ∀ (J : Type v₁) [h : small_category J] [h' : @fin_category J h],
    @preserves_limits_of_shape _ _ _ _ J h F) : representably_flat F := ⟨λ X,
begin
  haveI : has_finite_limits (structured_arrow X F) :=
    { out := λ J _ _, by { resetI, apply_instance } },
  apply_instance
end⟩

namespace preserves_finite_limit_of_flat
open structured_arrow
open structured_arrow_cone
variables {J : Type v₁} [small_category J] [fin_category J] {K : J ⥤ C}
variables (F : C ⥤ D) [representably_flat F] {c : cone K} (hc : is_limit c) (s : cone (K ⋙ F))
include hc

/--
(Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.map_cone c`.
-/
noncomputable def lift : s.X ⟶ F.obj c.X :=
let s' := is_cofiltered.cone (to_diagram s ⋙ structured_arrow.pre _ K F) in
s'.X.hom ≫ F.map (hc.lift ((cones.postcompose (eq_to_hom (by apply functor.hext; tidy))).obj
  ((structured_arrow.proj s.X F).map_cone s')))

lemma fac (x : J) : lift F hc s ≫ (F.map_cone c).π.app x = s.π.app x :=
by { dsimp [lift], simpa [← F.map_comp, -category.id_comp] using category.id_comp (s.π.app x) }

lemma uniq {K : J ⥤ C} {c : cone K} (hc : is_limit c)
  (s : cone (K ⋙ F)) (f₁ f₂ : s.X ⟶ F.obj c.X)
  (h₁ : ∀ (j : J), f₁ ≫ (F.map_cone c).π.app j = s.π.app j)
  (h₂ : ∀ (j : J), f₂ ≫ (F.map_cone c).π.app j = s.π.app j) : f₁ = f₂ :=
begin
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let c₁ : cone (to_diagram s ⋙ pre s.X K F) := (cones.postcompose
    (eq_to_hom (by simpa [←to_diagram_comp_map s (F.map_cone c) f₁ h₁]))).obj (to_cone F c f₁),
  let c₂ : cone (to_diagram s ⋙ pre s.X K F) := (cones.postcompose
    (eq_to_hom (by simpa [←to_diagram_comp_map s (F.map_cone c) f₂ h₂]))).obj (to_cone F c f₂),

  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `structured_arrow s.X F` is cofiltered.
  let c₀ := is_cofiltered.cone (bicone_mk _ c₁ c₂),
  let g₁ : c₀.X ⟶ c₁.X := c₀.π.app (bicone.left),
  let g₂ : c₀.X ⟶ c₂.X := c₀.π.app (bicone.right),

  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : ∀ (j : J), g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j,
  { intro j,
    injection c₀.π.naturality (bicone_hom.left  j) with _ e₁,
    injection c₀.π.naturality (bicone_hom.right j) with _ e₂,
    simpa [eq_to_hom_right] using e₁.symm.trans e₂ },
  have : c.extend g₁.right = c.extend g₂.right,
  { unfold cone.extend, congr' 1, ext x, apply this },

  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right,
  calc g₁.right = hc.lift (c.extend g₁.right) : by { apply hc.uniq (c.extend _), tidy }
            ... = hc.lift (c.extend g₂.right) : by { congr, exact this }
            ... = g₂.right                    : by { symmetry, apply hc.uniq (c.extend _), tidy },

  -- Finally, since `fᵢ` factors through `F(gᵢ)`, the result follows.
  calc f₁ = 𝟙 _ ≫ f₁                  : by simp
      ... = c₀.X.hom ≫ F.map g₁.right : g₁.w
      ... = c₀.X.hom ≫ F.map g₂.right : by rw this
      ... = 𝟙 _ ≫ f₂                  : g₂.w.symm
      ... = f₂                         : by simp
end

end preserves_finite_limit_of_flat

/-- Representably flat functors preserve finite limits. -/
noncomputable
def preserves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
(J : Type v₁) [small_category J] [fin_category J]
: preserves_limits_of_shape J F := ⟨λ K, ⟨λ c hc,
{ lift := preserves_finite_limit_of_flat.lift F hc,
  fac' := preserves_finite_limit_of_flat.fac F hc,
  uniq' := λ s m h, by
  { apply preserves_finite_limit_of_flat.uniq F hc,
    exact h,
    exact preserves_finite_limit_of_flat.fac F hc s } }⟩⟩

end has_limit

section small_category
variables {C D : Type u₁} [small_category C] [small_category D]

/--
(Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costructured arrows over `X`.
-/
lemma Lan_evaluation_eq_colim (E : Type u₂) [category.{u₁} E] (F : C ⥤ D) (X : D)
  [∀ (X : D), has_colimits_of_shape (costructured_arrow F X) E] :
  Lan F ⋙ (evaluation D E).obj X =
  ((whiskering_left _ _ E).obj (costructured_arrow.proj F X)) ⋙ colim :=
begin
  apply functor.hext,
  { intro Y, simp },
  intros Y₁ Y₂ f,
  simp only [functor.comp_map, evaluation_obj_map,
    whiskering_left_obj_map, Lan_map_app, heq_iff_eq],
  symmetry,
  apply (colimit.is_colimit (Lan.diagram F Y₁ X)).uniq { X := colimit _, ι := _ }
    (colim.map (whisker_left (costructured_arrow.proj F X) f)),
  intro Z,
  simp only [colimit.ι_map, colimit.cocone_ι, whisker_left_app, category.comp_id, category.assoc],
  transitivity f.app Z.left ≫ (colimit.ι (costructured_arrow.map Z.hom ⋙ Lan.diagram F Y₂ X :
    costructured_arrow F _ ⥤ _) (costructured_arrow.mk (𝟙 (F.obj Z.left))) : _)
    ≫ (colimit.pre (Lan.diagram F Y₂ X) (costructured_arrow.map Z.hom)),
  { rw colimit.ι_pre,
    congr,
    simp only [category.id_comp, costructured_arrow.map_mk],
    apply costructured_arrow.eq_mk },
  { congr }
end

/--
If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable
def Lan_presesrves_finite_limit_of_flat (F : C ⥤ D) [representably_flat F]
  (J : Type u₁) [small_category J] [fin_category J] :
  preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
begin
  apply preserves_limits_of_shape_of_evaluation (Lan F.op : (Cᵒᵖ ⥤ Type u₁) ⥤ (Dᵒᵖ ⥤ Type u₁)) J,
  intro K,
  rw Lan_evaluation_eq_colim,
  haveI : is_filtered (costructured_arrow F.op K) :=
    is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K)),
  apply_instance
end

/-- If `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves limits of shape `J`, so will `F`. -/
noncomputable
def preserves_limit_of_Lan_presesrves_limit (F : C ⥤ D) (J : Type u₁) [small_category J]
  [preserves_limits_of_shape J (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁))] :
  preserves_limits_of_shape J F :=
begin
  apply preserves_limits_of_shape_of_reflects_of_preserves F yoneda,
  exact preserves_limits_of_shape_of_nat_iso (comp_yoneda_iso_yoneda_comp_Lan F).symm,
  apply_instance
end

end small_category

namespace presieve.family_of_elements
open presieve
open category_theory.limits.walking_cospan (left right)
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]
variables (u : C ⥤ D) [representably_flat u] {P : Dᵒᵖ ⥤ Type v₁} {Z : C} {T : presieve Z}
variables {x : family_of_elements (u.op ⋙ P) T} (h : x.compatible)
include h

/-
We ought to show that for each `f₁ ≫ u.map g₁ = f₂ ≫ u.map g₂`, the restriction of
`x` along the two paths are the same given `x` is compatible in the image of `u`.
  -/
lemma family_of_elements_compatible_of_flat {Y₁ Y₂ : C} {X : D}
  (f₁ : X ⟶ u.obj Y₁) (f₂ : X ⟶ u.obj Y₂) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z}
  (hg₁ : T g₁) (hg₂ : T g₂) (eq : f₁ ≫ u.map g₁ = f₂ ≫ u.map g₂) :
  P.map f₁.op (x g₁ hg₁) = P.map f₂.op (x g₂ hg₂) :=
begin
  /- First, `f₁` and `f₂` forms a cone over `cospan g₁ g₂ ⋙ u`. -/
  let c : cone (cospan g₁ g₂ ⋙ u) :=
    (cones.postcompose (diagram_iso_cospan (cospan g₁ g₂ ⋙ u)).inv).obj
      (pullback_cone.mk f₁ f₂ eq),

  /-
  This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
  over it since `structured_arrow W u` is cofiltered.
  Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
  -/
  let c' := is_cofiltered.cone (structured_arrow_cone.to_diagram c ⋙ structured_arrow.pre _ _ _),
  have eq₁ : f₁ = (c'.X.hom ≫ u.map (c'.π.app left).right) ≫ eq_to_hom (by simp),
  { erw ← (c'.π.app left).w, dsimp, simp },
  have eq₂ : f₂ = (c'.X.hom ≫ u.map (c'.π.app right).right) ≫ eq_to_hom (by simp),
  { erw ← (c'.π.app right).w, dsimp, simp },
  conv_lhs { rw eq₁ },
  conv_rhs { rw eq₂ },
  simp only [op_comp, functor.map_comp, types_comp_apply, eq_to_hom_op, eq_to_hom_map],
  congr' 1,

  /-
  Now, since everything now falls in the image of `u`,
  the result follows from the compatibility of `x` in the image of `u`.
  -/
  injection c'.π.naturality walking_cospan.hom.inl with _ e₁,
  injection c'.π.naturality walking_cospan.hom.inr with _ e₂,
  exact h (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂),

end

lemma compatible.functor_pushforward : (x.functor_pushforward u).compatible :=
begin
  rintros Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq,
  unfold family_of_elements.functor_pushforward,
  rcases get_functor_pushforward_structure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩,
  rcases get_functor_pushforward_structure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩,
  suffices : P.map (g₁ ≫ h₁).op (x f₁ hf₁) = P.map (g₂ ≫ h₂).op (x f₂ hf₂), simpa using this,
  apply family_of_elements_compatible_of_flat u h,
  simpa using eq,
end

lemma functor_pushforward_apply_map {Y : C} {f: Y ⟶ Z} (hf) :
  x.functor_pushforward u (u.map f) (image_mem_functor_pushforward u T hf) = x f hf :=
begin
  unfold family_of_elements.functor_pushforward,
  rcases e₁ : get_functor_pushforward_structure (image_mem_functor_pushforward u T hf) with
    ⟨X, g, f', hg, eq⟩,
  simpa using family_of_elements_compatible_of_flat u h f' (𝟙 _) hg hf (by simp[eq]),
end

end presieve.family_of_elements

end category_theory
