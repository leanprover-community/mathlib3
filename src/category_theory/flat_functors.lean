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

/-!
# Representably flat functors

We define representably flat functors as functors such that the catetory of structured arrows
over `X` is cofiltered for each `X`. This concept is also knows as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to differentiate
this concept from other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limit`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
limits, then `F` is flat.
* `preserves_finite_limit_of_flat`: If `F : C ⥤ D` is a flat, then it preserves all finite limits.
* `Lan_preserves_finite_limit_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `preserves_limit_of_Lan_preserves_limit`: If the functor `Lan F.op` between presheaves of sets
preserves limits of shape `J`, then so will `F`.

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

/--
If a cone `s₁` factors through another cone `s₂`, then the two constructed diagrams are actually
the same.
-/
def to_diagram_comp_map (s₁ s₂ : cone K)
  (f : s₁.X ⟶ s₂.X) (H : ∀ (j : J), f ≫ s₂.π.app j = s₁.π.app j) :
    to_diagram s₂ ⋙ structured_arrow.map f = to_diagram s₁ := by { apply functor.ext, tidy }

end structured_arrow_cone


section representably_flat
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]


@[simp]
lemma eq_to_hom_right {A : Type*} [category A] {B : Type*} [category B] {T : Type*} [category T]
  {L : A ⥤ T} {R : B ⥤ T} (X Y : comma L R) (H : X = Y) :
  comma_morphism.right (eq_to_hom H) = eq_to_hom (by { cases H, refl }) := by { cases H, refl }

lemma comma.hext {A : Type*} [category A] {B : Type*} [category B] {T : Type*} [category T]
  {L : A ⥤ T} {R : B ⥤ T} (X Y : comma L R) (h₁ : X.left = Y.left) (h₂ : X.right = Y.right)
  (h₃ : X.hom == Y.hom) : X = Y := by { cases X, cases Y, congr; assumption }

lemma cone.ext {A : Type*} [category A] {B : Type*} [category B] {F : A ⥤ B} (c d : cone F)
  (h₁ : c.X = d.X) (h₂ : ∀ j : A, c.π.app j = (eq_to_hom h₁) ≫ d.π.app j) : c = d :=
begin
  cases c, cases d, cases h₁, congr,
  cases c_π, cases d_π, congr,
  { ext x,
    specialize h₂ x, dsimp only at h₂, rw h₂,
    simp }
end
/--
A functor `F : C ⥤ D` is representably-flat functor if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class representably_flat (F : C ⥤ D) : Prop :=
(cofiltered : ∀ (X : D), is_cofiltered (structured_arrow X F))

instance functor.flat_cofiltered (F : C ⥤ D) [representably_flat F] (X : D) :
 is_cofiltered (structured_arrow X F) := representably_flat.cofiltered X

end representably_flat

section has_limit
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

open structured_arrow
open structured_arrow_cone
variables {J : Type v₁} [small_category J] {F : C ⥤ D}
variables [preserves_limits_of_shape J F] {X : D} (K : J ⥤ structured_arrow X F)
variables (c : limit_cone (K ⋙ proj X F))

include c

@[simps] def lifts_limit_cone_of_preserve : cone K :=
begin
  let hc' : is_limit (F.map_cone c.cone) := preserves_limit.preserves c.is_limit,
  let s := to_cone F c.cone (hc'.lift (diagram_to_cone F K)),
  have K_eq : to_diagram (F.map_cone c.cone) ⋙ map (hc'.lift (diagram_to_cone F K)) ⋙
    pre (diagram_to_cone F K).X (K ⋙ proj X F) F = K,
  { apply functor.ext, { intros _ _ _, ext, simp },
    intro j,
    apply comma.hext,
    cases (K.obj j).left, refl, refl, simpa using hc'.fac (diagram_to_cone F K) j },
  exact (cones.postcompose (eq_to_hom K_eq)).obj s,
end

def lifts_limit_cone_of_preserve_is_limit : is_limit (lifts_limit_cone_of_preserve K c) :=
begin
  let hc' : is_limit (F.map_cone c.cone) := preserves_limit.preserves c.is_limit,
  refine { lift := λ s', hom_mk (c.is_limit.lift ((proj X F).map_cone s')) _,
    fac' := _, uniq' := _},
  { apply hc'.uniq (diagram_to_cone F K),
    intro j,
    simp [←F.map_comp, c.is_limit.fac ((proj X F).map_cone s') j] },
  { intros s' j, ext,
    change c.is_limit.lift _ ≫ c.cone.π.app j ≫ _ = _,
    rw [← category.assoc, c.is_limit.fac ((proj X F).map_cone s')j],
    simpa [-category.comp_id] using category.comp_id ((s'.π.app j).right) },
  { intros s' m h,
    ext,
    apply c.is_limit.uniq ((proj X F).map_cone s'),
    intro j, convert congr_arg comma_morphism.right (h j),
    simpa [-category.comp_id] using (category.comp_id (c.cone.π.app j)).symm }
end

lemma lifts_limit_cone_of_preserve_is_lift :
  (proj X F).map_cone (lifts_limit_cone_of_preserve K c) = c.cone :=
by { fapply cone.ext, { dsimp, refl }, { intro x, dsimp, simp, erw category.comp_id, } }

omit c

lemma lifts_limit_cone_of_preserve_of_proj_comp (c : cone K)
  (hc : is_limit ((proj X F).map_cone c)) : lifts_limit_cone_of_preserve K ⟨_, hc⟩ = c :=
begin
fapply cone.ext,
{ apply comma.hext,
  { simp },
  { simp },
  { symmetry,
    simp only [heq_iff_eq],
    apply (preserves_limit.preserves hc).uniq (diagram_to_cone F K),
    intro _, simp } },
{ intro j, dsimp, ext, simp, erw category.comp_id },
end

instance proj_reflects_limit_of_preserve : reflects_limit K (proj X F) := ⟨λ c hc,
begin
rw ← lifts_limit_cone_of_preserve_of_proj_comp K c,
apply lifts_limit_cone_of_preserve_is_limit _ ⟨_, hc⟩,
end⟩

instance proj_creates_limit_of_preserve : creates_limit K (proj X F) :=
⟨λ c hc, ⟨_, eq_to_iso (lifts_limit_cone_of_preserve_is_lift K ⟨c, hc⟩)⟩⟩

instance proj_preserves_limit_of_shape_preserve : preserves_limits_of_shape J (proj X F) := {}

instance proj_creates_limit_of_shape_preserve : creates_limits_of_shape J (proj X F) := {}

instance has_limits_of_preserve [has_limits_of_shape J C] :
  has_limits_of_shape J (structured_arrow X F) :=
has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (proj X F)

noncomputable
instance proj_preserves_limits_of_preserve [has_limits_of_shape J C] :
  preserves_limits_of_shape J (proj X F) := ⟨λ K,
begin
apply preserves_limit_of_preserves_limit_cone,
apply lifts_limit_cone_of_preserve_is_limit,
apply get_limit_cone,
rw lifts_limit_cone_of_preserve_is_lift,
apply limit_cone.is_limit
end⟩

section end

lemma flat_of_preserves_finite_limit [has_limits C] (F : C ⥤ D)
  (H : ∀ (J : Type v₁) [h : small_category J] [h' : @fin_category J h],
    @preserves_limits_of_shape _ _ _ _ J h F) : representably_flat F := ⟨λ X,
{ cocone_objs := λ A B, by
  { let fn := limits.binary_fan.mk A.hom B.hom,
    let is_lim := is_limit_of_has_binary_product_of_preserves_limit F A.right B.right,
    use structured_arrow.mk (is_lim.lift fn),
    use structured_arrow.hom_mk limits.prod.fst (is_lim.fac fn walking_pair.left),
    use structured_arrow.hom_mk limits.prod.snd (is_lim.fac fn walking_pair.right) },
  cocone_maps := λ A B f g, by
  { let fn : fork (F.map f.right) (F.map g.right) := limits.fork.of_ι A.hom (f.w.symm.trans g.w),
    let is_lim := is_limit_of_has_equalizer_of_preserves_limit F f.right g.right,
    use structured_arrow.mk (is_lim.lift fn),
    use structured_arrow.hom_mk (equalizer.ι f.right g.right)
      (is_lim.fac fn walking_parallel_pair.zero),
    ext,
    exact equalizer.condition f.right g.right },
  nonempty := by
  { haveI := has_terminal_of_has_terminal_of_preserves_limit F,
    exact nonempty.intro (structured_arrow.mk
      (terminal.from X ≫ (preserves_terminal.iso F).inv)) } }⟩

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
    simpa using e₁.symm.trans e₂ },
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

/-- Representably flat functors preserves finite limits. -/
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
The evaluation of `Lan F` at `X` is the colimit over the costrucuted arrows over `X`.
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
end category_theory
#lint
