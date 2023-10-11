/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.filtered_colimit_commutes_finite_limit
import category_theory.limits.preserves.functor_category
import category_theory.limits.bicones
import category_theory.limits.comma
import category_theory.limits.preserves.finite
import category_theory.limits.shapes.finite_limits

/-!
# Representably flat functors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preserves_finite_limits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preserves_finite_limits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `Lan_preserves_finite_limits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_Lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preserves_finite_limits_iff_Lan_preserves_finite_limits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/

universes w v₁ v₂ v₃ u₁ u₂ u₃

open category_theory
open category_theory.limits
open opposite

namespace category_theory


namespace structured_arrow_cone
open structured_arrow
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]
variables {J : Type w} [small_category J]
variables {K : J ⥤ C} (F : C ⥤ D) (c : cone K)

/--
Given a cone `c : cone K` and a map `f : X ⟶ c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point. This is the underlying diagram.
-/
@[simps]
def to_diagram : J ⥤ structured_arrow c.X K :=
{ obj := λ j, structured_arrow.mk (c.π.app j),
  map := λ j k g, structured_arrow.hom_mk g (by simpa) }

/-- Given a diagram of `structured_arrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps]
def diagram_to_cone {X : D} (G : J ⥤ structured_arrow X F) : cone (G ⋙ proj X F ⋙ F) :=
{ X := X, π := { app := λ j, (G.obj j).hom } }

/--
Given a cone `c : cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def to_cone {X : D} (f : X ⟶ F.obj c.X) :
  cone (to_diagram (F.map_cone c) ⋙ map f ⋙ pre _ K F) :=
{ X := mk f, π := { app := λ j, hom_mk (c.π.app j) rfl,
                    naturality' := λ j k g, by { ext, dsimp, simp } } }

end structured_arrow_cone

section representably_flat
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E]

/--
A functor `F : C ⥤ D` is representably-flat functor if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class representably_flat (F : C ⥤ D) : Prop :=
(cofiltered : ∀ (X : D), is_cofiltered (structured_arrow X F))

attribute [instance] representably_flat.cofiltered

local attribute [instance] is_cofiltered.nonempty

instance representably_flat.id : representably_flat (𝟭 C) :=
begin
  constructor,
  intro X,
  haveI : nonempty (structured_arrow X (𝟭 C)) := ⟨structured_arrow.mk (𝟙 _)⟩,
  rsufficesI : is_cofiltered_or_empty (structured_arrow X (𝟭 C)),
  { constructor },
  constructor,
  { intros Y Z,
    use structured_arrow.mk (𝟙 _),
    use structured_arrow.hom_mk Y.hom (by erw [functor.id_map, category.id_comp]),
    use structured_arrow.hom_mk Z.hom (by erw [functor.id_map, category.id_comp]) },
  { intros Y Z f g,
    use structured_arrow.mk (𝟙 _),
    use structured_arrow.hom_mk Y.hom (by erw [functor.id_map, category.id_comp]),
    ext,
    transitivity Z.hom; simp }
end

instance representably_flat.comp (F : C ⥤ D) (G : D ⥤ E)
  [representably_flat F] [representably_flat G] : representably_flat (F ⋙ G) :=
begin
  constructor,
  intro X,
  haveI : nonempty (structured_arrow X (F ⋙ G)),
  { have f₁ : structured_arrow X G := nonempty.some infer_instance,
    have f₂ : structured_arrow f₁.right F := nonempty.some infer_instance,
    exact ⟨structured_arrow.mk (f₁.hom ≫ G.map f₂.hom)⟩ },
  rsufficesI : is_cofiltered_or_empty (structured_arrow X (F ⋙ G)),
  { constructor },
  constructor,
  { intros Y Z,
    let W := @is_cofiltered.min (structured_arrow X G) _ _
      (structured_arrow.mk Y.hom) (structured_arrow.mk Z.hom),
    let Y' : W ⟶ _ := is_cofiltered.min_to_left _ _,
    let Z' : W ⟶ _ := is_cofiltered.min_to_right _ _,

    let W' := @is_cofiltered.min (structured_arrow W.right F) _ _
      (structured_arrow.mk Y'.right) (structured_arrow.mk Z'.right),
    let Y'' : W' ⟶ _ := is_cofiltered.min_to_left _ _,
    let Z'' : W' ⟶ _ := is_cofiltered.min_to_right _ _,

    use structured_arrow.mk (W.hom ≫ G.map W'.hom),
    use structured_arrow.hom_mk Y''.right (by simp [← G.map_comp]),
    use structured_arrow.hom_mk Z''.right (by simp [← G.map_comp]) },
  { intros Y Z f g,
    let W := @is_cofiltered.eq (structured_arrow X G) _ _
        (structured_arrow.mk Y.hom) (structured_arrow.mk Z.hom)
        (structured_arrow.hom_mk (F.map f.right) (structured_arrow.w f))
        (structured_arrow.hom_mk (F.map g.right) (structured_arrow.w g)),
    let h : W ⟶ _ := is_cofiltered.eq_hom _ _,
    let h_cond : h ≫ _ = h ≫ _ := is_cofiltered.eq_condition _ _,

    let W' := @is_cofiltered.eq (structured_arrow W.right F) _ _
        (structured_arrow.mk h.right) (structured_arrow.mk (h.right ≫ F.map f.right))
        (structured_arrow.hom_mk f.right rfl)
        (structured_arrow.hom_mk g.right (congr_arg comma_morphism.right h_cond).symm),
    let h' : W' ⟶ _ := is_cofiltered.eq_hom _ _,
    let h'_cond : h' ≫ _ = h' ≫ _ := is_cofiltered.eq_condition _ _,

    use structured_arrow.mk (W.hom ≫ G.map W'.hom),
    use structured_arrow.hom_mk h'.right (by simp [← G.map_comp]),
    ext,
    exact (congr_arg comma_morphism.right h'_cond : _) }
end

end representably_flat

section has_limit
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₁} D]

local attribute [instance] has_finite_limits_of_has_finite_limits_of_size

lemma cofiltered_of_has_finite_limits [has_finite_limits C] : is_cofiltered C :=
{ cone_objs := λ A B, ⟨limits.prod A B, limits.prod.fst, limits.prod.snd, trivial⟩,
  cone_maps :=  λ A B f g, ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩,
  nonempty := ⟨⊤_ C⟩ }

lemma flat_of_preserves_finite_limits [has_finite_limits C] (F : C ⥤ D)
  [preserves_finite_limits F] : representably_flat F := ⟨λ X,
begin
  haveI : has_finite_limits (structured_arrow X F) :=
  begin
    apply has_finite_limits_of_has_finite_limits_of_size.{v₁} (structured_arrow X F),
    intros J sJ fJ, resetI, constructor
  end,
  exact cofiltered_of_has_finite_limits
end⟩

namespace preserves_finite_limits_of_flat
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
s'.X.hom ≫ (F.map $ hc.lift $
  (cones.postcompose ({ app := λ X, 𝟙 _, naturality' := by simp }
      : (to_diagram s ⋙ pre s.X K F) ⋙ proj s.X F ⟶ K)).obj $
  (structured_arrow.proj s.X F).map_cone s')

lemma fac (x : J) : lift F hc s ≫ (F.map_cone c).π.app x = s.π.app x :=
by simpa [lift, ←functor.map_comp]

local attribute [simp] eq_to_hom_map

lemma uniq {K : J ⥤ C} {c : cone K} (hc : is_limit c)
  (s : cone (K ⋙ F)) (f₁ f₂ : s.X ⟶ F.obj c.X)
  (h₁ : ∀ (j : J), f₁ ≫ (F.map_cone c).π.app j = s.π.app j)
  (h₂ : ∀ (j : J), f₂ ≫ (F.map_cone c).π.app j = s.π.app j) : f₁ = f₂ :=
begin
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : to_diagram (F.map_cone c) ⋙ map f₁ ⟶ to_diagram s :=
  { app := λ X, eq_to_hom (by simp [←h₁]), naturality' := λ _ _ _, by { ext, simp } },
  let α₂ : to_diagram (F.map_cone c) ⋙ map f₂ ⟶ to_diagram s :=
  { app := λ X, eq_to_hom (by simp [←h₂]), naturality' := λ _ _ _, by { ext, simp } },
  let c₁ : cone (to_diagram s ⋙ pre s.X K F) :=
    (cones.postcompose (whisker_right α₁ (pre s.X K F) : _)).obj (to_cone F c f₁),
  let c₂ : cone (to_diagram s ⋙ pre s.X K F) :=
    (cones.postcompose (whisker_right α₂ (pre s.X K F) : _)).obj (to_cone F c f₂),

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

end preserves_finite_limits_of_flat

/-- Representably flat functors preserve finite limits. -/
noncomputable
def preserves_finite_limits_of_flat (F : C ⥤ D) [representably_flat F] :
  preserves_finite_limits F :=
begin
  apply preserves_finite_limits_of_preserves_finite_limits_of_size,
  intros J _ _, constructor,
  intros K, constructor,
  intros c hc,
  exactI { lift := preserves_finite_limits_of_flat.lift F hc,
    fac' := preserves_finite_limits_of_flat.fac F hc,
    uniq' := λ s m h, by
    { apply preserves_finite_limits_of_flat.uniq F hc,
      exact h,
      exact preserves_finite_limits_of_flat.fac F hc s } }
end

/--
If `C` is finitely cocomplete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
noncomputable
def preserves_finite_limits_iff_flat [has_finite_limits C] (F : C ⥤ D) :
  representably_flat F ≃ preserves_finite_limits F :=
{ to_fun := λ _, by exactI preserves_finite_limits_of_flat F,
  inv_fun := λ _, by exactI flat_of_preserves_finite_limits F,
  left_inv := λ _, proof_irrel _ _,
  right_inv := λ x, by { cases x, unfold preserves_finite_limits_of_flat,
    dunfold preserves_finite_limits_of_preserves_finite_limits_of_size, congr } }

end has_limit


section small_category
variables {C D : Type u₁} [small_category C] [small_category D] (E : Type u₂) [category.{u₁} E]

/--
(Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costructured arrows over `X`.
-/
noncomputable
def Lan_evaluation_iso_colim (F : C ⥤ D) (X : D)
  [∀ (X : D), has_colimits_of_shape (costructured_arrow F X) E] :
  Lan F ⋙ (evaluation D E).obj X ≅
  ((whiskering_left _ _ E).obj (costructured_arrow.proj F X)) ⋙ colim :=
nat_iso.of_components (λ G, colim.map_iso (iso.refl _))
begin
  intros G H i,
  ext,
  simp only [functor.comp_map, colimit.ι_desc_assoc, functor.map_iso_refl, evaluation_obj_map,
    whiskering_left_obj_map, category.comp_id, Lan_map_app, category.assoc],
  erw [colimit.ι_pre_assoc (Lan.diagram F H X) (costructured_arrow.map j.hom),
    category.id_comp, category.comp_id, colimit.ι_map],
  rcases j with ⟨j_left, ⟨⟨⟩⟩, j_hom⟩,
  congr,
  rw [costructured_arrow.map_mk, category.id_comp, costructured_arrow.mk]
end

variables [concrete_category.{u₁} E] [has_limits E] [has_colimits E]
variables [reflects_limits (forget E)] [preserves_filtered_colimits (forget E)]
variables [preserves_limits (forget E)]

/--
If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable
instance Lan_preserves_finite_limits_of_flat (F : C ⥤ D) [representably_flat F] :
  preserves_finite_limits (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ E)) :=
begin
  apply preserves_finite_limits_of_preserves_finite_limits_of_size.{u₁},
  intros J _ _, resetI,
  apply preserves_limits_of_shape_of_evaluation (Lan F.op : (Cᵒᵖ ⥤ E) ⥤ (Dᵒᵖ ⥤ E)) J,
  intro K,
  haveI : is_filtered (costructured_arrow F.op K) :=
    is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K)),
  exact preserves_limits_of_shape_of_nat_iso (Lan_evaluation_iso_colim _ _ _).symm,
end

instance Lan_flat_of_flat (F : C ⥤ D) [representably_flat F] :
  representably_flat (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ E)) := flat_of_preserves_finite_limits _

variable [has_finite_limits C]

noncomputable
instance Lan_preserves_finite_limits_of_preserves_finite_limits (F : C ⥤ D)
  [preserves_finite_limits F] : preserves_finite_limits (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ E)) :=
begin
  haveI := flat_of_preserves_finite_limits F,
  apply_instance
end

lemma flat_iff_Lan_flat (F : C ⥤ D) :
  representably_flat F ↔ representably_flat (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
⟨λ H, by exactI infer_instance, λ H,
begin
  resetI,
  haveI := preserves_finite_limits_of_flat (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)),
  haveI : preserves_finite_limits F :=
    begin
      apply preserves_finite_limits_of_preserves_finite_limits_of_size.{u₁},
      intros, resetI, apply preserves_limit_of_Lan_preserves_limit
    end,
  apply flat_of_preserves_finite_limits
end⟩

/--
If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
noncomputable
def preserves_finite_limits_iff_Lan_preserves_finite_limits (F : C ⥤ D) :
  preserves_finite_limits F ≃ preserves_finite_limits (Lan F.op : _ ⥤ (Dᵒᵖ ⥤ Type u₁)) :=
{ to_fun := λ _, by exactI infer_instance,
  inv_fun := λ _,
  begin
    apply preserves_finite_limits_of_preserves_finite_limits_of_size.{u₁},
    intros, resetI, apply preserves_limit_of_Lan_preserves_limit
  end,
  left_inv := λ x,
  begin
    cases x, unfold preserves_finite_limits_of_flat,
    dunfold preserves_finite_limits_of_preserves_finite_limits_of_size, congr
  end,
  right_inv := λ x,
  begin
    cases x,
    unfold preserves_finite_limits_of_flat,
    congr,
    unfold category_theory.Lan_preserves_finite_limits_of_preserves_finite_limits
      category_theory.Lan_preserves_finite_limits_of_flat,
    dunfold preserves_finite_limits_of_preserves_finite_limits_of_size, congr
  end }

end small_category
end category_theory
