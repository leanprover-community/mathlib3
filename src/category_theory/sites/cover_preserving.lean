/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf
import category_theory.flat_functors

universes v₁ v₂ u₁ u₂
noncomputable theory

open category_theory
open opposite
open category_theory.presieve.family_of_elements
open category_theory.presieve
open category_theory.limits

namespace category_theory
section cover_lifting
variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}
variables {L : grothendieck_topology E}

/--
A functor `u : (C, J) ⥤ (D, K)` between sites is called to have the cover-preserving property
if for all covering sieves `R` in `D`, `R.pushforward u` is a covering sieve in `C`.
-/
@[nolint has_inhabited_instance]
structure cover_preserving (J : grothendieck_topology C) (K : grothendieck_topology D) (u : C ⥤ D) :=
(cover_preserve : ∀ {U : C} {S : sieve U} (hS : S ∈ J U), S.functor_pushforward u ∈ K (u.obj U))

open category_theory.limits.walking_cospan (left right)

/-
We ought to show that for each `f₁ ≫ u.map g₁ = f₂ ≫ u.map g₂`, the restriction of
`x` along the two paths are the same given `x` is compatible in the image of `u`.
  -/
lemma family_of_elements_compatible_of_flat {C : Type*} {D : Type*} [category.{v₁} C] [category.{v₁} D]
  (u : C ⥤ D) [representably_flat u] {P : Dᵒᵖ ⥤ Type*} {Y₁ Y₂ Z : C} {T : presieve Z}
  {x : family_of_elements (u.op ⋙ P) T} (h : x.compatible) {X : D}
  (f₁ : X ⟶ u.obj Y₁) (f₂ : X ⟶ u.obj Y₂) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂)
  (eq : f₁ ≫ u.map g₁ = f₂ ≫ u.map g₂) : P.map f₁.op (x g₁ hg₁) = P.map f₂.op (x g₂ hg₂) :=
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
  the result follows from the compatibleness of `x` in the image of `u`.
  -/
  injection c'.π.naturality walking_cospan.hom.inl with _ e₁,
  injection c'.π.naturality walking_cospan.hom.inr with _ e₂,
  exact h (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂),

end

lemma presieve.family_of_elements.compatible.functor_pushforward {C : Type*} {D : Type*}
  [category.{v₁} C] [category.{v₁} D]
  (u : C ⥤ D) [representably_flat u] {P : Dᵒᵖ ⥤ Type _} {Z : C} {T : presieve Z}
  {x : family_of_elements (u.op ⋙ P) T} (h : x.compatible) :
  (x.functor_pushforward u).compatible :=
begin
  rintros Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq,
  unfold family_of_elements.functor_pushforward,
  rcases get_functor_pushforward_structure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩,
  rcases get_functor_pushforward_structure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩,
  suffices : P.map (g₁ ≫ h₁).op (x f₁ hf₁) = P.map (g₂ ≫ h₂).op (x f₂ hf₂), simpa using this,
  apply family_of_elements_compatible_of_flat u h,
  simpa using eq,
end


/-- The identity functor on a site is cover-preserving. -/
def id_cover_preserving : cover_preserving J J (𝟭 _) := ⟨λ U S hS, by simpa using hS⟩

/-- The composition of two cover-preserving functors are cover-lifting -/
def comp_cover_preserving {u} (hu : cover_preserving J K u) {v} (hv : cover_preserving K L v) :
  cover_preserving J L (u ⋙ v) := ⟨λ U S hS,
begin
  rw sieve.functor_pushforward_comp,
  exact hv.cover_preserve (hu.cover_preserve hS)
end⟩

lemma functor_pushforward_apply_map {C : Type*} {D : Type*} [category.{v₁} C] [category.{v₁} D]
  (u : C ⥤ D) [representably_flat u] {P : Dᵒᵖ ⥤ Type _} {Y Z : C} {T : presieve Z}
  {x : family_of_elements (u.op ⋙ P) T} (hx : x.compatible) {f: Y ⟶ Z} (hf) :
  x.functor_pushforward u (u.map f) (image_mem_functor_pushforward u T hf) = x f hf :=
begin
  unfold family_of_elements.functor_pushforward,
  rcases e₁ : get_functor_pushforward_structure (image_mem_functor_pushforward u T hf) with
    ⟨X, g, h, hg, eq⟩,
  simpa using family_of_elements_compatible_of_flat u hx h (𝟙 _) hg hf (by simp[eq]),
end

end cover_lifting

variables {C D : Type u₁} [category.{v₁} C] [category.{v₁} D]
variables {A : Type u₂} [category.{v₁} A] [has_limits A]
variables {J : grothendieck_topology C} {K : grothendieck_topology D}

/--
If `u` is cover-preserving, then `u.op ⋙ _` pulls sheaves back to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00WW,
but without the condition that `C` or `D` has pullbacks.
-/
theorem pullback_is_sheaf_of_cover_preserving {u : C ⥤ D} [representably_flat u]
  (hu : cover_preserving J K u) (ℱ : Sheaf K A) :
  presheaf.is_sheaf J (((whiskering_left _ _ _).obj u.op).obj ℱ.val) :=
begin
  intros X U S hS x hx,
  change family_of_elements (u.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) ⇑S at x,
  let H := ℱ.2 X _ (hu.cover_preserve hS),
  split, swap,
  { apply H.amalgamate (x.functor_pushforward u),
    exact hx.functor_pushforward u },
  split,
  { intros V f hf,
    convert H.is_amalgamation (hx.functor_pushforward u)
      (u.map f) (image_mem_functor_pushforward u S hf),
    rw functor_pushforward_apply_map u hx },
  { intros y hy,
    refine H.is_separated_for _ y _ _ (H.is_amalgamation (hx.functor_pushforward u)),
    rintros V f ⟨Z, f', g', h, rfl⟩,
    erw family_of_elements.comp_of_compatible (S.functor_pushforward u)
      (hx.functor_pushforward u) (image_mem_functor_pushforward u S h) g',
    simpa [functor_pushforward_apply_map u hx h, ←hy f' h], }
end

end category_theory
