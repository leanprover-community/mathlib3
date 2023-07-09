/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.subsheaf
import category_theory.sites.compatible_sheafification

/-!

# Locally surjective morphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

- `is_locally_surjective` : A morphism of presheaves valued in a concrete category is locally
  surjective with respect to a grothendieck topology if every section in the target is locally
  in the set-theoretic image, i.e. the image sheaf coincides with the target.

## Main results

- `to_sheafify_is_locally_surjective` : `to_sheafify` is locally surjective.

-/

universes v u w v' u' w'

open opposite category_theory category_theory.grothendieck_topology

namespace category_theory

variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variables {A : Type u'} [category.{v'} A] [concrete_category.{w'} A]

/-- Given `f : F ⟶ G`, a morphism between presieves, and `s : G.obj (op U)`, this is the sieve
of `U` consisting of the `i : V ⟶ U` such that `s` restricted along `i` is in the image of `f`. -/
@[simps (lemmas_only)]
def image_sieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) : sieve U :=
{ arrows := λ V i, ∃ t : F.obj (op V), f.app _ t = G.map i.op s,
  downward_closed' := begin
    rintros V W i ⟨t, ht⟩ j,
    refine ⟨F.map j.op t, _⟩,
    rw [op_comp, G.map_comp, comp_apply, ← ht, elementwise_of f.naturality],
  end }

lemma image_sieve_eq_sieve_of_section {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) :
  image_sieve f s = (image_presheaf (whisker_right f (forget A))).sieve_of_section s := rfl

lemma image_sieve_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : G.obj (op U)) :
  image_sieve (whisker_right f (forget A)) s = image_sieve f s := rfl

lemma image_sieve_app {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : F.obj (op U)) :
  image_sieve f (f.app _ s) = ⊤ :=
begin
  ext V i,
  simp only [sieve.top_apply, iff_true, image_sieve_apply],
  have := elementwise_of (f.naturality i.op),
  exact ⟨F.map i.op s, this s⟩,
end

/-- A morphism of presheaves `f : F ⟶ G` is locally surjective with respect to a grothendieck
topology if every section of `G` is locally in the image of `f`. -/
def is_locally_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : Prop :=
∀ (U : C) (s : G.obj (op U)), image_sieve f s ∈ J U

lemma is_locally_surjective_iff_image_presheaf_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
  is_locally_surjective J f ↔ (image_presheaf (whisker_right f (forget A))).sheafify J = ⊤ :=
begin
  simp only [subpresheaf.ext_iff, function.funext_iff, set.ext_iff, top_subpresheaf_obj,
    set.top_eq_univ, set.mem_univ, iff_true],
  exact ⟨λ H U, H (unop U), λ H U, H (op U)⟩
end

lemma is_locally_surjective_iff_image_presheaf_sheafify_eq_top'
  {F G : Cᵒᵖ ⥤ (Type w)} (f : F ⟶ G) :
  is_locally_surjective J f ↔ (image_presheaf f).sheafify J = ⊤ :=
begin
  simp only [subpresheaf.ext_iff, function.funext_iff, set.ext_iff, top_subpresheaf_obj,
    set.top_eq_univ, set.mem_univ, iff_true],
  exact ⟨λ H U, H (unop U), λ H U, H (op U)⟩
end

lemma is_locally_surjective_iff_is_iso
  {F G : Sheaf J (Type w)} (f : F ⟶ G) :
  is_locally_surjective J f.1 ↔ is_iso (image_sheaf_ι f) :=
begin
  rw [image_sheaf_ι, is_locally_surjective_iff_image_presheaf_sheafify_eq_top',
    subpresheaf.eq_top_iff_is_iso],
  exact ⟨λ h, @@is_iso_of_reflects_iso _ _ (image_sheaf_ι f) (Sheaf_to_presheaf J _) h _,
    λ h, @@functor.map_is_iso _ _ (Sheaf_to_presheaf J _) _ h⟩,
end

lemma is_locally_surjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
  is_locally_surjective J f ↔ is_locally_surjective J (whisker_right f (forget A)) :=
begin
  simpa only [is_locally_surjective_iff_image_presheaf_sheafify_eq_top]
end

lemma is_locally_surjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  (H : ∀ U, function.surjective (f.app U)) : is_locally_surjective J f :=
begin
  intros U s,
  obtain ⟨t, rfl⟩ := H _ s,
  rw image_sieve_app,
  exact J.top_mem _
end

lemma is_locally_surjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [is_iso f] :
  is_locally_surjective J f :=
begin
  apply is_locally_surjective_of_surjective,
  intro U,
  apply function.bijective.surjective,
  rw ← is_iso_iff_bijective,
  apply_instance
end

lemma is_locally_surjective.comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃}
  (h₁ : is_locally_surjective J f₁) (h₂ : is_locally_surjective J f₂) :
    is_locally_surjective J (f₁ ≫ f₂) :=
begin
  intros U s,
  have : sieve.bind (image_sieve f₂ s) (λ _ _ h, image_sieve f₁ h.some) ≤ image_sieve (f₁ ≫ f₂) s,
  { rintros V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩,
    refine ⟨t', _⟩,
    rw [op_comp, F₃.map_comp, nat_trans.comp_app, comp_apply, comp_apply, ht',
      elementwise_of f₂.naturality, H.some_spec] },
  apply J.superset_covering this,
  apply J.bind_covering,
  { apply h₂ },
  { intros, apply h₁ }
end

section

variables (F : Cᵒᵖ ⥤ Type (max u v))

/-- The image of `F` in `J.sheafify F` is isomorphic to the sheafification. -/
noncomputable
def sheafification_iso_image_presheaf :
  J.sheafify F ≅ ((image_presheaf (J.to_sheafify F)).sheafify J).to_presheaf :=
{ hom := J.sheafify_lift (to_image_presheaf_sheafify J _)
  ((is_sheaf_iff_is_sheaf_of_type J _).mpr $ subpresheaf.sheafify_is_sheaf _ $
    (is_sheaf_iff_is_sheaf_of_type J _).mp $ sheafify_is_sheaf J _),
  inv := subpresheaf.ι _,
  hom_inv_id' := J.sheafify_hom_ext _ _ (J.sheafify_is_sheaf _)
    (by simp [to_image_presheaf_sheafify]),
  inv_hom_id' := begin
    rw [← cancel_mono (subpresheaf.ι _), category.id_comp, category.assoc],
    refine eq.trans _ (category.comp_id _),
    congr' 1,
    exact J.sheafify_hom_ext _ _ (J.sheafify_is_sheaf _) (by simp [to_image_presheaf_sheafify]),
    apply_instance
  end }

-- We need to sheafify
variables {B : Type w} [category.{max u v} B]
  [concrete_category.{max u v} B]
  [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ B]
  [∀ (P : Cᵒᵖ ⥤ B) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
  [Π (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ B),
    limits.preserves_limit (W.index P).multicospan (forget B)]
  [Π (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget B)]
  [∀ (α β : Type (max u v)) (fst snd : β → α),
    limits.has_limits_of_shape (limits.walking_multicospan fst snd) B]

lemma to_sheafify_is_locally_surjective (F : Cᵒᵖ ⥤ B) :
  is_locally_surjective J (J.to_sheafify F) :=
begin
  rw [is_locally_surjective_iff_whisker_forget, ← to_sheafify_comp_sheafify_comp_iso_inv],
  apply is_locally_surjective.comp,
  { rw [is_locally_surjective_iff_image_presheaf_sheafify_eq_top, subpresheaf.eq_top_iff_is_iso],
    exact is_iso.of_iso_inv (sheafification_iso_image_presheaf J (F ⋙ forget B)) },
  { exact is_locally_surjective_of_iso _ _ }
end

end

end category_theory
