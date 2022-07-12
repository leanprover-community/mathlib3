/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.elementwise
import category_theory.sites.compatible_sheafification

/-!

# Image sheaf

We define the image presheaf of morphisms of presheaves, and upgrade it into a sheaf when the target
is.

## Main definitions

- `image_presheaf` : The image presheaf for a morphism between presheaves of types.
- `image_sheaf` : The image sheaf for a morphism between sheaves of types.

-/

universes v u w

open opposite category_theory

namespace category_theory.grothendieck_topology

variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)

section presheaf

variables {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G)

/-- For a map `f : F ⟶ G` between presheaves of types, the image presheaf is the subpresheaf
of `G` consisting the sections that are locally in the image of `f`. -/
def image_presheaf : Cᵒᵖ ⥤ Type w :=
{ obj := λ U, { s : G.obj U // ∃ (S : sieve (unop U)) (H : S ∈ J (unop U))
    (x : presieve.family_of_elements F S), (x.comp_presheaf_map f).is_amalgamation s },
  map := λ U V i s, ⟨G.map i s, begin
    obtain ⟨S, hS, x, hx⟩ := s.prop,
    exact ⟨_, J.pullback_stable i.unop hS, x.pullback i.unop,
      λ W j hj, (functor_to_types.map_comp_apply G i j.op _).symm.trans (hx _ hj)⟩,
  end⟩,
  map_id' := λ U, funext $ λ x, subtype.ext (functor_to_types.map_id_apply G ↑x),
  map_comp' := λ U V W i j, funext $ λ x, subtype.ext (functor_to_types.map_comp_apply G i j x) }

/-- The restriction of `f : F ⟶ G` into the image presheaf. -/
def to_image_presheaf : F ⟶ image_presheaf J f :=
{ app := λ X s, ⟨f.app X s, ⊤, J.top_mem _, λ _ i _, F.map i.op s,
    λ _ i _, (congr_fun (f.naturality i.op) s).symm⟩,
  naturality' := λ U V i, funext $ λ s, subtype.ext $ (congr_fun (f.naturality i) s) }

/-- The inclusion map from the image presheaf. -/
def image_presheaf_ι : image_presheaf J f ⟶ G :=
{ app := λ _ x, x.1, naturality' := λ U V i, funext $ λ x, rfl }

@[simp, reassoc]
lemma image_presheaf_to_ι : to_image_presheaf J f ≫ image_presheaf_ι J f = f :=
by { ext, refl }

instance : mono (image_presheaf_ι J f) :=
begin
  refine ⟨λ H f₁ f₂ e, _⟩,
  ext U x,
  exact congr_fun (congr_app e U) x,
end

/-- The image presheaf is a sheaf if the target presheaf is. -/
lemma image_presheaf_is_sheaf (hG : presieve.is_sheaf J G) :
    presieve.is_sheaf J (image_presheaf J f) :=
begin
  intros U S hS x hx,
  have := λ V (i : V ⟶ U) hi, (x i hi).2,
  choose S' hS' x' hx',
  have := λ {V} {i : V ⟶ U} (hi : sieve.bind S S' i), hi,
  choose W i₁ i₂ hi₂ h₁ h₂,
  let x'' : presieve.family_of_elements F (sieve.bind S S') := λ V i hi, x' _ _ (hi₂ hi) _ (h₁ hi),
  have H : ∀ s, x.is_amalgamation s ↔ (x''.comp_presheaf_map f).is_amalgamation s.1,
  { intro s,
    split,
    { intros H V i hi,
      refine eq.trans _ (hx' _ _ (hi₂ hi) _ (h₁ hi)),
      conv_lhs { rw ← h₂ hi },
      rw ← H _ (hi₂ hi),
      exact functor_to_types.map_comp_apply G (i₂ hi).op (i₁ hi).op _ },
    { intros H V i hi,
      ext1,
      apply (hG _ (hS' V i hi)).is_separated_for.ext,
      intros V' i' hi',
      have hi'' : sieve.bind S S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩,
      have := H _ hi'',
      rw [op_comp, G.map_comp] at this,
      refine this.trans ((hx' _ _ (hi₂ hi'') _ (h₁ hi'')).symm.trans _),
      exact congr_arg subtype.val (hx _ _ (hi₂ hi'') hi (h₂ hi'')) } },
  have : (x''.comp_presheaf_map f).compatible,
  { intros V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e,
    refine (congr_arg (G.map g₁.op) (hx' _ _ (hi₂ S₁) _ (h₁ S₁))).symm.trans
      (eq.trans _ $ congr_arg (G.map g₂.op) (hx' _ _ (hi₂ S₂) _ (h₁ S₂))),
    rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
    exact congr_arg subtype.val
      (hx (g₁ ≫ i₁ S₁) (g₂ ≫ i₁ S₂) (hi₂ S₁) (hi₂ S₂) (by simp only [category.assoc, h₂, e])) },
  obtain ⟨t, ht, ht'⟩ := hG _ (J.bind_covering hS hS') _ this,
  exact ⟨⟨t, _, J.bind_covering hS hS', _, ht⟩, (H ⟨t, _⟩).mpr ht, λ y hy,
    subtype.ext (ht' _ ((H _).mp hy))⟩,
end

end presheaf

section sheaf

variables {J} {F G : Sheaf J (Type w)} (f : F ⟶ G)

/-- For a map `f : F ⟶ G` between presheaves of types, the image sheaf is the subsheaf
of `G` consisting the sections that are locally in the image of `f`. -/
def image_sheaf : Sheaf J (Type w) :=
⟨image_presheaf J f.1, (is_sheaf_iff_is_sheaf_of_type J _).mpr $ image_presheaf_is_sheaf J _ $
  (is_sheaf_iff_is_sheaf_of_type J _).mp G.2⟩

/-- The restriction of `f : F ⟶ G` into the image sheaf. -/
def to_image_sheaf : F ⟶ image_sheaf f := ⟨to_image_presheaf J f.1⟩

/-- The inclusion map from the image sheaf. -/
def image_sheaf_ι : image_sheaf f ⟶ G := ⟨image_presheaf_ι J f.1⟩

@[simp] lemma image_sheaf_to_ι : to_image_sheaf f ≫ image_sheaf_ι f = f :=
Sheaf.hom.ext _ _ (image_presheaf_to_ι J f.1)

instance : epi (to_image_sheaf f) :=
begin
  refine ⟨λ G' g₁ g₂ e, _⟩,
  ext U ⟨s, S, hS, x, hx⟩,
  apply ((is_sheaf_iff_is_sheaf_of_type J _).mp G'.2 S hS).is_separated_for.ext,
  intros V i hi,
  change (g₁.val.app _ ≫ G'.val.map _) _ = (g₂.val.app _ ≫ G'.val.map _) _,
  rw [← nat_trans.naturality, ← nat_trans.naturality],
  have E : (to_image_sheaf f).val.app (op V) (x i hi) =
    (image_sheaf f).val.map i.op ⟨s, S, hS, x, hx⟩ := subtype.ext (hx i hi).symm,
  have := congr_arg (λ f : F ⟶ G', (Sheaf.hom.val f).app _ (x i hi)) e,
  dsimp at this ⊢,
  rwa E at this,
end

instance : mono (image_sheaf_ι f) :=
faithful_reflects_mono (Sheaf_to_presheaf J _)
  (show mono (image_presheaf_ι J f.1), by apply_instance)

end sheaf

end category_theory.grothendieck_topology
