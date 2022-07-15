/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.elementwise
import category_theory.sites.compatible_sheafification

/-!

# Image sheaf

## Main definitions

- `image_sheaf` : The image sheaf for a morphism between sheaves of types.
- `is_surjective` : A morphism of presheaves valued in a concrete category is surjective if
  every section in the target is locally in the set-theoretic image,
  i.e. the image sheaf coincides with the target.

## Main results

- `to_sheafify_is_surjective` : `to_sheafify` is surjective.

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
(Sheaf_to_presheaf J _).mono_of_mono_map
  (show mono (image_presheaf_ι J f.1), by apply_instance)

end sheaf

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

section surjective

variable (J)

universes w' v' u'

variables {A : Type u'} [category.{v'} A] [concrete_category.{w'} A]

/-- A morphism of presheaves `f : F ⟶ G` is surjective if every section of `G` is locally in the
image of `f`. -/
def is_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : Prop :=
∀ (U : C) (s : G.obj (op U)),
  ∃ (S : sieve U) (H : S ∈ J U) (x : Π {V : C} (i : V ⟶ U) (h : S i), F.obj (op V)),
    ∀ {V : C} (i : V ⟶ U) (h : S i), G.map i.op s = f.app (op V) (x i h)

lemma is_surjective_iff_image_presheaf_ι_is_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
  is_surjective J f ↔ is_iso (image_presheaf_ι J (whisker_right f (forget A))) :=
begin
  split,
  { intro H,
    apply nat_iso.is_iso_of_is_iso_app _,
    intro U,
    rw is_iso_iff_bijective,
    exact ⟨subtype.coe_injective, λ s, ⟨⟨_, H (unop U) s⟩, rfl⟩⟩ },
  { introsI H U s,
    obtain ⟨s, rfl⟩ := ((is_iso_iff_bijective ((J.image_presheaf_ι
      (whisker_right f (forget A))).app $ op U)).mp infer_instance).2 s,
    exact s.prop }
end

lemma is_surjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
  is_surjective J f ↔ is_surjective J (whisker_right f (forget A)) :=
begin
  rw [is_surjective_iff_image_presheaf_ι_is_iso, is_surjective_iff_image_presheaf_ι_is_iso],
  refl,
end

lemma is_surjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  (H : ∀ U, function.surjective (f.app U)) : is_surjective J f :=
begin
  intros U s,
  obtain ⟨t, rfl⟩ := H _ s,
  exact ⟨_, J.top_mem _, λ _ i _, F.map i.op t, λ _ i _,
    by simpa only [comp_apply] using (concrete_category.congr_hom (f.naturality i.op) t).symm⟩,
end

lemma is_surjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [is_iso f] : is_surjective J f :=
begin
  apply is_surjective_of_surjective,
  intro U,
  apply function.bijective.surjective,
  rw ← is_iso_iff_bijective,
  apply_instance
end

lemma is_surjective.comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃}
  (h₁ : is_surjective J f₁) (h₂ : is_surjective J f₂) : is_surjective J (f₁ ≫ f₂) :=
begin
  intros U s,
  obtain ⟨S, hS, x, hx⟩ := h₂ _ s,
  have := λ ⦃V⦄ ⦃i : V ⟶ U⦄ (h : S i), h₁ _ (x i h),
  choose S' hS' x' hx',
  have := λ {V} {i : V ⟶ U} (hi : sieve.bind S S' i), hi,
  choose W i₁ i₂ hi₂ h₁ h₂,
  refine ⟨_, J.bind_covering hS hS', λ V i hi, x' (hi₂ hi) _ (h₁ hi), _⟩,
  intros V i hi,
  simpa [← h₂ hi, hx _ (hi₂ hi), ← hx', -nat_trans.naturality] using
    (concrete_category.congr_hom (f₂.naturality (i₁ hi).op) (x _ (hi₂ hi))).symm,
end

end surjective

section

variables {F G : Cᵒᵖ ⥤ Type (max u v)} (f : F ⟶ G)

/-- If `G` is a sheaf, then we may lift `F ⟶ image_presheaf J f` to the sheafification of `F`. -/
noncomputable
abbreviation sheafification_to_image_presheaf (hG : presieve.is_sheaf J G) :
    J.sheafify F ⟶ image_presheaf J f :=
J.sheafify_lift (to_image_presheaf J f)
  ((is_sheaf_iff_is_sheaf_of_type J _).mpr $ image_presheaf_is_sheaf J f hG)

variable (F)

/-- The image of `F` in `J.sheafify F` is isomorphic to the sheafification. -/
noncomputable
def sheafification_iso_image_presheaf : J.sheafify F ≅ image_presheaf J (J.to_sheafify F) :=
{ hom := sheafification_to_image_presheaf _ _
    ((is_sheaf_iff_is_sheaf_of_type J _).mp $ J.sheafify_is_sheaf _),
  inv := image_presheaf_ι _ _,
  hom_inv_id' := J.sheafify_hom_ext _ _ (J.sheafify_is_sheaf _) (by simp),
  inv_hom_id' := begin
    rw [← cancel_mono (image_presheaf_ι J $ J.to_sheafify F), category.id_comp, category.assoc],
    refine eq.trans _ (category.comp_id _),
    congr' 1,
    exact J.sheafify_hom_ext _ _ (J.sheafify_is_sheaf _) (by simp),
  end }

-- We need to sheafify
variables {A : Type w} [category.{max u v} A]
  [concrete_category.{max u v} A]
  [∀ (X : C), limits.has_colimits_of_shape (J.cover X)ᵒᵖ A]
  [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), limits.has_multiequalizer (S.index P)]
  [Π (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ A),
    limits.preserves_limit (W.index P).multicospan (forget A)]
  [Π (X : C), limits.preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget A)]
  [∀ (α β : Type (max u v)) (fst snd : β → α),
    limits.has_limits_of_shape (limits.walking_multicospan fst snd) A]

lemma to_sheafify_is_surjective (F : Cᵒᵖ ⥤ A) :
  is_surjective J (J.to_sheafify F) :=
begin
  rw [is_surjective_iff_whisker_forget, ← to_sheafify_comp_sheafify_comp_iso_inv],
  apply is_surjective.comp,
  { rw is_surjective_iff_image_presheaf_ι_is_iso,
    exact is_iso.of_iso_inv (sheafification_iso_image_presheaf J (F ⋙ forget A)) },
  { exact is_surjective_of_iso _ _ }
end

end

end category_theory.grothendieck_topology
