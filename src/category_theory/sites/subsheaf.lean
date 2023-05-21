/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.elementwise
import category_theory.adjunction.evaluation
import category_theory.sites.sheafification

/-!

# Subsheaf of types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the sub(pre)sheaf of a type valued presheaf.

## Main results

- `category_theory.grothendieck_topology.subpresheaf` :
  A subpresheaf of a presheaf of types.
- `category_theory.grothendieck_topology.subpresheaf.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `category_theory.grothendieck_topology.subpresheaf.sheafify_is_sheaf` :
  The sheafification is a sheaf
- `category_theory.grothendieck_topology.subpresheaf.sheafify_lift` :
  The descent of a map into a sheaf to the sheafification.
- `category_theory.grothendieck_topology.image_sheaf` : The image sheaf of a morphism.
- `category_theory.grothendieck_topology.image_factorization` : The image sheaf as a
  `limits.image_factorization`.
-/

universes w v u

open opposite category_theory

namespace category_theory.grothendieck_topology

variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)

/-- A subpresheaf of a presheaf consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
structure subpresheaf (F : Cᵒᵖ ⥤ Type w) :=
(obj : Π U, set (F.obj U))
(map : Π {U V : Cᵒᵖ} (i : U ⟶ V), (obj U) ⊆ (F.map i) ⁻¹' (obj V))

variables {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : subpresheaf F)

instance : partial_order (subpresheaf F) :=
partial_order.lift subpresheaf.obj subpresheaf.ext

instance : has_top (subpresheaf F) :=
⟨⟨λ U, ⊤, λ U V i x h, _root_.trivial⟩⟩

instance : nonempty (subpresheaf F) := infer_instance

/-- The subpresheaf as a presheaf. -/
@[simps]
def subpresheaf.to_presheaf : Cᵒᵖ ⥤ Type w :=
{ obj := λ U, G.obj U,
  map := λ U V i x, ⟨F.map i x, G.map i x.prop⟩,
  map_id' := λ X, by { ext ⟨x, _⟩, dsimp, rw F.map_id, refl },
  map_comp' := λ X Y Z i j, by { ext ⟨x, _⟩, dsimp, rw F.map_comp, refl } }

instance {U} : has_coe (G.to_presheaf.obj U) (F.obj U) :=
coe_subtype

/-- The inclusion of a subpresheaf to the original presheaf. -/
@[simps]
def subpresheaf.ι : G.to_presheaf ⟶ F :=
{ app := λ U x, x }

instance : mono G.ι :=
⟨λ H f₁ f₂ e, nat_trans.ext f₁ f₂ $ funext $ λ U,
  funext $ λ x, subtype.ext $ congr_fun (congr_app e U) x⟩

/-- The inclusion of a subpresheaf to a larger subpresheaf -/
@[simps]
def subpresheaf.hom_of_le {G G' : subpresheaf F} (h : G ≤ G') : G.to_presheaf ⟶ G'.to_presheaf :=
{ app := λ U x, ⟨x, h U x.prop⟩ }

instance {G G' : subpresheaf F} (h : G ≤ G') : mono (subpresheaf.hom_of_le h) :=
⟨λ H f₁ f₂ e, nat_trans.ext f₁ f₂ $ funext $ λ U,
  funext $ λ x, subtype.ext $ (congr_arg subtype.val $ (congr_fun (congr_app e U) x : _) : _)⟩

@[simp, reassoc]
lemma subpresheaf.hom_of_le_ι  {G G' : subpresheaf F} (h : G ≤ G') :
  subpresheaf.hom_of_le h ≫ G'.ι = G.ι :=
by { ext, refl }

instance : is_iso (subpresheaf.ι (⊤ : subpresheaf F)) :=
begin
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  { intro X, rw is_iso_iff_bijective,
    exact ⟨subtype.coe_injective, λ x, ⟨⟨x, _root_.trivial⟩, rfl⟩⟩ }
end

lemma subpresheaf.eq_top_iff_is_iso : G = ⊤ ↔ is_iso G.ι :=
begin
  split,
  { rintro rfl, apply_instance },
  { introI H, ext U x, apply (iff_true _).mpr, rw ← is_iso.inv_hom_id_apply (G.ι.app U) x,
    exact ((inv (G.ι.app U)) x).2 }
end

/-- If the image of a morphism falls in a subpresheaf, then the morphism factors through it. -/
@[simps]
def subpresheaf.lift (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) : F' ⟶ G.to_presheaf :=
{ app := λ U x, ⟨f.app U x, hf U x⟩,
  naturality' := by { have := elementwise_of f.naturality, intros, ext, simp [this] } }

@[simp, reassoc]
lemma subpresheaf.lift_ι (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) :
  G.lift f hf ≫ G.ι = f := by { ext, refl }

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
def subpresheaf.sieve_of_section {U : Cᵒᵖ} (s : F.obj U) : sieve (unop U) :=
{ arrows := λ V f, F.map f.op s ∈ G.obj (op V),
  downward_closed' := λ V W i hi j,
    by { rw [op_comp, functor_to_types.map_comp_apply], exact G.map _ hi } }

/-- Given a `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
def subpresheaf.family_of_elements_of_section {U : Cᵒᵖ} (s : F.obj U) :
  (G.sieve_of_section s).1.family_of_elements G.to_presheaf :=
λ V i hi, ⟨F.map i.op s, hi⟩

lemma subpresheaf.family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
  (G.family_of_elements_of_section s).compatible :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e,
  ext1,
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s),
  rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply,
    ← op_comp, ← op_comp, e],
end

lemma subpresheaf.nat_trans_naturality (f : F' ⟶ G.to_presheaf) {U V : Cᵒᵖ} (i : U ⟶ V)
  (x : F'.obj U) :
  (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
congr_arg subtype.val (functor_to_types.naturality _ _ f i x)

include J

/-- The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf. -/
def subpresheaf.sheafify : subpresheaf F :=
{ obj := λ U, { s | G.sieve_of_section s ∈ J (unop U) },
  map := begin
    rintros U V i s hs,
    refine J.superset_covering _ (J.pullback_stable i.unop hs),
    intros _ _ h,
    dsimp at h ⊢,
    rwa ← functor_to_types.map_comp_apply,
  end }

lemma subpresheaf.le_sheafify : G ≤ G.sheafify J :=
begin
  intros U s hs,
  change _ ∈ J _,
  convert J.top_mem _,
  rw eq_top_iff,
  rintros V i -,
  exact G.map i.op hs,
end

variable {J}

lemma subpresheaf.eq_sheafify (h : presieve.is_sheaf J F)
  (hG : presieve.is_sheaf J G.to_presheaf) : G = G.sheafify J :=
begin
  apply (G.le_sheafify J).antisymm,
  intros U s hs,
  suffices : ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s,
  { rw ← this, exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2 },
  apply (h _ hs).is_separated_for.ext,
  intros V i hi,
  exact (congr_arg subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) : _)
end

lemma subpresheaf.sheafify_is_sheaf (hF : presieve.is_sheaf J F) :
  presieve.is_sheaf J (G.sheafify J).to_presheaf :=
begin
  intros U S hS x hx,
  let S' := sieve.bind S (λ Y f hf, G.sieve_of_section (x f hf).1),
  have := λ {V} {i : V ⟶ U} (hi : S' i), hi,
  choose W i₁ i₂ hi₂ h₁ h₂,
  dsimp [-sieve.bind_apply] at *,
  let x'' : presieve.family_of_elements F S' :=
    λ V i hi, F.map (i₁ hi).op (x _ (hi₂ hi)),
  have H : ∀ s, x.is_amalgamation s ↔ x''.is_amalgamation s.1,
  { intro s,
    split,
    { intros H V i hi,
      dsimp only [x''],
      conv_lhs { rw ← h₂ hi },
      rw ← H _ (hi₂ hi),
      exact functor_to_types.map_comp_apply F (i₂ hi).op (i₁ hi).op _ },
    { intros H V i hi,
      ext1,
      apply (hF _ (x i hi).2).is_separated_for.ext,
      intros V' i' hi',
      have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩,
      have := H _ hi'',
      rw [op_comp, F.map_comp] at this,
      refine this.trans (congr_arg subtype.val (hx _ _ (hi₂ hi'') hi (h₂ hi''))) } },
  have : x''.compatible,
  { intros V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e,
    rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
    exact congr_arg subtype.val
      (hx (g₁ ≫ i₁ S₁) (g₂ ≫ i₁ S₂) (hi₂ S₁) (hi₂ S₂) (by simp only [category.assoc, h₂, e])) },
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS (λ V i hi, (x i hi).2)) _ this,
  refine ⟨⟨t, _⟩, (H ⟨t, _⟩).mpr ht, λ y hy, subtype.ext (ht' _ ((H _).mp hy))⟩,
  show G.sieve_of_section t ∈ J _,
  refine J.superset_covering _ (J.bind_covering hS (λ V i hi, (x i hi).2)),
  intros V i hi,
  dsimp,
  rw ht _ hi,
  exact h₁ hi
end

lemma subpresheaf.eq_sheafify_iff (h : presieve.is_sheaf J F) :
  G = G.sheafify J ↔ presieve.is_sheaf J G.to_presheaf :=
⟨λ e, e.symm ▸ G.sheafify_is_sheaf h, G.eq_sheafify h⟩

lemma subpresheaf.is_sheaf_iff (h : presieve.is_sheaf J F) :
  presieve.is_sheaf J G.to_presheaf ↔
    ∀ U (s : F.obj U), G.sieve_of_section s ∈ J (unop U) → s ∈ G.obj U :=
begin
  rw ← G.eq_sheafify_iff h,
  change _ ↔ G.sheafify J ≤ G,
  exact ⟨eq.ge, (G.le_sheafify J).antisymm⟩
end

lemma subpresheaf.sheafify_sheafify (h : presieve.is_sheaf J F) :
  (G.sheafify J).sheafify J = G.sheafify J :=
((subpresheaf.eq_sheafify_iff _ h).mpr $ G.sheafify_is_sheaf h).symm

/-- The lift of a presheaf morphism onto the sheafification subpresheaf.  -/
noncomputable
def subpresheaf.sheafify_lift (f : G.to_presheaf ⟶ F') (h : presieve.is_sheaf J F') :
  (G.sheafify J).to_presheaf ⟶ F' :=
{ app := λ U s,
    (h _ s.prop).amalgamate _ ((G.family_of_elements_compatible ↑s).comp_presheaf_map f),
  naturality' :=
  begin
    intros U V i,
    ext s,
    apply (h _ ((subpresheaf.sheafify J G).to_presheaf.map i s).prop).is_separated_for.ext,
    intros W j hj,
    refine (presieve.is_sheaf_for.valid_glue _ _ _ hj).trans _,
    dsimp,
    conv_rhs { rw ← functor_to_types.map_comp_apply },
    change _ = F'.map (j ≫ i.unop).op _,
    refine eq.trans _ (presieve.is_sheaf_for.valid_glue _ _ _ _).symm,
    { dsimp at ⊢ hj, rwa functor_to_types.map_comp_apply },
    { dsimp [presieve.family_of_elements.comp_presheaf_map],
      congr' 1,
      ext1,
      exact (functor_to_types.map_comp_apply _ _ _ _).symm }
  end }

lemma subpresheaf.to_sheafify_lift (f : G.to_presheaf ⟶ F') (h : presieve.is_sheaf J F') :
  subpresheaf.hom_of_le (G.le_sheafify J) ≫ G.sheafify_lift f h = f :=
begin
  ext U s,
  apply (h _ ((subpresheaf.hom_of_le (G.le_sheafify J)).app U s).prop).is_separated_for.ext,
  intros V i hi,
  have := elementwise_of f.naturality,
  exact (presieve.is_sheaf_for.valid_glue _ _ _ hi).trans (this _ _)
end

lemma subpresheaf.to_sheafify_lift_unique (h : presieve.is_sheaf J F')
  (l₁ l₂ : (G.sheafify J).to_presheaf ⟶ F')
  (e : subpresheaf.hom_of_le (G.le_sheafify J) ≫ l₁ =
    subpresheaf.hom_of_le (G.le_sheafify J) ≫ l₂) : l₁ = l₂ :=
begin
  ext U ⟨s, hs⟩,
  apply (h _ hs).is_separated_for.ext,
  rintros V i hi,
  dsimp at hi,
  erw [← functor_to_types.naturality, ← functor_to_types.naturality],
  exact (congr_fun (congr_app e $ op V) ⟨_, hi⟩ : _)
end

lemma subpresheaf.sheafify_le (h : G ≤ G') (hF : presieve.is_sheaf J F)
  (hG' : presieve.is_sheaf J G'.to_presheaf) :
  G.sheafify J ≤ G' :=
begin
  intros U x hx,
  convert ((G.sheafify_lift (subpresheaf.hom_of_le h) hG').app U ⟨x, hx⟩).2,
  apply (hF _ hx).is_separated_for.ext,
  intros V i hi,
  have := congr_arg (λ f : G.to_presheaf ⟶ G'.to_presheaf, (nat_trans.app f (op V) ⟨_, hi⟩).1)
    (G.to_sheafify_lift (subpresheaf.hom_of_le h) hG'),
  convert this.symm,
  erw ← subpresheaf.nat_trans_naturality,
  refl,
end

omit J

section image

/-- The image presheaf of a morphism, whose components are the set-theoretic images. -/
@[simps]
def image_presheaf (f : F' ⟶ F) : subpresheaf F :=
{ obj := λ U, set.range (f.app U),
  map := λ U V i,
    by { rintros _ ⟨x, rfl⟩, have := elementwise_of f.naturality, exact ⟨_, this i x⟩ } }

@[simp] lemma top_subpresheaf_obj (U) : (⊤ : subpresheaf F).obj U = ⊤ := rfl

@[simp]
lemma image_presheaf_id : image_presheaf (𝟙 F) = ⊤ :=
by { ext, simp }

/-- A morphism factors through the image presheaf. -/
@[simps]
def to_image_presheaf (f : F' ⟶ F) : F' ⟶ (image_presheaf f).to_presheaf :=
(image_presheaf f).lift f (λ U x, set.mem_range_self _)

variables (J)

/-- A morphism factors through the sheafification of the image presheaf. -/
@[simps]
def to_image_presheaf_sheafify (f : F' ⟶ F) : F' ⟶ ((image_presheaf f).sheafify J).to_presheaf :=
 to_image_presheaf f ≫ subpresheaf.hom_of_le ((image_presheaf f).le_sheafify J)

variables {J}

@[simp, reassoc]
lemma to_image_presheaf_ι (f : F' ⟶ F) : to_image_presheaf f ≫ (image_presheaf f).ι = f :=
(image_presheaf f).lift_ι _ _

lemma image_presheaf_comp_le (f₁ : F ⟶ F') (f₂ : F' ⟶ F'') :
  image_presheaf (f₁ ≫ f₂) ≤ image_presheaf f₂ :=
λ U x hx, ⟨f₁.app U hx.some, hx.some_spec⟩

instance {F F' : Cᵒᵖ ⥤ Type (max v w)} (f : F ⟶ F') [hf : mono f] :
  is_iso (to_image_presheaf f) :=
begin
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intro X,
  rw is_iso_iff_bijective,
  split,
  { intros x y e,
    have := (nat_trans.mono_iff_mono_app _ _).mp hf X,
    rw mono_iff_injective at this,
    exact this (congr_arg subtype.val e : _) },
  { rintro ⟨_, ⟨x, rfl⟩⟩, exact ⟨x, rfl⟩ }
end

/-- The image sheaf of a morphism between sheaves, defined to be the sheafification of
`image_presheaf`. -/
@[simps]
def image_sheaf {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf J (Type w) :=
⟨((image_presheaf f.1).sheafify J).to_presheaf,
  by { rw is_sheaf_iff_is_sheaf_of_type, apply subpresheaf.sheafify_is_sheaf,
    rw ← is_sheaf_iff_is_sheaf_of_type, exact F'.2 }⟩

/-- A morphism factors through the image sheaf. -/
@[simps]
def to_image_sheaf {F F' : Sheaf J (Type w)} (f : F ⟶ F') : F ⟶ image_sheaf f :=
⟨to_image_presheaf_sheafify J f.1⟩

/-- The inclusion of the image sheaf to the target. -/
@[simps]
def image_sheaf_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') : image_sheaf f ⟶ F' :=
⟨subpresheaf.ι _⟩

@[simp, reassoc]
lemma to_image_sheaf_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
  to_image_sheaf f ≫ image_sheaf_ι f = f :=
by { ext1, simp [to_image_presheaf_sheafify] }

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : mono (image_sheaf_ι f) :=
(Sheaf_to_presheaf J _).mono_of_mono_map (by { dsimp, apply_instance })

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : epi (to_image_sheaf f) :=
begin
  refine ⟨λ G' g₁ g₂ e, _⟩,
  ext U ⟨s, hx⟩,
  apply ((is_sheaf_iff_is_sheaf_of_type J _).mp G'.2 _ hx).is_separated_for.ext,
  rintros V i ⟨y, e'⟩,
  change (g₁.val.app _ ≫ G'.val.map _) _ = (g₂.val.app _ ≫ G'.val.map _) _,
  rw [← nat_trans.naturality, ← nat_trans.naturality],
  have E : (to_image_sheaf f).val.app (op V) y =
    (image_sheaf f).val.map i.op ⟨s, hx⟩ := subtype.ext e',
  have := congr_arg (λ f : F ⟶ G', (Sheaf.hom.val f).app _ y) e,
  dsimp at this ⊢,
  convert this; exact E.symm
end

/-- The mono factorization given by `image_sheaf` for a morphism. -/
def image_mono_factorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
  limits.mono_factorisation f :=
{ I := image_sheaf f,
  m := image_sheaf_ι f,
  e := to_image_sheaf f }

/-- The mono factorization given by `image_sheaf` for a morphism is an image. -/
noncomputable
def image_factorization {F F' : Sheaf J (Type (max v u))} (f : F ⟶ F') :
  limits.image_factorisation f :=
{ F := image_mono_factorization f,
  is_image :=
  { lift := λ I, begin
      haveI := (Sheaf.hom.mono_iff_presheaf_mono J _ _).mp I.m_mono,
      refine ⟨subpresheaf.hom_of_le _ ≫ inv (to_image_presheaf I.m.1)⟩,
      apply subpresheaf.sheafify_le,
      { conv_lhs { rw ← I.fac }, apply image_presheaf_comp_le },
      { rw ← is_sheaf_iff_is_sheaf_of_type, exact F'.2 },
      { apply presieve.is_sheaf_iso J (as_iso $ to_image_presheaf I.m.1),
        rw ← is_sheaf_iff_is_sheaf_of_type, exact I.I.2 }
    end,
    lift_fac' := λ I, begin
      ext1,
      dsimp [image_mono_factorization],
      generalize_proofs h,
      rw [← subpresheaf.hom_of_le_ι h, category.assoc],
      congr' 1,
      rw [is_iso.inv_comp_eq, to_image_presheaf_ι],
    end } }

instance : limits.has_images (Sheaf J (Type (max v u))) :=
⟨λ _ _ f, ⟨⟨image_factorization f⟩⟩⟩

end image

end category_theory.grothendieck_topology
