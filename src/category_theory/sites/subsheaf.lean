/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.elementwise
import category_theory.sites.compatible_sheafification
import category_theory.limits.constructions.epi_mono

/-!

# Subsheaf of types

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
-/

universes w v u

open opposite category_theory

namespace category_theory.grothendieck_topology

variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)

/-- The subpresheaf of a presheaf. -/
@[ext]
structure subpresheaf (F : Cᵒᵖ ⥤ Type w) :=
(obj : Π U, set (F.obj U))
(map : Π {U V : Cᵒᵖ} (i : U ⟶ V), (obj U) ⊆ (F.map i) ⁻¹' (obj V))

variables {F F' : Cᵒᵖ ⥤ Type w} (G G' : subpresheaf F)

instance : partial_order (subpresheaf F) :=
partial_order.lift subpresheaf.obj subpresheaf.ext

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

attribute [elementwise] nat_trans.naturality

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
  exact (presieve.is_sheaf_for.valid_glue _ _ _ hi).trans (f.naturality_apply _ _)
end

end category_theory.grothendieck_topology
