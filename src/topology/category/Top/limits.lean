/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import topology.category.Top.epi_mono
import category_theory.limits.preserves.limits
import category_theory.category.ulift
import category_theory.limits.shapes.types
import category_theory.limits.concrete_category

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

open topological_space
open category_theory
open category_theory.limits
open opposite

universes u v w

noncomputable theory

namespace Top

variables {J : Type v} [small_category J]

local notation `forget` := forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{max v u}) : cone F :=
{ X := Top.of {u : Π j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j},
  π :=
  { app := λ j,
    { to_fun := λ u, u.val j,
      continuous_to_fun := show continuous ((λ u : Π j : J, F.obj j, u j) ∘ subtype.val),
        by continuity } } }

/--
A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone_infi (F : J ⥤ Top.{max v u}) : cone F :=
{ X := ⟨(types.limit_cone (F ⋙ forget)).X, ⨅j,
        (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
  π :=
  { app := λ j, ⟨(types.limit_cone (F ⋙ forget)).π.app j,
                 continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f, continuous_map.coe_injective
      ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{max v u}) : is_limit (limit_cone F) :=
{ lift := λ S, { to_fun := λ x, ⟨λ j, S.π.app _ x, λ i j f, by { dsimp, erw ← S.w f, refl }⟩ },
  uniq' := λ S m h, by { ext : 3, simpa [← h] } }

/--
The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_infi_is_limit (F : J ⥤ Top.{max v u}) : is_limit (limit_cone_infi F) :=
by { refine is_limit.of_faithful forget (types.limit_cone_is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.π.app j).continuous :
         _) ) }

instance Top_has_limits_of_size : has_limits_of_size.{v} Top.{max v u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance Top_has_limits : has_limits Top.{u} := Top.Top_has_limits_of_size.{u u}

instance forget_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget : Top.{max v u} ⥤ Type (max v u)) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
Top.forget_preserves_limits_of_size.{u u}

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{max v u}) : cocone F :=
{ X := ⟨(types.colimit_cocone (F ⋙ forget)).X, ⨆ j,
        (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
  ι :=
  { app := λ j, ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j,
                 continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f, continuous_map.coe_injective
      ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{max v u}) : is_colimit (colimit_cocone F) :=
by { refine is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (λ s, ⟨_, _⟩)
       (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.ι.app j).continuous :
         _) ) }

instance Top_has_colimits_of_size : has_colimits_of_size.{v} Top.{max v u} :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk { cocone := colimit_cocone F, is_colimit :=
    colimit_cocone_is_colimit F } } }

instance Top_has_colimits : has_colimits Top.{u} := Top.Top_has_colimits_of_size.{u u}

instance forget_preserves_colimits_of_size :
  preserves_colimits_of_size.{v v} (forget : Top.{max v u} ⥤ Type (max v u)) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
Top.forget_preserves_colimits_of_size.{u u}

/-- The projection from the product as a bundled continous map. -/
abbreviation pi_π {ι : Type v} (α : ι → Top.{max v u}) (i : ι) : Top.of (Π i, α i) ⟶ α i :=
⟨λ f, f i, continuous_apply i⟩

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps X π_app]
def pi_fan {ι : Type v} (α : ι → Top.{max v u}) : fan α :=
fan.mk (Top.of (Π i, α i)) (pi_π α)

/-- The constructed fan is indeed a limit -/
def pi_fan_is_limit {ι : Type v} (α : ι → Top.{max v u}) : is_limit (pi_fan α) :=
{ lift := λ S, { to_fun := λ s i, S.π.app i s },
  uniq' := by { intros S m h, ext x i, simp [← h i] } }

/--
The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def pi_iso_pi {ι : Type v} (α : ι → Top.{max v u}) : ∏ α ≅ Top.of (Π i, α i) :=
(limit.is_limit _).cone_point_unique_up_to_iso (pi_fan_is_limit α)

@[simp, reassoc]
lemma pi_iso_pi_inv_π {ι : Type v} (α : ι → Top.{max v u}) (i : ι) :
  (pi_iso_pi α).inv ≫ pi.π α i = pi_π α i :=
by simp [pi_iso_pi]

@[simp]
lemma pi_iso_pi_inv_π_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : Π i, α i) :
  (pi.π α i : _) ((pi_iso_pi α).inv x) = x i :=
concrete_category.congr_hom (pi_iso_pi_inv_π α i) x

@[simp]
lemma pi_iso_pi_hom_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : ∏ α) :
  (pi_iso_pi α).hom x i = (pi.π α i : _) x :=
begin
  have := pi_iso_pi_inv_π α i,
  rw iso.inv_comp_eq at this,
  exact concrete_category.congr_hom this x
end

/-- The inclusion to the coproduct as a bundled continous map. -/
abbreviation sigma_ι {ι : Type v} (α : ι → Top.{max v u}) (i : ι) : α i ⟶ Top.of (Σ i, α i) :=
⟨sigma.mk i⟩

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps X ι_app]
def sigma_cofan {ι : Type v} (α : ι → Top.{max v u}) : cofan α :=
cofan.mk (Top.of (Σ i, α i)) (sigma_ι α)

/-- The constructed cofan is indeed a colimit -/
def sigma_cofan_is_colimit {ι : Type v} (α : ι → Top.{max v u}) : is_colimit (sigma_cofan α) :=
{ desc := λ S, { to_fun := λ s, S.ι.app s.1 s.2,
    continuous_to_fun := by { continuity, dsimp only, continuity } },
  uniq' := by { intros S m h,  ext ⟨i, x⟩, simp [← h i] } }

/--
The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigma_iso_sigma {ι : Type v} (α : ι → Top.{max v u}) : ∐ α ≅ Top.of (Σ i, α i) :=
(colimit.is_colimit _).cocone_point_unique_up_to_iso (sigma_cofan_is_colimit α)

@[simp, reassoc]
lemma sigma_iso_sigma_hom_ι {ι : Type v} (α : ι → Top.{max v u}) (i : ι) :
  sigma.ι α i ≫ (sigma_iso_sigma α).hom = sigma_ι α i :=
by simp [sigma_iso_sigma]

@[simp]
lemma sigma_iso_sigma_hom_ι_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : α i) :
  (sigma_iso_sigma α).hom ((sigma.ι α i : _) x) = sigma.mk i x :=
concrete_category.congr_hom (sigma_iso_sigma_hom_ι α i) x

@[simp]
lemma sigma_iso_sigma_inv_apply {ι : Type v} (α : ι → Top.{max v u}) (i : ι) (x : α i) :
  (sigma_iso_sigma α).inv ⟨i, x⟩ = (sigma.ι α i : _) x :=
by { rw [← sigma_iso_sigma_hom_ι_apply, ← comp_app], simp, }

lemma induced_of_is_limit {F : J ⥤ Top.{max v u}} (C : cone F) (hC : is_limit C) :
  C.X.topological_space = ⨅ j, (F.obj j).topological_space.induced (C.π.app j) :=
begin
  let homeo := homeo_of_iso (hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit F)),
  refine homeo.inducing.induced.trans _,
  change induced homeo (⨅ (j : J), _) = _,
  simpa [induced_infi, induced_compose],
end

lemma limit_topology (F : J ⥤ Top.{max v u}) :
  (limit F).topological_space = ⨅ j, (F.obj j).topological_space.induced (limit.π F j) :=
induced_of_is_limit _ (limit.is_limit F)

section prod

/-- The first projection from the product. -/
abbreviation prod_fst {X Y : Top.{u}} : Top.of (X × Y) ⟶ X := ⟨prod.fst⟩

/-- The second projection from the product. -/
abbreviation prod_snd {X Y : Top.{u}} : Top.of (X × Y) ⟶ Y := ⟨prod.snd⟩

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
def prod_binary_fan (X Y : Top.{u}) : binary_fan X Y :=
binary_fan.mk prod_fst prod_snd

/-- The constructed binary fan is indeed a limit -/
def prod_binary_fan_is_limit (X Y : Top.{u}) : is_limit (prod_binary_fan X Y) :=
{ lift := λ (S : binary_fan X Y), { to_fun := λ s, (S.fst s, S.snd s) },
  fac' := begin
    rintros S (_|_),
    tidy
  end,
  uniq' := begin
    intros S m h,
    ext x,
    { specialize h walking_pair.left,
      apply_fun (λ e, (e x)) at h,
      exact h },
     { specialize h walking_pair.right,
      apply_fun (λ e, (e x)) at h,
      exact h },
  end }

/--
The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prod_iso_prod (X Y : Top.{u}) : X ⨯ Y ≅ Top.of (X × Y) :=
(limit.is_limit _).cone_point_unique_up_to_iso (prod_binary_fan_is_limit X Y)

@[simp, reassoc] lemma prod_iso_prod_hom_fst (X Y : Top.{u}) :
  (prod_iso_prod X Y).hom ≫ prod_fst = limits.prod.fst :=
by simpa [← iso.eq_inv_comp, prod_iso_prod]

@[simp, reassoc] lemma prod_iso_prod_hom_snd (X Y : Top.{u}) :
  (prod_iso_prod X Y).hom ≫ prod_snd = limits.prod.snd :=
by simpa [← iso.eq_inv_comp, prod_iso_prod]

@[simp] lemma prod_iso_prod_hom_apply {X Y : Top.{u}} (x : X ⨯ Y) :
  (prod_iso_prod X Y).hom x =
    ((limits.prod.fst : X ⨯ Y ⟶ _) x, (limits.prod.snd : X ⨯ Y ⟶ _) x) :=
begin
  ext,
  { exact concrete_category.congr_hom (prod_iso_prod_hom_fst X Y) x },
  { exact concrete_category.congr_hom (prod_iso_prod_hom_snd X Y) x }
end

@[simp, reassoc, elementwise] lemma prod_iso_prod_inv_fst (X Y : Top.{u}) :
  (prod_iso_prod X Y).inv ≫ limits.prod.fst = prod_fst :=
by simp [iso.inv_comp_eq]

@[simp, reassoc, elementwise] lemma prod_iso_prod_inv_snd (X Y : Top.{u}) :
  (prod_iso_prod X Y).inv ≫ limits.prod.snd = prod_snd :=
by simp [iso.inv_comp_eq]

lemma prod_topology {X Y : Top} :
  (X ⨯ Y).topological_space =
    induced (limits.prod.fst : X ⨯ Y ⟶ _) X.topological_space ⊓
      induced (limits.prod.snd : X ⨯ Y ⟶ _) Y.topological_space :=
begin
  let homeo := homeo_of_iso (prod_iso_prod X Y),
  refine homeo.inducing.induced.trans _,
  change induced homeo (_ ⊓ _) = _,
  simpa [induced_compose]
end

lemma range_prod_map {W X Y Z : Top.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
  set.range (limits.prod.map f g) =
    (limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' (set.range f) ∩
      (limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' (set.range g) :=
begin
  ext,
  split,
  { rintros ⟨y, rfl⟩,
    simp only [set.mem_preimage, set.mem_range, set.mem_inter_eq, ←comp_apply],
    simp only [limits.prod.map_fst, limits.prod.map_snd,
      exists_apply_eq_apply, comp_apply, and_self] },
  { rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩,
    use (prod_iso_prod W X).inv (x₁, x₂),
    apply concrete.limit_ext,
    rintro ⟨⟩,
    { simp only [← comp_apply, category.assoc], erw limits.prod.map_fst, simp [hx₁] },
    { simp only [← comp_apply, category.assoc], erw limits.prod.map_snd, simp [hx₂] } }
end

lemma inducing_prod_map {W X Y Z : Top} {f : W ⟶ X} {g : Y ⟶ Z}
  (hf : inducing f) (hg : inducing g) : inducing (limits.prod.map f g) :=
begin
  constructor,
  simp only [prod_topology, induced_compose, ←coe_comp, limits.prod.map_fst, limits.prod.map_snd,
    induced_inf],
  simp only [coe_comp],
  rw [← @induced_compose _ _ _ _ _ f, ← @induced_compose _ _ _ _ _ g, ← hf.induced, ← hg.induced]
end

lemma embedding_prod_map {W X Y Z : Top} {f : W ⟶ X} {g : Y ⟶ Z}
  (hf : embedding f) (hg : embedding g) : embedding (limits.prod.map f g) :=
⟨inducing_prod_map hf.to_inducing hg.to_inducing,
begin
  haveI := (Top.mono_iff_injective _).mpr hf.inj,
  haveI := (Top.mono_iff_injective _).mpr hg.inj,
  exact (Top.mono_iff_injective _).mp infer_instance
end⟩

end prod

section pullback

variables {X Y Z : Top.{u}}

/-- The first projection from the pullback. -/
abbreviation pullback_fst (f : X ⟶ Z) (g : Y ⟶ Z) : Top.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
⟨prod.fst ∘ subtype.val⟩

/-- The second projection from the pullback. -/
abbreviation pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z) : Top.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
⟨prod.snd ∘ subtype.val⟩

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullback_cone (f : X ⟶ Z) (g : Y ⟶ Z) : pullback_cone f g :=
pullback_cone.mk (pullback_fst f g) (pullback_snd f g) (by { ext ⟨x, h⟩, simp [h] })

/-- The constructed cone is a limit. -/
def pullback_cone_is_limit (f : X ⟶ Z) (g : Y ⟶ Z) :
  is_limit (pullback_cone f g) := pullback_cone.is_limit_aux' _
begin
  intro s,
  split, swap,
  exact { to_fun := λ x, ⟨⟨s.fst x, s.snd x⟩,
    by simpa using concrete_category.congr_hom s.condition x⟩ },
  refine ⟨_,_,_⟩,
  { ext, delta pullback_cone, simp },
  { ext, delta pullback_cone, simp },
  { intros m h₁ h₂,
    ext x,
    { simpa using concrete_category.congr_hom h₁ x },
    { simpa using concrete_category.congr_hom h₂ x } }
end

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullback_iso_prod_subtype (f : X ⟶ Z) (g : Y ⟶ Z) :
  pullback f g ≅ Top.of { p : X × Y // f p.1 = g p.2 } :=
(limit.is_limit _).cone_point_unique_up_to_iso (pullback_cone_is_limit f g)

@[simp, reassoc] lemma pullback_iso_prod_subtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).inv ≫ pullback.fst = pullback_fst f g :=
by simpa [pullback_iso_prod_subtype]

@[simp] lemma pullback_iso_prod_subtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
  (x : { p : X × Y // f p.1 = g p.2 }) :
  (pullback.fst : pullback f g ⟶ _) ((pullback_iso_prod_subtype f g).inv x) = (x : X × Y).fst :=
concrete_category.congr_hom (pullback_iso_prod_subtype_inv_fst f g) x

@[simp, reassoc] lemma pullback_iso_prod_subtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).inv ≫ pullback.snd = pullback_snd f g :=
by simpa [pullback_iso_prod_subtype]

@[simp] lemma pullback_iso_prod_subtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z)
  (x : { p : X × Y // f p.1 = g p.2 }) :
  (pullback.snd : pullback f g ⟶ _) ((pullback_iso_prod_subtype f g).inv x) = (x : X × Y).snd :=
concrete_category.congr_hom (pullback_iso_prod_subtype_inv_snd f g) x

lemma pullback_iso_prod_subtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).hom ≫ pullback_fst f g = pullback.fst :=
by rw [←iso.eq_inv_comp, pullback_iso_prod_subtype_inv_fst]

lemma pullback_iso_prod_subtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback_iso_prod_subtype f g).hom ≫ pullback_snd f g = pullback.snd :=
by rw [←iso.eq_inv_comp, pullback_iso_prod_subtype_inv_snd]

@[simp] lemma pullback_iso_prod_subtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z}
  (x : pullback f g) : (pullback_iso_prod_subtype f g).hom x =
    ⟨⟨(pullback.fst : pullback f g ⟶ _) x, (pullback.snd : pullback f g ⟶ _) x⟩,
      by simpa using concrete_category.congr_hom pullback.condition x⟩ :=
begin
  ext,
  exacts [concrete_category.congr_hom (pullback_iso_prod_subtype_hom_fst f g) x,
    concrete_category.congr_hom (pullback_iso_prod_subtype_hom_snd f g) x]
end

lemma pullback_topology {X Y Z : Top.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback f g).topological_space =
    induced (pullback.fst : pullback f g ⟶ _) X.topological_space ⊓
      induced (pullback.snd : pullback f g ⟶ _) Y.topological_space :=
begin
  let homeo := homeo_of_iso (pullback_iso_prod_subtype f g),
  refine homeo.inducing.induced.trans _,
  change induced homeo (induced _ (_ ⊓ _)) = _,
  simpa [induced_compose]
end

lemma range_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  set.range (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) =
  { x | (limits.prod.fst ≫ f) x = (limits.prod.snd ≫ g) x } :=
begin
  ext x,
  split,
  { rintros ⟨y, rfl⟩,
    simp only [←comp_apply, set.mem_set_of_eq],
    congr' 1,
    simp [pullback.condition] },
  { intro h,
    use (pullback_iso_prod_subtype f g).inv ⟨⟨_, _⟩, h⟩,
    apply concrete.limit_ext,
    rintro ⟨⟩; simp }
end

lemma inducing_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inducing ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
⟨by simp [prod_topology, pullback_topology, induced_compose, ←coe_comp]⟩

lemma embedding_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  embedding ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
⟨inducing_pullback_to_prod f g, (Top.mono_iff_injective _).mp infer_instance⟩

/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
lemma range_pullback_map {W X Y Z S T : Top} (f₁ : W ⟶ S) (f₂ : X ⟶ S)
  (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : mono i₃]
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  set.range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
    (pullback.fst : pullback g₁ g₂ ⟶ _) ⁻¹' (set.range i₁) ∩
      (pullback.snd : pullback g₁ g₂ ⟶ _) ⁻¹' (set.range i₂) :=
begin
  ext,
  split,
  { rintro ⟨y, rfl⟩, simp, },
  rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩,
  have : f₁ x₁ = f₂ x₂,
  { apply (Top.mono_iff_injective _).mp H₃,
    simp only [←comp_apply, eq₁, eq₂],
    simp only [comp_apply, hx₁, hx₂],
    simp only [←comp_apply, pullback.condition] },
  use (pullback_iso_prod_subtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩,
  apply concrete.limit_ext,
  rintros (_|_|_),
  { simp only [Top.comp_app, limit.lift_π_apply, category.assoc, pullback_cone.mk_π_app_one,
      hx₁, pullback_iso_prod_subtype_inv_fst_apply, subtype.coe_mk],
    simp only [← comp_apply],
    congr,
    apply limit.w _ walking_cospan.hom.inl },
  { simp [hx₁] },
  { simp [hx₂] },
end

lemma pullback_fst_range {X Y S : Top} (f : X ⟶ S) (g : Y ⟶ S) :
  set.range (pullback.fst : pullback f g ⟶ _) = { x : X | ∃ y : Y, f x = g y} :=
begin
  ext x,
  split,
  { rintro ⟨y, rfl⟩,
    use (pullback.snd : pullback f g ⟶ _) y,
    exact concrete_category.congr_hom pullback.condition y },
  { rintro ⟨y, eq⟩,
    use (Top.pullback_iso_prod_subtype f g).inv ⟨⟨x, y⟩, eq⟩,
    simp },
end

lemma pullback_snd_range {X Y S : Top} (f : X ⟶ S) (g : Y ⟶ S) :
  set.range (pullback.snd : pullback f g ⟶ _) = { y : Y | ∃ x : X, f x = g y} :=
begin
  ext y,
  split,
  { rintro ⟨x, rfl⟩,
    use (pullback.fst : pullback f g ⟶ _) x,
    exact concrete_category.congr_hom pullback.condition x },
  { rintro ⟨x, eq⟩,
    use (Top.pullback_iso_prod_subtype f g).inv ⟨⟨x, y⟩, eq⟩,
    simp },
end

/--
If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗      ↗
  X  ⟶  Z
-/
lemma pullback_map_embedding_of_embeddings {W X Y Z S T : Top}
  (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z}
  (H₁ : embedding i₁) (H₂ : embedding i₂) (i₃ : S ⟶ T)
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
begin
  refine embedding_of_embedding_compose (continuous_map.continuous_to_fun _)
    (show continuous (prod.lift pullback.fst pullback.snd : pullback g₁ g₂ ⟶ Y ⨯ Z), from
      continuous_map.continuous_to_fun _) _,
  suffices : embedding
    (prod.lift pullback.fst pullback.snd ≫ limits.prod.map i₁ i₂ : pullback f₁ f₂ ⟶ _),
  { simpa [←coe_comp] using this },
  rw coe_comp,
  refine embedding.comp (embedding_prod_map H₁ H₂)
    (embedding_pullback_to_prod _ _)
end

/--
If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.
  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗       ↗
  X  ⟶  Z
-/
lemma pullback_map_open_embedding_of_open_embeddings {W X Y Z S T : Top}
  (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z}
  (H₁ : open_embedding i₁) (H₂ : open_embedding i₂) (i₃ : S ⟶ T) [H₃ : mono i₃]
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  open_embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
begin
  split,
  { apply pullback_map_embedding_of_embeddings
      f₁ f₂ g₁ g₂ H₁.to_embedding H₂.to_embedding i₃ eq₁ eq₂ },
  { rw range_pullback_map,
    apply is_open.inter; apply continuous.is_open_preimage,
    continuity,
    exacts [H₁.open_range, H₂.open_range] }
end

lemma snd_embedding_of_left_embedding {X Y S : Top}
  {f : X ⟶ S} (H : embedding f) (g : Y ⟶ S) :
  embedding ⇑(pullback.snd : pullback f g ⟶ Y) :=
begin
  convert (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).embedding.comp
    (pullback_map_embedding_of_embeddings f g (𝟙 _) g H
      (homeo_of_iso (iso.refl _)).embedding (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

lemma fst_embedding_of_right_embedding {X Y S : Top}
  (f : X ⟶ S) {g : Y ⟶ S} (H : embedding g) :
  embedding ⇑(pullback.fst : pullback f g ⟶ X) :=
begin
  convert (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).embedding.comp
    (pullback_map_embedding_of_embeddings f g f (𝟙 _)
      (homeo_of_iso (iso.refl _)).embedding H (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

lemma embedding_of_pullback_embeddings {X Y S : Top}
  {f : X ⟶ S} {g : Y ⟶ S} (H₁ : embedding f) (H₂ : embedding g) :
  embedding (limit.π (cospan f g) walking_cospan.one) :=
begin
  convert H₂.comp (snd_embedding_of_left_embedding H₁ g),
  erw ←coe_comp,
  congr,
  exact (limit.w _ walking_cospan.hom.inr).symm
end

lemma snd_open_embedding_of_left_open_embedding {X Y S : Top}
  {f : X ⟶ S} (H : open_embedding f) (g : Y ⟶ S) :
  open_embedding ⇑(pullback.snd : pullback f g ⟶ Y) :=
begin
  convert (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).open_embedding.comp
    (pullback_map_open_embedding_of_open_embeddings f g (𝟙 _) g H
      (homeo_of_iso (iso.refl _)).open_embedding (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

lemma fst_open_embedding_of_right_open_embedding {X Y S : Top}
  (f : X ⟶ S) {g : Y ⟶ S} (H : open_embedding g) :
  open_embedding ⇑(pullback.fst : pullback f g ⟶ X) :=
begin
  convert (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).open_embedding.comp
    (pullback_map_open_embedding_of_open_embeddings f g f (𝟙 _)
      (homeo_of_iso (iso.refl _)).open_embedding H (𝟙 _) rfl (by simp)),
  erw ←coe_comp,
  simp
end

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
lemma open_embedding_of_pullback_open_embeddings {X Y S : Top}
  {f : X ⟶ S} {g : Y ⟶ S} (H₁ : open_embedding f) (H₂ : open_embedding g) :
  open_embedding (limit.π (cospan f g) walking_cospan.one) :=
begin
  convert H₂.comp (snd_open_embedding_of_left_open_embedding H₁ g),
  erw ←coe_comp,
  congr,
  exact (limit.w _ walking_cospan.hom.inr).symm
end

lemma fst_iso_of_right_embedding_range_subset {X Y S : Top} (f : X ⟶ S) {g : Y ⟶ S}
  (hg : embedding g) (H : set.range f ⊆ set.range g) : is_iso (pullback.fst : pullback f g ⟶ X) :=
begin
  let : (pullback f g : Top) ≃ₜ X :=
    (homeomorph.of_embedding _ (fst_embedding_of_right_embedding f hg)).trans
    { to_fun := coe,
      inv_fun := (λ x, ⟨x,
        by { rw pullback_fst_range, exact ⟨_, (H (set.mem_range_self x)).some_spec.symm⟩ }⟩),
      left_inv := λ ⟨_,_⟩, rfl,
      right_inv := λ x, rfl },
  convert is_iso.of_iso (iso_of_homeo this),
  ext,
  refl
end

lemma snd_iso_of_left_embedding_range_subset {X Y S : Top} {f : X ⟶ S} (hf : embedding f)
  (g : Y ⟶ S) (H : set.range g ⊆ set.range f) : is_iso (pullback.snd : pullback f g ⟶ Y) :=
begin
  let : (pullback f g : Top) ≃ₜ Y :=
    (homeomorph.of_embedding _ (snd_embedding_of_left_embedding hf g)).trans
    { to_fun := coe,
      inv_fun := (λ x, ⟨x,
        by { rw pullback_snd_range, exact ⟨_, (H (set.mem_range_self x)).some_spec⟩ }⟩),
      left_inv := λ ⟨_,_⟩, rfl,
      right_inv := λ x, rfl },
  convert is_iso.of_iso (iso_of_homeo this),
  ext,
  refl
end

lemma pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : set X) :
  (pullback.snd : pullback f g ⟶ _) '' ((pullback.fst : pullback f g ⟶ _) ⁻¹' U) =
    g ⁻¹' (f '' U) :=
begin
  ext x,
  split,
  { rintros ⟨y, hy, rfl⟩,
    exact ⟨(pullback.fst : pullback f g ⟶ _) y, hy,
    concrete_category.congr_hom pullback.condition y⟩ },
  { rintros ⟨y, hy, eq⟩,
    exact ⟨(Top.pullback_iso_prod_subtype f g).inv ⟨⟨_,_⟩, eq⟩, by simpa, by simp⟩ },
end

lemma pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : set Y) :
  (pullback.fst : pullback f g ⟶ _) '' ((pullback.snd : pullback f g ⟶ _) ⁻¹' U) =
    f ⁻¹' (g '' U) :=
begin
  ext x,
  split,
  { rintros ⟨y, hy, rfl⟩,
    exact ⟨(pullback.snd : pullback f g ⟶ _) y, hy,
    (concrete_category.congr_hom pullback.condition y).symm⟩ },
  { rintros ⟨y, hy, eq⟩,
    exact ⟨(Top.pullback_iso_prod_subtype f g).inv ⟨⟨_,_⟩,eq.symm⟩, by simpa, by simp⟩ },
end

end pullback

--TODO: Add analogous constructions for `coprod` and `pushout`.

lemma coinduced_of_is_colimit {F : J ⥤ Top.{max v u}} (c : cocone F) (hc : is_colimit c) :
  c.X.topological_space = ⨆ j, (F.obj j).topological_space.coinduced (c.ι.app j) :=
begin
  let homeo := homeo_of_iso (hc.cocone_point_unique_up_to_iso (colimit_cocone_is_colimit F)),
  ext,
  refine homeo.symm.is_open_preimage.symm.trans (iff.trans _ is_open_supr_iff.symm),
  exact is_open_supr_iff
end

lemma colimit_topology (F : J ⥤ Top.{max v u}) :
  (colimit F).topological_space = ⨆ j, (F.obj j).topological_space.coinduced (colimit.ι F j) :=
coinduced_of_is_colimit _ (colimit.is_colimit F)

lemma colimit_is_open_iff (F : J ⥤ Top.{max v u}) (U : set ((colimit F : _) : Type (max v u))) :
  is_open U ↔ ∀ j, is_open (colimit.ι F j ⁻¹' U) :=
begin
  conv_lhs { rw colimit_topology F },
  exact is_open_supr_iff
end

lemma coequalizer_is_open_iff (F : walking_parallel_pair.{u} ⥤ Top.{u})
  (U : set ((colimit F : _) : Type u)) :
  is_open U ↔ is_open (colimit.ι F walking_parallel_pair.one ⁻¹' U) :=
begin
  rw colimit_is_open_iff.{u},
  split,
  { intro H, exact H _ },
  { intros H j,
    cases j,
    { rw ←colimit.w F walking_parallel_pair_hom.left,
      exact (F.map walking_parallel_pair_hom.left).continuous_to_fun.is_open_preimage _ H },
    { exact H } }
end

end Top

namespace Top

section cofiltered_limit

variables {J : Type v} [small_category J] [is_cofiltered J] (F : J ⥤ Top.{max v u})
  (C : cone F) (hC : is_limit C)

include hC

/--
Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit
  (T : Π j, set (set (F.obj j))) (hT : ∀ j, is_topological_basis (T j))
  (univ : ∀ (i : J), set.univ ∈ T i)
  (inter : ∀ i (U1 U2 : set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
  (compat : ∀ (i j : J) (f : i ⟶ j) (V : set (F.obj j)) (hV : V ∈ T j), (F.map f) ⁻¹' V ∈ T i) :
  is_topological_basis { U : set C.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } :=
begin
  classical,
  -- The limit cone for `F` whose topology is defined as an infimum.
  let D := limit_cone_infi F,
  -- The isomorphism between the cone point of `C` and the cone point of `D`.
  let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _),
  have hE : inducing E.hom := (Top.homeo_of_iso E).inducing,
  -- Reduce to the assertion of the theorem with `D` instead of `C`.
  suffices : is_topological_basis
    { U : set D.X | ∃ j (V : set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V },
  { convert this.inducing hE,
    ext U0,
    split,
    { rintro ⟨j, V, hV, rfl⟩,
      refine ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩ },
    { rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩,
      refine ⟨j, V, hV, rfl⟩ } },
  -- Using `D`, we can apply the characterization of the topological basis of a
  -- topology defined as an infimum...
  convert is_topological_basis_infi hT (λ j (x : D.X), D.π.app j x),
  ext U0,
  split,
  { rintros  ⟨j, V, hV, rfl⟩,
    let U : Π i, set (F.obj i) := λ i, if h : i = j then (by {rw h, exact V}) else set.univ,
    refine ⟨U,{j},_,_⟩,
    { rintro i h,
      rw finset.mem_singleton at h,
      dsimp [U],
      rw dif_pos h,
      subst h,
      exact hV },
    { dsimp [U],
      simp } },
  { rintros ⟨U, G, h1, h2⟩,
    obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G,
    let g : ∀ e (he : e ∈ G), j ⟶ e := λ _ he, (hj he).some,
    let Vs : J → set (F.obj j) := λ e, if h : e ∈ G then F.map (g e h) ⁻¹' (U e) else set.univ,
    let V : set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e,
    refine ⟨j, V, _, _⟩,
    { -- An intermediate claim used to apply induction along `G : finset J` later on.
      have : ∀ (S : set (set (F.obj j))) (E : finset J) (P : J → set (F.obj j))
        (univ : set.univ ∈ S)
        (inter : ∀ A B : set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
        (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S), (⋂ e (he : e ∈ E), P e) ∈ S,
      { intros S E,
        apply E.induction_on,
        { intros P he hh,
          simpa },
        { intros a E ha hh1 hh2 hh3 hh4 hh5,
          rw finset.set_bInter_insert,
          refine hh4 _ _ (hh5 _ (finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _),
          intros e he,
          exact hh5 e (finset.mem_insert_of_mem he) } },
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine this _ _ _ (univ _) (inter _) _,
      intros e he,
      dsimp [Vs],
      rw dif_pos he,
      exact compat j e (g e he) (U e) (h1 e he), },
    { -- conclude...
      rw h2,
      dsimp [V],
      rw set.preimage_Inter,
      congr' 1,
      ext1 e,
      rw set.preimage_Inter,
      congr' 1,
      ext1 he,
      dsimp [Vs],
      rw [dif_pos he, ← set.preimage_comp],
      congr' 1,
      change _ = ⇑(D.π.app j ≫ F.map (g e he)),
      rw D.w } }
end

end cofiltered_limit

section topological_konig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [preorder J] [is_directed J (≤)]` and
`F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in `nonempty_sections_of_fintype_cofiltered_system` and
`nonempty_sections_of_fintype_inverse_system`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/

variables {J : Type u} [small_category J]
variables (F : J ⥤ Top.{u})

private abbreviation finite_diagram_arrow {J : Type u} [small_category J] (G : finset J) :=
Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y
private abbreviation finite_diagram (J : Type u) [small_category J] :=
Σ (G : finset J), finset (finite_diagram_arrow G)

/--
Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partial_sections {J : Type u} [small_category J] (F : J ⥤ Top.{u})
  {G : finset J} (H : finset (finite_diagram_arrow G)) : set (Π j, F.obj j) :=
{ u | ∀ {f : finite_diagram_arrow G} (hf : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1 }

lemma partial_sections.nonempty [is_cofiltered J] [h : Π (j : J), nonempty (F.obj j)]
  {G : finset J} (H : finset (finite_diagram_arrow G)) :
  (partial_sections F H).nonempty :=
begin
  classical,
  use λ (j : J), if hj : j ∈ G
                 then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some
                 else (h _).some,
  rintros ⟨X, Y, hX, hY, f⟩ hf,
  dsimp only,
  rwa [dif_pos hX, dif_pos hY, ←comp_app, ←F.map_comp,
       @is_cofiltered.inf_to_commutes _ _ _ G H],
end

lemma partial_sections.directed :
  directed superset (λ (G : finite_diagram J), partial_sections F G.2) :=
begin
  classical,
  intros A B,
  let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1 ⊔ B.1) :=
    λ f, ⟨f.1, f.2.1, finset.mem_union_left _ f.2.2.1, finset.mem_union_left _ f.2.2.2.1,
          f.2.2.2.2⟩,
  let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1 ⊔ B.1) :=
    λ f, ⟨f.1, f.2.1, finset.mem_union_right _ f.2.2.1, finset.mem_union_right _ f.2.2.2.1,
          f.2.2.2.2⟩,
  refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, _, _⟩,
  { rintro u hu f hf,
    have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB,
    { apply finset.mem_union_left,
      rw finset.mem_image,
      refine ⟨f, hf, rfl⟩ },
    exact hu this },
  { rintro u hu f hf,
    have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB,
    { apply finset.mem_union_right,
      rw finset.mem_image,
      refine ⟨f, hf, rfl⟩ },
    exact hu this }
end

lemma partial_sections.closed [Π (j : J), t2_space (F.obj j)]
  {G : finset J} (H : finset (finite_diagram_arrow G)) :
  is_closed (partial_sections F H) :=
begin
  have : partial_sections F H =
    ⋂ {f : finite_diagram_arrow G} (hf : f ∈ H), { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 },
  { ext1,
    simp only [set.mem_Inter, set.mem_set_of_eq],
    refl, },
  rw this,
  apply is_closed_bInter,
  intros f hf,
  apply is_closed_eq,
  continuity,
end

/--
Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
--/
lemma nonempty_limit_cone_of_compact_t2_cofiltered_system
  [is_cofiltered J]
  [Π (j : J), nonempty (F.obj j)]
  [Π (j : J), compact_space (F.obj j)]
  [Π (j : J), t2_space (F.obj j)] :
  nonempty (Top.limit_cone.{u} F).X :=
begin
  classical,
  obtain ⟨u, hu⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ G, partial_sections F _)
    (partial_sections.directed F)
    (λ G, partial_sections.nonempty F _)
    (λ G, is_closed.is_compact (partial_sections.closed F _))
    (λ G, partial_sections.closed F _),
  use u,
  intros X Y f,
  let G : finite_diagram J :=
    ⟨{X, Y},
     {⟨X, Y,
      by simp only [true_or, eq_self_iff_true, finset.mem_insert],
      by simp only [eq_self_iff_true, or_true, finset.mem_insert, finset.mem_singleton],
      f⟩}⟩,
  exact hu _ ⟨G, rfl⟩ (finset.mem_singleton_self _),
end

end topological_konig

end Top

section fintype_konig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
lemma nonempty_sections_of_fintype_cofiltered_system.init
  {J : Type u} [small_category J] [is_cofiltered J] (F : J ⥤ Type u)
  [hf : Π (j : J), fintype (F.obj j)] [hne : Π (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  let F' : J ⥤ Top := F ⋙ Top.discrete,
  haveI : Π (j : J), fintype (F'.obj j) := hf,
  haveI : Π (j : J), nonempty (F'.obj j) := hne,
  obtain ⟨⟨u, hu⟩⟩ := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system F',
  exact ⟨u, λ _ _ f, hu f⟩,
end

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_fintype_cofiltered_system
  {J : Type u} [category.{w} J] [is_cofiltered J] (F : J ⥤ Type v)
  [Π (j : J), fintype (F.obj j)] [Π (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type (max w v u) := as_small.{max w v} J,
  let down : J' ⥤ J := as_small.down,
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ ulift_functor.{(max u w) v},
  haveI : ∀ i, nonempty (F'.obj i) := λ i, ⟨⟨classical.arbitrary (F.obj (down.obj i))⟩⟩,
  haveI : ∀ i, fintype (F'.obj i) := λ i, fintype.of_equiv (F.obj (down.obj i)) equiv.ulift.symm,
  -- Step 2: apply the bootstrap theorem
  obtain ⟨u, hu⟩ := nonempty_sections_of_fintype_cofiltered_system.init F',
  -- Step 3: interpret the results
  use λ j, (u ⟨j⟩).down,
  intros j j' f,
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ulift.up f),
  simp only [as_small.down, functor.comp_map, ulift_functor_map, functor.op_map] at h,
  simp_rw [←h],
  refl,
end

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_fintype_inverse_system
  {J : Type u} [preorder J] [is_directed J (≤)] (F : Jᵒᵖ ⥤ Type v)
  [Π (j : Jᵒᵖ), fintype (F.obj j)] [Π (j : Jᵒᵖ), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  casesI is_empty_or_nonempty J,
  { haveI : is_empty Jᵒᵖ := ⟨λ j, is_empty_elim j.unop⟩,  -- TODO: this should be a global instance
    exact ⟨is_empty_elim, is_empty_elim⟩, },
  { exact nonempty_sections_of_fintype_cofiltered_system _, },
end

end fintype_konig
