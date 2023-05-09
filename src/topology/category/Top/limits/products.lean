/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import topology.category.Top.epi_mono
import topology.category.Top.limits.basic

/-!
# Products and coproducts in the category of topological spaces

-/

open topological_space
open category_theory
open category_theory.limits

universes u v w

noncomputable theory

namespace Top

variables {J : Type v} [small_category J]

/-- The projection from the product as a bundled continous map. -/
abbreviation pi_π {ι : Type v} (α : ι → Top.{max v u}) (i : ι) : Top.of (Π i, α i) ⟶ α i :=
⟨λ f, f i, continuous_apply i⟩

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps X π_app]
def pi_fan {ι : Type v} (α : ι → Top.{max v u}) : fan α :=
fan.mk (Top.of (Π i, α i)) (pi_π α)

/-- The constructed fan is indeed a limit -/
def pi_fan_is_limit {ι : Type v} (α : ι → Top.{max v u}) : is_limit (pi_fan α) :=
{ lift := λ S, { to_fun := λ s i, S.π.app ⟨i⟩ s },
  uniq' := by { intros S m h, ext x i, simp [← h ⟨i⟩] },
  fac' := λ s j, by { cases j, tidy, }, }

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
{ desc := λ S, { to_fun := λ s, S.ι.app ⟨s.1⟩ s.2,
    continuous_to_fun := continuous_sigma $ λ i, map_continuous (S.ι.app ⟨i⟩) },
  uniq' := by { intros S m h,  ext ⟨i, x⟩, simp [← h ⟨i⟩] },
  fac' := λ s j, by { cases j, tidy, }, }

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
    { specialize h ⟨walking_pair.left⟩,
      apply_fun (λ e, (e x)) at h,
      exact h },
     { specialize h ⟨walking_pair.right⟩,
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
    simp only [set.mem_preimage, set.mem_range, set.mem_inter_iff, ←comp_apply],
    simp only [limits.prod.map_fst, limits.prod.map_snd,
      exists_apply_eq_apply, comp_apply, and_self] },
  { rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩,
    use (prod_iso_prod W X).inv (x₁, x₂),
    apply concrete.limit_ext,
    rintro ⟨⟨⟩⟩,
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


/-- The binary coproduct cofan in `Top`. -/
protected
def binary_cofan (X Y : Top.{u}) : binary_cofan X Y :=
binary_cofan.mk (⟨sum.inl⟩ : X ⟶ Top.of (X ⊕ Y)) ⟨sum.inr⟩

/-- The constructed binary coproduct cofan in `Top` is the coproduct. -/
def binary_cofan_is_colimit (X Y : Top.{u}) : is_colimit (Top.binary_cofan X Y) :=
begin
  refine limits.binary_cofan.is_colimit_mk (λ s, ⟨sum.elim s.inl s.inr⟩) _ _ _,
  { intro s, ext, refl },
  { intro s, ext, refl },
  { intros s m h₁ h₂, ext (x|x),
    exacts [(concrete_category.congr_hom h₁ x : _), (concrete_category.congr_hom h₂ x : _)] },
end

lemma binary_cofan_is_colimit_iff {X Y : Top} (c : binary_cofan X Y) :
  nonempty (is_colimit c) ↔
    open_embedding c.inl ∧ open_embedding c.inr ∧ is_compl (set.range c.inl) (set.range c.inr) :=
begin
  classical,
  split,
  { rintro ⟨h⟩,
    rw [← show _ = c.inl, from h.comp_cocone_point_unique_up_to_iso_inv
      (binary_cofan_is_colimit X Y) ⟨walking_pair.left⟩,
      ← show _ = c.inr, from h.comp_cocone_point_unique_up_to_iso_inv
      (binary_cofan_is_colimit X Y) ⟨walking_pair.right⟩],
    dsimp,
    refine
    ⟨(homeo_of_iso $ h.cocone_point_unique_up_to_iso (binary_cofan_is_colimit X Y)).symm
      .open_embedding.comp open_embedding_inl, (homeo_of_iso $ h.cocone_point_unique_up_to_iso
        (binary_cofan_is_colimit X Y)).symm.open_embedding.comp open_embedding_inr, _⟩,
    erw [set.range_comp, ← eq_compl_iff_is_compl, set.range_comp _ sum.inr, ← set.image_compl_eq
      (homeo_of_iso $ h.cocone_point_unique_up_to_iso (binary_cofan_is_colimit X Y))
      .symm.bijective],
    congr' 1,
    exact set.compl_range_inr.symm },
  { rintros ⟨h₁, h₂, h₃⟩,
    have : ∀ x, x ∈ set.range c.inl ∨ x ∈ set.range c.inr,
    { rw [eq_compl_iff_is_compl.mpr h₃.symm], exact λ _, or_not },
    refine ⟨binary_cofan.is_colimit.mk _ _ _ _ _⟩,
    { intros T f g,
      refine continuous_map.mk _ _,
      { exact λ x, if h : x ∈ set.range c.inl
        then f ((equiv.of_injective _ h₁.inj).symm ⟨x, h⟩)
        else g ((equiv.of_injective _ h₂.inj).symm ⟨x, (this x).resolve_left h⟩) },
      rw continuous_iff_continuous_at,
      intro x,
      by_cases x ∈ set.range c.inl,
      { revert h x,
      apply (is_open.continuous_on_iff _).mp,
      { rw continuous_on_iff_continuous_restrict,
        convert_to continuous (f ∘ (homeomorph.of_embedding _ h₁.to_embedding).symm),
        { ext ⟨x, hx⟩, exact dif_pos hx },
        continuity },
      { exact h₁.open_range } },
    { revert h x,
      apply (is_open.continuous_on_iff _).mp,
      { rw continuous_on_iff_continuous_restrict,
        have : ∀ a, a ∉ set.range c.inl → a ∈ set.range c.inr,
        { rintros a (h : a ∈ (set.range c.inl)ᶜ), rwa eq_compl_iff_is_compl.mpr h₃.symm },
        convert_to continuous
          (g ∘ (homeomorph.of_embedding _ h₂.to_embedding).symm ∘ subtype.map _ this),
        { ext ⟨x, hx⟩, exact dif_neg hx },
        continuity,
        rw embedding_subtype_coe.to_inducing.continuous_iff,
        exact continuous_subtype_coe },
      { change is_open (set.range c.inl)ᶜ, rw ← eq_compl_iff_is_compl.mpr h₃.symm,
        exact h₂.open_range } } },
    { intros T f g, ext x, refine (dif_pos _).trans _, { exact ⟨x, rfl⟩ },
        { rw equiv.of_injective_symm_apply } },
    { intros T f g, ext x, refine (dif_neg _).trans _,
      { rintro ⟨y, e⟩, have : c.inr x ∈ set.range c.inl ⊓ set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩,
        rwa disjoint_iff.mp h₃.1 at this },
      { exact congr_arg g (equiv.of_injective_symm_apply _ _) } },
    { rintro T _ _ m rfl rfl, ext x, change m x = dite _ _ _,
      split_ifs; exact congr_arg _ (equiv.apply_of_injective_symm _ ⟨_, _⟩).symm } }
end

--TODO: Add analogous constructions for `pushout`.

end Top
