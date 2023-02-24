/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.open_immersion
import category_theory.limits.opposites
import ring_theory.localization.inv_submonoid

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `algebraic_geometry.is_affine_open.from_Spec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

open Spec (structure_sheaf)

/-- The category of affine schemes -/
@[derive category, nolint has_nonempty_instance]
def AffineScheme := Scheme.Spec.ess_image_subcategory

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class is_affine (X : Scheme) : Prop :=
(affine : is_iso (Γ_Spec.adjunction.unit.app X))

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.iso_Spec (X : Scheme) [is_affine X] :
  X ≅ Scheme.Spec.obj (op $ Scheme.Γ.obj $ op X) :=
as_iso (Γ_Spec.adjunction.unit.app X)

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typclass version. -/
@[simps]
def AffineScheme.mk (X : Scheme) (h : is_affine X) : AffineScheme :=
⟨X, @@mem_ess_image_of_unit_is_iso _ _ _ _ h.1⟩

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
def AffineScheme.of (X : Scheme) [h : is_affine X] : AffineScheme :=
AffineScheme.mk X h

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
def AffineScheme.of_hom {X Y : Scheme} [is_affine X] [is_affine Y] (f : X ⟶ Y) :
  AffineScheme.of X ⟶ AffineScheme.of Y :=
f

lemma mem_Spec_ess_image (X : Scheme) : X ∈ Scheme.Spec.ess_image ↔ is_affine X :=
⟨λ h, ⟨functor.ess_image.unit_is_iso h⟩, λ h, @@mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : is_affine X.obj :=
⟨functor.ess_image.unit_is_iso X.property⟩

instance Spec_is_affine (R : CommRingᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
algebraic_geometry.is_affine_AffineScheme ⟨_, Scheme.Spec.obj_mem_ess_image R⟩

lemma is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] :
  is_affine X :=
by { rw [← mem_Spec_ess_image] at h ⊢, exact functor.ess_image.of_iso (as_iso f).symm h }

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
@[derive [full, faithful, ess_surj]]
def Spec : CommRingᵒᵖ ⥤ AffineScheme := Scheme.Spec.to_ess_image

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[derive [full, faithful], simps]
def forget_to_Scheme : AffineScheme ⥤ Scheme := Scheme.Spec.ess_image_inclusion

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRing := forget_to_Scheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equiv_CommRing : AffineScheme ≌ CommRingᵒᵖ :=
equiv_ess_image_of_reflective.symm

instance Γ_is_equiv : is_equivalence Γ.{u} :=
begin
  haveI : is_equivalence Γ.{u}.right_op.op := is_equivalence.of_equivalence equiv_CommRing.op,
  exact (functor.is_equivalence_trans Γ.{u}.right_op.op (op_op_equivalence _).functor : _),
end

instance : has_colimits AffineScheme.{u} :=
begin
  haveI := adjunction.has_limits_of_equivalence.{u} Γ.{u},
  exactI adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse
end

instance : has_limits AffineScheme.{u} :=
begin
  haveI := adjunction.has_colimits_of_equivalence Γ.{u},
  haveI : has_limits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits,
  exactI adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse
end

noncomputable
instance : preserves_limits Γ.{u}.right_op :=
@@adjunction.is_equivalence_preserves_limits _ _ Γ.right_op
  (is_equivalence.of_equivalence equiv_CommRing)

noncomputable
instance : preserves_limits forget_to_Scheme :=
begin
  apply_with (@@preserves_limits_of_nat_iso _ _
    (iso_whisker_right equiv_CommRing.unit_iso forget_to_Scheme).symm) { instances := ff },
  change preserves_limits (equiv_CommRing.functor ⋙ Scheme.Spec),
  apply_instance,
end

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def is_affine_open {X : Scheme} (U : opens X.carrier) : Prop :=
is_affine (X.restrict U.open_embedding)

/-- The set of affine opens as a subset of `opens X.carrier`. -/
def Scheme.affine_opens (X : Scheme) : set (opens X.carrier) :=
{ U : opens X.carrier | is_affine_open U }

lemma range_is_affine_open_of_open_immersion {X Y : Scheme} [is_affine X] (f : X ⟶ Y)
  [H : is_open_immersion f] : is_affine_open f.opens_range :=
begin
  refine is_affine_of_iso (is_open_immersion.iso_of_range_eq f (Y.of_restrict _) _).inv,
  exact subtype.range_coe.symm,
  apply_instance
end

lemma top_is_affine_open (X : Scheme) [is_affine X] : is_affine_open (⊤ : opens X.carrier) :=
begin
  convert range_is_affine_open_of_open_immersion (𝟙 X),
  ext1,
  exact set.range_id.symm
end

instance Scheme.affine_cover_is_affine (X : Scheme) (i : X.affine_cover.J) :
  is_affine (X.affine_cover.obj i) :=
algebraic_geometry.Spec_is_affine _

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affine_basis_cover.J) :
  is_affine (X.affine_basis_cover.obj i) :=
algebraic_geometry.Spec_is_affine _

lemma is_basis_affine_open (X : Scheme) :
  opens.is_basis X.affine_opens :=
begin
  rw opens.is_basis_iff_nbhd,
  rintros U x (hU : x ∈ (U : set X.carrier)),
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.is_open,
  refine ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩,
  rcases hS with ⟨i, rfl⟩,
  exact range_is_affine_open_of_open_immersion _,
end

/-- The open immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`. -/
def is_affine_open.from_Spec {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  Scheme.Spec.obj (op $ X.presheaf.obj $ op U) ⟶ X :=
begin
  haveI : is_affine (X.restrict U.open_embedding) := hU,
  have : U.open_embedding.is_open_map.functor.obj ⊤ = U,
  { ext1, exact set.image_univ.trans subtype.range_coe },
  exact Scheme.Spec.map (X.presheaf.map (eq_to_hom this.symm).op).op ≫
    (X.restrict U.open_embedding).iso_Spec.inv ≫ X.of_restrict _
end

instance is_affine_open.is_open_immersion_from_Spec {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  is_open_immersion hU.from_Spec :=
by { delta is_affine_open.from_Spec, apply_instance }

lemma is_affine_open.from_Spec_range {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  set.range hU.from_Spec.1.base = (U : set X.carrier) :=
begin
  delta is_affine_open.from_Spec,
  erw [← category.assoc, Scheme.comp_val_base],
  rw [coe_comp, set.range_comp, set.range_iff_surjective.mpr, set.image_univ],
  exact subtype.range_coe,
  rw ← Top.epi_iff_surjective,
  apply_instance
end

lemma is_affine_open.from_Spec_image_top {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  hU.is_open_immersion_from_Spec.base_open.is_open_map.functor.obj ⊤ = U :=
by { ext1, exact set.image_univ.trans hU.from_Spec_range }

lemma is_affine_open.is_compact {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  is_compact (U : set X.carrier) :=
begin
  convert @is_compact.image _ _ _ _ set.univ hU.from_Spec.1.base
    prime_spectrum.compact_space.1 (by continuity),
  convert hU.from_Spec_range.symm,
  exact set.image_univ
end

lemma is_affine_open.image_is_open_immersion {X Y : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U)
  (f : X ⟶ Y) [H : is_open_immersion f] : is_affine_open (f.opens_functor.obj U) :=
begin
  haveI : is_affine _ := hU,
  convert range_is_affine_open_of_open_immersion (X.of_restrict U.open_embedding ≫ f),
  ext1,
  exact set.image_eq_range _ _
end

lemma is_affine_open_iff_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  (U : opens X.carrier) :
  is_affine_open (H.open_functor.obj U) ↔ is_affine_open U :=
begin
  refine ⟨λ hU, @@is_affine_of_iso _ _ hU, λ hU, hU.image_is_open_immersion f⟩,
  refine (is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _).hom,
  { rw [Scheme.comp_val_base, coe_comp, set.range_comp],
    dsimp [opens.inclusion],
    rw [subtype.range_coe, subtype.range_coe],
    refl },
  { apply_instance }
end

instance Scheme.quasi_compact_of_affine (X : Scheme) [is_affine X] : compact_space X.carrier :=
⟨(top_is_affine_open X).is_compact⟩

lemma is_affine_open.from_Spec_base_preimage
  {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    (opens.map hU.from_Spec.val.base).obj U = ⊤ :=
begin
  ext1,
  change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
  rw [← hU.from_Spec_range, ← set.image_univ],
  exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
end

lemma Scheme.Spec_map_presheaf_map_eq_to_hom {X : Scheme} {U V : opens X.carrier} (h : U = V) (W) :
  (Scheme.Spec.map (X.presheaf.map (eq_to_hom h).op).op).val.c.app W =
    eq_to_hom (by { cases h, induction W using opposite.rec, dsimp, simp, refl }) :=
begin
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _,
  { rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]  },
  cases h,
  refine (Scheme.congr_app this _).trans _,
  erw category.id_comp,
  simpa [eq_to_hom_map],
end

lemma is_affine_open.Spec_Γ_identity_hom_app_from_Spec {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  (Spec_Γ_identity.hom.app (X.presheaf.obj $ op U)) ≫ hU.from_Spec.1.c.app (op U) =
    (Scheme.Spec.obj _).presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
begin
  haveI : is_affine _ := hU,
  have e₁ :=
    Spec_Γ_identity.hom.naturality (X.presheaf.map (eq_to_hom U.open_embedding_obj_top).op),
  rw ← is_iso.comp_inv_eq at e₁,
  have e₂ := Γ_Spec.adjunction_unit_app_app_top (X.restrict U.open_embedding),
  erw ← e₂ at e₁,
  simp only [functor.id_map, quiver.hom.unop_op, functor.comp_map, ← functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, category.assoc, functor.right_op_map, inv_eq_to_hom] at e₁,
  delta is_affine_open.from_Spec Scheme.iso_Spec,
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app, ← e₁],
  simp_rw category.assoc,
  erw ← X.presheaf.map_comp_assoc,
  rw ← op_comp,
  have e₃ : U.open_embedding.is_open_map.adjunction.counit.app U ≫
    eq_to_hom U.open_embedding_obj_top.symm =
    U.open_embedding.is_open_map.functor.map (eq_to_hom U.inclusion_map_eq_top) :=
    subsingleton.elim _ _,
  have e₄ : X.presheaf.map _ ≫ _ = _ :=
    (as_iso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding)))
    .inv.1.c.naturality_assoc (eq_to_hom U.inclusion_map_eq_top).op _,
  erw [e₃, e₄, ← Scheme.comp_val_c_app_assoc, iso.inv_hom_id],
  simp only [eq_to_hom_map, eq_to_hom_op, Scheme.Spec_map_presheaf_map_eq_to_hom],
  erw [Scheme.Spec_map_presheaf_map_eq_to_hom, category.id_comp],
  simpa only [eq_to_hom_trans]
end

@[elementwise]
lemma is_affine_open.from_Spec_app_eq {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  hU.from_Spec.1.c.app (op U) = Spec_Γ_identity.inv.app (X.presheaf.obj $ op U) ≫
    (Scheme.Spec.obj _).presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
by rw [← hU.Spec_Γ_identity_hom_app_from_Spec, iso.inv_hom_id_app_assoc]

lemma is_affine_open.basic_open_is_affine {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) : is_affine_open (X.basic_open f) :=
begin
  convert range_is_affine_open_of_open_immersion (Scheme.Spec.map (CommRing.of_hom
    (algebra_map (X.presheaf.obj (op U)) (localization.away f))).op ≫ hU.from_Spec),
  ext1,
  have : hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : set X.carrier)) =
    (X.basic_open f : set X.carrier),
  { rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset, hU.from_Spec_range],
    exact Scheme.basic_open_le _ _ },
  rw [Scheme.hom.opens_range_coe, Scheme.comp_val_base, ← this, coe_comp, set.range_comp],
  congr' 1,
  refine (congr_arg coe $ Scheme.preimage_basic_open hU.from_Spec f).trans _,
  refine eq.trans _ (prime_spectrum.localization_away_comap_range (localization.away f) f).symm,
  congr' 1,
  have : (opens.map hU.from_Spec.val.base).obj U = ⊤,
  { ext1,
    change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
    rw [← hU.from_Spec_range, ← set.image_univ],
    exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj },
  refine eq.trans _ (basic_open_eq_of_affine f),
  have lm : ∀ s, (opens.map hU.from_Spec.val.base).obj U ⊓ s = s := λ s, this.symm ▸ top_inf_eq,
  refine eq.trans _ (lm _),
  refine eq.trans _
    ((Scheme.Spec.obj $ op $ X.presheaf.obj $ op U).basic_open_res _ (eq_to_hom this).op),
  rw ← comp_apply,
  congr' 2,
  rw iso.eq_inv_comp,
  erw hU.Spec_Γ_identity_hom_app_from_Spec,
end

lemma is_affine_open.map_restrict_basic_open {X : Scheme} (r : X.presheaf.obj (op ⊤))
  {U : opens X.carrier} (hU : is_affine_open U) :
  is_affine_open ((opens.map (X.of_restrict (X.basic_open r).open_embedding).1.base).obj U) :=
begin
  apply (is_affine_open_iff_of_is_open_immersion
    (X.of_restrict (X.basic_open r).open_embedding) _).mp,
  delta PresheafedSpace.is_open_immersion.open_functor,
  dsimp,
  erw [opens.functor_obj_map_obj, opens.open_embedding_obj_top, inf_comm,
    ← Scheme.basic_open_res _ _ (hom_of_le le_top).op],
  exact hU.basic_open_is_affine _,
end

lemma Scheme.map_prime_spectrum_basic_open_of_affine (X : Scheme) [is_affine X]
  (f : Scheme.Γ.obj (op X)) :
  (opens.map X.iso_Spec.hom.1.base).obj (prime_spectrum.basic_open f) = X.basic_open f :=
begin
  rw ← basic_open_eq_of_affine,
  transitivity (opens.map X.iso_Spec.hom.1.base).obj ((Scheme.Spec.obj
    (op (Scheme.Γ.obj (op X)))).basic_open ((inv (X.iso_Spec.hom.1.c.app
      (op ((opens.map (inv X.iso_Spec.hom).val.base).obj ⊤)))) ((X.presheaf.map (eq_to_hom _)) f))),
  congr,
  { rw [← is_iso.inv_eq_inv, is_iso.inv_inv, is_iso.iso.inv_inv, nat_iso.app_hom],
    erw ← Γ_Spec.adjunction_unit_app_app_top,
    refl },
  { rw eq_to_hom_map, refl },
  { dsimp, congr },
  { refine (Scheme.preimage_basic_open _ _).trans _,
    rw [is_iso.inv_hom_id_apply, Scheme.basic_open_res_eq] }
end

lemma is_basis_basic_open (X : Scheme) [is_affine X] :
  opens.is_basis (set.range (X.basic_open : X.presheaf.obj (op ⊤) → opens X.carrier)) :=
begin
  delta opens.is_basis,
  convert prime_spectrum.is_basis_basic_opens.inducing
    (Top.homeo_of_iso (Scheme.forget_to_Top.map_iso X.iso_Spec)).inducing using 1,
  ext,
  simp only [set.mem_image, exists_exists_eq_and],
  split,
  { rintro ⟨_, ⟨x, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, _⟩,
    exact congr_arg opens.carrier (X.map_prime_spectrum_basic_open_of_affine x) },
  { rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩,
    refine ⟨_, ⟨x, rfl⟩, _⟩,
    exact congr_arg opens.carrier (X.map_prime_spectrum_basic_open_of_affine x).symm }
end

lemma is_affine_open.exists_basic_open_le {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) {V : opens X.carrier} (x : V) (h : ↑x ∈ U) :
  ∃ f : X.presheaf.obj (op U), X.basic_open f ≤ V ∧ ↑x ∈ X.basic_open f :=
begin
  haveI : is_affine _ := hU,
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ := (is_basis_basic_open (X.restrict U.open_embedding))
    .exists_subset_of_mem_open _ ((opens.map U.inclusion).obj V).is_open,
  swap, exact ⟨x, h⟩,
  have : U.open_embedding.is_open_map.functor.obj ((X.restrict U.open_embedding).basic_open r)
    = X.basic_open (X.presheaf.map (eq_to_hom U.open_embedding_obj_top.symm).op r),
  { refine (Scheme.image_basic_open (X.of_restrict U.open_embedding) r).trans _,
    erw ← Scheme.basic_open_res_eq _ _ (eq_to_hom U.open_embedding_obj_top).op,
    rw [← comp_apply, ← category_theory.functor.map_comp, ← op_comp, eq_to_hom_trans,
      eq_to_hom_refl, op_id, category_theory.functor.map_id, Scheme.hom.inv_app],
    erw PresheafedSpace.is_open_immersion.of_restrict_inv_app,
    congr },
  use X.presheaf.map (eq_to_hom U.open_embedding_obj_top.symm).op r,
  rw ← this,
  exact ⟨set.image_subset_iff.mpr h₂, set.mem_image_of_mem _ h₁⟩,
  exact x.prop,
end

instance {X : Scheme} {U : opens X.carrier} (f : X.presheaf.obj (op U)) :
  algebra (X.presheaf.obj (op U)) (X.presheaf.obj (op $ X.basic_open f)) :=
(X.presheaf.map (hom_of_le $ RingedSpace.basic_open_le _ f : _ ⟶ U).op).to_algebra

lemma is_affine_open.opens_map_from_Spec_basic_open {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) :
  (opens.map hU.from_Spec.val.base).obj (X.basic_open f) =
    RingedSpace.basic_open _ (Spec_Γ_identity.inv.app (X.presheaf.obj $ op U) f) :=
begin
  erw LocallyRingedSpace.preimage_basic_open,
  refine eq.trans _ (RingedSpace.basic_open_res_eq (Scheme.Spec.obj $ op $ X.presheaf.obj (op U))
    .to_LocallyRingedSpace.to_RingedSpace (eq_to_hom hU.from_Spec_base_preimage).op _),
  congr,
  rw ← comp_apply,
  congr,
  erw ← hU.Spec_Γ_identity_hom_app_from_Spec,
  rw iso.inv_hom_id_app_assoc,
end

/-- The canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(Spec_Γ_identity.inv f))`
This is an isomorphism, as witnessed by an `is_iso` instance. -/
def basic_open_sections_to_affine {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) : X.presheaf.obj (op $ X.basic_open f) ⟶
    (Scheme.Spec.obj $ op $ X.presheaf.obj (op U)).presheaf.obj
      (op $ Scheme.basic_open _ $ Spec_Γ_identity.inv.app (X.presheaf.obj (op U)) f) :=
hU.from_Spec.1.c.app (op $ X.basic_open f) ≫ (Scheme.Spec.obj $ op $ X.presheaf.obj (op U))
  .presheaf.map (eq_to_hom $ (hU.opens_map_from_Spec_basic_open f).symm).op

instance {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) : is_iso (basic_open_sections_to_affine hU f) :=
begin
  delta basic_open_sections_to_affine,
  apply_with is_iso.comp_is_iso { instances := ff },
  { apply PresheafedSpace.is_open_immersion.is_iso_of_subset,
    rw hU.from_Spec_range,
    exact RingedSpace.basic_open_le _ _ },
  apply_instance
end

lemma is_localization_basic_open {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) :
  is_localization.away f (X.presheaf.obj (op $ X.basic_open f)) :=
begin
  apply (is_localization.is_localization_iff_of_ring_equiv (submonoid.powers f)
    (as_iso $ basic_open_sections_to_affine hU f ≫ (Scheme.Spec.obj _).presheaf.map
      (eq_to_hom (basic_open_eq_of_affine _).symm).op).CommRing_iso_to_ring_equiv).mpr,
  convert structure_sheaf.is_localization.to_basic_open _ f,
  change _ ≫ (basic_open_sections_to_affine hU f ≫ _) = _,
  delta basic_open_sections_to_affine,
  erw ring_hom.algebra_map_to_algebra,
  simp only [Scheme.comp_val_c_app, category.assoc],
  erw hU.from_Spec.val.c.naturality_assoc,
  rw hU.from_Spec_app_eq,
  dsimp,
  simp only [category.assoc, ← functor.map_comp, ← op_comp],
  apply structure_sheaf.to_open_res,
end

instance {X : Scheme} [is_affine X] (r : X.presheaf.obj (op ⊤)) :
  is_localization.away r (X.presheaf.obj (op $ X.basic_open r)) :=
is_localization_basic_open (top_is_affine_open X) r

lemma is_localization_of_eq_basic_open {X : Scheme} {U V : opens X.carrier} (i : V ⟶ U)
  (hU : is_affine_open U) (r : X.presheaf.obj (op U)) (e : V = X.basic_open r) :
  @@is_localization.away _ r (X.presheaf.obj (op V)) _ (X.presheaf.map i.op).to_algebra :=
by { subst e, convert is_localization_basic_open hU r using 3 }

instance Γ_restrict_algebra
  {X : Scheme} {Y : Top} {f : Y ⟶ X.carrier} (hf : open_embedding f) :
  algebra (Scheme.Γ.obj (op X)) (Scheme.Γ.obj (op $ X.restrict hf)) :=
(Scheme.Γ.map (X.of_restrict hf).op).to_algebra

instance Γ_restrict_is_localization (X : Scheme.{u}) [is_affine X] (r : Scheme.Γ.obj (op X)) :
   is_localization.away r (Scheme.Γ.obj (op $ X.restrict (X.basic_open r).open_embedding)) :=
 is_localization_of_eq_basic_open _ (top_is_affine_open X) r (opens.open_embedding_obj_top _)

lemma basic_open_basic_open_is_basic_open {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) (g : X.presheaf.obj (op $ X.basic_open f)) :
  ∃ f' : X.presheaf.obj (op U), X.basic_open f' = X.basic_open g :=
begin
  haveI := is_localization_basic_open hU f,
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := is_localization.surj' (submonoid.powers f) g,
  use f * x,
  rw [algebra.smul_def, Scheme.basic_open_mul, Scheme.basic_open_mul],
  erw Scheme.basic_open_res,
  refine (inf_eq_left.mpr _).symm,
  convert inf_le_left using 1,
  apply Scheme.basic_open_of_is_unit,
  apply submonoid.left_inv_le_is_unit _ (is_localization.to_inv_submonoid (submonoid.powers f)
    (X.presheaf.obj (op $ X.basic_open f)) _).prop
end

lemma exists_basic_open_le_affine_inter {X : Scheme} {U V : opens X.carrier}
  (hU : is_affine_open U) (hV : is_affine_open V) (x : X.carrier) (hx : x ∈ U ⊓ V) :
  ∃ (f : X.presheaf.obj $ op U) (g : X.presheaf.obj $ op V),
    X.basic_open f = X.basic_open g ∧ x ∈ X.basic_open f :=
begin
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basic_open_le ⟨x, hx.2⟩ hx.1,
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basic_open_le ⟨x, hf₂⟩ hx.2,
  obtain ⟨f', hf'⟩ := basic_open_basic_open_is_basic_open hU f
    (X.presheaf.map (hom_of_le hf₁ : _ ⟶ V).op g),
  replace hf' := (hf'.trans (RingedSpace.basic_open_res _ _ _)).trans (inf_eq_right.mpr hg₁),
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩
end

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable
def is_affine_open.prime_ideal_of {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (x : U) :
  prime_spectrum (X.presheaf.obj $ op U) :=
((Scheme.Spec.map (X.presheaf.map (eq_to_hom $
  show U.open_embedding.is_open_map.functor.obj ⊤ = U, from
    opens.ext (set.image_univ.trans subtype.range_coe)).op).op).1.base
  ((@@Scheme.iso_Spec (X.restrict U.open_embedding) hU).hom.1.base x))

lemma is_affine_open.from_Spec_prime_ideal_of {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (x : U) :
  hU.from_Spec.val.base (hU.prime_ideal_of x) = x.1 :=
begin
  dsimp only [is_affine_open.from_Spec, subtype.coe_mk],
  erw [← Scheme.comp_val_base_apply, ← Scheme.comp_val_base_apply],
  simpa only [← functor.map_comp_assoc, ← functor.map_comp, ← op_comp, eq_to_hom_trans, op_id,
    eq_to_hom_refl, category_theory.functor.map_id, category.id_comp, iso.hom_inv_id_assoc]
end

lemma is_affine_open.is_localization_stalk_aux {X : Scheme} (U : opens X.carrier)
  [is_affine (X.restrict U.open_embedding)] :
  (inv (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).1.c.app
    (op ((opens.map U.inclusion).obj U)) =
      X.presheaf.map (eq_to_hom $ by rw opens.inclusion_map_eq_top :
        U.open_embedding.is_open_map.functor.obj ⊤ ⟶
          (U.open_embedding.is_open_map.functor.obj ((opens.map U.inclusion).obj U))).op ≫
      to_Spec_Γ (X.presheaf.obj $ op (U.open_embedding.is_open_map.functor.obj ⊤)) ≫
      (Scheme.Spec.obj $ op $ X.presheaf.obj $ _).presheaf.map
        (eq_to_hom (by { rw [opens.inclusion_map_eq_top], refl }) : unop _ ⟶ ⊤).op :=
begin
  have e : (opens.map (inv (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).1.base).obj
    ((opens.map U.inclusion).obj U) = ⊤,
  by { rw [opens.inclusion_map_eq_top], refl },
  rw [Scheme.inv_val_c_app, is_iso.comp_inv_eq, Scheme.app_eq _ e,
    Γ_Spec.adjunction_unit_app_app_top],
  simp only [category.assoc, eq_to_hom_op],
  erw ← functor.map_comp_assoc,
  rw [eq_to_hom_trans, eq_to_hom_refl, category_theory.functor.map_id,
    category.id_comp],
  erw Spec_Γ_identity.inv_hom_id_app_assoc,
  simp only [eq_to_hom_map, eq_to_hom_trans],
end

lemma is_affine_open.is_localization_stalk {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (x : U) :
  is_localization.at_prime (X.presheaf.stalk x) (hU.prime_ideal_of x).as_ideal :=
begin
  haveI : is_affine _ := hU,
  haveI : nonempty U := ⟨x⟩,
  rcases x with ⟨x, hx⟩,
  let y := hU.prime_ideal_of ⟨x, hx⟩,
  have : hU.from_Spec.val.base y = x := hU.from_Spec_prime_ideal_of ⟨x, hx⟩,
  change is_localization y.as_ideal.prime_compl _,
  clear_value y,
  subst this,
  apply (is_localization.is_localization_iff_of_ring_equiv _
    (as_iso $ PresheafedSpace.stalk_map hU.from_Spec.1 y).CommRing_iso_to_ring_equiv).mpr,
  convert structure_sheaf.is_localization.to_stalk _ _ using 1,
  delta structure_sheaf.stalk_algebra,
  congr' 1,
  rw ring_hom.algebra_map_to_algebra,
  refine (PresheafedSpace.stalk_map_germ hU.from_Spec.1 _ ⟨_, _⟩).trans _,
  delta is_affine_open.from_Spec Scheme.iso_Spec structure_sheaf.to_stalk,
  simp only [Scheme.comp_val_c_app, category.assoc],
  dsimp only [functor.op, as_iso_inv, unop_op],
  erw is_affine_open.is_localization_stalk_aux,
  simp only [category.assoc],
  conv_lhs { rw ← category.assoc },
  erw [← X.presheaf.map_comp, Spec_Γ_naturality_assoc],
  congr' 1,
  simp only [← category.assoc],
  transitivity _ ≫ (structure_sheaf (X.presheaf.obj $ op U)).presheaf.germ ⟨_, _⟩,
  { refl },
  convert ((structure_sheaf (X.presheaf.obj $ op U)).presheaf.germ_res (hom_of_le le_top) ⟨_, _⟩)
    using 2,
  rw category.assoc,
  erw nat_trans.naturality,
  rw [← LocallyRingedSpace.Γ_map_op, ← LocallyRingedSpace.Γ.map_comp_assoc, ← op_comp],
  erw ← Scheme.Spec.map_comp,
  rw [← op_comp, ← X.presheaf.map_comp],
  transitivity LocallyRingedSpace.Γ.map (quiver.hom.op $ Scheme.Spec.map
    (X.presheaf.map (𝟙 (op U))).op) ≫ _,
  { congr },
  simp only [category_theory.functor.map_id, op_id],
  erw category_theory.functor.map_id,
  rw category.id_comp,
  refl
end

/-- The basic open set of a section `f` on an an affine open as an `X.affine_opens`. -/
@[simps]
def Scheme.affine_basic_open (X : Scheme) {U : X.affine_opens}
  (f : X.presheaf.obj $ op U) : X.affine_opens :=
⟨X.basic_open f, U.prop.basic_open_is_affine f⟩

@[simp]
lemma is_affine_open.basic_open_from_Spec_app {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) :
  @Scheme.basic_open (Scheme.Spec.obj $ op (X.presheaf.obj $ op U))
    ((opens.map hU.from_Spec.1.base).obj U)
    (hU.from_Spec.1.c.app (op U) f) = prime_spectrum.basic_open f :=
begin
  rw [← Scheme.basic_open_res_eq _ _ (eq_to_hom hU.from_Spec_base_preimage.symm).op,
    basic_open_eq_of_affine', is_affine_open.from_Spec_app_eq],
  congr,
  rw [← comp_apply, ← comp_apply, category.assoc, ← functor.map_comp_assoc,
    eq_to_hom_op, eq_to_hom_op, eq_to_hom_trans, eq_to_hom_refl, category_theory.functor.map_id,
    category.id_comp, ← iso.app_inv, iso.inv_hom_id],
  refl
end

lemma is_affine_open.from_Spec_map_basic_open {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) :
  (opens.map hU.from_Spec.val.base).obj (X.basic_open f) = prime_spectrum.basic_open f :=
by simp

lemma is_affine_open.basic_open_union_eq_self_iff {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (s : set (X.presheaf.obj $ op U)) :
    (⨆ (f : s), X.basic_open (f : X.presheaf.obj $ op U)) = U ↔ ideal.span s = ⊤ :=
begin
  transitivity (⋃ (i : s), (prime_spectrum.basic_open i.1).1) = set.univ,
  transitivity hU.from_Spec.1.base ⁻¹' (⨆ (f : s), X.basic_open (f : X.presheaf.obj $ op U)).1 =
    hU.from_Spec.1.base ⁻¹' U.1,
  { refine ⟨λ h, by rw h, _⟩,
    intro h,
    apply_fun set.image hU.from_Spec.1.base at h,
    rw [set.image_preimage_eq_inter_range, set.image_preimage_eq_inter_range,
      hU.from_Spec_range] at h,
    simp only [set.inter_self, opens.carrier_eq_coe, set.inter_eq_right_iff_subset]
      at h,
    ext1,
    refine set.subset.antisymm _ h,
    simp only [set.Union_subset_iff, set_coe.forall, opens.coe_supr],
    intros x hx,
    exact X.basic_open_le x },
  { simp only [opens.supr_def, subtype.coe_mk, set.preimage_Union, subtype.val_eq_coe],
    congr' 3,
    { ext1 x,
      exact congr_arg opens.carrier (hU.from_Spec_map_basic_open _) },
    { exact congr_arg opens.carrier hU.from_Spec_base_preimage } },
  { simp only [opens.carrier_eq_coe, prime_spectrum.basic_open_eq_zero_locus_compl],
    rw [← set.compl_Inter, set.compl_univ_iff, ← prime_spectrum.zero_locus_Union,
      ← prime_spectrum.zero_locus_empty_iff_eq_top, prime_spectrum.zero_locus_span],
    simp only [set.Union_singleton_eq_range, subtype.range_val_subtype, set.set_of_mem_eq] }
end

lemma is_affine_open.self_le_basic_open_union_iff {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (s : set (X.presheaf.obj $ op U)) :
    U ≤ (⨆ (f : s), X.basic_open (f : X.presheaf.obj $ op U)) ↔ ideal.span s = ⊤ :=
begin
  rw [← hU.basic_open_union_eq_self_iff, @comm _ eq],
  refine ⟨λ h, le_antisymm h _, le_of_eq⟩,
  simp only [supr_le_iff, set_coe.forall],
  intros x hx,
  exact X.basic_open_le x
end

/--
Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea]. -/
@[elab_as_eliminator]
lemma of_affine_open_cover {X : Scheme} (V : X.affine_opens) (S : set X.affine_opens)
  {P : X.affine_opens → Prop}
  (hP₁ : ∀ (U : X.affine_opens) (f : X.presheaf.obj $ op U.1), P U →
    P (X.affine_basic_open f))
  (hP₂ : ∀ (U : X.affine_opens) (s : finset (X.presheaf.obj $ op U))
    (hs : ideal.span (s : set (X.presheaf.obj $ op U)) = ⊤),
    (∀ (f : s), P (X.affine_basic_open f.1)) → P U)
  (hS : (⋃ (i : S), i : set X.carrier) = set.univ)
  (hS' : ∀ (U : S), P U) : P V :=
begin
  classical,
  have : ∀ (x : V), ∃ (f : X.presheaf.obj $ op V.1),
    ↑x ∈ (X.basic_open f) ∧ P (X.affine_basic_open f),
  { intro x,
    have : ↑x ∈ (set.univ : set X.carrier) := trivial,
    rw ← hS at this,
    obtain ⟨W, hW⟩ := set.mem_Union.mp this,
    obtain ⟨f, g, e, hf⟩ := exists_basic_open_le_affine_inter V.prop W.1.prop x ⟨x.prop, hW⟩,
    refine ⟨f, hf, _⟩,
    convert hP₁ _ g (hS' W) using 1,
    ext1,
    exact e },
  choose f hf₁ hf₂ using this,
  suffices : ideal.span (set.range f) = ⊤,
  { obtain ⟨t, ht₁, ht₂⟩ := (ideal.span_eq_top_iff_finite _).mp this,
    apply hP₂ V t ht₂,
    rintro ⟨i, hi⟩,
    obtain ⟨x, rfl⟩ := ht₁ hi,
    exact hf₂ x },
  rw ← V.prop.self_le_basic_open_union_iff,
  intros x hx,
  rw [supr_range', opens.mem_supr],
  exact ⟨_, hf₁ ⟨x, hx⟩⟩
end

end algebraic_geometry
