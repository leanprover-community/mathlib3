/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.open_immersion
import category_theory.limits.opposites

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

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

/-- The category of affine schemes -/
def AffineScheme := Scheme.Spec.ess_image

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class is_affine (X : Scheme) : Prop :=
(affine : is_iso (Γ_Spec.adjunction.unit.app X))

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.iso_Spec (X : Scheme) [is_affine X] :
  X ≅ Scheme.Spec.obj (op $ Scheme.Γ.obj $ op X) :=
as_iso (Γ_Spec.adjunction.unit.app X)

lemma mem_AffineScheme (X : Scheme) : X ∈ AffineScheme ↔ is_affine X :=
⟨λ h, ⟨functor.ess_image.unit_is_iso h⟩, λ h, @@mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : is_affine (X : Scheme.{u}) :=
(mem_AffineScheme _).mp X.prop

instance Spec_is_affine (R : CommRingᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
(mem_AffineScheme _).mp (Scheme.Spec.obj_mem_ess_image R)

lemma is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] :
  is_affine X :=
by { rw [← mem_AffineScheme] at h ⊢, exact functor.ess_image.of_iso (as_iso f).symm h }

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
@[derive [full, faithful, ess_surj], simps]
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
  haveI : has_colimits AffineScheme.{u} ᵒᵖᵒᵖ := has_colimits_op_of_has_limits,
  exactI adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse
end

instance : has_limits AffineScheme.{u} :=
begin
  haveI := adjunction.has_colimits_of_equivalence Γ.{u},
  haveI : has_limits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits,
  exactI adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse
end

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def is_affine_open {X : Scheme} (U : opens X.carrier) : Prop :=
is_affine (X.restrict U.open_embedding)

lemma range_is_affine_open_of_open_immersion {X Y : Scheme} [is_affine X] (f : X ⟶ Y)
  [H : is_open_immersion f] : is_affine_open ⟨set.range f.1.base, H.base_open.open_range⟩ :=
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

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affine_basis_cover.J) :
  is_affine (X.affine_basis_cover.obj i) :=
algebraic_geometry.Spec_is_affine _

lemma is_basis_affine_open (X : Scheme) :
  opens.is_basis { U : opens X.carrier | is_affine_open U } :=
begin
  rw opens.is_basis_iff_nbhd,
  rintros U x (hU : x ∈ (U : set X.carrier)),
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop,
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
  erw [← category.assoc, LocallyRingedSpace.comp_val, PresheafedSpace.comp_base],
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
  convert @is_compact.image _ _ _ set.univ _ hU.from_Spec.1.base
    prime_spectrum.compact_space.1 (by continuity),
  convert hU.from_Spec_range.symm,
  exact set.image_univ
end

abbreviation Scheme.basic_open (X : Scheme) {U : opens X.carrier} (f : X.presheaf.obj (op U)) :
  opens X.carrier := X.to_LocallyRingedSpace.to_RingedSpace.basic_open f

lemma basic_open_eq_of_affine {R : CommRing} (f : R) :
  RingedSpace.basic_open (Spec.to_SheafedSpace.obj (op R)) ((Spec_Γ_identity.app R).inv f) =
    prime_spectrum.basic_open f :=
begin
  ext,
  change ↑(⟨x, trivial⟩ : (⊤ : opens _)) ∈
    RingedSpace.basic_open (Spec.to_SheafedSpace.obj (op R)) _ ↔ _,
  rw RingedSpace.mem_basic_open,
  suffices : is_unit (structure_sheaf.to_stalk R x f) ↔ f ∉ prime_spectrum.as_ideal x,
  { exact this },
  erw [← is_unit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk],
  exact (is_localization.at_prime.is_unit_to_map_iff
    (localization.at_prime (prime_spectrum.as_ideal x)) (prime_spectrum.as_ideal x) f : _)
end

lemma basic_open_eq_of_affine' {R : CommRing}
  (f : (Spec.to_SheafedSpace.obj (op R)).presheaf.obj (op ⊤)) :
  RingedSpace.basic_open (Spec.to_SheafedSpace.obj (op R)) f =
    prime_spectrum.basic_open ((Spec_Γ_identity.app R).hom f) :=
begin
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).hom f),
  exact (coe_hom_inv_id _ _).symm
end

lemma is_affine_open.from_Spec_base_preimage
  {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    (opens.map hU.from_Spec.val.base).obj U = ⊤ :=
begin
  ext1,
  change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
  rw [← hU.from_Spec_range, ← set.image_univ],
  exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
end
.

lemma Γ_Spec.adjunction.unit.app_app_top (X : Scheme) :
  @eq ((Scheme.Spec.obj (op $ X.presheaf.obj (op ⊤))).presheaf.obj (op ⊤) ⟶
    ((Γ_Spec.adjunction.unit.app X).1.base _* X.presheaf).obj (op ⊤))
  ((Γ_Spec.adjunction.unit.app X).val.c.app (op ⊤))
    (Spec_Γ_identity.hom.app (X.presheaf.obj (op ⊤))) :=
begin
  have := congr_app Γ_Spec.adjunction.left_triangle X,
  dsimp at this,
  rw ← is_iso.eq_comp_inv at this,
  simp only [Γ_Spec.LocallyRingedSpace_adjunction_counit, nat_trans.op_app, category.id_comp,
    Γ_Spec.adjunction_counit_app] at this,
  rw [← op_inv, nat_iso.inv_inv_app, quiver.hom.op_inj.eq_iff] at this,
  exact this
end
.
@[reassoc, simp]
lemma Scheme.comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ := rfl

lemma Scheme.congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
  f.val.c.app U = g.val.c.app U ≫ X.presheaf.map (eq_to_hom (by subst e)) :=
by { subst e, dsimp, simp, }

lemma _root_.topological_space.opens.open_embedding_obj_top {X : Top} (U : opens X) :
  U.open_embedding.is_open_map.functor.obj ⊤ = U :=
by { ext1, exact set.image_univ.trans subtype.range_coe }

lemma _root_.topological_space.opens.inclusion_map_eq_top {X : Top} (U : opens X) :
  (opens.map U.inclusion).obj U = ⊤ :=
by { ext1, exact subtype.coe_preimage_self _ }

lemma Scheme.Spec_map_presheaf_map_eq_to_hom {X : Scheme} {U V : opens X.carrier} (h : U = V) (W) :
  (Scheme.Spec.map (X.presheaf.map (eq_to_hom h).op).op).val.c.app W =
    eq_to_hom (by { cases h, dsimp, induction W using opposite.rec, congr, ext1, simpa }) :=
begin
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _,
  { rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]  },
  cases h,
  refine (Scheme.congr_app this _).trans _,
  erw category.id_comp,
  simpa
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
  have e₂ := Γ_Spec.adjunction.unit.app_app_top (X.restrict U.open_embedding),
  erw ← e₂ at e₁,
  simp only [functor.id_map, quiver.hom.unop_op, functor.comp_map, ← functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, category.assoc, functor.right_op_map, inv_eq_to_hom] at e₁,
  delta is_affine_open.from_Spec Scheme.iso_Spec,
  erw [LocallyRingedSpace.comp_val_c_app, LocallyRingedSpace.comp_val_c_app],
  rw ← e₁,
  simp_rw category.assoc,
  erw ← X.presheaf.map_comp_assoc,
  rw ← op_comp,
  have : U.open_embedding.is_open_map.adjunction.counit.app U ≫ eq_to_hom U.open_embedding_obj_top
    .symm = U.open_embedding.is_open_map.functor.map (eq_to_hom U.inclusion_map_eq_top) :=
    subsingleton.elim _ _,
  erw this,
  have : X.presheaf.map _ ≫ _ = _ :=
    (as_iso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding)))
    .inv.1.c.naturality_assoc (eq_to_hom U.inclusion_map_eq_top).op _,
  erw this,
  erw ← Scheme.comp_val_c_app_assoc,
  erw iso.inv_hom_id,
  simp only [eq_to_hom_map, eq_to_hom_op, Scheme.Spec_map_presheaf_map_eq_to_hom],
  erw [Scheme.Spec_map_presheaf_map_eq_to_hom, category.id_comp],
  simpa only [eq_to_hom_trans]
end

lemma is_affine_open.basic_open_is_affine {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) : is_affine_open (X.basic_open f) :=
begin
  convert range_is_affine_open_of_open_immersion (Scheme.Spec.map (CommRing.of_hom
    (algebra_map (X.presheaf.obj (op U)) (localization.away f))).op ≫ hU.from_Spec),
  ext1,
  rw subtype.coe_mk,
  have : hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : set X.carrier)) =
    (X.basic_open f : set X.carrier),
  { rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset, hU.from_Spec_range],
    exact RingedSpace.basic_open_subset _ _ },
  erw [LocallyRingedSpace.comp_val, PresheafedSpace.comp_base],
  rw [← this, coe_comp, set.range_comp],
  congr' 1,
  refine (congr_arg coe $ LocallyRingedSpace.preimage_basic_open hU.from_Spec f).trans _,
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
  refine eq.trans _ ((Scheme.Spec.obj $ op $ X.presheaf.obj $ op U)
    .to_LocallyRingedSpace.to_RingedSpace.basic_open_res (eq_to_hom this).op _),
  rw ← comp_apply,
  congr' 2,
  rw iso.eq_inv_comp,
  erw hU.Spec_Γ_identity_hom_app_from_Spec,
  congr
end

instance Scheme.quasi_compact_of_affine (X : Scheme) [is_affine X] : compact_space X.carrier :=
⟨(top_is_affine_open X).is_compact⟩

end algebraic_geometry
