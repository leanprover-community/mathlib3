/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.affine
import ring_theory.local_properties

/-!
# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that comes from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `affine_and @P`: the preimage of an affine open `U = Spec A` is affine (`= Spec B`) and `A ⟶ B`
  satisfies `P`.
- `target_affine_locally (source_affine_locally @P)`: For each pair of affine open
  `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on source (`ring_hom.respects_iso P`)


-/

universe u

open category_theory opposite topological_space category_theory.limits

namespace algebraic_geometry

variable (P : ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S), Prop)

def CommRing.iso_of (R : CommRing) : R ≅ CommRing.of R :=
{ hom := ring_hom.id R,
  inv := ring_hom.id R }

noncomputable
abbreviation Scheme.restrict_map_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] (U : opens Y.carrier) :
  X.restrict ((opens.map f.1.base).obj U).open_embedding ≅ Y.restrict U.open_embedding :=
is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _)
begin
  dsimp [opens.inclusion],
  rw [coe_comp, set.range_comp],
  dsimp,
  rw [subtype.range_coe, subtype.range_coe],
  refine @set.image_preimage_eq _ _ f.1.base U.1 _,
  rw ← Top.epi_iff_surjective,
  apply_instance
end

noncomputable
def is_affine_open.restrict_basic_open_iso_Spec_basic_open {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (r : X.presheaf.obj (op U)) :
  X.restrict (X.basic_open r).open_embedding ≅
    Scheme.Spec.obj (op (X.presheaf.obj (op (X.basic_open r)))) :=
begin
  haveI := is_localization_basic_open hU r,
  refine hU.restrict_basic_open_iso_Spec r ≪≫ Scheme.Spec.map_iso _,
  refine (CommRing.iso_of _ ≪≫ (is_localization.alg_equiv (submonoid.powers r)
    (X.presheaf.obj (op (X.basic_open r))) (localization.away r)).to_ring_equiv.to_CommRing_iso).op,
end

lemma morphism_restrict_base_coe {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (x) :
  @coe U Y.carrier _ ((f ∣_ U).1.base x) = f.1.base x.1 :=
congr_arg (λ f, PresheafedSpace.hom.base (subtype.val f) x) (morphism_restrict_ι f U)

lemma image_morphism_restrict_preimage {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier)
  (V : opens U) :
  ((opens.map f.val.base).obj U).open_embedding.is_open_map.functor.obj
    ((opens.map (f ∣_ U).val.base).obj V) =
    (opens.map f.val.base).obj (U.open_embedding.is_open_map.functor.obj V) :=
begin
  ext1,
  ext x,
  split,
  { rintro ⟨⟨x, hx⟩, (hx' : (f ∣_ U).1.base _ ∈ _), rfl⟩,
    refine ⟨⟨_, hx⟩, _, rfl⟩,
    convert hx',
    ext1,
    exact (morphism_restrict_base_coe f U ⟨x, hx⟩).symm },
  { rintro ⟨⟨x, hx⟩, hx', (rfl : x = _)⟩,
    refine ⟨⟨_, hx⟩, (_: ((f ∣_ U).1.base ⟨x, hx⟩) ∈ V.1), rfl⟩,
    convert hx',
    ext1,
    exact morphism_restrict_base_coe f U ⟨x, hx⟩ }
end

@[simp]
lemma _root_.topological_space.opens.adjunction_counit_app_image {X : Top} (U : opens X) (V : opens U) :
  U.open_embedding.is_open_map.adjunction.counit.app (U.open_embedding.is_open_map.functor.obj V) =
  U.open_embedding.is_open_map.functor.map
    (eq_to_hom (by { ext1, exact set.preimage_image_eq _ subtype.coe_injective })) :=
by ext

lemma morphism_restrict_c_app {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (V : opens U) :
   (f ∣_ U).1.c.app (op V) = f.1.c.app (op (U.open_embedding.is_open_map.functor.obj V)) ≫
    X.presheaf.map (eq_to_hom (image_morphism_restrict_preimage f U V)).op :=
begin
  have := Scheme.congr_app (morphism_restrict_ι f U)
    (op (U.open_embedding.is_open_map.functor.obj V)),
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this,
  have e : (opens.map U.inclusion).obj (U.open_embedding.is_open_map.functor.obj V) = V,
  { ext1, exact set.preimage_image_eq _ subtype.coe_injective },
  have : _ ≫ X.presheaf.map _ = _ :=
    (((f ∣_ U).1.c.naturality (eq_to_hom e).op).symm.trans _).trans this,
  swap, { change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _, congr,  },
  rw [← is_iso.eq_comp_inv, ← functor.map_inv, category.assoc] at this,
  rw this,
  congr' 1,
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp],
  congr' 1,
end

lemma Γ_map_morphism_restrict {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
  Scheme.Γ.map (f ∣_ U).op = Y.presheaf.map (eq_to_hom $ U.open_embedding_obj_top.symm).op ≫
    f.1.c.app (op U) ≫
      X.presheaf.map (eq_to_hom (((opens.map f.val.base).obj U).open_embedding_obj_top)).op :=
begin
  rw [Scheme.Γ_map_op, morphism_restrict_c_app f U ⊤, f.val.c.naturality_assoc],
  erw ← X.presheaf.map_comp,
  congr,
end

instance {X : Scheme} [is_affine X] (f : X.presheaf.obj $ op ⊤) :
  is_localization.away f (X.presheaf.obj $ op $ X.basic_open f) :=
is_localization_basic_open (top_is_affine_open X) f

lemma is_localization_away_of_is_unit_bijective {R : Type*} (S : Type*) [comm_ring R] [comm_ring S]
  [algebra R S] {r : R} (hr : is_unit r) (H : function.bijective (algebra_map R S)) :
  is_localization.away r S :=
{ map_units := by { rintros ⟨_, n, rfl⟩, exact (algebra_map R S).is_unit_map (hr.pow _) },
  surj := λ z, by { obtain ⟨z', rfl⟩ := H.2 z, exact ⟨⟨z', 1⟩, by simp⟩ },
  eq_iff_exists := λ x y, begin
    erw H.1.eq_iff,
    split,
    { rintro rfl, exact ⟨1, rfl⟩ },
    { rintro ⟨⟨_, n, rfl⟩, e⟩, exact (hr.pow _).mul_left_inj.mp e }
  end }

instance Γ_restrict_algebra (X : Scheme.{u}) {U : Top.{u}} {f : U ⟶ X.carrier}
  (hf : open_embedding f) :
  algebra ( X.presheaf.obj (op ⊤)) (Scheme.Γ.obj (op $ X.restrict hf)) :=
(Scheme.Γ.map (X.of_restrict hf).op).to_algebra

instance Γ_restrict_is_localization (X : Scheme.{u}) [is_affine X] (r : X.presheaf.obj (op ⊤)) :
  is_localization.away r (Scheme.Γ.obj (op $ X.restrict (X.basic_open r).open_embedding)) :=
begin
  convert (is_localization.is_localization_iff_of_ring_equiv (submonoid.powers r) _).mp
    (is_localization_basic_open (top_is_affine_open X : _) r) using 1,
  swap,
  { refine (X.presheaf.map_iso (eq_to_iso _)).CommRing_iso_to_ring_equiv,
    { dsimp only [functor.op, unop_op],
    congr' 1,
    ext1,
    exact (subtype.coe_image_univ _).symm } },
  { apply algebra.algebra_ext,
    intro _, congr' 1,
    refine (ring_hom.algebra_map_to_algebra _).trans
      (eq.trans _ (ring_hom.algebra_map_to_algebra _).symm),
    rw [ring_hom.algebra_map_to_algebra, iso.CommRing_iso_to_ring_equiv_to_ring_hom,
      functor.map_iso_hom, Scheme.Γ_map_op],
    change X.presheaf.map _ = _ ≫ _,
    rw ← X.presheaf.map_comp,
    congr }
end

lemma is_open_immersion.is_affine_open_iff {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  (U : opens X.carrier) :
  is_affine_open U ↔ is_affine_open (H.open_functor.obj U) :=
begin
  refine ⟨λ hU, hU.image_is_open_immersion f, λ hU, @@is_affine_of_iso _ _ hU⟩,
  refine (is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _).hom,
  { rw [Scheme.comp_val_base, coe_comp, set.range_comp],
    dsimp [opens.inclusion],
    rw [subtype.range_coe, subtype.range_coe],
    refl },
  { apply_instance }
end

instance {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
  affine (X.of_restrict (X.basic_open r).open_embedding) :=
begin
  constructor,
  intros U hU,
  fapply (is_open_immersion.is_affine_open_iff (X.of_restrict _) _).mpr,
  swap,
  { apply_instance },
  convert hU.basic_open_is_affine (X.presheaf.map (hom_of_le le_top).op r),
  ext1,
  rw X.basic_open_res,
  dsimp [opens.map, opens.inclusion],
  rw [set.image_preimage_eq_inter_range, subtype.range_coe],
  refl
end

@[simps]
def affine_preimage {X Y : Scheme} (f : X ⟶ Y) [affine f] (U : Y.affine_opens) :
  X.affine_opens :=
⟨(opens.map f.1.base).obj (U : opens Y.carrier), affine.is_affine_preimage _ U.prop⟩

universes v₁ v₂

noncomputable
def Scheme.open_cover.inter {X : Scheme.{u}} (𝒰₁ : Scheme.open_cover.{v₁} X)
  (𝒰₂ : Scheme.open_cover.{v₂} X) : X.open_cover :=
{ J := 𝒰₁.J × 𝒰₂.J,
  obj := λ ij, pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2),
  map := λ ij, pullback.fst ≫ 𝒰₁.map ij.1,
  f := λ x, ⟨𝒰₁.f x, 𝒰₂.f x⟩,
  covers := λ x, by { rw is_open_immersion.range_pullback_one, exact ⟨𝒰₁.covers x, 𝒰₂.covers x⟩ } }


def Scheme.AffineScheme (X : Scheme) [is_affine X] : AffineScheme :=
⟨X, (mem_AffineScheme X).mpr infer_instance⟩

def AffineScheme.of_hom {X Y : Scheme} (f : X ⟶ Y) [is_affine X] [is_affine Y] :
  X.AffineScheme ⟶ Y.AffineScheme := f

noncomputable
instance : preserves_limits AffineScheme.Γ.{u}.right_op :=
@@adjunction.is_equivalence_preserves_limits _ _ AffineScheme.Γ.right_op
  (is_equivalence.of_equivalence AffineScheme.equiv_CommRing)

noncomputable
instance : preserves_limits AffineScheme.forget_to_Scheme :=
begin
  apply_with (@@preserves_limits_of_nat_iso _ _
    (iso_whisker_right AffineScheme.equiv_CommRing.unit_iso AffineScheme.forget_to_Scheme).symm)
    { instances := ff },
  change preserves_limits_of_size (AffineScheme.equiv_CommRing.functor ⋙ Scheme.Spec),
  apply_instance,
end

instance {C : Type*} [category C] {X Y : Cᵒᵖ} (f : X ⟶ Y) [H : is_iso f] : is_iso f.unop :=
@@is_iso_of_op _ f.unop H

noncomputable
def pullback_iso_unop_pushout {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_pushout f.op g.op] : pullback f g ≅ unop (pushout f.op g.op) :=
{ hom := (pushout.desc pullback.fst.op pullback.snd.op
    (congr_arg quiver.hom.op pullback.condition) : pushout f.op g.op ⟶ op _).unop,
  inv := pullback.lift (pushout.inl : _ ⟶ pushout f.op g.op).unop
    (pushout.inr : _ ⟶ pushout f.op g.op).unop (congr_arg quiver.hom.unop
      (@pushout.condition _ _ _ _ _ f.op g.op _)),
  hom_inv_id' := by ext; simp [← unop_comp],
  inv_hom_id' := by { apply quiver.hom.op_inj, ext; simp [← op_comp] } }

@[simp, reassoc]
lemma pullback_iso_unop_pushout_inv_fst {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  (pullback_iso_unop_pushout f g).inv ≫ pullback.fst =
    (pushout.inl : _ ⟶ pushout f.op g.op).unop :=
pullback.lift_fst _ _ _

@[simp, reassoc]
lemma pullback_iso_unop_pushout_inv_snd {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  (pullback_iso_unop_pushout f g).inv ≫ pullback.snd =
    (pushout.inr : _ ⟶ pushout f.op g.op).unop :=
pullback.lift_snd _ _ _

@[simp, reassoc]
lemma pullback_iso_unop_pushout_hom_inl {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  pushout.inl ≫ (pullback_iso_unop_pushout f g).hom.op = pullback.fst.op :=
pushout.inl_desc _ _ _

@[simp, reassoc]
lemma pullback_iso_unop_pushout_hom_inr {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z)
  (g : Y ⟶ Z) [has_pullback f g] [has_pushout f.op g.op] :
  pushout.inr ≫ (pullback_iso_unop_pushout f g).hom.op = pullback.snd.op :=
pushout.inr_desc _ _ _

noncomputable
def pushout_iso_unop_pullback {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] : pushout f g ≅ unop (pullback f.op g.op) :=
{ hom := pushout.desc (pullback.fst : pullback f.op g.op ⟶ _).unop
    (pullback.snd : pullback f.op g.op ⟶ _).unop (congr_arg quiver.hom.unop
      (@pullback.condition _ _ _ _ _ f.op g.op _)),
  inv := (pullback.lift pushout.inl.op pushout.inr.op
    (congr_arg quiver.hom.op pushout.condition) : op _ ⟶ pullback f.op g.op).unop,
  hom_inv_id' := by ext; simp [← unop_comp],
  inv_hom_id' := by { apply quiver.hom.op_inj, ext; erw [category.id_comp]; simp [← op_comp] } }
.
@[simp, reassoc]
lemma pushout_iso_unop_pullback_inl_hom {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  pushout.inl ≫ (pushout_iso_unop_pullback f g).hom =
    (pullback.fst : pullback f.op g.op ⟶ _).unop :=
pushout.inl_desc _ _ _

@[simp, reassoc]
lemma pushout_iso_unop_pullback_inr_hom {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  pushout.inr ≫ (pushout_iso_unop_pullback f g).hom =
    (pullback.snd : pullback f.op g.op ⟶ _).unop :=
pushout.inr_desc _ _ _

@[simp]
lemma pushout_iso_unop_pullback_inv_fst {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  (pushout_iso_unop_pullback f g).inv.op ≫ pullback.fst = pushout.inl.op :=
pullback.lift_fst _ _ _

@[simp]
lemma pushout_iso_unop_pullback_inv_snd {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y)
  [has_pushout f g] [has_pullback f.op g.op] :
  (pushout_iso_unop_pullback f g).inv.op ≫ pullback.snd = pushout.inr.op :=
pullback.lift_snd _ _ _

include P

def affine_and : affine_target_morphism_property :=
λ X Y f hY, is_affine X ∧ P (Scheme.Γ.map f.op)

local attribute [reducible] CommRing.of

def _root_.ring_hom.respects_iso : Prop :=
(∀ {R S T : Type u} [comm_ring R] [comm_ring S] [comm_ring T], by exactI
    ∀ (f : R →+* S) (e : S ≃+* T) (hf : P f), P (e.to_ring_hom.comp f)) ∧
  (∀ {R S T : Type u} [comm_ring R] [comm_ring S] [comm_ring T], by exactI
    ∀ (f : S →+* T) (e : R ≃+* S) (hf : P f), P (f.comp e.to_ring_hom))

variable {P}

lemma _root_.ring_hom.respects_iso.cancel_left_is_iso (hP : ring_hom.respects_iso @P) {R S T : CommRing}
  (f : R ⟶ S) (g : S ⟶ T)
  [is_iso f] : P (f ≫ g) ↔ P g :=
⟨λ H, by { convert hP.2 (f ≫ g) (as_iso f).symm.CommRing_iso_to_ring_equiv H,
  exact (is_iso.inv_hom_id_assoc _ _).symm }, hP.2 g (as_iso f).CommRing_iso_to_ring_equiv⟩

lemma _root_.ring_hom.respects_iso.cancel_right_is_iso (hP : ring_hom.respects_iso @P) {R S T : CommRing}
  (f : R ⟶ S) (g : S ⟶ T)
  [is_iso g] : P (f ≫ g) ↔ P f :=
⟨λ H, by { convert hP.1 (f ≫ g) (as_iso g).symm.CommRing_iso_to_ring_equiv H,
  change f = f ≫ g ≫ (inv g), simp }, hP.1 f (as_iso g).CommRing_iso_to_ring_equiv⟩

lemma _root_.ring_hom.respects_iso.basic_open_iff (hP : ring_hom.respects_iso @P) {X Y : Scheme}
  [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (@is_localization.away.map (Y.presheaf.obj (op ⊤)) _ (Y.presheaf.obj (op $ Y.basic_open r)) _ _
    (X.presheaf.obj (op ⊤)) _ (X.presheaf.obj (op $ X.basic_open (Scheme.Γ.map f.op r))) _ _
      (Scheme.Γ.map f.op) r _ _) :=
begin
  rw [Γ_map_morphism_restrict, hP.cancel_left_is_iso, hP.cancel_right_is_iso,
    ← (hP.cancel_right_is_iso (f.val.c.app (op (Y.basic_open r))) (X.presheaf.map
      (eq_to_hom (Scheme.preimage_basic_open f r).symm).op)), ← eq_iff_iff],
  congr,
  delta is_localization.away.map,
  refine is_localization.ring_hom_ext (submonoid.powers r) _,
  convert (is_localization.map_comp _).symm using 1,
  change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _,
  rw f.val.c.naturality_assoc,
  erw ← X.presheaf.map_comp,
  congr,
end

lemma _root_.ring_hom.respects_iso.is_localization_away_iff (hP : ring_hom.respects_iso @P) {R S : Type*}
  (R' S' : Type*)[comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S'] [algebra R R']
  [algebra S S'] (f : R →+* S) (r : R) [is_localization.away r R'] [is_localization.away (f r) S'] :
  P (localization.away_map f r) ↔ P (is_localization.away.map R' S' f r) :=
begin
  let e₁ : R' ≃+* localization.away r :=
    (is_localization.alg_equiv (submonoid.powers r) _ _).to_ring_equiv,
  let e₂ : localization.away (f r) ≃+* S' :=
    (is_localization.alg_equiv (submonoid.powers (f r)) _ _).to_ring_equiv,
  refine (hP.cancel_left_is_iso e₁.to_CommRing_iso.hom (CommRing.of_hom _)).symm.trans _,
  refine (hP.cancel_right_is_iso (CommRing.of_hom _) e₂.to_CommRing_iso.hom).symm.trans _,
  rw ← eq_iff_iff,
  congr' 1,
  dsimp [CommRing.of_hom, CommRing.of, bundled.of],
  refine is_localization.ring_hom_ext (submonoid.powers r) _,
  ext1,
  revert e₁ e₂,
  dsimp [ring_equiv.to_ring_hom, is_localization.away.map],
  simp only [comp_apply, ring_equiv.refl_apply, is_localization.alg_equiv_apply,
    is_localization.ring_equiv_of_ring_equiv_apply, ring_hom.coe_mk, ring_equiv.to_fun_eq_coe,
    is_localization.ring_equiv_of_ring_equiv_eq, is_localization.map_eq],
end

lemma _root_.ring_hom.respects_iso.basic_open_iff_localization (hP : ring_hom.respects_iso @P)
  {X Y : Scheme} [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (localization.away_map (Scheme.Γ.map f.op) r) :=
(hP.basic_open_iff _ _).trans (hP.is_localization_away_iff _ _ _ _).symm

lemma _root_.ring_hom.localization_preserves.away (hP : ring_hom.localization_preserves @P)
  {R S : Type*} (R' S' : Type*) [comm_ring R] [comm_ring R'] [comm_ring S] [comm_ring S']
    [algebra R R'] [algebra S S'] (f : R →+* S) (r : R) [is_localization.away r R']
    [hS' : is_localization.away (f r) S'] (H : P f) : P (is_localization.away.map R' S' f r) :=
begin
  haveI : is_localization (submonoid.map (f : R →* S) (submonoid.powers r)) S',
  { convert hS', rw submonoid.map_powers, refl },
  exact hP f (submonoid.powers r) R' S' H
end

lemma _root_.ring_hom.respects_iso.of_restrict_morphism_restrict_iff (hP : ring_hom.respects_iso @P)
  {X Y : Scheme} [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (op ⊤)) (U : opens X.carrier)
  (hU : is_affine_open U) {V : opens _}
  (e : V = (opens.map (X.of_restrict ((opens.map f.1.base).obj _).open_embedding).1.base).obj U) :
  P (Scheme.Γ.map ((X.restrict ((opens.map f.1.base).obj _).open_embedding).of_restrict
    V.open_embedding ≫ f ∣_ Y.basic_open r).op) ↔
    P (localization.away_map (Scheme.Γ.map (X.of_restrict U.open_embedding ≫ f).op) r) :=
begin
  subst e,
  convert (hP.is_localization_away_iff _ _ _ _).symm,
  rotate,
  { exact algebraic_geometry.Γ_restrict_algebra _ _ },
  { apply ring_hom.to_algebra,
    refine X.presheaf.map
      (@hom_of_le _ _ ((is_open_map.functor _).obj _) ((is_open_map.functor _).obj _) _).op,
    change coe '' (coe '' set.univ) ⊆ coe '' set.univ,
    rw [subtype.coe_image_univ, subtype.coe_image_univ],
    exact set.image_preimage_subset _ _ },
  { exact algebraic_geometry.Γ_restrict_is_localization Y r },
  { rw ← U.open_embedding_obj_top at hU,
    dsimp only [Scheme.Γ_obj_op, Scheme.Γ_map_op, Scheme.restrict],
    convert (is_localization.is_localization_iff_of_ring_equiv _ (X.presheaf.map_iso (eq_to_iso _))
      .CommRing_iso_to_ring_equiv).mp (is_localization_basic_open hU _) using 2,
    swap,
    { dsimp only [functor.op, unop_op],
      congr' 1,
      ext1,
      rw [Scheme.comp_val_c_app, comp_apply],
      erw X.basic_open_res,
      rw [opens.open_embedding_obj_top, opens.open_embedding_obj_top],
      refine eq.trans _ (set.image_preimage_eq_inter_range).symm,
      erw subtype.range_coe,
      rw Scheme.preimage_basic_open,
      refl },
    { rw [ring_hom.algebra_map_to_algebra, iso.CommRing_iso_to_ring_equiv_to_ring_hom],
      refine eq.trans _ (X.presheaf.map_comp _ _),
      congr } },
  { apply is_localization.ring_hom_ext (submonoid.powers r) _,
    { apply_instance },
    { apply_instance },
    rw [is_localization.away.map, is_localization.map_comp, ring_hom.algebra_map_to_algebra,
      ring_hom.algebra_map_to_algebra, op_comp, functor.map_comp, op_comp, functor.map_comp],
    refine (@category.assoc CommRing _ _ _ _ _ _ _ _).symm.trans _,
    refine eq.trans _ (@category.assoc CommRing _ _ _ _ _ _ _ _),
    dsimp only [Scheme.Γ_map, quiver.hom.unop_op],
    rw [morphism_restrict_c_app, category.assoc, category.assoc, category.assoc],
    erw [f.1.c.naturality_assoc, ← X.presheaf.map_comp, ← X.presheaf.map_comp,
      ← X.presheaf.map_comp],
    congr },
end

variable (P)

lemma is_local_affine_and
  (hP : ring_hom.respects_iso @P)
  (h₃ : ring_hom.localization_preserves @P)
  (h₄ : ring_hom.of_localization_span @P) : (affine_and @P).is_local :=
begin
  constructor,
  { split,
    { rintros X Y Z e f _ ⟨H₁, H₂⟩,
      resetI,
      refine ⟨is_affine_of_iso e.hom, _⟩,
      rw [op_comp, functor.map_comp],
      exact hP.1 (Scheme.Γ.map f.op) (Scheme.Γ.map_iso e.op).CommRing_iso_to_ring_equiv H₂ },
    { rintros X Y Z e f _ ⟨H₁, H₂⟩,
      resetI,
      refine ⟨H₁, _⟩,
      rw [op_comp, functor.map_comp],
      exact hP.2 (Scheme.Γ.map f.op) (Scheme.Γ.map_iso e.op).CommRing_iso_to_ring_equiv H₂ } },
  { rintros X Y hY f r ⟨H₁, H₂⟩,
    resetI,
    refine ⟨affine_affine_property_is_local.2 f r H₁, _⟩,
    rw hP.basic_open_iff,
    apply ring_hom.localization_preserves.away @h₃,
    all_goals { assumption } },
  { rintros X Y hY f s hs H,
    obtain ⟨H₁, H₂⟩ := forall_and_distrib.mp H,
    resetI,
    haveI := affine_affine_property_is_local.3 f s hs H₁,
    refine ⟨_, _⟩,
    swap,
    apply h₄ (Scheme.Γ.map f.op) ↑s hs,
    intro r,
    specialize H₂ r,
    rw hP.basic_open_iff_localization at H₂,
    all_goals { assumption } },
end

def _root_.ring_hom.stable_under_composition : Prop :=
  ∀ {R S T} [comm_ring R] [comm_ring S] [comm_ring T],
    by exactI ∀ (f : R →+* S) (g : S →+* T) (hf : P f) (hg : P g), P (g.comp f)

lemma affine_and_stable_under_composition (hP' : ring_hom.stable_under_composition @P) :
  stable_under_composition (target_affine_locally (affine_and @P)) :=
begin
  introv X h₁ h₂ U,
  obtain ⟨h₃, h₄⟩ := h₂ U,
  obtain ⟨h₅, h₆⟩ := h₁ ⟨_, h₃⟩,
  split,
  { exact h₅ },
  { rw [morphism_restrict_comp, op_comp, functor.map_comp],
    apply hP'; assumption }
end

def _root_.ring_hom.stable_under_base_change : Prop :=
  ∀ ⦃R S T⦄ [comm_ring R] [comm_ring S] [comm_ring T], by exactI ∀ [algebra R S] [algebra R T],
    by exactI (P (algebra_map R T) →
      P (algebra.tensor_product.include_left.to_ring_hom : S →+* tensor_product R S T))

lemma _root_.ring_hom.stable_under_base_change.pushout_inl
  (hP : ring_hom.stable_under_base_change @P) (hP' : ring_hom.respects_iso @P) {R S T : CommRing}
  (f : R ⟶ S) (g : R ⟶ T) (H : P g) : P (pushout.inl : S ⟶ pushout f g) :=
begin
  rw [← (show _ = pushout.inl, from colimit.iso_colimit_cocone_ι_inv
    ⟨_, CommRing.pushout_cocone_is_colimit f g⟩ walking_span.left), hP'.cancel_right_is_iso],
  apply hP,
  exact H,
end

lemma _root_.ring_hom.stable_under_base_change.Γ_pullback_fst
  (hP : ring_hom.stable_under_base_change @P) (hP' : ring_hom.respects_iso @P) {X Y S : Scheme}
  [is_affine X] [is_affine Y] [is_affine S]
  (f : X ⟶ S) (g : Y ⟶ S) (H : P (Scheme.Γ.map g.op)) :
    P (Scheme.Γ.map (pullback.fst : pullback f g ⟶ _).op) :=
begin
  rw [← preserves_pullback.iso_inv_fst AffineScheme.forget_to_Scheme
    (AffineScheme.of_hom f) (AffineScheme.of_hom g), op_comp, functor.map_comp,
    hP'.cancel_right_is_iso, AffineScheme.forget_to_Scheme_map],
  have := congr_arg quiver.hom.unop (preserves_pullback.iso_hom_fst AffineScheme.Γ.right_op
    (AffineScheme.of_hom f) (AffineScheme.of_hom g)),
  simp only [quiver.hom.unop_op, functor.right_op_map, unop_comp] at this,
  delta AffineScheme.Γ at this,
  simp only [quiver.hom.unop_op, functor.comp_map, AffineScheme.forget_to_Scheme_map,
    functor.op_map] at this,
  rw [← this, hP'.cancel_right_is_iso,
    ← pushout_iso_unop_pullback_inl_hom (quiver.hom.unop _) (quiver.hom.unop _),
    hP'.cancel_right_is_iso],
  exact hP.pushout_inl _ hP' _ _ H
end

lemma affine_and_stable_under_base_change
  (hP : ring_hom.respects_iso @P)
  (h₁ : ring_hom.localization_preserves @P)
  (h₂ : ring_hom.of_localization_span @P)
  (h₃ : _root_.ring_hom.stable_under_base_change @P) :
  stable_under_base_change (target_affine_locally (affine_and @P)) :=
begin
  apply (is_local_affine_and @P hP @h₁ @h₂).stable_under_base_change,
  rintros X Y S hS hX f g ⟨hY, H⟩,
  exactI ⟨infer_instance, h₃.Γ_pullback_fst _ hP _ _ H⟩
end

def source_affine_locally : affine_target_morphism_property :=
λ X Y f hY, ∀ (U : X.affine_opens), P (Scheme.Γ.map (X.of_restrict U.1.open_embedding ≫ f).op)

def _root_.ring_hom.localization_away_is : Prop :=
∀ {R : Type*} (S : Type*) [comm_ring R] [comm_ring S] [by exactI algebra R S] (r : R)
  [by exactI is_localization.away r S], by exactI P (algebra_map R S)

lemma is_local_source_affine_locally
  (h₁ : ring_hom.respects_iso @P)
  (h₂ : ring_hom.localization_preserves @P)
  (h₃ : ring_hom.of_localization_span @P) : (source_affine_locally @P).is_local :=
begin
  constructor,
  { split,
    { introv H U,
      rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (Scheme.restrict_map_is_iso e.inv U.1).hom.op),
        ← functor.map_comp, ← op_comp],
      convert H ⟨_, U.prop.map_is_iso e.inv⟩ using 3,
      rw [is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac_assoc,
        category.assoc, e.inv_hom_id_assoc],
      refl },
    { introv H U,
      rw [← category.assoc, op_comp, functor.map_comp, h₁.cancel_left_is_iso],
      exact H U } },
  { introv H U,
    resetI,
    specialize H ⟨_, U.2.image_is_open_immersion (X.of_restrict _)⟩,
    convert (h₁.of_restrict_morphism_restrict_iff _ _ _ _ _).mpr _ using 1,
    swap 5,
    { exact ring_hom.localization_preserves.away @h₂ _ _ _ r H },
    { apply_instance },
    { exact U.2.image_is_open_immersion _},
    { ext1, exact (set.preimage_image_eq _ subtype.coe_injective).symm } },
  { introv hs hs' U,
    resetI,
    apply h₃ _ _ hs,
    intro r,
    have := hs' r (@@affine_preimage (X.of_restrict _) (show _, from _) U),
    rwa h₁.of_restrict_morphism_restrict_iff at this,
    { exact U.2 },
    { refl },
    { apply_instance },
    { convert Scheme.of_restrict.affine (Scheme.Γ.map f.op r.1) using 3;
        rw Scheme.preimage_basic_open; refl } }
end
.

def _root_.ring_hom.of_localization_span_target : Prop :=
  ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S)
    (s : set S) (hs : by exactI ideal.span s = ⊤)
    (H : by exactI (∀ (r : s), P ((algebra_map S (localization.away (r : S))).comp f))),
    by exactI P f

structure _root_.ring_hom.property_is_local : Prop :=
(localization_preserves : ring_hom.localization_preserves @P)
(of_localization_span_target :  ring_hom.of_localization_span_target @P)
(stable_under_composition : ring_hom.stable_under_composition @P)
(localization_away_is : ring_hom.localization_away_is @P)

variables {P} (hP : ring_hom.property_is_local @P)

lemma _root_.ring_hom.stable_under_composition.respects_iso (hP : ring_hom.stable_under_composition @P)
  (hP' : ∀ {R S : Type*} [comm_ring R] [comm_ring S] (e : by exactI R ≃+* S),
    by exactI P e.to_ring_hom) : ring_hom.respects_iso @P :=
begin
  split,
  { introv H, resetI, apply hP, exacts [H, hP' e] },
  { introv H, resetI, apply hP, exacts [hP' e, H] }
end

lemma source_affine_locally_of_source_open_cover_aux
  (h₁ : ring_hom.respects_iso @P)
  (h₃ : ring_hom.of_localization_span_target @P)
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] (U : X.affine_opens)
  (s : set (X.presheaf.obj (op U.1))) (hs : ideal.span s = ⊤)
  (hs' : ∀ (r : s), P (Scheme.Γ.map (X.of_restrict (X.basic_open r.1).open_embedding ≫ f).op)) :
    P (Scheme.Γ.map (X.of_restrict U.1.open_embedding ≫ f).op) :=
begin
  apply_fun ideal.map (X.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op) at hs,
  rw [ideal.map_span, ideal.map_top] at hs,
  apply h₃ _ _ hs,
  rintro ⟨_, r, hr, rfl⟩,
  refine (h₁.cancel_right_is_iso _
    (localization.alg_equiv _ _).to_ring_equiv.to_CommRing_iso.hom).mp _,
  swap 4,
  { exact @@algebraic_geometry.Γ_restrict_is_localization _ U.2 _ },
  { apply_instance },
  change P (ring_hom.comp _ _),
  rw ← ring_hom.comp_assoc,
  erw [is_localization.map_comp, ring_hom.comp_id],
  rw [ring_hom.algebra_map_to_algebra, op_comp, functor.map_comp],
  convert_to P (@category_struct.comp CommRing _ _ _ _ _ _),
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.Γ_map_op, category.assoc],
  erw ← X.presheaf.map_comp,
  rw [← h₁.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _))],
  convert hs' ⟨r, hr⟩ using 1,
  { erw category.assoc, rw [← X.presheaf.map_comp, op_comp, Scheme.Γ.map_comp,
    Scheme.Γ_map_op, Scheme.Γ_map_op], congr },
  { dsimp [functor.op],
    conv_lhs { rw opens.open_embedding_obj_top },
    conv_rhs { rw opens.open_embedding_obj_top },
    erw image_basic_open_of_is_open_immersion (X.of_restrict U.1.open_embedding),
    erw of_restrict_inv_app_apply,
    rw Scheme.basic_open_res_eq },
  { apply_instance }
end

lemma is_open_immersion_comp_of_source_affine_locally (h₁ : ring_hom.respects_iso @P)
  {X Y Z : Scheme} [is_affine X] [is_affine Z] (f : X ⟶ Y) [is_open_immersion f] (g : Y ⟶ Z)
  (h₂ : source_affine_locally @P g) :
  P (Scheme.Γ.map (f ≫ g).op) :=
begin
  rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq
    (Y.of_restrict _) f _).hom.op), ← functor.map_comp, ← op_comp],
  convert h₂ ⟨_, range_is_affine_open_of_open_immersion f⟩ using 3,
  { rw [is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac_assoc] },
  { apply_instance },
  { exact subtype.range_coe },
  { apply_instance }
end

lemma source_affine_locally_respects_iso (h : ring_hom.respects_iso @P) :
  (source_affine_locally @P).respects_iso :=
begin
  split,
  { introv H U,
    rw ← category.assoc,
    haveI : is_affine _ := U.2,
    exact is_open_immersion_comp_of_source_affine_locally h _ _ H },
  { introv H U,
    rw [← category.assoc, op_comp, functor.map_comp, h.cancel_left_is_iso],
    apply H }
end

include hP

lemma _root_.ring_hom.property_is_local.respects_iso : ring_hom.respects_iso @P :=
begin
  apply hP.stable_under_composition.respects_iso,
  introv,
  resetI,
  letI := e.to_ring_hom.to_algebra,
  apply_with hP.localization_away_is { instances := ff },
  apply is_localization_away_of_is_unit_bijective _ is_unit_one,
  exact e.bijective
end

lemma _root_.ring_hom.property_is_local.source_affine_locally_of_source_open_cover
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y]
  (𝒰 : X.open_cover) [∀ i, is_affine (𝒰.obj i)] (H : ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :
  source_affine_locally @P f :=
begin
  let S := λ i, (⟨⟨set.range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
    range_is_affine_open_of_open_immersion (𝒰.map i)⟩ : X.affine_opens),
  apply of_affine_open_cover,
  swap 5, { exact set.range S },
  { intros U r H,
    convert hP.stable_under_composition _ _ H _ using 1,
    swap,
    { refine X.presheaf.map
        (@hom_of_le _ _ ((is_open_map.functor _).obj _) ((is_open_map.functor _).obj _) _).op,
      rw [unop_op, unop_op, opens.open_embedding_obj_top, opens.open_embedding_obj_top],
      exact X.basic_open_subset _ },
    { rw [op_comp, op_comp, functor.map_comp, functor.map_comp],
      refine (eq.trans _ (category.assoc _ _ _).symm : _),
      congr' 1,
      refine eq.trans _ (X.presheaf.map_comp _ _),
      change X.presheaf.map _ = _,
      congr },
    convert hP.localization_away_is _ (X.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op r),
    { exact (ring_hom.algebra_map_to_algebra _).symm },
    { dsimp [Scheme.Γ],
      have := U.2,
      rw ← U.1.open_embedding_obj_top at this,
      convert is_localization_basic_open this _ using 6;
        rw opens.open_embedding_obj_top; exact (Scheme.basic_open_res_eq _ _ _).symm } },
  { introv hs hs',
    exact source_affine_locally_of_source_open_cover_aux hP.respects_iso hP.2 _ _ _ hs hs' },
  { rw set.eq_univ_iff_forall,
    intro x,
    rw set.mem_Union,
    exact ⟨⟨_, 𝒰.f x, rfl⟩, 𝒰.covers x⟩ },
  { rintro ⟨_, i, rfl⟩,
    specialize H i,
    rw ← hP.respects_iso.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq
      (𝒰.map i) (X.of_restrict (S i).1.open_embedding) subtype.range_coe.symm).inv.op) at H,
    rwa [← Scheme.Γ.map_comp, ← op_comp, is_open_immersion.iso_of_range_eq_inv,
      is_open_immersion.lift_fac_assoc] at H }
end

lemma _root_.ring_hom.property_is_local.affine_open_cover_tfae {X Y : Scheme.{u}}
  [is_affine Y] (f : X ⟶ Y) :
  tfae [source_affine_locally @P f,
    ∃ (𝒰 : Scheme.open_cover.{u} X) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), P (Scheme.Γ.map (𝒰.map i ≫ f).op),
    ∀ (𝒰 : Scheme.open_cover.{u} X) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      P (Scheme.Γ.map (𝒰.map i ≫ f).op),
    ∀ {U : Scheme} (g : U ⟶ X) [is_affine U] [is_open_immersion g],
      P (Scheme.Γ.map (g ≫ f).op)] :=
begin
  tfae_have : 1 → 4,
  { intros H U g _ hg,
    resetI,
    specialize H ⟨⟨_, hg.base_open.open_range⟩,
      range_is_affine_open_of_open_immersion g⟩,
    rw [← hP.respects_iso.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq
      g (X.of_restrict (opens.open_embedding ⟨_, hg.base_open.open_range⟩))
      subtype.range_coe.symm).hom.op), ← Scheme.Γ.map_comp, ← op_comp,
      is_open_immersion.iso_of_range_eq_hom] at H,
    erw is_open_immersion.lift_fac_assoc at H,
    exact H },
  tfae_have : 4 → 3,
  { intros H 𝒰 _ i, resetI, apply H },
  tfae_have : 3 → 2,
  { intro H, refine ⟨X.affine_cover, infer_instance, H _⟩ },
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, _, h𝒰⟩,
    exactI hP.source_affine_locally_of_source_open_cover f 𝒰 h𝒰 },
  tfae_finish
end

lemma _root_.ring_hom.property_is_local.open_cover_tfae {X Y : Scheme.{u}} [is_affine Y] (f : X ⟶ Y) :
  tfae [source_affine_locally @P f,
    ∃ (𝒰 : Scheme.open_cover.{u} X), ∀ (i : 𝒰.J), source_affine_locally @P (𝒰.map i ≫ f),
    ∀ (𝒰 : Scheme.open_cover.{u} X) (i : 𝒰.J), source_affine_locally @P (𝒰.map i ≫ f),
    ∀ {U : Scheme} (g : U ⟶ X) [is_open_immersion g], source_affine_locally @P (g ≫ f)] :=
begin
  tfae_have : 1 → 4,
  { intros H U g hg V,
    resetI,
    rw (hP.affine_open_cover_tfae f).out 0 3 at H,
    haveI : is_affine _ := V.2,
    rw ← category.assoc,
    apply H },
  tfae_have : 4 → 3,
  { intros H 𝒰 _ i, resetI, apply H },
  tfae_have : 3 → 2,
  { intro H, refine ⟨X.affine_cover, H _⟩ },
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, h𝒰⟩,
    rw (hP.affine_open_cover_tfae f).out 0 1,
    refine ⟨𝒰.bind (λ _, Scheme.affine_cover _), _, _⟩,
    { intro i, dsimp, apply_instance },
    { intro i,
      specialize h𝒰 i.1,
      rw (hP.affine_open_cover_tfae (𝒰.map i.fst ≫ f)).out 0 3 at h𝒰,
      erw category.assoc,
      apply @@h𝒰 _ (show _, from _),
      dsimp, apply_instance } },
  tfae_finish
end

lemma _root_.ring_hom.property_is_local.source_affine_locally_of_is_open_immersion_comp
  {X Y Z : Scheme.{u}} [is_affine Z] (f : X ⟶ Y) (g : Y ⟶ Z) [is_open_immersion f]
  (H : source_affine_locally @P g) : source_affine_locally @P (f ≫ g) :=
by apply ((hP.open_cover_tfae g).out 0 3).mp H

lemma _root_.ring_hom.property_is_local.source_affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  [is_affine Y] (𝒰 : Scheme.open_cover.{u} X) [∀ i, is_affine (𝒰.obj i)] :
  source_affine_locally @P f ↔ (∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :=
⟨λ H, let h := ((hP.affine_open_cover_tfae f).out 0 2).mp H in h 𝒰,
  λ H, let h := ((hP.affine_open_cover_tfae f).out 1 0).mp in h ⟨𝒰, infer_instance, H⟩⟩

lemma _root_.ring_hom.property_is_local.of_localization_span :
  ring_hom.of_localization_span @P :=
begin
  introv R hs hs',
  resetI,
  apply_fun (ideal.map f) at hs,
  rw [ideal.map_span, ideal.map_top] at hs,
  apply hP.of_localization_span_target _ _ hs,
  rintro ⟨_, r, hr, rfl⟩,
  have := hs' ⟨r, hr⟩,
  convert hP.stable_under_composition _ _ (hP.localization_away_is (localization.away r) r)
    (hs' ⟨r, hr⟩) using 1,
  exact (is_localization.map_comp _).symm
end

lemma _root_.ring_hom.property_is_local.is_local_source_affine_locally :
  (source_affine_locally @P).is_local :=
is_local_source_affine_locally _ hP.respects_iso hP.localization_preserves
  (@ring_hom.property_is_local.of_localization_span _ hP)

lemma _root_.ring_hom.property_is_local.affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
  (𝒰' : ∀ i, Scheme.open_cover.{u} ((𝒰.pullback_cover f).obj i)) [∀ i j, is_affine ((𝒰' i).obj j)] :
  target_affine_locally (source_affine_locally @P) f ↔
    (∀ i j, P (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op)) :=
(hP.is_local_source_affine_locally.affine_open_cover_iff f 𝒰).trans
    (forall_congr (λ i, hP.source_affine_open_cover_iff _ (𝒰' i)))

lemma _root_.ring_hom.property_is_local.source_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} X) :
  target_affine_locally (source_affine_locally @P) f ↔
    (∀ i, target_affine_locally (source_affine_locally @P) (𝒰.map i ≫ f)) :=
begin
  split,
  { intros H i U,
    rw morphism_restrict_comp,
    delta morphism_restrict,
    apply hP.source_affine_locally_of_is_open_immersion_comp,
    apply H },
  { intros H U,
    haveI : is_affine _ := U.2,
    apply ((hP.open_cover_tfae (f ∣_ U.1)).out 1 0).mp,
    use 𝒰.pullback_cover (X.of_restrict _),
    intro i,
    specialize H i U,
    rw morphism_restrict_comp at H,
    delta morphism_restrict at H,
    rw [category.assoc, (source_affine_locally_respects_iso hP.respects_iso).cancel_left_is_iso,
      ← (source_affine_locally_respects_iso hP.respects_iso).cancel_left_is_iso
        (pullback_symmetry _ _).hom, pullback_symmetry_hom_comp_snd_assoc] at H,
    exact H }
end
.
lemma affine_locally_stable_composition :
  stable_under_composition (target_affine_locally (source_affine_locally @P)) :=
begin
  intros X Y S f g hf hg,
  let 𝒰 : ∀ i, ((S.affine_cover.pullback_cover (f ≫ g)).obj i).open_cover,
  { intro i,
    refine Scheme.open_cover.bind _ (λ i, Scheme.affine_cover _),
    apply Scheme.open_cover.pushforward_iso _
    (pullback_right_pullback_fst_iso g (S.affine_cover.map i) f).hom,
    apply Scheme.pullback.open_cover_of_right,
    exact (pullback g (S.affine_cover.map i)).affine_cover },
  rw hP.affine_open_cover_iff (f ≫ g) S.affine_cover _,
  rotate,
  { exact 𝒰 },
  { intros i j, dsimp at *, apply_instance },
  { rintros i ⟨j, k⟩,
    dsimp at i j k,
    dsimp only [Scheme.open_cover.bind_map, Scheme.open_cover.pushforward_iso_obj,
      Scheme.pullback.open_cover_of_right_obj, Scheme.open_cover.pushforward_iso_map,
      Scheme.pullback.open_cover_of_right_map, Scheme.open_cover.bind_obj],
    rw [category.assoc, category.assoc, pullback_right_pullback_fst_iso_hom_snd,
      pullback.lift_snd_assoc, category.assoc, ← category.assoc, op_comp, functor.map_comp],
    apply hP.stable_under_composition,
    { exact (hP.affine_open_cover_iff _ _ _).mp hg _ _ },
    { rw (hP.is_local_source_affine_locally.affine_open_cover_tfae f).out 0 3 at hf,
      specialize hf ((pullback g (S.affine_cover.map i)).affine_cover.map j ≫ pullback.fst),
      rw (hP.affine_open_cover_tfae (pullback.snd : pullback f ((pullback g (S.affine_cover.map i))
        .affine_cover.map j ≫ pullback.fst) ⟶ _)).out 0 3 at hf,
      apply hf } }
end

lemma source_affine_locally_stable_under_base_change (h : ring_hom.stable_under_base_change @P) :
  (source_affine_locally @P).stable_under_base_change :=
begin
  intros X Y S hS hX f g H,
  resetI,
  rw (hP.affine_open_cover_tfae (pullback.fst : pullback f g ⟶ _)).out 0 1,
  rw (hP.affine_open_cover_tfae g).out 0 2 at H,
  use Scheme.pullback.open_cover_of_right Y.affine_cover f g,
  split,
  { intro i, dsimp, apply_instance },
  intro i,
  erw pullback.lift_fst,
  rw category.comp_id,
  exact h.Γ_pullback_fst _ hP.respects_iso _ _ (H Y.affine_cover i),
end

end algebraic_geometry
