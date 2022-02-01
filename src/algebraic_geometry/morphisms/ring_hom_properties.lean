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
of ring homs.

-/

universe u

open category_theory opposite topological_space

namespace algebraic_geometry

variable (P : ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S), Prop)

def CommRing.iso_of (R : CommRing) : R ≅ CommRing.of R :=
{ hom := ring_hom.id R,
  inv := ring_hom.id R }

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

def morphism_restrict_c_app {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (V : opens U) :
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

def Γ_map_morphism_restrict {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
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

lemma _root_.ring_hom.respects_iso.basic_open_iff_localization (hP : ring_hom.respects_iso @P)
  {X Y : Scheme} [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (localization.away_map (Scheme.Γ.map f.op) r) :=
begin
  refine (hP.basic_open_iff _ _).trans _,
  let e₁ : localization.away r ≃+* Y.presheaf.obj (op (Y.basic_open r)) :=
    (is_localization.alg_equiv (submonoid.powers r) _ _).to_ring_equiv,
  let e₂ : X.presheaf.obj (op (X.basic_open $ Scheme.Γ.map f.op r)) ≃+*
    localization.away (show X.presheaf.obj (op ⊤), from Scheme.Γ.map f.op r) :=
    (is_localization.alg_equiv (submonoid.powers
      (show X.presheaf.obj (op ⊤), from Scheme.Γ.map f.op r)) _ _).to_ring_equiv,
  rw [← hP.cancel_left_is_iso e₁.to_CommRing_iso.hom,
    ← hP.cancel_right_is_iso _ e₂.to_CommRing_iso.hom, ← eq_iff_iff],
  congr' 1,
  change e₂.to_ring_hom.comp (ring_hom.comp _ e₁.to_ring_hom) = _,
  refine is_localization.ring_hom_ext (submonoid.powers r) _,
  ext,
  erw is_localization.alg_equiv_apply,
  dsimp,
  delta localization.away_map is_localization.away.map,
  erw is_localization.alg_equiv_apply,
  rw [ring_equiv.to_fun_eq_coe, is_localization.ring_equiv_of_ring_equiv_eq, is_localization.map_eq,
    is_localization.map_eq, is_localization.map_eq],
  refl
end

lemma _root_.ring_hom.localization_preserves.away (hP : ring_hom.localization_preserves @P)
  {R S : Type*} (R' S' : Type*) [comm_ring R] [comm_ring R'] [comm_ring S] [comm_ring S']
    [algebra R R'] [algebra S S'] (f : R →+* S) (r : R) [is_localization.away r R']
    [hS' : is_localization.away (f r) S'] (H : P f) : P (is_localization.away.map R' S' f r) :=
begin
  haveI : is_localization (submonoid.map (f : R →* S) (submonoid.powers r)) S',
  { convert hS', rw submonoid.map_powers, refl },
  exact hP f (submonoid.powers r) R' S' H
end

variable (P)

lemma is_local_affine_and
  (hP : ring_hom.respects_iso @P)
  (h₃ : ring_hom.localization_preserves @P)
  (h₄ : ring_hom.of_localization_span @P) : (affine_and @P).is_local :=
begin
  constructor,
  { split,
    { rintros X Y Z e f ⟨H₁, H₂, H₃⟩,
      resetI,
      refine ⟨H₁, is_affine_of_iso e.hom, _⟩,
      rw [op_comp, functor.map_comp],
      exact hP.1 (Scheme.Γ.map f.op) (Scheme.Γ.map_iso e.op).CommRing_iso_to_ring_equiv H₃ },
    { rintros X Y Z e f ⟨H₁, H₂, H₃⟩,
      resetI,
      refine ⟨is_affine_of_iso e.inv, H₂, _⟩,
      rw [op_comp, functor.map_comp],
      exact hP.2 (Scheme.Γ.map f.op) (Scheme.Γ.map_iso e.op).CommRing_iso_to_ring_equiv H₃ } },
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


end algebraic_geometry
