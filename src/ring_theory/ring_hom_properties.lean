/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebra.category.Ring.constructions
import algebra.category.Ring.colimits
import category_theory.isomorphism
import ring_theory.localization.away
import ring_theory.is_tensor_product

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `ring_hom.respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `ring_hom.stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `ring_hom.stable_under_base_change`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/

universe u

open category_theory opposite category_theory.limits

namespace ring_hom

variable (P : ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S), Prop)

include P

section respects_iso

/-- A property `respects_iso` if it still holds when composed with an isomorphism -/
def respects_iso : Prop :=
(∀ {R S T : Type u} [comm_ring R] [comm_ring S] [comm_ring T], by exactI
    ∀ (f : R →+* S) (e : S ≃+* T) (hf : P f), P (e.to_ring_hom.comp f)) ∧
  (∀ {R S T : Type u} [comm_ring R] [comm_ring S] [comm_ring T], by exactI
    ∀ (f : S →+* T) (e : R ≃+* S) (hf : P f), P (f.comp e.to_ring_hom))

variable {P}

lemma respects_iso.cancel_left_is_iso (hP : respects_iso @P) {R S T : CommRing}
  (f : R ⟶ S) (g : S ⟶ T)
  [is_iso f] : P (f ≫ g) ↔ P g :=
⟨λ H, by { convert hP.2 (f ≫ g) (as_iso f).symm.CommRing_iso_to_ring_equiv H,
  exact (is_iso.inv_hom_id_assoc _ _).symm }, hP.2 g (as_iso f).CommRing_iso_to_ring_equiv⟩

lemma respects_iso.cancel_right_is_iso (hP : respects_iso @P) {R S T : CommRing}
  (f : R ⟶ S) (g : S ⟶ T)
  [is_iso g] : P (f ≫ g) ↔ P f :=
⟨λ H, by { convert hP.1 (f ≫ g) (as_iso g).symm.CommRing_iso_to_ring_equiv H,
  change f = f ≫ g ≫ (inv g), simp }, hP.1 f (as_iso g).CommRing_iso_to_ring_equiv⟩

lemma respects_iso.is_localization_away_iff (hP : ring_hom.respects_iso @P) {R S : Type*}
  (R' S' : Type*) [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S'] [algebra R R']
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
  simp only [category_theory.comp_apply, ring_equiv.refl_apply, is_localization.alg_equiv_apply,
    is_localization.ring_equiv_of_ring_equiv_apply, ring_hom.coe_mk, ring_equiv.to_fun_eq_coe,
    is_localization.ring_equiv_of_ring_equiv_eq, is_localization.map_eq],
end

end respects_iso

section stable_under_composition

/-- A property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def stable_under_composition : Prop :=
  ∀ ⦃R S T⦄ [comm_ring R] [comm_ring S] [comm_ring T],
    by exactI ∀ (f : R →+* S) (g : S →+* T) (hf : P f) (hg : P g), P (g.comp f)

variable {P}

lemma stable_under_composition.respects_iso (hP : ring_hom.stable_under_composition @P)
  (hP' : ∀ {R S : Type*} [comm_ring R] [comm_ring S] (e : by exactI R ≃+* S),
    by exactI P e.to_ring_hom) : ring_hom.respects_iso @P :=
begin
  split,
  { introv H, resetI, apply hP, exacts [H, hP' e] },
  { introv H, resetI, apply hP, exacts [hP' e, H] }
end

end stable_under_composition

section stable_under_base_change

/-- A morphism property `P` is `stable_under_base_change` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`. -/
def stable_under_base_change : Prop :=
  ∀ (R S R' S') [comm_ring R] [comm_ring S] [comm_ring R'] [comm_ring S'],
    by exactI ∀ [algebra R S] [algebra R R'] [algebra R S'] [algebra S S'] [algebra R' S'],
    by exactI ∀ [is_scalar_tower R S S'] [is_scalar_tower R R' S'],
    by exactI ∀ [algebra.is_pushout R S R' S'], P (algebra_map R S) → P (algebra_map R' S')

lemma stable_under_base_change.mk
  (h₁ : respects_iso @P)
  (h₂ : ∀ ⦃R S T⦄ [comm_ring R] [comm_ring S] [comm_ring T],
    by exactI ∀ [algebra R S] [algebra R T], by exactI (P (algebra_map R T) →
      P (algebra.tensor_product.include_left.to_ring_hom : S →+* tensor_product R S T))) :
  stable_under_base_change @P :=
begin
  introv R h H,
  resetI,
  let e := h.symm.1.equiv,
  let f' := algebra.tensor_product.product_map (is_scalar_tower.to_alg_hom R R' S')
    (is_scalar_tower.to_alg_hom R S S'),
  have : ∀ x, e x = f' x,
  { intro x,
    change e.to_linear_map.restrict_scalars R x = f'.to_linear_map x,
    congr' 1,
    apply tensor_product.ext',
    intros x y,
    simp [is_base_change.equiv_tmul, algebra.smul_def] },
  convert h₁.1 _ _ (h₂ H : P (_ : R' →+* _)),
  swap,
  { refine { map_mul' := λ x y, _, ..e },
    change e (x * y) = e x * e y,
    simp_rw this,
    exact map_mul f' _ _ },
  { ext,
    change _ = e (x ⊗ₜ[R] 1),
    dsimp only [e],
    rw [h.symm.1.equiv_tmul, algebra.smul_def, alg_hom.to_linear_map_apply, map_one, mul_one] }
end

omit P

local attribute [instance] algebra.tensor_product.right_algebra

lemma stable_under_base_change.pushout_inl
  (hP : ring_hom.stable_under_base_change @P) (hP' : ring_hom.respects_iso @P) {R S T : CommRing}
  (f : R ⟶ S) (g : R ⟶ T) (H : P g) : P (pushout.inl : S ⟶ pushout f g) :=
begin
  rw [← (show _ = pushout.inl, from colimit.iso_colimit_cocone_ι_inv
    ⟨_, CommRing.pushout_cocone_is_colimit f g⟩ walking_span.left), hP'.cancel_right_is_iso],
  letI := f.to_algebra,
  letI := g.to_algebra,
  dsimp only [CommRing.pushout_cocone_inl, pushout_cocone.ι_app_left],
  apply hP R T S (tensor_product R S T),
  exact H,
end

end stable_under_base_change

end ring_hom
