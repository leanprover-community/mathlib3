/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Scheme
import category_theory.adjunction.limits
import category_theory.adjunction.reflective

/-!
# Adjunction between `Γ` and `Spec`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the adjunction `Γ_Spec.adjunction : Γ ⊣ Spec` by defining the unit (`to_Γ_Spec`,
in multiple steps in this file) and counit (done in Spec.lean) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in structure_sheaf.lean extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `algebraic_geometry.identity_to_Γ_Spec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `algebraic_geometry.Γ_Spec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/

noncomputable theory
universes u

open prime_spectrum

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf Spec (structure_sheaf)
open topological_space
open algebraic_geometry.LocallyRingedSpace
open Top.presheaf
open Top.presheaf.sheaf_condition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The map from the global sections to a stalk. -/
def Γ_to_stalk (x : X) : Γ.obj (op X) ⟶ X.presheaf.stalk x :=
X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def to_Γ_Spec_fun : X → prime_spectrum (Γ.obj (op X)) :=
λ x, comap (X.Γ_to_stalk x) (local_ring.closed_point (X.presheaf.stalk x))

lemma not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
  r ∉ (X.to_Γ_Spec_fun x).as_ideal ↔ is_unit (X.Γ_to_stalk x r) :=
by erw [local_ring.mem_maximal_ideal, not_not]

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
lemma to_Γ_Spec_preim_basic_open_eq (r : Γ.obj (op X)) :
  X.to_Γ_Spec_fun⁻¹' (basic_open r).1 = (X.to_RingedSpace.basic_open r).1 :=
by { ext, erw X.to_RingedSpace.mem_top_basic_open, apply not_mem_prime_iff_unit_in_stalk }

/-- `to_Γ_Spec_fun` is continuous. -/
lemma to_Γ_Spec_continuous : continuous X.to_Γ_Spec_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintro _ ⟨r, rfl⟩,
  erw X.to_Γ_Spec_preim_basic_open_eq r,
  exact (X.to_RingedSpace.basic_open r).2,
end

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
@[simps]
def to_Γ_Spec_base : X.to_Top ⟶ Spec.Top_obj (Γ.obj (op X)) :=
{ to_fun := X.to_Γ_Spec_fun,
  continuous_to_fun := X.to_Γ_Spec_continuous }

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbreviation to_Γ_Spec_map_basic_open : opens X :=
(opens.map X.to_Γ_Spec_base).obj (basic_open r)

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
lemma to_Γ_Spec_map_basic_open_eq : X.to_Γ_Spec_map_basic_open r = X.to_RingedSpace.basic_open r :=
opens.ext (X.to_Γ_Spec_preim_basic_open_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbreviation to_to_Γ_Spec_map_basic_open :
  X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r) :=
X.presheaf.map (X.to_Γ_Spec_map_basic_open r).le_top.op

/-- `r` is a unit as a section on the basic open defined by `r`. -/
lemma is_unit_res_to_Γ_Spec_map_basic_open :
  is_unit (X.to_to_Γ_Spec_map_basic_open r r) :=
begin
  convert (X.presheaf.map $ (eq_to_hom $ X.to_Γ_Spec_map_basic_open_eq r).op)
    .is_unit_map (X.to_RingedSpace.is_unit_res_basic_open r),
  rw ← comp_apply,
  erw ← functor.map_comp,
  congr
end

/-- Define the sheaf hom on individual basic opens for the unit. -/
def to_Γ_Spec_c_app :
  (structure_sheaf $ Γ.obj $ op X).val.obj (op $ basic_open r) ⟶
    X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r) :=
is_localization.away.lift r (is_unit_res_to_Γ_Spec_map_basic_open _ r)

/-- Characterization of the sheaf hom on basic opens,
    direction ← (next lemma) is used at various places, but → is not used in this file. -/
lemma to_Γ_Spec_c_app_iff
  (f : (structure_sheaf $ Γ.obj $ op X).val.obj (op $ basic_open r) ⟶
    X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r)) :
  to_open _ (basic_open r) ≫ f = X.to_to_Γ_Spec_map_basic_open r ↔ f = X.to_Γ_Spec_c_app r :=
begin
  rw ← (is_localization.away.away_map.lift_comp r
    (X.is_unit_res_to_Γ_Spec_map_basic_open r)),
  swap 5, exact is_localization.to_basic_open _ r,
  split,
  { intro h, refine is_localization.ring_hom_ext _ _,
    swap 5, exact is_localization.to_basic_open _ r, exact h },
  apply congr_arg,
end

lemma to_Γ_Spec_c_app_spec :
  to_open _ (basic_open r) ≫ X.to_Γ_Spec_c_app r = X.to_to_Γ_Spec_map_basic_open r :=
(X.to_Γ_Spec_c_app_iff r _).2 rfl

/-- The sheaf hom on all basic opens, commuting with restrictions. -/
def to_Γ_Spec_c_basic_opens :
  (induced_functor basic_open).op ⋙ (structure_sheaf (Γ.obj (op X))).1 ⟶
  (induced_functor basic_open).op ⋙ ((Top.sheaf.pushforward X.to_Γ_Spec_base).obj X.𝒪).1 :=
{ app := λ r, X.to_Γ_Spec_c_app r.unop,
  naturality' := λ r s f, begin
    apply (structure_sheaf.to_basic_open_epi (Γ.obj (op X)) r.unop).1,
    simp only [← category.assoc],
    erw X.to_Γ_Spec_c_app_spec r.unop,
    convert X.to_Γ_Spec_c_app_spec s.unop,
    symmetry,
    apply X.presheaf.map_comp
  end }

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps]
def to_Γ_Spec_SheafedSpace : X.to_SheafedSpace ⟶ Spec.to_SheafedSpace.obj (op (Γ.obj (op X))) :=
{ base := X.to_Γ_Spec_base,
  c := Top.sheaf.restrict_hom_equiv_hom (structure_sheaf (Γ.obj (op X))).1 _
    is_basis_basic_opens X.to_Γ_Spec_c_basic_opens }

lemma to_Γ_Spec_SheafedSpace_app_eq :
  X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_Γ_Spec_c_app r :=
Top.sheaf.extend_hom_app _ _ _ _ _

lemma to_Γ_Spec_SheafedSpace_app_spec (r : Γ.obj (op X)) :
  to_open _ (basic_open r) ≫ X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) =
    X.to_to_Γ_Spec_map_basic_open r :=
(X.to_Γ_Spec_SheafedSpace_app_eq r).symm ▸ X.to_Γ_Spec_c_app_spec r

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
lemma to_stalk_stalk_map_to_Γ_Spec (x : X) : to_stalk _ _ ≫
  PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x = X.Γ_to_stalk x :=
begin
  rw PresheafedSpace.stalk_map,
  erw ← to_open_germ _ (basic_open (1 : Γ.obj (op X)))
    ⟨X.to_Γ_Spec_fun x, by rw basic_open_one; trivial⟩,
  rw [← category.assoc, category.assoc (to_open _ _)],
  erw stalk_functor_map_germ,
  rw [← category.assoc (to_open _ _), X.to_Γ_Spec_SheafedSpace_app_spec 1],
  unfold Γ_to_stalk,
  rw ← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤,
  congr' 1,
  change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _,
  apply germ_res,
end

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps val_base]
def to_Γ_Spec : X ⟶ Spec.LocallyRingedSpace_obj (Γ.obj (op X)) :=
{ val := X.to_Γ_Spec_SheafedSpace,
  prop :=
  begin
    intro x,
    let p : prime_spectrum (Γ.obj (op X)) := X.to_Γ_Spec_fun x,
    constructor, /- show stalk map is local hom ↓ -/
    let S := (structure_sheaf _).presheaf.stalk p,
    rintros (t : S) ht,
    obtain ⟨⟨r, s⟩, he⟩ := is_localization.surj p.as_ideal.prime_compl t,
    dsimp at he,
    apply is_unit_of_mul_is_unit_left,
    rw he,
    refine is_localization.map_units S (⟨r, _⟩ : p.as_ideal.prime_compl),
    apply (not_mem_prime_iff_unit_in_stalk _ _ _).mpr,
    rw [← to_stalk_stalk_map_to_Γ_Spec, comp_apply],
    erw ← he,
    rw ring_hom.map_mul,
    exact ht.mul ((is_localization.map_units S s : _).map
      (PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x))
  end }

lemma comp_ring_hom_ext {X : LocallyRingedSpace} {R : CommRing}
  {f : R ⟶ Γ.obj (op X)} {β : X ⟶ Spec.LocallyRingedSpace_obj R}
  (w : X.to_Γ_Spec.1.base ≫ (Spec.LocallyRingedSpace_map f).1.base = β.1.base)
  (h : ∀ r : R,
    f ≫ X.presheaf.map (hom_of_le le_top : (opens.map β.1.base).obj (basic_open r) ⟶ _).op =
      to_open R (basic_open r) ≫ β.1.c.app (op (basic_open r))) :
  X.to_Γ_Spec ≫ Spec.LocallyRingedSpace_map f = β :=
begin
  ext1,
  apply Spec.basic_open_hom_ext,
  { intros r _,
    rw LocallyRingedSpace.comp_val_c_app,
    erw to_open_comp_comap_assoc,
    rw category.assoc,
    erw [to_Γ_Spec_SheafedSpace_app_spec, ← X.presheaf.map_comp],
    convert h r },
  exact w,
end

/-- `to_Spec_Γ _` is an isomorphism so these are mutually two-sided inverses. -/
lemma Γ_Spec_left_triangle : to_Spec_Γ (Γ.obj (op X)) ≫ X.to_Γ_Spec.1.c.app (op ⊤) = 𝟙 _ :=
begin
  unfold to_Spec_Γ,
  rw ← to_open_res _ (basic_open (1 : Γ.obj (op X))) ⊤ (eq_to_hom basic_open_one.symm),
  erw category.assoc,
  rw [nat_trans.naturality, ← category.assoc],
  erw [X.to_Γ_Spec_SheafedSpace_app_spec 1, ← functor.map_comp],
  convert eq_to_hom_map X.presheaf _, refl,
end

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identity_to_Γ_Spec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.right_op ⋙ Spec.to_LocallyRingedSpace :=
{ app := LocallyRingedSpace.to_Γ_Spec,
  naturality' := λ X Y f, begin
    symmetry,
    apply LocallyRingedSpace.comp_ring_hom_ext,
    { ext1 x,
      dsimp [Spec.Top_map, LocallyRingedSpace.to_Γ_Spec_fun],
      rw [← local_ring.comap_closed_point (PresheafedSpace.stalk_map _ x),
        ← prime_spectrum.comap_comp_apply, ← prime_spectrum.comap_comp_apply],
      congr' 2,
      exact (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x,trivial⟩).symm,
      apply_instance },
    { intro r,
      rw [LocallyRingedSpace.comp_val_c_app, ← category.assoc],
      erw [Y.to_Γ_Spec_SheafedSpace_app_spec, f.1.c.naturality],
      refl },
  end }

namespace Γ_Spec

lemma left_triangle (X : LocallyRingedSpace) :
  Spec_Γ_identity.inv.app (Γ.obj (op X)) ≫ (identity_to_Γ_Spec.app X).val.c.app (op ⊤) = 𝟙 _ :=
X.Γ_Spec_left_triangle


/-- `Spec_Γ_identity` is iso so these are mutually two-sided inverses. -/
lemma right_triangle (R : CommRing) :
  identity_to_Γ_Spec.app (Spec.to_LocallyRingedSpace.obj $ op R) ≫
  Spec.to_LocallyRingedSpace.map (Spec_Γ_identity.inv.app R).op = 𝟙 _ :=
begin
  apply LocallyRingedSpace.comp_ring_hom_ext,
  { ext (p : prime_spectrum R) x,
    erw ← is_localization.at_prime.to_map_mem_maximal_iff
      ((structure_sheaf R).presheaf.stalk p) p.as_ideal x,
    refl },
  { intro r, apply to_open_res },
end

-- Removing this makes the following definition time out.
local attribute [irreducible] Spec_Γ_identity identity_to_Γ_Spec Spec.to_LocallyRingedSpace

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps unit counit] def LocallyRingedSpace_adjunction : Γ.right_op ⊣ Spec.to_LocallyRingedSpace :=
adjunction.mk_of_unit_counit
{ unit := identity_to_Γ_Spec,
  counit := (nat_iso.op Spec_Γ_identity).inv,
  left_triangle' := by { ext X, erw category.id_comp,
    exact congr_arg quiver.hom.op (left_triangle X) },
  right_triangle' := by { ext1, ext1 R, erw category.id_comp,
    exact right_triangle R.unop } }

local attribute [semireducible] Spec.to_LocallyRingedSpace

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.right_op ⊣ Scheme.Spec :=
LocallyRingedSpace_adjunction.restrict_fully_faithful
  Scheme.forget_to_LocallyRingedSpace (𝟭 _)
  (nat_iso.of_components (λ X, iso.refl _) (λ _ _ f, by simpa))
  (nat_iso.of_components (λ X, iso.refl _) (λ _ _ f, by simpa))

lemma adjunction_hom_equiv_apply {X : Scheme} {R : CommRingᵒᵖ}
  (f : (op $ Scheme.Γ.obj $ op X) ⟶ R) :
  Γ_Spec.adjunction.hom_equiv X R f =
    LocallyRingedSpace_adjunction.hom_equiv X.1 R f :=
by { dsimp [adjunction, adjunction.restrict_fully_faithful], simp }

local attribute [irreducible] LocallyRingedSpace_adjunction Γ_Spec.adjunction

lemma adjunction_hom_equiv (X : Scheme) (R : CommRingᵒᵖ) :
  Γ_Spec.adjunction.hom_equiv X R = LocallyRingedSpace_adjunction.hom_equiv X.1 R :=
equiv.ext $ λ f, adjunction_hom_equiv_apply f

lemma adjunction_hom_equiv_symm_apply {X : Scheme} {R : CommRingᵒᵖ}
  (f : X ⟶ Scheme.Spec.obj R) :
  (Γ_Spec.adjunction.hom_equiv X R).symm f =
    (LocallyRingedSpace_adjunction.hom_equiv X.1 R).symm f :=
by { congr' 2, exact adjunction_hom_equiv _ _ }

@[simp] lemma adjunction_counit_app {R : CommRingᵒᵖ} :
  Γ_Spec.adjunction.counit.app R = LocallyRingedSpace_adjunction.counit.app R :=
by { rw [← adjunction.hom_equiv_symm_id, ← adjunction.hom_equiv_symm_id,
  adjunction_hom_equiv_symm_apply], refl }

@[simp] lemma adjunction_unit_app {X : Scheme} :
  Γ_Spec.adjunction.unit.app X = LocallyRingedSpace_adjunction.unit.app X.1 :=
by { rw [← adjunction.hom_equiv_id, ← adjunction.hom_equiv_id, adjunction_hom_equiv_apply], refl }

local attribute [semireducible] LocallyRingedSpace_adjunction Γ_Spec.adjunction

instance is_iso_LocallyRingedSpace_adjunction_counit :
  is_iso LocallyRingedSpace_adjunction.counit :=
is_iso.of_iso_inv _

instance is_iso_adjunction_counit : is_iso Γ_Spec.adjunction.counit :=
begin
  apply_with nat_iso.is_iso_of_is_iso_app { instances := ff },
  intro R,
  rw adjunction_counit_app,
  apply_instance,
end

-- This is just
-- `(Γ_Spec.adjunction.unit.app X).1.c.app (op ⊤) = Spec_Γ_identity.hom.app (X.presheaf.obj (op ⊤))`
-- But lean times out when trying to unify the types of the two sides.
lemma adjunction_unit_app_app_top (X : Scheme) :
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

end Γ_Spec

/-! Immediate consequences of the adjunction. -/

/-- Spec preserves limits. -/
instance : limits.preserves_limits Spec.to_LocallyRingedSpace :=
Γ_Spec.LocallyRingedSpace_adjunction.right_adjoint_preserves_limits
instance Spec.preserves_limits : limits.preserves_limits Scheme.Spec :=
Γ_Spec.adjunction.right_adjoint_preserves_limits

/-- Spec is a full functor. -/
instance : full Spec.to_LocallyRingedSpace :=
R_full_of_counit_is_iso Γ_Spec.LocallyRingedSpace_adjunction
instance Spec.full : full Scheme.Spec :=
R_full_of_counit_is_iso Γ_Spec.adjunction

/-- Spec is a faithful functor. -/
instance : faithful Spec.to_LocallyRingedSpace :=
R_faithful_of_counit_is_iso Γ_Spec.LocallyRingedSpace_adjunction
instance Spec.faithful : faithful Scheme.Spec :=
R_faithful_of_counit_is_iso Γ_Spec.adjunction

instance : is_right_adjoint Spec.to_LocallyRingedSpace := ⟨_, Γ_Spec.LocallyRingedSpace_adjunction⟩
instance : is_right_adjoint Scheme.Spec := ⟨_, Γ_Spec.adjunction⟩

instance : reflective Spec.to_LocallyRingedSpace := ⟨⟩
instance Spec.reflective : reflective Scheme.Spec := ⟨⟩

end algebraic_geometry
