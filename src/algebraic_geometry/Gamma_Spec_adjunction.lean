/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Spec
import category_theory.adjunction.limits
import category_theory.adjunction.fully_faithful

/-!
# Adjunction between `Γ` and `Spec`

Define the adjunction `Γ_Spec.adjunction : Γ ⊣ Spec` (or more technically,
`Γ.right_op ⊣ Spec.to_LocallyRingedSpace`) by defining the unit (done in Spec.lean) and
counit (`to_Γ_Spec`, in multiple steps in this file) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in structure_sheaf.lean extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.
-/

noncomputable theory
universes u

open prime_spectrum

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf
open topological_space
open algebraic_geometry.LocallyRingedSpace
open Top.presheaf
open Top.presheaf.sheaf_condition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- Map from the global sections to a stalk. -/
def Γ_to_stalk (x : X) : Γ.obj (op X) ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))
-- or @Top.presheaf.germ _ _ _ _ _ ⊤ ⟨x,trivial⟩

/-- Unit on the underlying set. -/
def to_Γ_Spec_fun : X → prime_spectrum (Γ.obj (op X)) := λ x,
  comap (X.Γ_to_stalk x) (@local_ring.closed_point _ _ (X.local_ring x))
-- or Spec.to_Top.map (X.Γ_to_stalk x).op (@local_ring.closed_point ...)

lemma not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
  r ∉ (X.to_Γ_Spec_fun x).as_ideal ↔ is_unit (X.Γ_to_stalk x r) :=
by erw [local_ring.mem_maximal_ideal, not_not]

/-- Preimage of a basic open in `Spec Γ(X)` under the unit is the basic open in `X`
    defined by the same element (equal as sets). -/
lemma to_Γ_Spec_preim_basic_open_eq (r : Γ.obj (op X)) :
  X.to_Γ_Spec_fun⁻¹' (basic_open r).1
  = (X.to_RingedSpace.basic_open r).1 :=
by { ext, erw X.to_RingedSpace.mem_top_basic_open, apply not_mem_prime_iff_unit_in_stalk }

/-- Unit is continuous. -/
lemma to_Γ_Spec_continuous : continuous X.to_Γ_Spec_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintro _ ⟨r,rfl⟩, erw X.to_Γ_Spec_preim_basic_open_eq r,
  exact (X.to_RingedSpace.basic_open r).2,
end

/-- Unit as a continuous map. -/
@[simps]
def to_Γ_Spec_base : X.to_Top ⟶ Spec.Top_obj (Γ.obj (op X)) :=
{ to_fun := X.to_Γ_Spec_fun,
  continuous_to_fun := X.to_Γ_Spec_continuous }

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbreviation to_Γ_Spec_map_basic_open : opens X :=
(opens.map X.to_Γ_Spec_base).obj (basic_open r)

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
lemma to_Γ_Spec_map_basic_open_eq :
  X.to_Γ_Spec_map_basic_open r = X.to_RingedSpace.basic_open r :=
subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

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
def to_Γ_Spec_c_app (r : Γ.obj (op X)) := CommRing.of_hom $
by { refine is_localization.away.lift r (is_unit_res_to_Γ_Spec_map_basic_open _ r),
     swap 4, exact is_localization.to_basic_open _ r }

/-- Characterization of the sheaf hom on basic opens,
    direction ← (next lemma) is used at various places, but → is not used in this file. -/
lemma to_Γ_Spec_c_app_iff
  (f : (structure_sheaf $ Γ.obj $ op X).val.obj (op $ basic_open r) ⟶
    X.presheaf.obj (op $ X.to_Γ_Spec_map_basic_open r)) :
  to_open _ (basic_open r) ≫ f = X.to_to_Γ_Spec_map_basic_open r ↔ f = X.to_Γ_Spec_c_app r :=
begin
  rw ← (is_localization.away.away_map.lift_comp r
    (X.is_unit_res_to_Γ_Spec_map_basic_open r) : _ = X.to_to_Γ_Spec_map_basic_open r),
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
  naturality' := λ r s f,
  begin
    apply (structure_sheaf.to_basic_open_epi (Γ.obj (op X)) r.unop).1,
    simp only [← category.assoc],
    erw X.to_Γ_Spec_c_app_spec r.unop,
    convert X.to_Γ_Spec_c_app_spec s.unop,
    apply eq.symm, apply X.presheaf.map_comp
  end }

/-- Unit as a hom of sheafed spaces. -/
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
  erw ← to_open_germ _ (basic_open (1 : Γ.obj (op X))) ⟨X.to_Γ_Spec_fun x, by rw basic_open_one; triv⟩,
  rw [← category.assoc, category.assoc (to_open _ _)],
  erw stalk_functor_map_germ,
  rw [← category.assoc (to_open _ _), X.to_Γ_Spec_SheafedSpace_app_spec 1],
  unfold Γ_to_stalk, rw ← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤,
  congr' 1, change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _,
  apply germ_res,
end

/-- Unit as a hom of locally ringed spaces. -/
@[simps coe_base]
def to_Γ_Spec : X ⟶ Spec.LocallyRingedSpace_obj (Γ.obj (op X)) :=
begin
  fsplit, exact X.to_Γ_Spec_SheafedSpace,
  intro x, let p : prime_spectrum (Γ.obj (op X)) := X.to_Γ_Spec_fun x,
  fsplit, /- show stalk map is local hom ↓ -/
  have h := is_localization.to_stalk (Γ.obj (op X)) p,
  letI := (to_stalk _ p).to_algebra, have he' := h.surj,
  intros t ht, rcases he' t with ⟨⟨r,s⟩,he⟩,
  have hu := h.map_units,
  let sm := PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x,
  have hr : is_unit (X.Γ_to_stalk x r),
  { apply_fun sm at he,
    rw [← to_stalk_stalk_map_to_Γ_Spec, comp_apply],
    erw ← he,
    rw ring_hom.map_mul,
    apply is_unit.mul ht,
    exact is_unit.map sm.to_monoid_hom (hu s) },
  rw ← not_mem_prime_iff_unit_in_stalk at hr,
  have hr' := hu ⟨r,hr⟩, erw ← he at hr',
  exact is_unit_of_mul_is_unit_left hr',
end

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
    erw [to_Γ_Spec_SheafedSpace_app_spec, ←X.presheaf.map_comp],
    convert h r },
  exact w,
end

/-- `to_Spec_Γ _` is iso so these are mutually two-sided inverses. -/
lemma left_triangle : to_Spec_Γ (Γ.obj (op X)) ≫ X.to_Γ_Spec.1.c.app (op ⊤) = 𝟙 (Γ.obj (op X)) :=
begin
  unfold to_Spec_Γ,
  rw ← to_open_res _ (basic_open (1 : Γ.obj (op X))) ⊤ (eq_to_hom basic_open_one.symm),
  erw category.assoc,
  rw [nat_trans.naturality, ← category.assoc],
  erw [X.to_Γ_Spec_SheafedSpace_app_spec 1, ← functor.map_comp],
  convert eq_to_hom_map X.presheaf _, refl,
end

end LocallyRingedSpace

@[simp] lemma _root_.prime_spectrum.comap_comp_apply {R S S': Type*} [comm_ring R] [comm_ring S] [comm_ring S'] (f : R →+* S) (g : S →+* S') (x : prime_spectrum S') :
  prime_spectrum.comap (g.comp f) x = (prime_spectrum.comap f) (prime_spectrum.comap g x) :=
rfl

/-- Unit as a natural transformation. -/
def identity_to_Γ_Spec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.right_op ⋙ Spec.to_LocallyRingedSpace :=
{ app := LocallyRingedSpace.to_Γ_Spec,
  naturality' := λ X Y f, begin
    symmetry,
    apply LocallyRingedSpace.comp_ring_hom_ext,
    { ext1 x,
      symmetry,
      dsimp [Spec.Top_map, LocallyRingedSpace.to_Γ_Spec_fun],
      rw ← prime_spectrum.comap_comp_apply,
      rw (local_ring.local_hom_iff_comap_closed_point
        (PresheafedSpace.stalk_map f.val x)).mp infer_instance,
      have := (@local_ring.local_hom_iff_comap_closed_point
        _ _ (Y.2 _) _ _ (X.2 x) _).1 (f.2 x),
      -- convert congr_fun (congr_arg prime_spectrum.comap
      --   (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x,trivial⟩))
      --   (@local_ring.closed_point _ _ (X.local_ring x)),
      -- erw prime_spectrum.comap_comp, rw function.comp_apply,
      -- erw (@local_ring.local_hom_iff_comap_closed_point
      --   _ _ (Y.2 _) _ _ (X.2 x) _).1 (f.2 x), refl
        },
    { intro r, rw [LocallyRingedSpace.comp_val_c_app, ←category.assoc],
      erw [Y.to_Γ_Spec_SheafedSpace_app_spec, f.1.c.naturality], refl },
  end }

namespace Γ_Spec

/-- `Spec_Γ_identity` is iso so these are mutually two-sided inverses. -/
lemma right_triangle (R : CommRing) :
  identity_to_Γ_Spec.app (Spec.LocallyRingedSpace_obj R) ≫
  Spec.LocallyRingedSpace_map (Spec_Γ_identity.inv.app R) = 𝟙 _ :=
begin
  apply LocallyRingedSpace.comp_ring_hom_ext,
  { ext1 p, ext, erw ← @is_localization.at_prime.to_map_mem_maximal_iff _ _ _ _
      (to_stalk R p).to_algebra p.1 _ (is_localization.to_stalk R p) x, refl },
  { intro r, apply to_open_res },
end

/-- The adjunction `Γ ⊣ Spec`. -/
def adjunction : Γ.right_op ⊣ Spec.to_LocallyRingedSpace := adjunction.mk_of_unit_counit
{ unit := identity_to_Γ_Spec,
  counit := (nat_iso.op Spec_Γ_identity).inv,
  left_triangle' := by { ext X, erw category.id_comp,
    convert congr_arg quiver.hom.op X.left_triangle using 1 },
  right_triangle' := by { ext1, ext1 R, erw category.id_comp,
    exact right_triangle R.unop } }
/- left triangle takes 33s and right triangle takes 7s on my machine. -/

end Γ_Spec

/-! Immediate consequences of the adjunction. -/

/-- Spec preserves limits. -/
instance Spec.preserves_limits : limits.preserves_limits Spec.to_LocallyRingedSpace :=
adjunction.right_adjoint_preserves_limits Γ_Spec.adjunction

/-- Spec is a full functor. -/
instance Spec.full : full Spec.to_LocallyRingedSpace :=
@R_full_of_counit_is_iso _ _ _ _ _ _ Γ_Spec.adjunction (is_iso.of_iso_inv _)

/-- Spec is a faithful functor. -/
instance Spec.faithful : faithful Spec.to_LocallyRingedSpace :=
@R_faithful_of_counit_is_iso _ _ _ _ _ _ Γ_Spec.adjunction (is_iso.of_iso_inv _)

end algebraic_geometry
