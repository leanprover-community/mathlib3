/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Spec
import algebraic_geometry.ringed_space
import topology.sheaves.sheaf_condition.basis_le
import topology.sheaves.functors
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
universe variables u v

open prime_spectrum

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf
open topological_space
open algebraic_geometry.LocallyRingedSpace
open Top.presheaf
open Top.presheaf.sheaf_condition


variable (R : CommRing)

/-- Basic opens in `Spec R` indexed by elements of `R`. -/
def basic_open_B : (Spec.Top_obj R).opens_index_struct := ⟨R, λ r, basic_open r⟩
-- Much nicer to work directly with the indexing function than the range set

private def idfb := induced_functor (op ∘ (basic_open_B R).f)

lemma basic_opens_is_basis {R} : Top.is_basis_range (basic_open_B R) := is_basis_basic_opens

/- to do : prime spectrum version of sheaf hom_ext, direcly unfold to basic open r -/
/- to do : remove bundled indexed family -/

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{v})

/-- `Γ` (global sections) as a function from LocallyRingedSpace to CommRing. -/
abbreviation Γ' := Γ.obj (op X)

/-- Map from the global sections to a stalk. -/
def Γ_to_stalk (x : X) : Γ' X ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))
-- or @Top.presheaf.germ _ _ _ _ _ ⊤ ⟨x,trivial⟩

/-- Unit on the underlying set. -/
def to_Γ_Spec_fun : X → prime_spectrum (Γ' X) := λ x,
  comap (X.Γ_to_stalk x) (@local_ring.closed_point _ _ (X.local_ring x))
-- or Spec.to_Top.map (X.Γ_to_stalk x).op (@local_ring.closed_point ...)

lemma not_mem_prime_iff_unit_in_stalk (r : Γ' X) (x : X) :
  r ∉ (X.to_Γ_Spec_fun x).as_ideal ↔ is_unit (X.Γ_to_stalk x r) :=
by erw [local_ring.mem_maximal_ideal, not_not]

/-- Preimage of a basic open under the unit is a basic open. -/
lemma to_Γ_Spec_preim_basic_open_eq (r : Γ' X) :
  X.to_Γ_Spec_fun⁻¹' (basic_open r).1
  = (X.to_RingedSpace.basic_open r).1 :=
by { ext, erw X.to_RingedSpace.mem_basic_open, apply not_mem_prime_iff_unit_in_stalk }

/-- Unit is continuous. -/
lemma to_Γ_Spec_continuous : continuous X.to_Γ_Spec_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintro _ ⟨r,rfl⟩, erw X.to_Γ_Spec_preim_basic_open_eq r,
  exact (X.to_RingedSpace.basic_open r).2,
end

/-- Unit as a continuous map. -/
def to_Γ_Spec_base : X.to_Top ⟶ Spec.Top_obj (Γ' X) :=
{ to_fun := X.to_Γ_Spec_fun,
  continuous_to_fun := X.to_Γ_Spec_continuous }

/-- The preimage in `X` of a basic open in `Spec Γ(X)`. -/
abbreviation opens_map_basic_open (r : Γ' X) :=
  (opens.map X.to_Γ_Spec_base).obj (basic_open r)

/-- The preimage is a basic open in `X` defined by the same element `r`. -/
lemma to_Γ_Spec_opens_map_obj_basic_open_eq (r : Γ' X) :
  X.opens_map_basic_open r = X.to_RingedSpace.basic_open r :=
subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbreviation to_opens_map_basic_open (r : Γ' X) :=
  X.presheaf.map (X.opens_map_basic_open r).le_top.op

/-- `r` is a unit in the sections on the basic open defined by `r`. -/
lemma is_unit_res_opens_map_basic_open (r : Γ' X) :
  is_unit (X.to_opens_map_basic_open r r) :=
by { have h := X.to_RingedSpace.is_unit_res_basic_open r,
     rw ← to_Γ_Spec_opens_map_obj_basic_open_eq at h, exact h }

/-- Define the unit as a sheaf hom on individual basic opens. -/
def to_Γ_Spec_c_app (r : Γ' X) := CommRing.of_hom $
  by { refine is_localization.away.lift r (is_unit_res_opens_map_basic_open _ r),
       swap 4, exact is_localization.to_basic_open _ r }

/-- Characterization of the sheaf morphism on basic opens,
    direction ← is used at various places, but → is not used in this file. -/
lemma to_Γ_Spec_c_app_iff (r : Γ' X) :
  ∀ f, to_open _ (basic_open r) ≫ f = X.to_opens_map_basic_open r
  ↔ f = X.to_Γ_Spec_c_app r :=
λ f, begin
  rw ← (is_localization.away.away_map.lift_comp r
    (X.is_unit_res_opens_map_basic_open r) : _ = X.to_opens_map_basic_open r),
  swap 5, exact is_localization.to_basic_open _ r, split,
  { intro h, refine is_localization.ring_hom_ext _ _,
    swap 5, exact is_localization.to_basic_open _ r, exact h },
  apply congr_arg,
end

lemma to_Γ_Spec_c_app_spec (r : Γ' X) :
  to_open _ (basic_open r) ≫ X.to_Γ_Spec_c_app r = X.to_opens_map_basic_open r :=
(X.to_Γ_Spec_c_app_iff r _).2 rfl

/-- Unit as a sheaf hom on all basic opens, commuting with restrictions. -/
def to_Γ_Spec_c_basic_opens : idfb _ ⋙ (structure_sheaf (Γ' X)).1
                          ⟶ idfb _ ⋙ X.to_Γ_Spec_base _* X.presheaf :=
{ app := X.to_Γ_Spec_c_app,
  naturality' := λ r s f, by {
    apply (to_basic_open_epi (Γ' X) r).1,
    simp only [←category.assoc],
    erw X.to_Γ_Spec_c_app_spec r,
    convert X.to_Γ_Spec_c_app_spec s,
    apply eq.symm, apply X.presheaf.map_comp } }

/-- Unit as a sheaf hom. -/
def to_Γ_Spec_c := Top.sheaf.uniq_hom_extn_from_basis _
  ((Top.sheaf.pushforward _).obj X.𝒪).2
  basic_opens_is_basis X.to_Γ_Spec_c_basic_opens

/-- Unit as a sheafed space hom. -/
def to_Γ_Spec_SheafedSpace : X.to_SheafedSpace ⟶ Spec.to_SheafedSpace.obj (op (Γ' X)) :=
{ base := X.to_Γ_Spec_base,
  c := X.to_Γ_Spec_c.lift }

lemma to_Γ_Spec_SheafedSpace_app_eq (r : Γ' X) :
  X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_Γ_Spec_c_app r :=
by { change _ = X.to_Γ_Spec_c_basic_opens.app r, rw ← X.to_Γ_Spec_c.fac, refl }
/- once worked but now timeouts:
by change (whisker_left (idfb _) _).app r = _; erw X.to_Γ_Spec_c.fac; refl -/

lemma to_Γ_Spec_SheafedSpace_app_spec (r : Γ' X) :
  to_open _ (basic_open r) ≫ X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) =
  X.to_opens_map_basic_open r :=
(X.to_Γ_Spec_SheafedSpace_app_eq r).symm ▸ X.to_Γ_Spec_c_app_spec r

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
lemma to_stalk_comm (x : X) : to_stalk _ _ ≫
  PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x = X.Γ_to_stalk x :=
begin
  rw PresheafedSpace.stalk_map,
  erw ← to_open_germ _ (basic_open (1 : Γ' X))
    ⟨X.to_Γ_Spec_fun x, by rw basic_open_one; triv⟩,
  rw [←category.assoc, category.assoc (to_open _ _)],
  erw stalk_functor_map_germ,
  rw [←category.assoc (to_open _ _), (X.to_Γ_Spec_SheafedSpace_app_spec 1)],
  unfold Γ_to_stalk, rw ← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤,
  congr' 1, change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _,
  apply germ_res,
end

/-- Unit as a hom of locally ringed spaces. -/
def to_Γ_Spec : X ⟶ Spec.LocallyRingedSpace_obj (Γ' X) :=
begin
  fsplit, exact X.to_Γ_Spec_SheafedSpace,
  intro x, let p : prime_spectrum (Γ' X) := X.to_Γ_Spec_fun x,
  fsplit, /- show stalk map is local hom ↓ -/
  have h := is_localization.to_stalk (Γ' X) p,
  letI := (to_stalk _ p).to_algebra, have he' := h.surj,
  intros t ht, rcases he' t with ⟨⟨r,s⟩,he⟩,
  have hu := h.map_units,
  let sm := PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x,
  have hr : is_unit (X.Γ_to_stalk x r),
    apply_fun sm at he,
    rw [←to_stalk_comm, comp_apply],
    erw ← he, rw ring_hom.map_mul,
    apply is_unit.mul ht,
    exact is_unit.map sm.to_monoid_hom (hu s),
  rw ← not_mem_prime_iff_unit_in_stalk at hr,
  have hr' := hu ⟨r,hr⟩, erw ← he at hr',
  exact is_unit_of_mul_is_unit_left hr',
end

variables {Y : LocallyRingedSpace.{v}} (f : X ⟶ Y)

lemma to_Γ_Spec_base_naturality : (f ≫ Y.to_Γ_Spec).1.1 =
  (X.to_Γ_Spec ≫ (Γ.right_op ⋙ Spec.to_LocallyRingedSpace).map f).1.1 :=
begin
  ext1 x, convert congr_fun (congr_arg comap
    (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x,trivial⟩))
    (@local_ring.closed_point _ _ (X.local_ring x)),
  erw prime_spectrum.comap_comp, rw function.comp_apply,
  erw (@local_ring.local_hom_iff_comap_closed_point
        _ _ (Y.2 _) _ _ (X.2 x) _).1 (f.2 x), refl,
end

lemma to_Γ_Spec_c_naturality (r : Γ' Y) : let f' := Γ.map f.op,
  eq := λ U, congr_arg (λ g, op $ (opens.map g).obj U) (X.to_Γ_Spec_base_naturality f) in
  (Y.to_Γ_Spec_SheafedSpace.c.app (op $ basic_open r) ≫
    f.1.c.app (op $ Y.opens_map_basic_open r)) ≫
    X.presheaf.map (eq_to_hom $ eq $ basic_open r) =
  comap f' (basic_open r) (basic_open $ f' r) (λ _ h, h) ≫
    X.to_Γ_Spec_SheafedSpace.c.app (op $ basic_open $ f' r) :=
begin
  apply (to_basic_open_epi (Γ' Y) r).1, erw to_open_comp_comap_assoc,
  erw X.to_Γ_Spec_SheafedSpace_app_spec (Γ.map f.op r),
  iterate 2 {rw ← category.assoc},
  rw Y.to_Γ_Spec_SheafedSpace_app_spec r,
  erw [f.1.c.naturality, category.assoc], congr,
  erw ← X.presheaf.map_comp, congr,
end

/-- `to_Spec_Γ _` is iso so these are mutually two-sided inverses. -/
lemma left_triangle : to_Spec_Γ (Γ' X) ≫ X.to_Γ_Spec.1.c.app (op ⊤) = 𝟙 (Γ' X) :=
begin
  unfold to_Spec_Γ,
  rw ← to_open_res _ (basic_open (1 : Γ' X)) ⊤ (eq_to_hom basic_open_one.symm),
  erw category.assoc, rw [nat_trans.naturality, ←category.assoc],
  erw [X.to_Γ_Spec_SheafedSpace_app_spec 1, ← functor.map_comp],
  convert eq_to_hom_map X.presheaf _, refl,
end

end LocallyRingedSpace

/-- Unit as a natural transformation. -/
def identity_to_Γ_Spec : 𝟭 LocallyRingedSpace ⟶ Γ.right_op ⋙ Spec.to_LocallyRingedSpace :=
{ app := LocallyRingedSpace.to_Γ_Spec,
  naturality' := λ X Y f, begin
    ext1, ext1, swap, exact X.to_Γ_Spec_base_naturality f,
    { apply Top.sheaf.hom_ext (basic_open_B Y.Γ') ((Top.sheaf.pushforward _).obj X.𝒪).2,
      exact basic_opens_is_basis, intro r, rw nat_trans.comp_app,
      iterate 2 {rw LocallyRingedSpace.comp_val_c_app'},
      convert X.to_Γ_Spec_c_naturality f r using 2, simpa /- Slow! `exact` timeouts.
      In general, `dsimp` and `erw` are slow in this proof, often timeout (loop?).
      Must mark `uniq_hom_extn_from_basis` as `irreducible` to avoid timeout here
      (the terminal `convert`). Maybe more `irreducible` at appropriate places can
      further speed this up. -/ },
  end }

namespace Γ_Spec

lemma right_triangle_base :
  ((Spec.LocallyRingedSpace_obj R).to_Γ_Spec ≫
  Spec.to_LocallyRingedSpace.map (to_Spec_Γ R).op).1.1 = 𝟙 _ :=
begin
  ext1 p, ext, erw ← @is_localization.at_prime.to_map_mem_maximal_iff _ _ _ _
    (to_stalk R p).to_algebra p.1 _ (is_localization.to_stalk R p) x, refl,
end

lemma right_triangle_c (r : R) :
  let S := Spec.LocallyRingedSpace_obj R, f := to_Spec_Γ R,
  eq := λ U, congr_arg (λ g, (opens.map g).obj U) (right_triangle_base R).symm in
  (CommRing.of_hom (comap f (basic_open r) (basic_open (f r)) (λ _ h, h)) ≫
    S.to_Γ_Spec_SheafedSpace.c.app (op $ basic_open (f r))) ≫
    S.presheaf.map (eq_to_hom $ eq $ basic_open r).op = 𝟙 _ :=
begin
  apply (to_basic_open_epi R r).1, rw category.assoc,
  erw to_open_comp_comap_assoc, rw ← category.assoc (to_open _ _),
  erw (Spec.LocallyRingedSpace_obj R).to_Γ_Spec_SheafedSpace_app_spec,
  erw [←functor.map_comp, category.comp_id, ←op_comp], apply to_open_res,
end

/-- `Spec_Γ_identity` is iso so these are mutually two-sided inverses. -/
lemma right_triangle :
  identity_to_Γ_Spec.app (Spec.LocallyRingedSpace_obj R) ≫
  Spec.LocallyRingedSpace_map (Spec_Γ_identity.inv.app R) = 𝟙 _ :=
begin
  ext1, ext1, swap, exact right_triangle_base R,
  { apply Top.sheaf.hom_ext (basic_open_B R) ((Top.sheaf.pushforward _).obj (structure_sheaf R)).2,
    exact basic_opens_is_basis, intro r,
    rw [nat_trans.comp_app, LocallyRingedSpace.comp_val_c_app'],
    convert right_triangle_c R r using 2, simpa },
end

/-- Auxiliary data structure for defining the adjunction. -/
def core_unit_counit :
  adjunction.core_unit_counit Γ.right_op Spec.to_LocallyRingedSpace :=
{ unit := identity_to_Γ_Spec,
  counit := (nat_iso.op Spec_Γ_identity).inv,
  left_triangle' := by { ext X, rw nat_trans.comp_app, erw category.id_comp,
    convert congr_arg quiver.hom.op X.left_triangle using 1 },
  right_triangle' := by { ext1, ext1 R, erw category.id_comp, exact right_triangle R.unop } }
/- left and right triangle identities above are slow. -/

/-- The adjunction `Γ ⊣ Spec`. -/
def adjunction := adjunction.mk_of_unit_counit core_unit_counit

end Γ_Spec

/- Easy consequences of the adjunction. -/

/-- Spec preserves limits. -/
def Spec_preserves_limits := adjunction.right_adjoint_preserves_limits Γ_Spec.adjunction

/-- Spec is a full functor. -/
def Spec_full := @R_full_of_counit_is_iso
  _ _ _ _ _ _ Γ_Spec.adjunction (is_iso.of_iso_inv _)

/-- Spec is a faithful functor. -/
lemma Spec_faithful : faithful Spec.to_LocallyRingedSpace :=
  @R_faithful_of_counit_is_iso _ _ _ _ _ _ Γ_Spec.adjunction (is_iso.of_iso_inv _)

end algebraic_geometry
