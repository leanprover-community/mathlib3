/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Spec
import algebraic_geometry.ringed_space
import topology.sheaves.sheaf_condition.basis_le
import topology.sheaves.functors

/-!
# Adjunction between `Γ` and `Spec`

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

abbreviation Spec' := Spec.to_LocallyRingedSpace.obj (op R)

/- basic opens in Spec R -/
def basic_open_B : (Spec' R).to_Top.opens_index_struct := ⟨R, λ r, basic_open r⟩
-- Much nicer to work directly with the indexing function than the range set

private def idfb := induced_functor (op ∘ (basic_open_B R).f)

lemma basic_opens_is_basis {R} : Top.is_basis_range (basic_open_B R) := is_basis_basic_opens


/-
def comap_opens_map {R S : CommRing} (f : R ⟶ S) (U : opens (Spec' R)) :=
  comap f U ((opens.map $ Spec.Top_map f).obj U) (λ _, id)

lemma to_basic_open_comp_comap {S : CommRing} (f : R ⟶ S) (r : R) :
  to_open R (basic_open r) ≫ comap_opens_map f (basic_open r) =
  f ≫ to_open S (basic_open $ f r) := to_open_comp_comap' R f (basic_open r)
-/

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{v})

abbreviation Γ' := Γ.obj (op X)

/- map from the global sections to a stalk -/
def Γ_to_stalk (x : X) : Γ' X ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))
-- or @Top.presheaf.germ _ _ _ _ _ ⊤ ⟨x,trivial⟩

/- counit on the underlying set -/
def to_Γ_Spec_fun : X → Spec' (Γ' X) := λ x,
  comap (X.Γ_to_stalk x) (@local_ring.closed_point _ _ _ (X.local_ring x))
-- or Spec.to_Top.map (X.Γ_to_stalk x).op (@local_ring.closed_point ...)

lemma mem_ideal_Γ_to_stalk_iff (r : Γ' X) (x : X) :
  r ∉ (X.to_Γ_Spec_fun x).as_ideal ↔ is_unit (X.Γ_to_stalk x r) :=
by erw [local_ring.mem_maximal_ideal, not_not]; refl

/- preimage of a basic open under the counit is a basic open -/
lemma to_Γ_Spec_preim_basic_open_eq (r : Γ' X) :
  X.to_Γ_Spec_fun⁻¹' (basic_open r).1
  = (X.to_RingedSpace.basic_open r).1 :=
by ext; erw X.to_RingedSpace.mem_basic_open; apply mem_ideal_Γ_to_stalk_iff

/- counit is continuous -/
lemma to_Γ_Spec_continuous : continuous X.to_Γ_Spec_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintro _ ⟨r,rfl⟩, erw X.to_Γ_Spec_preim_basic_open_eq r,
  exact (X.to_RingedSpace.basic_open r).2,
end

def to_Γ_Spec_base : continuous_map X (Spec' (Γ' X)) :=
{ to_fun := X.to_Γ_Spec_fun,
  continuous_to_fun := X.to_Γ_Spec_continuous }

def opens_map_basic_open (r : Γ' X) := (opens.map X.to_Γ_Spec_base).obj (basic_open r)

lemma to_Γ_Spec_opens_map_obj_basic_open_eq (r : Γ' X) :
  X.opens_map_basic_open r = X.to_RingedSpace.basic_open r :=
subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

def to_opens_map_basic_open (r : Γ' X) :=
  X.presheaf.map (X.opens_map_basic_open r).le_top.op

def is_unit_res_opens_map_basic_open (r : Γ' X) :=
  by { have h := X.to_RingedSpace.is_unit_res_basic_open r,
  rw ← to_Γ_Spec_opens_map_obj_basic_open_eq at h, exact h }

def to_Γ_Spec_c_app (r : Γ' X) := CommRing.of_hom
(by { refine is_localization.away.lift r (is_unit_res_opens_map_basic_open _ r),
      swap 4, exact is_localization.to_basic_open _ r })

/- characterization of the sheaf morphism on basic opens,
   direction → used in proving naturality of the morphism,
   direction ← ... May be only ← direction is useful ... -/
lemma to_Γ_Spec_c_app_prop (r : Γ' X) :
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


def to_Γ_Spec_c_basic_opens : idfb _ ⋙ (Spec' (Γ' X)).presheaf
                          ⟶ idfb _ ⋙ X.to_Γ_Spec_base _* X.presheaf :=
{ app := X.to_Γ_Spec_c_app,
  naturality' := λ r s f, by {
    apply (to_basic_open_epi (Γ' X) r).1,
    simp only [←category.assoc],
    rw (X.to_Γ_Spec_c_app_prop r _).2 rfl,
    convert (X.to_Γ_Spec_c_app_prop s _).2 rfl,
    apply eq.symm, apply X.presheaf.map_comp } }

def to_Γ_Spec_c := Top.sheaf.uniq_hom_extn_from_basis _
  ((Top.sheaf.pushforward _).obj X.𝒪).2
  basic_opens_is_basis X.to_Γ_Spec_c_basic_opens

def to_Γ_Spec_SheafedSpace : X.to_SheafedSpace ⟶ (Spec' (Γ' X)).to_SheafedSpace :=
{ base := X.to_Γ_Spec_base,
  c := X.to_Γ_Spec_c.lift }

lemma to_Γ_Spec_SheafedSpace_app_eq (r : Γ' X) :
  X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_Γ_Spec_c_app r :=
by { change _ = X.to_Γ_Spec_c_basic_opens.app r, rw ← X.to_Γ_Spec_c.fac, refl }
/- once worked but now timeouts:
by change (whisker_left (idfb _) _).app r = _; erw X.to_Γ_Spec_c.fac; refl -/

-- write down the lemma explicitly ...
def to_Γ_Spec_SheafedSpace_app_prop (r : Γ' X) := by {
  have h := X.to_Γ_Spec_c_app_prop r,
  rw ← to_Γ_Spec_SheafedSpace_app_eq at h,
  exact h }
--#check to_Γ_Spec_SheafedSpace_app_prop

lemma to_stalk_comm (x : X) : to_stalk _ _ ≫
  PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x = X.Γ_to_stalk x :=
begin
  rw PresheafedSpace.stalk_map,
  erw ← to_open_germ _ (basic_open (1 : Γ' X))
    ⟨X.to_Γ_Spec_fun x, by rw basic_open_one; triv⟩,
  rw [←category.assoc, category.assoc (to_open _ _)],
  erw stalk_functor_map_germ,
  rw [←category.assoc (to_open _ _), (X.to_Γ_Spec_SheafedSpace_app_prop 1 _).2 rfl],
  unfold Γ_to_stalk, rw ← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤,
  congr' 1, change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _,
  apply germ_res,
end

def to_Γ_Spec : X ⟶ Spec' (Γ' X) :=
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
  rw ← mem_ideal_Γ_to_stalk_iff at hr,
  have hr' := hu ⟨r,hr⟩, erw ← he at hr',
  exact is_unit_of_mul_is_unit_left hr',
end

variables {Y : LocallyRingedSpace.{v}} (f : X ⟶ Y)

lemma to_Γ_Spec_base_naturality : (f ≫ Y.to_Γ_Spec).1.1 =
  (X.to_Γ_Spec ≫ (Γ.right_op ⋙ Spec.to_LocallyRingedSpace).map f).1.1 :=
begin
  ext1 x, convert congr_fun (congr_arg comap
    (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x,trivial⟩))
    (@local_ring.closed_point _ _ _ (X.local_ring x)),
  erw prime_spectrum.comap_comp, rw function.comp_apply,
  erw (@local_ring.local_hom_iff_comap_closed_point
        _ _ _ (Y.2 _) _ _ (X.2 x) _).1 (f.2 x), refl,
end

private def eha := nat_trans.app $ eq_to_hom $
  congr_arg (λ g, g _* X.presheaf) (X.to_Γ_Spec_base_naturality f)

lemma to_Γ_Spec_c_naturality (r : Γ' Y) : let f' := Γ.map f.op in
  (Y.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) ≫
    f.1.c.app (op $ Y.opens_map_basic_open r)) ≫ eha X f (op (basic_open r)) =
  comap f' (basic_open r) (basic_open $ f' r) (λ _ h, h)
    ≫ X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open (f' r))) :=
begin
  apply (to_basic_open_epi (Γ' Y) r).1, erw to_open_comp_comap_assoc,
  erw (X.to_Γ_Spec_SheafedSpace_app_prop (Γ.map f.op r) _).2 rfl,
  iterate 2 {rw ← category.assoc},
  rw (Y.to_Γ_Spec_SheafedSpace_app_prop r _).2 rfl,
  erw [f.1.c.naturality, category.assoc], congr, rw eha,
  rw [pushforward_eq'_hom_app, pushforward_obj_map, ←functor.map_comp],
  congr, exact X.to_Γ_Spec_base_naturality f,
end

def identity_Γ_Spec : 𝟭 LocallyRingedSpace ⟶ Γ.right_op ⋙ Spec.to_LocallyRingedSpace :=
{ app := to_Γ_Spec,
  naturality' := λ X Y f, begin
    ext1, ext1, swap, exact X.to_Γ_Spec_base_naturality f,
    apply Top.sheaf.hom_ext (basic_open_B (Γ' Y)) ((Top.sheaf.pushforward _).obj X.𝒪).2,
    exact basic_opens_is_basis, intro r,
    rw nat_trans.comp_app,
    iterate 2 {rw LocallyRingedSpace.comp_val_c_app'},
    convert X.to_Γ_Spec_c_naturality f r using 1,
  end }


end LocallyRingedSpace

end algebraic_geometry
