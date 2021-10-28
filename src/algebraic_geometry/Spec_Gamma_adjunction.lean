/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Spec
import algebraic_geometry.ringed_space
import topology.sheaves.sheaf_condition.basis_le

/-!
# Adjunction between `Γ` and `Spec`

-/

noncomputable theory
universe variables u v

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf
open prime_spectrum
open topological_space
open algebraic_geometry.LocallyRingedSpace
open Top.presheaf
open Top.presheaf.sheaf_condition

def local_ring.closed_point (R : CommRing) [local_ring R] :
  prime_spectrum R :=
⟨local_ring.maximal_ideal R, (local_ring.maximal_ideal.is_maximal R).is_prime⟩
-- move to local_ring
-- to do : maximal ideals are closed points in the prime spectrum of any ring
-- minimal primes are generic points of irreducible components

lemma local_ring.comap_maximal_ideal {R S : CommRing}
  [local_ring R] [local_ring S] {f : R ⟶ S} : is_local_ring_hom f ↔
  comap f (local_ring.closed_point S) = local_ring.closed_point R :=
begin
  split, intro, resetI, ext,
  exact not_iff_not.2 (is_unit_map_iff f x),
  intro h, split, intro x, rw ← not_imp_not,
  change x ∈ (local_ring.closed_point R).1 → _,
  rw ← h, exact id,
end

variable (R : CommRing)

abbreviation Spec' := Spec.to_LocallyRingedSpace.obj (op R)

/- basic opens on Spec R -/
def basic_open_B : @Top.opens_index_struct (Spec' R).to_Top := ⟨R, λ r, basic_open r⟩
-- lesson: better directly work with the indexing function than the range set!

private def idfo := induced_functor (op ∘ (basic_open_B R).f)

lemma basic_opens_is_basis : Top.is_basis_range (basic_open_B R) :=
begin
  unfold Top.is_basis_range opens.is_basis basic_open_B,
  convert is_topological_basis_basic_opens,
  rw ← set.range_comp, dsimp, congr,
end

def sheaf_hom.extn_basic_opens {F G : (Spec' R).to_Top.presheaf CommRing} (h : G.is_sheaf)
  (α : idfo _ ⋙ F ⟶ idfo _ ⋙ G) : sheaf_hom.uniq_extn_struct α :=
sheaf_hom.uniq_extn_from_basis
  ((is_sheaf_iff_is_sheaf_opens_le_cover _).1 h)
  (basic_opens_is_basis _) α

def sheaf_hom.ext_basic_opens {F G : (Spec' R).to_Top.presheaf CommRing} (hs : G.is_sheaf)
  {α β : F ⟶ G} (h : whisker_left (idfo _) α = whisker_left (idfo _) β) : α = β :=
begin
  rw (sheaf_hom.extn_basic_opens _ hs _).uniq _ h,
  exact ((sheaf_hom.extn_basic_opens _ hs _).uniq _ rfl).symm,
end


def comap_opens_map {R S : CommRing} (f : R ⟶ S) (U : opens (Spec' R)) :=
  comap f U ((opens.map $ Spec.Top_map f).obj U) (λ _, id)

lemma to_open_comp_comap' {S : CommRing} (f : R ⟶ S) (U : opens (Spec' R)) :
  to_open R U ≫ comap_opens_map f U =
  f ≫ to_open S ((opens.map $ Spec.Top_map f).obj U) :=
ring_hom.ext $ λ r, subtype.eq $ funext $ λ p,
begin
  unfold comap_opens_map,
  simp_rw [comp_apply, comap_apply, subtype.val_eq_coe],
  erw localization.local_ring_hom_to_map, refl,
end

lemma to_basic_open_comp_comap {S : CommRing} (f : R ⟶ S) (r : R) :
  to_open R (basic_open r) ≫ comap_opens_map f (basic_open r) =
  f ≫ to_open S (basic_open $ f r) := to_open_comp_comap' R f (basic_open r)


lemma is_localization_iso_comp {M : submonoid R} {S T : CommRing}
  [i : algebra R S] [h : is_localization M S] (f : S ≅ T) :
  @is_localization _ _ M T _ (f.hom.comp i.to_ring_hom).to_algebra :=
{ map_units := let hm := h.1 in
    λ t, is_unit.map f.hom.to_monoid_hom (hm t),
  surj := let hs := h.2 in λ t, let ⟨⟨r,s⟩,he⟩ := hs (f.inv t) in ⟨⟨r,s⟩, by {
    convert congr_arg f.hom he, rw [ring_hom.map_mul, ←comp_apply, iso.inv_hom_id], refl}⟩,
  eq_iff_exists := let he := h.3 in λ t t', by { rw ← he, split,
    apply f.CommRing_iso_to_ring_equiv.injective, exact congr_arg f.hom } }

instance (r : R) : algebra R ((structure_sheaf R).1.obj (op $ basic_open r)) :=
  (to_open R (basic_open r)).to_algebra

/- instance of sections of structure sheaf on basic open as localization of the ring -/
instance is_localization.to_basic_open (r : R) :
  is_localization.away r ((structure_sheaf R).1.obj (op $ basic_open r)) :=
by { convert is_localization_iso_comp _ (basic_open_iso R r).symm, /- can't replace _ by R -/
  change ring_hom.to_algebra _ = _, congr' 1,
  exact (localization_to_basic_open R r).symm,
  exact localization.is_localization }

lemma to_basic_open_epi (r : R) : epi (to_open R (basic_open r)) :=
⟨λ S f g h, by { refine is_localization.ring_hom_ext _ _,
  swap 5, exact is_localization.to_basic_open _ r, exact h }⟩

instance (x : prime_spectrum R) : algebra R ((structure_sheaf R).1.stalk x) :=
  (to_stalk R x).to_algebra

instance (x : prime_spectrum R) :
  is_localization.at_prime ((structure_sheaf R).1.stalk x) x.as_ideal :=
by { convert is_localization_iso_comp _ (stalk_iso R x).symm,
  change ring_hom.to_algebra _ = _, congr' 1, erw iso.eq_comp_inv,
  exact to_stalk_comp_stalk_to_fiber_ring_hom R x,
  exact localization.is_localization }

namespace LocallyRingedSpace
variable (X : LocallyRingedSpace.{v})
abbreviation Γ' := Γ.obj (op X)

/- map from the global sections to a stalk -/
def Γ_to_stalk (x : X) : Γ' X ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))
  -- or @Top.presheaf.germ _ _ _ _ _ ⊤ ⟨x,trivial⟩

/- counit on the underlying set -/
def to_Γ_Spec_fun : X → Spec' (Γ' X) := λ x,
--Spec.to_Top.map (X.Γ_to_stalk x).op (@local_ring.closed_point _ _ (X.local_ring x))
comap (X.Γ_to_stalk x) (@local_ring.closed_point _ (X.local_ring x))

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

def to_Γ_Spec_Top : continuous_map X (Spec' (Γ' X)) :=
{ to_fun := X.to_Γ_Spec_fun,
  continuous_to_fun := X.to_Γ_Spec_continuous }

def opens_map_basic_open (r : Γ' X) := (opens.map X.to_Γ_Spec_Top).obj (basic_open r)

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
   direction ← ... -/
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


def to_Γ_Spec_c_basic_opens : idfo _ ⋙ (Spec' (Γ' X)).presheaf
                               ⟶ idfo _ ⋙ X.to_Γ_Spec_Top _* X.presheaf :=
{ app := X.to_Γ_Spec_c_app,
  naturality' := λ r s f, by {
    apply (to_basic_open_epi _ r).1,
    simp only [←category.assoc],
    rw (X.to_Γ_Spec_c_app_prop r _).2 rfl,
    convert (X.to_Γ_Spec_c_app_prop s _).2 rfl,
    apply eq.symm, apply X.presheaf.map_comp } }

def to_Γ_Spec_c := sheaf_hom.extn_basic_opens _
  (pushforward_sheaf_of_sheaf X.𝒪.2) X.to_Γ_Spec_c_basic_opens

def to_Γ_Spec_SheafedSpace : X.to_SheafedSpace ⟶ (Spec' (Γ' X)).to_SheafedSpace :=
{ base := X.to_Γ_Spec_Top,
  c := X.to_Γ_Spec_c.lift }

lemma to_Γ_Spec_SheafedSpace_app_eq (r : Γ' X) :
  X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_Γ_Spec_c_app r :=
by change (whisker_left (idfo _) _).app r = _; erw X.to_Γ_Spec_c.fac; refl

def to_Γ_Spec_SheafedSpace_app_prop (r : Γ' X) := by {
  have h := X.to_Γ_Spec_c_app_prop r,
  rw ← to_Γ_Spec_SheafedSpace_app_eq at h,
  exact h }

lemma to_stalk_comm (x : X) : to_stalk _ _ ≫
  PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x = X.Γ_to_stalk x :=
begin
  rw PresheafedSpace.stalk_map,
  erw ← to_open_germ _ (basic_open (1 : Γ' X))
    ⟨X.to_Γ_Spec_fun x, by rw basic_open_one; triv⟩,
  rw [←category.assoc, category.assoc (to_open _ _)],
  erw stalk_functor_map_germ,
  rw [←category.assoc (to_open _ _), (X.to_Γ_Spec_SheafedSpace_app_prop 1 _).2 rfl],
  unfold Γ_to_stalk, rw ← stalk_pushforward_germ _ X.to_Γ_Spec_Top X.presheaf ⊤,
  congr' 1, change (X.to_Γ_Spec_Top _* X.presheaf).map le_top.hom.op ≫ _ = _,
  apply germ_res,
end

def to_Γ_Spec : X ⟶ Spec' (Γ' X) :=
begin
  fsplit, exact X.to_Γ_Spec_SheafedSpace,
  intro x, let p : prime_spectrum (Γ' X) := X.to_Γ_Spec_fun x,
  fsplit, intros t ht,
  have h : is_localization.at_prime ((structure_sheaf (Γ' X)).1.stalk p) p.as_ideal,
  apply_instance,
  have he' := h.surj, rcases he' t with ⟨⟨r,s⟩,he⟩,
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

lemma Γ_map_eq : Γ.map f.op = f.1.c.app (op ⊤) := by
{ change _ ≫ X.presheaf.map (𝟙 _) = _,
  rw [X.presheaf.map_id, category.comp_id], refl }
/- this should be defeq, but due to an unnecessary additional composition in the definition
   of Γ.map, it's no longer so. To do: modify the definition in presheafed_space.lean. -/

lemma to_Γ_Spec_fun_naturality : f.1.1 ≫ Y.to_Γ_Spec.1.1 =
  X.to_Γ_Spec.1.1 ≫ ((Γ.right_op ⋙ Spec.to_LocallyRingedSpace).map f).1.1 :=
begin
  ext1 x, convert congr_fun (congr_arg comap
    (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x,trivial⟩))
    (@local_ring.closed_point _ (X.local_ring x)),
  { erw prime_spectrum.comap_comp, rw function.comp_apply,
    erw (@local_ring.comap_maximal_ideal _ _ (Y.2 _) (X.2 x) _).1 (f.2 x), refl },
  { erw prime_spectrum.comap_comp, rw [function.comp_apply, comp_apply],
    refine congr_fun _ (X.to_Γ_Spec_fun x), rw ← Γ_map_eq, refl },
end

/-
lemma to_Γ_Spec_sheaf_naturality (r : Γ' Y) :
  Y.to_Γ_Spec_sheaf_app r ≫ f.1.c.app (op (Y.opens_map_basic_open r)) =
  comap_opens_map (Γ.map f.op) (basic_open r) ≫ X.to_Γ_Spec_sheaf_app (Γ.map f.op r) :=

lemma to_Γ_Spec_sheaf_naturality (r : Γ' Y) : let f' := Γ.map f.op in
  Y.to_Γ_Spec_sheaf_app r ≫ f.1.c.app (op (Y.opens_map_basic_open r)) =
  comap f' (basic_open r) (basic_open $ f' r) (λ _ h, h) ≫ X.to_Γ_Spec_sheaf_app (f' r) :=
begin

end-/

-- algebraic_geometry.stalk_map_to_stalk
-- to_open_comp_comap

def identity_Γ_Spec : 𝟭 LocallyRingedSpace ⟶ Γ.right_op ⋙ Spec.to_LocallyRingedSpace :=
begin
  fsplit, exact to_Γ_Spec, intros X Y f, ext1, ext1, swap,
  exact X.to_Γ_Spec_fun_naturality f,
  apply sheaf_hom.ext_basic_opens (Γ' Y) (pushforward_sheaf_of_sheaf X.𝒪.2),
  ext1, ext1 r,-- dsimp,--apply (to_basic_open_epi _ r).1,
  --erw ← category.assoc, rw (Y.to_Γ_Spec_sheaf_app_prop r _).2 rfl,
end


end LocallyRingedSpace

end algebraic_geometry
