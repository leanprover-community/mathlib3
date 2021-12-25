/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.open_immersion
import ring_theory.nilpotent
import topology.sheaves.sheaf_condition.sites
import category_theory.limits.constructions.binary_products
import algebra.category.CommRing.constructions
import ring_theory.integral_domain

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `algebraic_geometry.is_integral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `algebraic_geometry.is_reduced`: A scheme is reduced if all the components of the structure sheaf
  is reduced.
-/

open topological_space opposite category_theory category_theory.limits Top

namespace algebraic_geometry

variable (X : Scheme)

-- TODO: add sober spaces, and show that schemes are sober
instance : t0_space X.carrier :=
begin
  rw t0_space_iff_distinguishable,
  intros x y h h',
  obtain ⟨U, R, ⟨e⟩⟩ := X.local_affine x,
  have hy := (h' _ U.1.2).mp U.2,
  erw ← subtype_indistinguishable_iff (⟨x, U.2⟩ : U.1.1) (⟨y, hy⟩ : U.1.1) at h',
  let e' : U.1 ≃ₜ prime_spectrum R :=
    homeo_of_iso ((LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget _).map_iso e),
  have := t0_space_of_injective_of_continuous e'.injective e'.continuous,
  rw t0_space_iff_distinguishable at this,
  exact this ⟨x, U.2⟩ ⟨y, hy⟩ (by simpa using h) h'
end

/-- A scheme `X` is integral if its carrier is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class is_integral : Prop :=
(nonempty : nonempty X.carrier . tactic.apply_instance)
(component_integral : ∀ (U : opens X.carrier) [_root_.nonempty U],
  is_domain (X.presheaf.obj (op U)) . tactic.apply_instance)

attribute [instance] is_integral.component_integral is_integral.nonempty

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
class is_reduced : Prop :=
(component_reduced : ∀ U, _root_.is_reduced (X.presheaf.obj (op U)) . tactic.apply_instance)

attribute [instance] is_reduced.component_reduced

lemma is_reduced_of_stalk_is_reduced [∀ x : X.carrier, _root_.is_reduced (X.presheaf.stalk x)] :
  is_reduced X :=
begin
  refine ⟨λ U, ⟨λ s hs, _⟩⟩,
  apply presheaf.section_ext X.sheaf U s 0,
  intro x,
  rw ring_hom.map_zero,
  change X.presheaf.germ x s = 0,
  exact (hs.map _).eq_zero
end

instance stalk_is_reduced_of_reduced [is_reduced X] (x : X.carrier) :
  _root_.is_reduced (X.presheaf.stalk x) :=
begin
  constructor,
  rintros g ⟨n, e⟩,
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.germ_exist x g,
  rw [← map_pow, ← map_zero (X.presheaf.germ ⟨x, hxU⟩)] at e,
  obtain ⟨V, hxV, iU, iV, e'⟩ := X.presheaf.germ_eq x hxU hxU _ 0 e,
  rw [map_pow, map_zero] at e',
  replace e' := (is_nilpotent.mk _ _ e').eq_zero,
  erw ← concrete_category.congr_hom (X.presheaf.germ_res iU ⟨x, hxV⟩) s,
  rw [comp_apply, e', map_zero]
end

lemma is_reduced_of_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  [is_reduced Y] : is_reduced X :=
begin
  constructor,
  intro U,
  have : U = (opens.map f.1.base).obj (H.base_open.is_open_map.functor.obj U),
  { ext1, exact (set.preimage_image_eq _ H.base_open.inj).symm },
  rw this,
  exact is_reduced_of_injective (inv $ f.1.c.app (op $ H.base_open.is_open_map.functor.obj U))
    (as_iso $ f.1.c.app (op $ H.base_open.is_open_map.functor.obj U) : Y.presheaf.obj _ ≅ _).symm
      .CommRing_iso_to_ring_equiv.injective
end

local attribute [elementwise] category_theory.is_iso.hom_inv_id

lemma basic_open_eq_of_affine {R : CommRing}
  (f : R) :
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

lemma eq_zero_of_basic_open_empty {X : Scheme} [is_reduced X] {U : opens X.carrier}
  (s : X.presheaf.obj (op U)) (hs : X.to_LocallyRingedSpace.to_RingedSpace.basic_open s = ∅) :
  s = 0 :=
begin
  apply Top.presheaf.section_ext X.sheaf U,
  intro x,
  obtain ⟨_,⟨j,rfl⟩,hx,i⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open x.prop U.2,
  let V : opens X.carrier := ⟨_, (X.affine_basis_cover.is_open j).base_open.open_range⟩,
  replace i : V ⟶ U := hom_of_le i,
  let s' : (X.affine_basis_cover.obj j).presheaf.obj (op $ (opens.map _).obj _) :=
    ((X.affine_basis_cover.map j).1.c.app (op V) (X.presheaf.map i.op s) : _),
  have Veq : V = (X.affine_basis_cover.is_open j).base_open
    .is_open_map.functor.obj ⟨_, is_open_univ⟩ := by simp [is_open_map.functor],
  have Veq' : (opens.map (X.affine_basis_cover.map j).val.base).obj V = ⊤,
  { rw Veq, ext1, exact set.preimage_image_eq _ (X.affine_basis_cover.is_open j).base_open.inj },
  suffices : s' = 0,
  { haveI : is_iso ((X.affine_basis_cover.map j).1.c.app (op V)),
    { rw Veq,
      exact PresheafedSpace.is_open_immersion.c_iso ⟨_, is_open_univ⟩ },
    have : X.presheaf.map i.op s = 0,
    { apply_fun (inv $ (X.affine_basis_cover.map j).1.c.app _) at this,
      rwa [category_theory.is_iso.hom_inv_id_apply, map_zero] at this },
    erw ← X.presheaf.germ_res_apply i ⟨↑x, hx⟩ s,
    rw [this, map_zero, map_zero] },
  replace hs : (X.affine_basis_cover.obj j).to_LocallyRingedSpace.to_RingedSpace.basic_open s' = ⊥,
  { rw ← LocallyRingedSpace.preimage_basic_open,
    erw RingedSpace.basic_open_res,
    ext1,
    simp [hs, opens.map] },
  clear_value s',
  revert s',
  erw Veq',
  intros s' hs,
  erw [basic_open_eq_of_affine', prime_spectrum.basic_open_empty_iff] at hs,
  replace hs := hs.map (Spec_Γ_identity.app (X.affine_basis_cover_ring j)).inv,
  erw category_theory.iso.hom_inv_id_apply at hs,
  haveI := is_reduced_of_open_immersion (X.affine_basis_cover.map j),
  apply is_nilpotent.eq_zero,
  exact hs,
end

lemma basic_open_empty_iff {X : Scheme} [is_reduced X] {U : opens X.carrier}
  (s : X.presheaf.obj $ op U) :
  X.to_LocallyRingedSpace.to_RingedSpace.basic_open s = ∅ ↔ s = 0 :=
begin
  refine ⟨eq_zero_of_basic_open_empty s, _⟩,
  rintro rfl,
  simp,
end

@[priority 900]
instance is_reduced_of_is_integral [is_integral X] : is_reduced X :=
begin
  constructor,
  intro U,
  cases U.1.eq_empty_or_nonempty,
  { have : U = ∅ := subtype.eq h,
    haveI := CommRing.subsingleton_of_is_terminal (X.sheaf.is_terminal_of_eq_empty this),
    change _root_.is_reduced (X.sheaf.val.obj (op U)),
    apply_instance },
  { haveI : nonempty U := by simpa, apply_instance }
end

instance is_irreducible_of_is_integral [is_integral X] : irreducible_space X.carrier :=
begin
  by_contradiction H,
  replace H : ¬ is_preirreducible (⊤ : set X.carrier) := λ h,
    H { to_preirreducible_space := ⟨h⟩, to_nonempty := infer_instance },
  simp_rw [is_preirreducible_iff_closed_union_closed, not_forall, not_or_distrib] at H,
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩,
  erw not_forall at h₂ h₃,
  simp_rw not_forall at h₂ h₃,
  haveI : nonempty (⟨Sᶜ, hS.1⟩ : opens X.carrier) := ⟨⟨_, h₂.some_spec.some_spec⟩⟩,
  haveI : nonempty (⟨Tᶜ, hT.1⟩ : opens X.carrier) := ⟨⟨_, h₃.some_spec.some_spec⟩⟩,
  haveI : nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : opens X.carrier) :=
    ⟨⟨_, or.inl h₂.some_spec.some_spec⟩⟩,
  let e : X.presheaf.obj _ ≅ CommRing.of _ := (X.sheaf.is_product_of_disjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ _)
    .cone_point_unique_up_to_iso (CommRing.prod_fan_is_limit _ _),
  apply_with false_of_nontrivial_of_product_domain { instances := ff },
  { exact e.symm.CommRing_iso_to_ring_equiv.is_domain _ },
  { apply X.to_LocallyRingedSpace.component_nontrivial },
  { apply X.to_LocallyRingedSpace.component_nontrivial },
  { ext x,
    split,
    { rintros ⟨hS,hT⟩,
      cases h₁ (show x ∈ ⊤, by trivial),
      exacts [hS h, hT h] },
    { intro x, exact x.rec _ } }
end

end algebraic_geometry
