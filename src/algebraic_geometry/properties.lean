/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.AffineScheme
import ring_theory.nilpotent
import topology.sheaves.sheaf_condition.sites
import category_theory.limits.constructions.binary_products
import algebra.category.Ring.constructions
import ring_theory.integral_domain
import ring_theory.local_properties

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

instance : quasi_sober X.carrier :=
begin
  apply_with (quasi_sober_of_open_cover
    (set.range (λ x, set.range $ (X.affine_cover.map x).1.base)))
    { instances := ff },
  { rintro ⟨_,i,rfl⟩, exact (X.affine_cover.is_open i).base_open.open_range },
  { rintro ⟨_,i,rfl⟩,
    exact @@open_embedding.quasi_sober _ _ _
      (homeomorph.of_embedding _ (X.affine_cover.is_open i).base_open.to_embedding)
      .symm.open_embedding prime_spectrum.quasi_sober },
  { rw [set.top_eq_univ, set.sUnion_range, set.eq_univ_iff_forall],
    intro x, exact ⟨_, ⟨_, rfl⟩, X.affine_cover.covers x⟩ }
end

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

instance {R : CommRing} [H : _root_.is_reduced R] : is_reduced (Scheme.Spec.obj $ op R) :=
begin
  apply_with is_reduced_of_stalk_is_reduced { instances := ff },
  intro x, dsimp,
  haveI : _root_.is_reduced (CommRing.of $ localization.at_prime (prime_spectrum.as_ideal x)),
  { dsimp, apply_instance },
  exact is_reduced_of_injective (structure_sheaf.stalk_iso R x).hom
    (structure_sheaf.stalk_iso R x).CommRing_iso_to_ring_equiv.injective,
end

lemma affine_is_reduced_iff (R : CommRing) :
  is_reduced (Scheme.Spec.obj $ op R) ↔ _root_.is_reduced R :=
begin
  refine ⟨_, λ h, by exactI infer_instance⟩,
  intro h,
  resetI,
  haveI : _root_.is_reduced (LocallyRingedSpace.Γ.obj (op $ Spec.to_LocallyRingedSpace.obj $ op R)),
  { change _root_.is_reduced ((Scheme.Spec.obj $ op R).presheaf.obj $ op ⊤), apply_instance },
  exact is_reduced_of_injective (to_Spec_Γ R)
    ((as_iso $ to_Spec_Γ R).CommRing_iso_to_ring_equiv.injective)
end

lemma is_reduced_of_is_affine_is_reduced [is_affine X]
  [h : _root_.is_reduced (X.presheaf.obj (op ⊤))] : is_reduced X :=
begin
  haveI : is_reduced (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))),
  { rw affine_is_reduced_iff, exact h },
  exact is_reduced_of_open_immersion X.iso_Spec.hom,
end

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immerison `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
lemma reduce_to_affine_global (P : ∀ (X : Scheme) (U : opens X.carrier), Prop)
  (h₁ : ∀ (X : Scheme) (U : opens X.carrier),
    (∀ (x : U), ∃ {V} (h : x.1 ∈ V) (i : V ⟶ U), P X V) → P X U)
  (h₂ : ∀ {X Y} (f : X ⟶ Y) [hf : is_open_immersion f], ∃ {U : set X.carrier} {V : set Y.carrier}
    (hU : U = ⊤) (hV : V = set.range f.1.base), P X ⟨U, hU.symm ▸ is_open_univ⟩ →
      P Y ⟨V, hV.symm ▸ hf.base_open.open_range⟩)
  (h₃ : ∀ (R : CommRing), P (Scheme.Spec.obj $ op R) ⊤) :
  ∀ (X : Scheme) (U : opens X.carrier), P X U :=
begin
  intros X U,
  apply h₁,
  intro x,
  obtain ⟨_,⟨j,rfl⟩,hx,i⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open x.prop U.2,
  let U' : opens _ := ⟨_, (X.affine_basis_cover.is_open j).base_open.open_range⟩,
  let i' : U' ⟶ U :=
    hom_of_le i,
  refine ⟨U', hx, i', _⟩,
  obtain ⟨_,_,rfl,rfl,h₂'⟩ := h₂ (X.affine_basis_cover.map j),
  apply h₂',
  apply h₃
end
.
lemma reduce_to_affine_nbhd (P : ∀ (X : Scheme) (x : X.carrier), Prop)
  (h₁ : ∀ (R : CommRing) (x : prime_spectrum R), P (Scheme.Spec.obj $ op R) x)
  (h₂ : ∀ {X Y} (f : X ⟶ Y) [is_open_immersion f] (x : X.carrier), P X x → P Y (f.1.base x)) :
  ∀ (X : Scheme) (x : X.carrier), P X x :=
begin
  intros X x,
  obtain ⟨y, e⟩ := X.affine_cover.covers x,
  convert h₂ (X.affine_cover.map (X.affine_cover.f x)) y _,
  { rw e },
  apply h₁,
end

lemma eq_zero_of_basic_open_empty {X : Scheme} [hX : is_reduced X] {U : opens X.carrier}
  (s : X.presheaf.obj (op U)) (hs : X.basic_open s = ∅) :
  s = 0 :=
begin
  apply Top.presheaf.section_ext X.sheaf U,
  simp_rw ring_hom.map_zero,
  unfreezingI { revert X U hX s },
  refine reduce_to_affine_global _ _ _ _,
  { intros X U hx hX s hs x,
    obtain ⟨V, hx, i, H⟩ := hx x,
    unfreezingI { specialize H (X.presheaf.map i.op s) },
    erw Scheme.basic_open_res at H,
    rw [hs, ← subtype.coe_injective.eq_iff, opens.empty_eq, opens.inter_eq, inf_bot_eq] at H,
    specialize H rfl ⟨x, hx⟩,
    erw Top.presheaf.germ_res_apply at H,
    exact H },
  { rintros X Y f hf,
    have e : (f.val.base) ⁻¹' set.range ⇑(f.val.base) = ⊤,
    { rw [← set.image_univ, set.preimage_image_eq _ hf.base_open.inj, set.top_eq_univ] },
    refine ⟨_, _, e, rfl, _⟩,
    rintros H hX s hs ⟨_, x, rfl⟩,
    unfreezingI { haveI := is_reduced_of_open_immersion f },
    specialize H (f.1.c.app _ s) _ ⟨x, by { change x ∈ (f.val.base) ⁻¹' _, rw e, trivial }⟩,
    { rw [← Scheme.preimage_basic_open, hs], ext1, simp [opens.map] },
    { erw ← PresheafedSpace.stalk_map_germ_apply f.1 ⟨_,_⟩ ⟨x,_⟩ at H,
      apply_fun (inv $ PresheafedSpace.stalk_map f.val x) at H,
      erw [category_theory.is_iso.hom_inv_id_apply, map_zero] at H,
      exact H } },
  { intros R hX s hs x,
    erw [basic_open_eq_of_affine', prime_spectrum.basic_open_eq_bot_iff] at hs,
    replace hs := (hs.map (Spec_Γ_identity.app R).inv),
    -- what the hell?!
    replace hs := @is_nilpotent.eq_zero _ _ _ _ (show _, from _) hs,
    rw iso.hom_inv_id_apply at hs,
    rw [hs, map_zero],
    exact @@is_reduced.component_reduced hX ⊤ }
end

@[simp]
lemma basic_open_eq_bot_iff {X : Scheme} [is_reduced X] {U : opens X.carrier}
  (s : X.presheaf.obj $ op U) :
  X.basic_open s = ⊥ ↔ s = 0 :=
begin
  refine ⟨eq_zero_of_basic_open_empty s, _⟩,
  rintro rfl,
  simp,
end

/-- A scheme `X` is integral if its carrier is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class is_integral : Prop :=
(nonempty : nonempty X.carrier . tactic.apply_instance)
(component_integral : ∀ (U : opens X.carrier) [_root_.nonempty U],
  is_domain (X.presheaf.obj (op U)) . tactic.apply_instance)

attribute [instance] is_integral.component_integral is_integral.nonempty

instance [h : is_integral X] : is_domain (X.presheaf.obj (op ⊤)) :=
@@is_integral.component_integral _ _ (by simp)

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

lemma is_integral_of_is_irreducible_is_reduced [is_reduced X] [H : irreducible_space X.carrier] :
  is_integral X :=
begin
  split, refine λ U hU, ⟨λ a b e, _,
    (@@LocallyRingedSpace.component_nontrivial X.to_LocallyRingedSpace U hU).1⟩,
  simp_rw [← basic_open_eq_bot_iff, ← opens.not_nonempty_iff_eq_bot],
  by_contra' h,
  obtain ⟨_, ⟨x, hx₁, rfl⟩, ⟨x, hx₂, e'⟩⟩ := @@nonempty_preirreducible_inter _ H.1
    (X.basic_open a).2 (X.basic_open b).2
    h.1 h.2,
  replace e' := subtype.eq e',
  subst e',
  replace e := congr_arg (X.presheaf.germ x) e,
  rw [ring_hom.map_mul, ring_hom.map_zero] at e,
  refine @zero_ne_one (X.presheaf.stalk x.1) _ _ (is_unit_zero_iff.1 _),
  convert hx₁.mul hx₂,
  exact e.symm
end

lemma is_integral_iff_is_irreducible_and_is_reduced :
  is_integral X ↔ irreducible_space X.carrier ∧ is_reduced X :=
⟨λ _, by exactI ⟨infer_instance, infer_instance⟩,
  λ ⟨_, _⟩, by exactI is_integral_of_is_irreducible_is_reduced X⟩

lemma is_integral_of_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  [is_integral Y] [nonempty X.carrier] : is_integral X :=
begin
  constructor,
  intros U hU,
  have : U = (opens.map f.1.base).obj (H.base_open.is_open_map.functor.obj U),
  { ext1, exact (set.preimage_image_eq _ H.base_open.inj).symm },
  rw this,
  haveI : is_domain (Y.presheaf.obj (op (H.base_open.is_open_map.functor.obj U))),
  { apply_with is_integral.component_integral { instances := ff },
    apply_instance,
    refine ⟨⟨_, _, hU.some.prop, rfl⟩⟩ },
  exact (as_iso $ f.1.c.app (op $ H.base_open.is_open_map.functor.obj U) :
    Y.presheaf.obj _ ≅ _).symm.CommRing_iso_to_ring_equiv.is_domain _
end

instance {R : CommRing} [H : is_domain R] : is_integral (Scheme.Spec.obj $ op R) :=
begin
  apply_with is_integral_of_is_irreducible_is_reduced { instances := ff },
  { apply_instance },
  { dsimp [Spec.Top_obj],
    apply_instance },
end

lemma affine_is_integral_iff (R : CommRing) :
  is_integral (Scheme.Spec.obj $ op R) ↔ is_domain R :=
⟨λ h, by exactI ring_equiv.is_domain ((Scheme.Spec.obj $ op R).presheaf.obj _)
  (as_iso $ to_Spec_Γ R).CommRing_iso_to_ring_equiv, λ h, by exactI infer_instance⟩

lemma is_integral_of_is_affine_is_domain [is_affine X] [nonempty X.carrier]
  [h : is_domain (X.presheaf.obj (op ⊤))] : is_integral X :=
begin
  haveI : is_integral (Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))),
  { rw affine_is_integral_iff, exact h },
  exact is_integral_of_open_immersion X.iso_Spec.hom,
end

lemma map_injective_of_is_integral [is_integral X] {U V : opens X.carrier} (i : U ⟶ V)
  [H : nonempty U] :
  function.injective (X.presheaf.map i.op) :=
begin
  rw injective_iff_map_eq_zero,
  intros x hx,
  rw ← basic_open_eq_bot_iff at ⊢ hx,
  rw Scheme.basic_open_res at hx,
  revert hx,
  contrapose!,
  simp_rw [← opens.not_nonempty_iff_eq_bot, not_not],
  apply nonempty_preirreducible_inter U.prop (RingedSpace.basic_open _ _).prop,
  simpa using H
end

end algebraic_geometry
