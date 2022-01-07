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

namespace topological_space

lemma _root_.topological_space.opens.not_nonempty_iff_eq_bot {α : Type*} [topological_space α] (U : opens α) :
  ¬ set.nonempty (U : set α) ↔ U = ⊥ :=
by rw [← subtype.coe_injective.eq_iff, opens.coe_bot, ← set.not_nonempty_iff_eq_empty]

lemma _root_.topological_space.opens.ne_bot_iff_nonempty {α : Type*} [topological_space α] (U : opens α) :
  U ≠ ⊥ ↔ set.nonempty (U : set α) :=
by rw [ne.def, ← opens.not_nonempty_iff_eq_bot, not_not]

@[simp] lemma _root_.topological_space.opens.top_coe (α : Type*) [topological_space α] :
  ((⊤ : opens α) : set α) = set.univ := rfl


end topological_space

namespace is_localization

variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] (T : Type*) [comm_ring T] {P : Type*} [comm_ring P]

variables {S T}

lemma is_localization_of_alg_equiv [algebra R T] [is_localization M S] (h : S ≃ₐ[R] T) :
  is_localization M T :=
begin
  constructor,
  { intro y,
    convert (is_localization.map_units S y).map h.to_alg_hom.to_ring_hom.to_monoid_hom,
    exact (h.commutes y).symm },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj M (h.symm y),
    apply_fun h at e,
    simp only [h.map_mul, h.apply_symm_apply, h.commutes] at e,
    exact ⟨⟨x, s⟩, e⟩ },
  { intros x y,
    rw [← h.symm.to_equiv.injective.eq_iff, ← is_localization.eq_iff_exists M S,
      ← h.symm.commutes, ← h.symm.commutes],
    refl }
end

lemma is_localization_iff_of_alg_equiv [algebra R T] (h : S ≃ₐ[R] T) :
  is_localization M S ↔ is_localization M T :=
⟨λ _, by exactI is_localization_of_alg_equiv M h,
  λ _, by exactI is_localization_of_alg_equiv M h.symm⟩

lemma is_localization_iff_of_ring_equiv (h : S ≃+* T) :
  is_localization M S ↔
    @@is_localization _ M T _ (h.to_ring_hom.comp $ algebra_map R S).to_algebra :=
begin
  letI := (h.to_ring_hom.comp $ algebra_map R S).to_algebra,
  exact is_localization_iff_of_alg_equiv M { commutes' := λ _, rfl, ..h },
end

lemma is_localization_of_base_ring_equiv [is_localization M S] (h : R ≃+* T) :
  @@is_localization _ (M.map h.to_monoid_hom) S _
    ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  constructor,
  { rintros ⟨_, ⟨y, hy, rfl⟩⟩,
    convert is_localization.map_units S ⟨y, hy⟩,
    dsimp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply],
    exact congr_arg _ (h.symm_apply_apply _) },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj M y,
    refine ⟨⟨h x, _, _, s.prop, rfl⟩, _⟩,
    dsimp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply] at ⊢ e,
    convert e; exact h.symm_apply_apply _ },
  { intros x y,
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply, ring_hom.comp_apply,
      is_localization.eq_iff_exists M S],
    simp_rw ← h.to_equiv.apply_eq_iff_eq,
    change (∃ (c : M), h (h.symm x * c) = h (h.symm y * c)) ↔ _,
    simp only [ring_equiv.apply_symm_apply, ring_equiv.map_mul],
    exact ⟨λ ⟨c, e⟩, ⟨⟨_, _, c.prop, rfl⟩, e⟩, λ ⟨⟨_, c, h, e₁⟩, e₂⟩, ⟨⟨_, h⟩, e₁.symm ▸ e₂⟩⟩ }
end

lemma is_localization_iff_of_base_ring_equiv (h : R ≃+* T) :
  is_localization M S ↔ @@is_localization _ (M.map h.to_monoid_hom) S _
    ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  refine ⟨λ _, by exactI is_localization_of_base_ring_equiv _ h, _⟩,
  letI := ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra,
  intro H,
  convert @@is_localization_of_base_ring_equiv _ _ _ _ _ H h.symm,
  { erw [submonoid.map_equiv_eq_comap_symm, submonoid.comap_map_eq_of_injective],
    exact h.to_equiv.injective },
  rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_assoc],
  simp only [ring_hom.comp_id, ring_equiv.symm_symm, ring_equiv.symm_to_ring_hom_comp_to_ring_hom],
  apply algebra.algebra_ext,
  intro r,
  rw ring_hom.algebra_map_to_algebra
end

lemma is_fraction_ring_iff_of_base_ring_equiv (h : R ≃+* T) :
  is_fraction_ring R S ↔
    @@is_fraction_ring T _ S _ ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  delta is_fraction_ring,
  convert @@is_localization_iff_of_base_ring_equiv _ _ _ _ _ h,
  ext x,
  erw submonoid.map_equiv_eq_comap_symm,
  simp only [mul_equiv.coe_to_monoid_hom,
    ring_equiv.to_mul_equiv_eq_coe, submonoid.mem_comap],
  split,
  { rintros hx z (hz : z * h.symm x = 0),
    rw ← h.map_eq_zero_iff,
    apply hx,
    simpa only [h.map_zero, h.apply_symm_apply, h.map_mul] using congr_arg h hz },
  { rintros (hx : h.symm x ∈ _) z hz,
    rw ← h.symm.map_eq_zero_iff,
    apply hx,
    rw [← h.symm.map_mul, hz, h.symm.map_zero] }
end

noncomputable
lemma localization_algebra_of_submonoid_le
  {R S T: Type*} [comm_ring R] [comm_ring S] [comm_ring T] [algebra R S] [algebra R T]
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T] :
  algebra S T :=
begin
  apply ring_hom.to_algebra,
  apply @is_localization.lift _ _ M _ _ _ _ _ _ (algebra_map _ _),
  any_goals { apply_instance },
  intro y,
  apply is_localization.map_units T ⟨_, h y.prop⟩,
end

lemma localization_is_scalar_tower_of_submonoid_le
  {R S T: Type*} [comm_ring R] [comm_ring S] [comm_ring T] [algebra R S] [algebra R T]
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T] :
  (by { letI : algebra S T := localization_algebra_of_submonoid_le M N h,
    exact is_scalar_tower R S T }) :=
begin
  apply is_scalar_tower.of_algebra_map_eq',
  delta localization_algebra_of_submonoid_le,
  exact (is_localization.lift_comp _).symm,
end

noncomputable
instance {R : Type*} [comm_ring R] (x : ideal R) [H : x.is_prime] [is_domain R] :
  algebra (localization.at_prime x) (localization (non_zero_divisors R)) :=
localization_algebra_of_submonoid_le x.prime_compl (non_zero_divisors R)
  (by { intros a ha, rw mem_non_zero_divisors_iff_ne_zero, exact λ h, ha (h.symm ▸ x.zero_mem) })

lemma exist_image_iff {α β : Type*} (f : α → β) (x : set α) (P : β → Prop) :
  (∃ (a : f '' x), P a) ↔ ∃ (a : x), P (f a) :=
⟨λ h, ⟨⟨_, h.some.prop.some_spec.1⟩, h.some.prop.some_spec.2.symm ▸ h.some_spec⟩,
  λ h, ⟨⟨_, _, h.some.prop, rfl⟩, h.some_spec⟩⟩

variables (S T)

lemma is_localization_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [algebra R T] [is_localization N T]
  [algebra S T] [is_scalar_tower R S T] :
  is_localization (N.map (algebra_map R S).to_monoid_hom) T :=
begin
  constructor,
  { rintro ⟨_, ⟨y, hy, rfl⟩⟩,
    convert is_localization.map_units T ⟨y, hy⟩,
    exact (is_scalar_tower.algebra_map_apply _ _ _ _).symm },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj N y,
    refine ⟨⟨algebra_map _ _ x, _, _, s.prop, rfl⟩, _⟩,
    simpa [← is_scalar_tower.algebra_map_apply] using e },
  { intros x₁ x₂,
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := is_localization.surj M x₁,
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := is_localization.surj M x₂,
    refine iff.trans _ (exist_image_iff (algebra_map R S) N (λ c, x₁ * c = x₂ * c)).symm,
    rw [← (is_localization.map_units T ⟨_, h s₁.prop⟩).mul_left_inj,
        ← (is_localization.map_units T ⟨_, h s₂.prop⟩).mul_right_inj],
    simp_rw [is_scalar_tower.algebra_map_apply R S T, ← map_mul],
    dsimp only [subtype.coe_mk] at e₁ e₂ ⊢,
    rw [e₁, ← mul_assoc, mul_comm _ x₂, e₂],
    simp_rw [← map_mul, ← is_scalar_tower.algebra_map_apply R S T],
    rw is_localization.eq_iff_exists N T,
    simp only [← (is_localization.map_units S s₁).mul_right_inj] { single_pass := tt },
    simp only [← @is_unit.mul_right_inj _ _ _ _ (_ * (x₂ * _)) (is_localization.map_units S s₂)]
      { single_pass := tt },
    simp only [← mul_assoc] { single_pass := tt },
    simp only [mul_comm _ x₁, mul_comm _ x₂, ← mul_assoc _ x₂, e₁, e₂, ← map_mul,
      is_localization.eq_iff_exists M S],
    split,
    { rintro ⟨a, e⟩, exact ⟨a, 1, by simpa using e⟩ },
    { rintro ⟨a, b, e⟩, exact ⟨a * (⟨_, h b.prop⟩ : N), by simpa [mul_assoc] using e⟩ } }
end

lemma is_localization_of_is_exists_mul_mem
  {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*)
    [comm_ring S] [algebra R S] [is_localization M S] (N : submonoid R) (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : is_localization N S :=
begin
  constructor,
  { intro y,
    obtain ⟨m, hm⟩ := h' y,
    have := is_localization.map_units S ⟨_, hm⟩,
    erw map_mul at this,
    exact (is_unit.mul_iff.mp this).2 },
  { intro z,
    obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M z,
    exact ⟨⟨y, _, h s.prop⟩, e⟩ },
  { intros x₁ x₂,
    rw is_localization.eq_iff_exists M,
    refine ⟨λ ⟨x, hx⟩, ⟨⟨_, h x.prop⟩, hx⟩, _⟩,
    rintros ⟨x, h⟩,
    obtain ⟨m, hm⟩ := h' x,
    refine ⟨⟨_, hm⟩, _⟩,
    simp [mul_comm m, ← mul_assoc, h] }
end

end is_localization

open topological_space opposite category_theory category_theory.limits Top

namespace Top.presheaf

noncomputable
def stalk_specializes {C : Type*} [category C] [has_colimits C] {X : Top} (F : X.presheaf C)
  {x y : X} (h : x ⤳ y) : F.stalk y ⟶ F.stalk x :=
begin
  refine colimit.desc _ ⟨_,λ U, _,_⟩,
  { exact colimit.ι ((open_nhds.inclusion x).op ⋙ F)
      (op ⟨(unop U).1, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩) },
  { intros U V i,
    dsimp,
    rw category.comp_id,
    let U' : open_nhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop U).1.2 (unop U).2 : _)⟩,
    let V' : open_nhds x := ⟨_, (specializes_iff_forall_open.mp h _ (unop V).1.2 (unop V).2 : _)⟩,
    exact colimit.w ((open_nhds.inclusion x).op ⋙ F) (show V' ⟶ U', from i.unop).op }
end

@[simp, reassoc, elementwise]
lemma germ_stalk_specializes {C : Type*} [category C] [has_colimits C] {X : Top}
  (F : X.presheaf C) {U : opens X} {y : U} {x : X} (h : x ⤳ y) :
  F.germ y ≫ F.stalk_specializes h =
    F.germ ⟨x, specializes_iff_forall_open.mp h _ U.2 y.prop⟩ := colimit.ι_desc _ _

@[simp, reassoc, elementwise]
lemma germ_stalk_specializes' {C : Type*} [category C] [has_colimits C] {X : Top}
  (F : X.presheaf C) {U : opens X} {x y : X} (h : x ⤳ y) (hy : y ∈ U) :
  F.germ ⟨y, hy⟩ ≫ F.stalk_specializes h =
    F.germ ⟨x, specializes_iff_forall_open.mp h _ U.2 hy⟩ := colimit.ι_desc _ _

@[simp, reassoc, elementwise]
lemma stalk_specializes_stalk_functor_map {C : Type*} [category C] [has_colimits C] {X : Top}
  {F G : X.presheaf C} (f : F ⟶ G) {x y : X} (h : x ⤳ y) :
  F.stalk_specializes h ≫ (stalk_functor C x).map f =
    (stalk_functor C y).map f ≫ G.stalk_specializes h :=
by { ext, delta stalk_functor, simpa [stalk_specializes] }

@[simp, reassoc, elementwise]
lemma pushforward_stalk_specializes {C : Type*} [category C] [has_colimits C] {X Y : Top}
  (f : X ⟶ Y) (F : X.presheaf C) {x y : X} (h : x ⤳ y) :
  (f _* F).stalk_specializes (f.map_specialization h) ≫ F.stalk_pushforward _ f x =
F.stalk_pushforward _ f y ≫ F.stalk_specializes h :=
by { ext, delta stalk_pushforward, simpa [stalk_specializes] }

end Top.presheaf

namespace algebraic_geometry.structure_sheaf
open algebraic_geometry

noncomputable
def stalk_algebra_of_specializes {R : Type*} [comm_ring R] {x y : prime_spectrum R}
  (h : x ⤳ y) :
  algebra (localization.at_prime y.as_ideal) (localization.at_prime x.as_ideal) :=
begin
  apply is_localization.localization_algebra_of_submonoid_le
    y.as_ideal.prime_compl x.as_ideal.prime_compl _,
  any_goals { apply_instance },
  apply set.compl_subset_compl.mpr,
  apply (prime_spectrum.le_iff_mem_closure x y).mpr,
  exact h
end

@[simp, reassoc, elementwise]
lemma to_stalk_stalk_specializes {R : Type*} [comm_ring R]
  {x y : prime_spectrum R} (h : x ⤳ y) :
  to_stalk R y ≫ (structure_sheaf R).val.stalk_specializes h = to_stalk R x :=
by { dsimp [ to_stalk], simpa }

@[simp, reassoc, elementwise]
lemma localization_to_stalk_stalk_specializes {R : Type*} [comm_ring R]
  {x y : prime_spectrum R} (h : x ⤳ y) :
  structure_sheaf.localization_to_stalk R y ≫ (structure_sheaf R).val.stalk_specializes h =
    CommRing.of_hom (@@algebra_map _ _ _ _ (stalk_algebra_of_specializes h)) ≫
      structure_sheaf.localization_to_stalk R x :=
begin
  delta stalk_algebra_of_specializes is_localization.localization_algebra_of_submonoid_le,
  rw ring_hom.algebra_map_to_algebra,
  apply is_localization.ring_hom_ext y.as_ideal.prime_compl,
  any_goals { dsimp, apply_instance },
  erw ring_hom.comp_assoc,
  conv_rhs { erw ring_hom.comp_assoc },
  dsimp [CommRing.of_hom, localization_to_stalk],
  rw [is_localization.lift_comp, is_localization.lift_comp, is_localization.lift_comp],
  exact to_stalk_stalk_specializes h
end

@[simp, reassoc, elementwise]
lemma stalk_specializes_stalk_to_fiber {R : Type*} [comm_ring R]
  {x y : prime_spectrum R} (h : x ⤳ y) :
  (structure_sheaf R).val.stalk_specializes h ≫ structure_sheaf.stalk_to_fiber_ring_hom R x =
    structure_sheaf.stalk_to_fiber_ring_hom R y ≫
      @@algebra_map _ _ _ _ (stalk_algebra_of_specializes h) :=
begin
  change _ ≫ (structure_sheaf.stalk_iso R x).hom = (structure_sheaf.stalk_iso R y).hom ≫ _,
  rw [← iso.eq_comp_inv, category.assoc, ← iso.inv_comp_eq],
  exact localization_to_stalk_stalk_specializes h,
end

lemma stalk_specializes_eq_of_affine {R : Type*} [comm_ring R]
  {x y : prime_spectrum R} (h : x ⤳ y) :
  (structure_sheaf R).val.stalk_specializes h = (structure_sheaf.stalk_iso R y).hom ≫
    CommRing.of_hom (@@algebra_map _ _ _ _ (stalk_algebra_of_specializes h)) ≫
    (structure_sheaf.stalk_iso R x).inv :=
begin
  erw [← stalk_specializes_stalk_to_fiber_assoc, (structure_sheaf.stalk_iso R x).hom_inv_id],
  simp,
end


end algebraic_geometry.structure_sheaf

namespace algebraic_geometry.PresheafedSpace
open algebraic_geometry

@[simp, reassoc, elementwise]
lemma stalk_specializes_stalk_map {C : Type*} [category C] [has_colimits C]
  {X Y : PresheafedSpace C} (f : X ⟶ Y) {x y : X} (h : x ⤳ y) :
  Y.presheaf.stalk_specializes (f.base.map_specialization h) ≫ stalk_map f x =
    stalk_map f y ≫ X.presheaf.stalk_specializes h :=
by { delta PresheafedSpace.stalk_map, simp [stalk_map] }

end algebraic_geometry.PresheafedSpace

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

lemma basic_open_eq_of_affine {R : CommRing} (f : R) :
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
  (s : X.presheaf.obj (op U)) (hs : X.to_LocallyRingedSpace.to_RingedSpace.basic_open s = ∅) :
  s = 0 :=
begin
  apply Top.presheaf.section_ext X.sheaf U,
  simp_rw ring_hom.map_zero,
  tactic.unfreeze_local_instances,
  revert X U hX s,
  refine reduce_to_affine_global _ _ _ _,
  { intros X U hx hX s hs x,
    obtain ⟨V, hx, i, H⟩ := hx x,
    specialize H (X.presheaf.map i.op s),
    erw RingedSpace.basic_open_res at H,
    rw [hs, ← subtype.coe_injective.eq_iff, opens.empty_eq, opens.inter_eq, inf_bot_eq] at H,
    specialize H rfl ⟨x, hx⟩,
    erw Top.presheaf.germ_res_apply at H,
    exact H },
  { rintros X Y f hf,
    have e : (f.val.base) ⁻¹' set.range ⇑(f.val.base) = ⊤,
    { rw [← set.image_univ, set.preimage_image_eq _ hf.base_open.inj, set.top_eq_univ] },
    refine ⟨_, _, e, rfl, _⟩,
    rintros H hX s hs ⟨_, x, rfl⟩,
    haveI := is_reduced_of_open_immersion f,
    specialize H (f.1.c.app _ s) _ ⟨x, by { change x ∈ (f.val.base) ⁻¹' _, rw e, trivial }⟩,
    { rw [← LocallyRingedSpace.preimage_basic_open, hs], ext1, simp [opens.map] },
    { erw ← PresheafedSpace.stalk_map_germ_apply f.1 ⟨_,_⟩ ⟨x,_⟩ at H,
      apply_fun (inv $ PresheafedSpace.stalk_map f.val x) at H,
      erw [category_theory.is_iso.hom_inv_id_apply, map_zero] at H,
      exact H } },
  { intros R hX s hs x,
    erw [basic_open_eq_of_affine', prime_spectrum.basic_open_eq_bot_iff] at hs,
    replace hs := (hs.map (Spec_Γ_identity.app R).inv).eq_zero,
    rw coe_hom_inv_id at hs,
    rw [hs, map_zero],
    exact @@is_reduced.component_reduced hX ⊤ }
end

@[simp]
lemma basic_open_eq_bot_iff {X : Scheme} [is_reduced X] {U : opens X.carrier}
  (s : X.presheaf.obj $ op U) :
  X.to_LocallyRingedSpace.to_RingedSpace.basic_open s = ⊥ ↔ s = 0 :=
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
  split,
  intros U hU,
  split,
  { intros a b e,
    simp_rw [← basic_open_eq_bot_iff, ← opens.not_nonempty_iff_eq_bot],
    by_contra h,
    push_neg at h,
    exfalso,
    obtain ⟨_, ⟨x, hx₁, rfl⟩, ⟨x, hx₂, e'⟩⟩ := @@nonempty_preirreducible_inter _ H.1
      (X.to_LocallyRingedSpace.to_RingedSpace.basic_open a).2
      (X.to_LocallyRingedSpace.to_RingedSpace.basic_open b).2
      h.1 h.2,
    replace e' := subtype.eq e',
    subst e',
    replace e := congr_arg (X.presheaf.germ x) e,
    rw [ring_hom.map_mul, ring_hom.map_zero] at e,
    apply @zero_ne_one (X.presheaf.stalk x.1),
    rw ← is_unit_zero_iff,
    convert hx₁.mul hx₂,
    exact e.symm },
  exact (@@LocallyRingedSpace.component_nontrivial X.to_LocallyRingedSpace U hU).1,
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

lemma map_injective_of_is_integral [is_integral X] {U V : opens X.carrier} (i : U ⟶ V)
  [H : nonempty U] :
  function.injective (X.presheaf.map i.op) :=
begin
  rw ring_hom.injective_iff,
  intros x hx,
  rw ← basic_open_eq_bot_iff at ⊢ hx,
  erw RingedSpace.basic_open_res at hx,
  revert hx,
  contrapose!,
  simp_rw [← opens.not_nonempty_iff_eq_bot, not_not, unop_op],
  apply nonempty_preirreducible_inter U.prop (RingedSpace.basic_open _ _).prop,
  simpa using H
end

lemma germ_injective_of_is_integral [is_integral X] {U : opens X.carrier} (x : U) :
  function.injective (X.presheaf.germ x) :=
begin
  rw ring_hom.injective_iff,
  intros y hy,
  rw ← (X.presheaf.germ x).map_zero at hy,
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ x.prop x.prop _ _ hy,
  cases (show iU = iV, from subsingleton.elim _ _),
  haveI : nonempty W := ⟨⟨_, hW⟩⟩,
  exact map_injective_of_is_integral X iU e
end

lemma Scheme.germ_to_function_field_injective [is_integral X] (U : opens X.carrier)
  [nonempty U] : function.injective (X.germ_to_function_field U) :=
germ_injective_of_is_integral _ _

instance {R : CommRing} [H : _root_.is_reduced R] : is_reduced (Scheme.Spec.obj $ op R) :=
begin
  apply_with is_reduced_of_stalk_is_reduced { instances := ff },
  intro x, dsimp,
  haveI : _root_.is_reduced (CommRing.of $ localization.at_prime (prime_spectrum.as_ideal x)),
  { dsimp, apply_instance },
  exact is_reduced_of_injective (structure_sheaf.stalk_iso R x).hom
    (structure_sheaf.stalk_iso R x).CommRing_iso_to_ring_equiv.injective,
end

instance {R : CommRing} [H : is_domain R] : is_integral (Scheme.Spec.obj $ op R) :=
begin
  apply_with is_integral_of_is_irreducible_is_reduced { instances := ff },
  apply_instance,
  dsimp [Spec.Top_obj],
  apply_instance,
end

lemma affine_is_integral_iff (R : CommRing) :
  is_integral (Scheme.Spec.obj $ op R) ↔ is_domain R :=
⟨λ h, by exactI ring_equiv.is_domain ((Scheme.Spec.obj $ op R).presheaf.obj _)
  (as_iso $ to_Spec_Γ R).CommRing_iso_to_ring_equiv, λ h, by exactI infer_instance⟩

noncomputable
instance stalk_function_field_algebra [is_integral X] (x : X.carrier) :
  algebra (X.presheaf.stalk x) X.function_field :=
begin
  apply ring_hom.to_algebra,
  exact X.presheaf.stalk_specializes ((generic_point_spec X.carrier).specializes trivial)
end

noncomputable
instance (R : CommRing) [is_domain R] : algebra R (Scheme.Spec.obj $ op R).function_field :=
begin
  apply ring_hom.to_algebra,
  exact structure_sheaf.to_stalk R _,
end

@[simp] lemma generic_point_eq_bot_of_affine (R : CommRing) [is_domain R] :
  generic_point (Scheme.Spec.obj $ op R).carrier = (⟨0, ideal.bot_prime⟩ : prime_spectrum R) :=
begin
  apply (generic_point_spec (Scheme.Spec.obj $ op R).carrier).eq,
  simp [is_generic_point_def, ← prime_spectrum.zero_locus_vanishing_ideal_eq_closure]
end

instance function_field_is_fraction_ring_of_affine (R : CommRing.{u}) [is_domain R] :
  is_fraction_ring R (Scheme.Spec.obj $ op R).function_field :=
begin
  apply (is_localization.is_localization_iff_of_ring_equiv _
    (structure_sheaf.stalk_iso _ _).CommRing_iso_to_ring_equiv).mpr,
  convert localization.is_localization,
  { rw generic_point_eq_bot_of_affine, ext, exact mem_non_zero_divisors_iff_ne_zero },
  apply algebra.algebra_ext,
  intro _, congr' 1,
  delta function_field.algebra,
  rw [ring_hom.algebra_map_to_algebra, ring_hom.algebra_map_to_algebra],
  dsimp,
  exact structure_sheaf.to_stalk_comp_stalk_to_fiber_ring_hom R _,
end
.

lemma affine_function_field_is_fraction_ring_of_stalk_aux
  (R : CommRing) [is_domain R] (x : prime_spectrum R) :
  ((algebra_map ((Scheme.Spec.obj $ op R).presheaf.stalk x)
    ((Scheme.Spec.obj $ op R).function_field)).comp
      (structure_sheaf.localization_to_stalk R x)).to_algebra =
  (is_localization.localization_algebra_of_submonoid_le x.as_ideal.prime_compl
    (non_zero_divisors R) (by { intros a ha, rw mem_non_zero_divisors_iff_ne_zero,
      exact λ h, ha (h.symm ▸ x.as_ideal.zero_mem) }) :
        algebra (localization.at_prime x.as_ideal) _) :=
begin
  apply algebra.algebra_ext, intro y, congr' 1,
  refine (structure_sheaf.localization_to_stalk_stalk_specializes _).trans _,
  dsimp,
  apply is_localization.ring_hom_ext x.as_ideal.prime_compl,
  any_goals { dsimp, apply_instance },
  ext z,
  dsimp [CommRing.of_hom],
  rw category_theory.comp_apply,
  delta function_field.algebra structure_sheaf.stalk_algebra_of_specializes
    is_localization.localization_algebra_of_submonoid_le,
  rw [ring_hom.algebra_map_to_algebra, ring_hom.algebra_map_to_algebra,
    is_localization.lift_eq, is_localization.lift_eq, ring_hom.algebra_map_to_algebra,
    structure_sheaf.localization_to_stalk_of],
  refl,
end

instance affine_function_field_is_fraction_ring_of_stalk (R : CommRing) [is_domain R]
  (x : prime_spectrum R) :
  is_fraction_ring ((Scheme.Spec.obj $ op R).presheaf.stalk x)
    ((Scheme.Spec.obj $ op R).function_field) :=
begin
  apply (is_localization.is_fraction_ring_iff_of_base_ring_equiv
    (structure_sheaf.stalk_iso _ _).CommRing_iso_to_ring_equiv).mpr,
  have e : x.as_ideal.prime_compl ≤ non_zero_divisors R,
  { intros a ha, rw mem_non_zero_divisors_iff_ne_zero,
    exact λ h, ha (h.symm ▸ x.as_ideal.zero_mem) },
  letI : algebra (localization.at_prime x.as_ideal) ((Scheme.Spec.obj (op R)).function_field) :=
    is_localization.localization_algebra_of_submonoid_le _ _ e,
  letI : is_scalar_tower R (localization.at_prime x.as_ideal)
    ((Scheme.Spec.obj (op R)).function_field) :=
    is_localization.localization_is_scalar_tower_of_submonoid_le _ _ e,
  have := is_localization.is_localization_of_submonoid_le (localization.at_prime x.as_ideal)
    ((Scheme.Spec.obj (op R)).function_field) x.as_ideal.prime_compl
    (non_zero_divisors R) e,
  apply_with (is_localization.is_localization_of_is_exists_mul_mem _ _ _
    (ring_hom.map_le_non_zero_divisors_of_injective _
      (is_localization.injective _ e) (le_of_eq rfl))) { instances := ff },
  any_goals { dsimp, apply_instance },
  swap,
  { convert this, apply affine_function_field_is_fraction_ring_of_stalk_aux R x },
  { dsimp,
    rintro ⟨y, hy⟩,
    obtain ⟨⟨y', s⟩, e'⟩ := is_localization.surj x.as_ideal.prime_compl y,
    use algebra_map R _ s,
    dsimp only [subtype.coe_mk] at e' ⊢,
    rw mul_comm,
    rw e',
    refine set.mem_image_of_mem _ _,
    simp only [algebra.id.map_eq_id, ring_hom.id_apply, set_like.mem_coe],
    apply mem_non_zero_divisors_iff_ne_zero.mpr,
    rintro rfl,
    simp only [map_zero, subtype.val_eq_coe, mul_eq_zero] at e',
    replace e' := e'.resolve_left (non_zero_divisors.ne_zero hy),
    revert e',
    apply is_localization.to_map_ne_zero_of_mem_non_zero_divisors _ e (e s.prop),
    all_goals { apply_instance } }
end
.
lemma generic_point_eq_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  [hX : is_integral X] [is_integral Y] :
    f.1.base (generic_point X.carrier : _) = (generic_point Y.carrier : _) :=
begin
  apply ((generic_point_spec _).eq _).symm,
  show t0_space Y.carrier, by apply_instance,
  convert (generic_point_spec X.carrier).image (show continuous f.1.base, by continuity),
  symmetry,
  rw [eq_top_iff, set.top_eq_univ, set.top_eq_univ],
  convert subset_closure_inter_of_is_preirreducible_of_is_open _ H.base_open.open_range _,
  rw [set.univ_inter, set.image_univ],
  apply_with preirreducible_space.is_preirreducible_univ { instances := ff },
  show preirreducible_space Y.carrier, by apply_instance,
  exact ⟨_, trivial, set.mem_range_self hX.1.some⟩,
end

noncomputable
def function_field_iso_of_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  [hX : is_integral X] [is_integral Y] : X.function_field ≅ Y.function_field :=
begin
  refine (as_iso $ PresheafedSpace.stalk_map f.val _).symm.trans (eq_to_iso _),
  rw generic_point_eq_of_is_open_immersion,
  refl,
end

instance {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f] [hX : is_integral X]
  [is_integral Y] (U : opens Y.carrier) [hU : nonempty U] :
    nonempty ((opens.map f.val.base).obj U) :=
begin
  obtain ⟨_, hx, x, rfl⟩ := nonempty_preirreducible_inter U.prop H.base_open.open_range _ _,
  exacts [⟨⟨_, hx⟩⟩, ⟨_, hU.some.prop⟩, ⟨_, set.mem_range_self hX.1.some⟩],
end

@[simp, reassoc]
lemma germ_function_field_iso_of_open_immersion {X Y : Scheme} (f : X ⟶ Y)
  [is_open_immersion f] [is_integral X] [is_integral Y] (U : opens Y.carrier) [nonempty U] :
    Y.germ_to_function_field U ≫ (function_field_iso_of_open_immersion f).inv =
    f.1.c.app _ ≫ X.germ_to_function_field ((opens.map f.1.base).obj U) :=
begin
  delta function_field_iso_of_open_immersion,
  simp only [iso.symm_inv, iso.trans_inv, eq_to_iso.inv, as_iso_hom],
  rw [← PresheafedSpace.stalk_map_germ, ← category.assoc],
  congr,
  delta Scheme.germ_to_function_field,
  have : ∀ (x y : U) (h : x.1 = y.1), Y.presheaf.germ x ≫ eq_to_hom (by { congr, exact h }) =
    Y.presheaf.germ y,
  { rintros ⟨x, _⟩ ⟨y, _⟩ (rfl : x = y), exact category.comp_id _ },
  apply this ⟨_, _⟩ ⟨_, _⟩,
  exact (generic_point_eq_of_is_open_immersion f).symm
end

instance affine_cover_is_integral [is_integral X] (x : X.carrier) :
  is_integral (X.affine_cover.obj x) :=
begin
  haveI : nonempty (X.affine_cover.obj x).carrier,
  { refine ⟨(X.affine_cover.covers x).some⟩ },
  exact is_integral_of_open_immersion (X.affine_cover.map x)
end

instance [h : is_integral X] (x : X.carrier) :
  is_fraction_ring (X.presheaf.stalk x) X.function_field :=
begin
  tactic.unfreeze_local_instances,
  obtain ⟨y, hy⟩ := X.affine_cover.covers x,
  rw ← hy,
  erw is_localization.is_fraction_ring_iff_of_base_ring_equiv
    (as_iso $ PresheafedSpace.stalk_map (X.affine_cover.map _).val y).CommRing_iso_to_ring_equiv,
  apply (is_localization.is_localization_iff_of_ring_equiv _ (function_field_iso_of_open_immersion
    (X.affine_cover.map x)).symm.CommRing_iso_to_ring_equiv).mpr,
  let R := (X.local_affine x).some_spec.some,
  haveI : is_domain R,
  { rw ← affine_is_integral_iff, show is_integral (X.affine_cover.obj x), apply_instance },
  convert algebraic_geometry.affine_function_field_is_fraction_ring_of_stalk R y,
  delta algebraic_geometry.stalk_function_field_algebra,
  rw [ring_hom.algebra_map_to_algebra, ring_hom.algebra_map_to_algebra],
  -- generalize_proofs,
  suffices : ((as_iso (PresheafedSpace.stalk_map (X.affine_cover.map x).val y)).inv ≫
    X.presheaf.stalk_specializes _) ≫
    (function_field_iso_of_open_immersion (X.affine_cover.map x)).inv =
      (Scheme.Spec.obj (op R)).presheaf.stalk_specializes _,
  { exact this },
  rw [category.assoc, iso.inv_comp_eq],
  apply Top.presheaf.stalk_hom_ext,
  intros U hU,
  haveI : nonempty U := ⟨⟨_, hU⟩⟩,
  dsimp,
  rw [Top.presheaf.germ_stalk_specializes'_assoc],
  erw [germ_function_field_iso_of_open_immersion, PresheafedSpace.stalk_map_germ_assoc
    (X.affine_cover.map x).1 U ⟨y, hU⟩, Top.presheaf.germ_stalk_specializes'],
  refl,
end

end algebraic_geometry
