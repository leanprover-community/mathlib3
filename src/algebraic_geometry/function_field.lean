/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.properties
import algebraic_geometry.AffineScheme

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `algebraic_geometry.Scheme.function_field`: The function field of an integral scheme.
* `algebraic_geometry.germ_to_function_field`: The canonical map from a component into the function
  field. This map is injective.
-/

universes u v

open topological_space opposite category_theory category_theory.limits Top

namespace algebraic_geometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable
abbreviation Scheme.function_field [irreducible_space X.carrier] : CommRing :=
X.presheaf.stalk (generic_point X.carrier)

/-- The restriction map from a component to the function field. -/
noncomputable
abbreviation Scheme.germ_to_function_field [irreducible_space X.carrier] (U : opens X.carrier)
  [h : nonempty U] : X.presheaf.obj (op U) ⟶ X.function_field :=
X.presheaf.germ ⟨generic_point X.carrier,
  ((generic_point_spec X.carrier).mem_open_set_iff U.prop).mpr (by simpa using h)⟩

noncomputable
instance [irreducible_space X.carrier] (U : opens X.carrier) [nonempty U] :
  algebra (X.presheaf.obj (op U)) X.function_field :=
(X.germ_to_function_field U).to_algebra

noncomputable
instance [is_integral X] : field X.function_field :=
begin
  apply field_of_is_unit_or_eq_zero,
  intro a,
  obtain ⟨U, m, s, rfl⟩ := Top.presheaf.germ_exist _ _ a,
  rw [or_iff_not_imp_right, ← (X.presheaf.germ ⟨_, m⟩).map_zero],
  intro ha,
  replace ha := ne_of_apply_ne _ ha,
  have hs : generic_point X.carrier ∈ RingedSpace.basic_open _ s,
  { rw [← opens.mem_coe, (generic_point_spec X.carrier).mem_open_set_iff, set.top_eq_univ,
      set.univ_inter, ← set.ne_empty_iff_nonempty, ne.def, ← opens.coe_bot,
      subtype.coe_injective.eq_iff, ← opens.empty_eq],
    erw basic_open_eq_bot_iff,
    exacts [ha, (RingedSpace.basic_open _ _).prop] },
  have := (X.presheaf.germ ⟨_, hs⟩).is_unit_map (RingedSpace.is_unit_res_basic_open _ s),
  rwa Top.presheaf.germ_res_apply at this
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

lemma function_field_is_fraction_ring_of_is_affine_open [is_integral X] (U : opens X.carrier)
  (hU : is_affine_open U) [nonempty U] :
  is_fraction_ring (X.presheaf.obj $ op U) X.function_field := sorry

lemma affine_function_field_is_fraction_ring_of_stalk_aux
  (R : CommRing) [is_domain R] (x : prime_spectrum R) :
  (algebra_map ((Scheme.Spec.obj $ op R).presheaf.stalk x)
    ((Scheme.Spec.obj $ op R).function_field)).comp
      (structure_sheaf.localization_to_stalk R x) =
  (is_localization.localization_algebra_of_submonoid_le _ _ x.as_ideal.prime_compl
    (non_zero_divisors R) (by { intros a ha, rw mem_non_zero_divisors_iff_ne_zero,
      exact λ h, ha (h.symm ▸ x.as_ideal.zero_mem) }) :
        algebra (localization.at_prime x.as_ideal) _).to_ring_hom :=
begin
  refine (structure_sheaf.localization_to_stalk_stalk_specializes _).trans _,
  dsimp,
  apply is_localization.ring_hom_ext x.as_ideal.prime_compl,
  any_goals { dsimp, apply_instance },
  ext z,
  dsimp [CommRing.of_hom],
  rw category_theory.comp_apply,
  delta is_localization.localization_algebra_of_submonoid_le
    prime_spectrum.localization_map_of_specializes,
  rw [is_localization.lift_eq, structure_sheaf.localization_to_stalk_of],
  exact (is_localization.lift_eq _ _).symm
end

instance affine_function_field_is_fraction_ring_of_stalk (R : CommRing) [is_domain R]
  (x : prime_spectrum R) :
  is_fraction_ring ((Scheme.Spec.obj $ op R).presheaf.stalk x)
    ((Scheme.Spec.obj $ op R).function_field) :=
begin
  apply (is_fraction_ring.is_fraction_ring_iff_of_base_ring_equiv _
    (structure_sheaf.stalk_iso _ _).CommRing_iso_to_ring_equiv).mpr,
  have e : x.as_ideal.prime_compl ≤ non_zero_divisors R,
  { intros a ha, rw mem_non_zero_divisors_iff_ne_zero,
    exact λ h, ha (h.symm ▸ x.as_ideal.zero_mem) },
  letI : algebra (localization.at_prime x.as_ideal) ((Scheme.Spec.obj (op R)).function_field) :=
    is_localization.localization_algebra_of_submonoid_le _ _ _ _ e,
  letI : is_scalar_tower R (localization.at_prime x.as_ideal)
    ((Scheme.Spec.obj (op R)).function_field) :=
    is_localization.localization_is_scalar_tower_of_submonoid_le _ _ _ _ e,
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
  erw is_fraction_ring.is_fraction_ring_iff_of_base_ring_equiv _
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
