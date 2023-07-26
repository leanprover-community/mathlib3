/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.properties

/-!
# Function field of integral schemes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  ((generic_point_spec X.carrier).mem_open_set_iff U.is_open).mpr (by simpa using h)⟩

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
  { rw [← set_like.mem_coe, (generic_point_spec X.carrier).mem_open_set_iff, set.top_eq_univ,
      set.univ_inter, set.nonempty_iff_ne_empty, ne.def, ← opens.coe_bot,
      ← set_like.ext'_iff],
    erw basic_open_eq_bot_iff,
    exacts [ha, (RingedSpace.basic_open _ _).is_open] },
  have := (X.presheaf.germ ⟨_, hs⟩).is_unit_map (RingedSpace.is_unit_res_basic_open _ s),
  rwa Top.presheaf.germ_res_apply at this
end

lemma germ_injective_of_is_integral [is_integral X] {U : opens X.carrier} (x : U) :
  function.injective (X.presheaf.germ x) :=
begin
  rw injective_iff_map_eq_zero,
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
  [hX : irreducible_space X.carrier] [irreducible_space Y.carrier] :
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
  exact ⟨_, trivial, set.mem_range_self hX.2.some⟩,
end

noncomputable
instance stalk_function_field_algebra [irreducible_space X.carrier] (x : X.carrier) :
  algebra (X.presheaf.stalk x) X.function_field :=
begin
  apply ring_hom.to_algebra,
  exact X.presheaf.stalk_specializes ((generic_point_spec X.carrier).specializes trivial)
end

instance function_field_is_scalar_tower [irreducible_space X.carrier] (U : opens X.carrier) (x : U)
  [nonempty U] :
  is_scalar_tower (X.presheaf.obj $ op U) (X.presheaf.stalk x) X.function_field :=
begin
  apply is_scalar_tower.of_algebra_map_eq',
  simp_rw [ring_hom.algebra_map_to_algebra],
  change _ = X.presheaf.germ x ≫ _,
  rw X.presheaf.germ_stalk_specializes,
  refl
end

noncomputable
instance (R : CommRing) [is_domain R] : algebra R (Scheme.Spec.obj $ op R).function_field :=
ring_hom.to_algebra $ by { change CommRing.of R ⟶ _, apply structure_sheaf.to_stalk }

@[simp] lemma generic_point_eq_bot_of_affine (R : CommRing) [is_domain R] :
  generic_point (Scheme.Spec.obj $ op R).carrier = (⟨0, ideal.bot_prime⟩ : prime_spectrum R) :=
begin
  apply (generic_point_spec (Scheme.Spec.obj $ op R).carrier).eq,
  simp [is_generic_point_def, ← prime_spectrum.zero_locus_vanishing_ideal_eq_closure]
end

instance function_field_is_fraction_ring_of_affine (R : CommRing.{u}) [is_domain R] :
  is_fraction_ring R (Scheme.Spec.obj $ op R).function_field :=
begin
  convert structure_sheaf.is_localization.to_stalk R _,
  delta is_fraction_ring is_localization.at_prime,
  congr' 1,
  rw generic_point_eq_bot_of_affine,
  ext,
  exact mem_non_zero_divisors_iff_ne_zero
end

instance {X : Scheme} [is_integral X] {U : opens X.carrier} [hU : nonempty U] :
  is_integral (X.restrict U.open_embedding) :=
begin
  haveI : nonempty (X.restrict U.open_embedding).carrier := hU,
  exact is_integral_of_open_immersion (X.of_restrict U.open_embedding)
end

lemma is_affine_open.prime_ideal_of_generic_point {X : Scheme} [is_integral X]
  {U : opens X.carrier} (hU : is_affine_open U) [h : nonempty U] :
  hU.prime_ideal_of ⟨generic_point X.carrier,
    ((generic_point_spec X.carrier).mem_open_set_iff U.is_open).mpr (by simpa using h)⟩ =
  generic_point (Scheme.Spec.obj $ op $ X.presheaf.obj $ op U).carrier :=
begin
  haveI : is_affine _ := hU,
  have e : U.open_embedding.is_open_map.functor.obj ⊤ = U,
  { ext1, exact set.image_univ.trans subtype.range_coe },
  delta is_affine_open.prime_ideal_of,
  rw ← Scheme.comp_val_base_apply,
  convert (generic_point_eq_of_is_open_immersion ((X.restrict U.open_embedding).iso_Spec.hom ≫
    Scheme.Spec.map (X.presheaf.map (eq_to_hom e).op).op)),
  ext1,
  exact (generic_point_eq_of_is_open_immersion (X.of_restrict U.open_embedding)).symm
end

lemma function_field_is_fraction_ring_of_is_affine_open [is_integral X] (U : opens X.carrier)
  (hU : is_affine_open U) [hU' : nonempty U] :
  is_fraction_ring (X.presheaf.obj $ op U) X.function_field :=
begin
  haveI : is_affine _ := hU,
  haveI : nonempty (X.restrict U.open_embedding).carrier := hU',
  haveI : is_integral (X.restrict U.open_embedding) := @@is_integral_of_is_affine_is_domain _ _ _
    (by { dsimp, rw opens.open_embedding_obj_top, apply_instance }),
  have e : U.open_embedding.is_open_map.functor.obj ⊤ = U,
  { ext1, exact set.image_univ.trans subtype.range_coe },
  delta is_fraction_ring Scheme.function_field,
  convert hU.is_localization_stalk ⟨generic_point X.carrier, _⟩ using 1,
  rw [hU.prime_ideal_of_generic_point, generic_point_eq_bot_of_affine],
  ext, exact mem_non_zero_divisors_iff_ne_zero
end

instance (x : X.carrier) : is_affine (X.affine_cover.obj x) :=
algebraic_geometry.Spec_is_affine _

instance [h : is_integral X] (x : X.carrier) :
  is_fraction_ring (X.presheaf.stalk x) X.function_field :=
begin
  let U : opens X.carrier := ⟨set.range (X.affine_cover.map x).1.base,
    PresheafedSpace.is_open_immersion.base_open.open_range⟩,
  haveI : nonempty U := ⟨⟨_, X.affine_cover.covers x⟩⟩,
  have hU : is_affine_open U := range_is_affine_open_of_open_immersion (X.affine_cover.map x),
  exact @@is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization _ _ _ _ _ _ _ _ _ _ _
    (hU.is_localization_stalk ⟨x, X.affine_cover.covers x⟩)
      (function_field_is_fraction_ring_of_is_affine_open X U hU)
end

end algebraic_geometry
