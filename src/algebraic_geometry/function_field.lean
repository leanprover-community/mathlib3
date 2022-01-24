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
instance (U : opens X.carrier) (x : U) : algebra (X.presheaf.obj $ op U) (X.presheaf.stalk x) :=
(X.presheaf.germ x).to_algebra

noncomputable
instance stalk_function_field_algebra [is_integral X] (x : X.carrier) :
  algebra (X.presheaf.stalk x) X.function_field :=
begin
  apply ring_hom.to_algebra,
  exact X.presheaf.stalk_specializes ((generic_point_spec X.carrier).specializes trivial)
end

instance function_field_is_scalar_tower [is_integral X] (U : opens X.carrier) (x : U) [nonempty U] :
  is_scalar_tower (X.presheaf.obj $ op U) (X.presheaf.stalk x) X.function_field :=
begin
  haveI : nonempty U := ⟨x⟩,
  apply is_scalar_tower.of_algebra_map_eq',
  simp_rw [ring_hom.algebra_map_to_algebra],
  change _ = X.presheaf.germ x ≫ _,
  rw X.presheaf.germ_stalk_specializes,
  refl
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
    ((generic_point_spec X.carrier).mem_open_set_iff U.prop).mpr (by simpa using h)⟩ =
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

lemma prime_compl_le_non_zero_divisors {R : Type*} [comm_ring R] [no_zero_divisors R]
  (p : ideal R) [p.is_prime] :
  p.prime_compl ≤ non_zero_divisors R :=
begin
  nontriviality R,
  intros a ha, rw mem_non_zero_divisors_iff_ne_zero,
  exact λ h, ha (h.symm ▸ p.zero_mem)
end

lemma is_localization.mk'_eq_zero_iff {R : Type*} [comm_ring R] {M : submonoid R}
  (S : Type*) [comm_ring S] [algebra R S] [is_localization M S] (x : R) (s : M) :
    is_localization.mk' S x s = 0 ↔ ∃ (m : M), x * m = 0 :=
by rw [← (is_localization.map_units S s).mul_left_inj, is_localization.mk'_spec, zero_mul,
  is_localization.map_eq_zero_iff M]

lemma is_localization.non_zero_divisors_le_comap {R : Type*} [comm_ring R] (M : submonoid R)
  (S : Type*) [comm_ring S] [algebra R S] [is_localization M S] :
    non_zero_divisors R ≤ (non_zero_divisors S).comap (algebra_map R S)  :=
begin
  rintros a ha b (e : b * algebra_map R S a = 0),
  obtain ⟨x, s, rfl⟩ := is_localization.mk'_surjective M b,
  rw [← @is_localization.mk'_one R _ M, ← is_localization.mk'_mul, ← (algebra_map R S).map_zero,
    ← @is_localization.mk'_one R _ M, is_localization.eq] at e,
  obtain ⟨c, e⟩ := e,
  rw [zero_mul, zero_mul, submonoid.coe_one, mul_one, mul_comm x a, mul_assoc, mul_comm] at e,
  rw is_localization.mk'_eq_zero_iff,
  exact ⟨c, ha _ e⟩
end

lemma is_localization.map_non_zero_divisors_le {R : Type*} [comm_ring R] (M : submonoid R)
  (S : Type*) [comm_ring S] [algebra R S] [is_localization M S] :
    (non_zero_divisors R).map (algebra_map R S).to_monoid_hom ≤ non_zero_divisors S  :=
submonoid.map_le_iff_le_comap.mpr (is_localization.non_zero_divisors_le_comap M S)

lemma is_localization.is_fraction_ring_of_is_localization {R : Type*} (S T: Type*) [comm_ring R]
  [comm_ring S] [comm_ring T] (M : submonoid R)
  [algebra R S] [algebra R T] [algebra S T] [is_scalar_tower R S T]
  [is_localization M S] [is_fraction_ring R T] (hM : M ≤ non_zero_divisors R) :
    is_fraction_ring S T :=
begin
  have := is_localization.is_localization_of_submonoid_le S T M (non_zero_divisors R) _,
  refine @@is_localization.is_localization_of_is_exists_mul_mem _ _ _ _ _ _ this _ _,
  { exact is_localization.map_non_zero_divisors_le M S },
  { rintro ⟨x, hx⟩,
    obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M x,
    use algebra_map R S s,
    rw [mul_comm, subtype.coe_mk, e],
    refine set.mem_image_of_mem (algebra_map R S) _,
    intros z hz,
    apply is_localization.injective S hM,
    rw map_zero,
    apply hx,
    rw [← (is_localization.map_units S s).mul_left_inj, mul_assoc, e, ← map_mul,
      hz, map_zero, zero_mul] },
  { exact hM }
end

lemma is_localization.is_fraction_ring_of_is_domain_of_is_localization {R : Type*} (S T: Type*)
  [comm_ring R] [is_domain R] [comm_ring S] [nontrivial S] [comm_ring T] (M : submonoid R)
  [algebra R S] [algebra R T] [algebra S T] [is_scalar_tower R S T]
  [is_localization M S] [is_fraction_ring R T] : is_fraction_ring S T :=
begin
  apply is_localization.is_fraction_ring_of_is_localization S T M,
  intros x hx,
  rw mem_non_zero_divisors_iff_ne_zero,
  intro hx',
  apply @zero_ne_one S,
  rw [← (algebra_map R S).map_one, ← @is_localization.mk'_one R _ M, @comm _ eq,
    is_localization.mk'_eq_zero_iff],
  exact ⟨⟨_, hx⟩, (one_mul x).symm ▸ hx'⟩,
end

instance [h : is_integral X] (x : X.carrier) :
  is_fraction_ring (X.presheaf.stalk x) X.function_field :=
begin
  let U : opens X.carrier := ⟨set.range (X.affine_cover.map x).1.base,
    PresheafedSpace.is_open_immersion.base_open.open_range⟩,
  haveI : nonempty U := ⟨⟨_, X.affine_cover.covers x⟩⟩,
  have hU : is_affine_open U := range_is_affine_open_of_open_immersion (X.affine_cover.map x),
  exact @@is_localization.is_fraction_ring_of_is_domain_of_is_localization _ _ _ _ _ _ _ _ _ _ _ _
    (hU.is_localization_stalk ⟨x, X.affine_cover.covers x⟩)
      (function_field_is_fraction_ring_of_is_affine_open X U hU)
end

end algebraic_geometry
