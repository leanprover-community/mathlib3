/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import algebra.algebra.tower
import ring_theory.localization.basic

/-!
# Fraction ring / fraction field Frac(R) as localization

## Main definitions

 * `is_fraction_ring R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
   `is_localization (non_zero_divisors R) K`

## Main results

 * `is_fraction_ring.field`: a definition (not an instance) stating the localization of an integral
   domain `R` at `R \ {0}` is a field
 * `rat.is_fraction_ring` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables (R : Type*) [comm_ring R] {M : submonoid R} (S : Type*) [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]
variables {A : Type*} [comm_ring A] [is_domain A] (K : Type*)

/-- `is_fraction_ring R K` states `K` is the field of fractions of an integral domain `R`. -/
-- TODO: should this extend `algebra` instead of assuming it?
abbreviation is_fraction_ring [comm_ring K] [algebra R K] := is_localization (non_zero_divisors R) K

/-- The cast from `int` to `rat` as a `fraction_ring`. -/
instance rat.is_fraction_ring : is_fraction_ring ℤ ℚ :=
{ map_units :=
  begin
    rintro ⟨x, hx⟩,
    rw mem_non_zero_divisors_iff_ne_zero at hx,
    simpa only [eq_int_cast, is_unit_iff_ne_zero, int.cast_eq_zero,
                ne.def, subtype.coe_mk] using hx,
    end,
  surj :=
  begin
    rintro ⟨n, d, hd, h⟩,
    refine ⟨⟨n, ⟨d, _⟩⟩, rat.mul_denom_eq_num⟩,
    rwa [mem_non_zero_divisors_iff_ne_zero, int.coe_nat_ne_zero_iff_pos]
  end,
  eq_iff_exists :=
  begin
    intros x y,
    rw [eq_int_cast, eq_int_cast, int.cast_inj],
    refine ⟨by { rintro rfl, use 1 }, _⟩,
    rintro ⟨⟨c, hc⟩, h⟩,
    apply mul_left_cancel₀ _ h,
    rwa mem_non_zero_divisors_iff_ne_zero at hc,
  end }

namespace is_fraction_ring

open is_localization

variables {R K}

section comm_ring

variables [comm_ring K] [algebra R K] [is_fraction_ring R K] [algebra A K] [is_fraction_ring A K]

lemma to_map_eq_zero_iff {x : R} :
  algebra_map R K x = 0 ↔ x = 0 :=
to_map_eq_zero_iff _ (le_of_eq rfl)

variables (R K)

protected theorem injective : function.injective (algebra_map R K) :=
is_localization.injective _ (le_of_eq rfl)

variables {R K}

@[norm_cast, simp] lemma coe_inj {a b : R} : (↑a : K) = ↑b ↔ a = b :=
(is_fraction_ring.injective R K).eq_iff

@[priority 100] instance [no_zero_divisors K] : no_zero_smul_divisors R K :=
no_zero_smul_divisors.of_algebra_map_injective $ is_fraction_ring.injective R K

variables {R K}

protected lemma to_map_ne_zero_of_mem_non_zero_divisors [nontrivial R]
  {x : R} (hx : x ∈ non_zero_divisors R) : algebra_map R K x ≠ 0 :=
is_localization.to_map_ne_zero_of_mem_non_zero_divisors _ le_rfl hx

variables (A)

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
protected theorem is_domain : is_domain K :=
is_domain_of_le_non_zero_divisors _ (le_refl (non_zero_divisors A))

local attribute [instance] classical.dec_eq

/-- The inverse of an element in the field of fractions of an integral domain. -/
@[irreducible]
protected noncomputable def inv (z : K) : K :=
if h : z = 0 then 0 else
mk' K ↑(sec (non_zero_divisors A) z).2
  ⟨(sec _ z).1,
   mem_non_zero_divisors_iff_ne_zero.2 $ λ h0, h $
    eq_zero_of_fst_eq_zero (sec_spec (non_zero_divisors A) z) h0⟩

protected lemma mul_inv_cancel (x : K) (hx : x ≠ 0) :
  x * is_fraction_ring.inv A x = 1 :=
begin
  rw [is_fraction_ring.inv, dif_neg hx, ←is_unit.mul_left_inj
    (map_units K ⟨(sec _ x).1, mem_non_zero_divisors_iff_ne_zero.2 $
      λ h0, hx $ eq_zero_of_fst_eq_zero (sec_spec (non_zero_divisors A) x) h0⟩),
    one_mul, mul_assoc],
  rw [mk'_spec, ←eq_mk'_iff_mul_eq],
  exact (mk'_sec _ x).symm
end

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def to_field : field K :=
{ inv := is_fraction_ring.inv A,
  mul_inv_cancel := is_fraction_ring.mul_inv_cancel A,
  inv_zero := begin
    change is_fraction_ring.inv A (0 : K) = 0,
    rw [is_fraction_ring.inv],
    exact dif_pos rfl
  end,
  .. is_fraction_ring.is_domain A,
  .. show comm_ring K, by apply_instance }

end comm_ring

variables {B : Type*} [comm_ring B] [is_domain B] [field K] {L : Type*} [field L]
  [algebra A K] [is_fraction_ring A K] {g : A →+* L}

lemma mk'_mk_eq_div {r s} (hs : s ∈ non_zero_divisors A) :
  mk' K r ⟨s, hs⟩ = algebra_map A K r / algebra_map A K s :=
mk'_eq_iff_eq_mul.2 $ (div_mul_cancel (algebra_map A K r)
    (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors hs)).symm

@[simp] lemma mk'_eq_div {r} (s : non_zero_divisors A) :
  mk' K r s = algebra_map A K r / algebra_map A K s :=
mk'_mk_eq_div s.2

lemma div_surjective (z : K) : ∃ (x y : A) (hy : y ∈ non_zero_divisors A),
  algebra_map _ _ x / algebra_map _ _ y = z :=
let ⟨x, ⟨y, hy⟩, h⟩ := mk'_surjective (non_zero_divisors A) z
in ⟨x, y, hy, by rwa mk'_eq_div at h⟩

lemma is_unit_map_of_injective (hg : function.injective g)
  (y : non_zero_divisors A) : is_unit (g y) :=
is_unit.mk0 (g y) $ show g.to_monoid_with_zero_hom y ≠ 0,
  from map_ne_zero_of_mem_non_zero_divisors g hg y.2

@[simp] lemma mk'_eq_zero_iff_eq_zero [algebra R K] [is_fraction_ring R K] {x : R}
  {y : non_zero_divisors R} : mk' K x y = 0 ↔ x = 0 :=
begin
  refine ⟨λ hxy, _, λ h, by rw [h, mk'_zero]⟩,
  { simp_rw [mk'_eq_zero_iff, mul_left_coe_non_zero_divisors_eq_zero_iff] at hxy,
    exact (exists_const _).mp hxy },
end

lemma mk'_eq_one_iff_eq {x : A} {y : non_zero_divisors A} : mk' K x y = 1 ↔ x = y :=
begin
  refine ⟨_, λ hxy, by rw [hxy, mk'_self']⟩,
  { intro hxy, have hy : (algebra_map A K) ↑y ≠ (0 : K) :=
    is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors y.property,
    rw [is_fraction_ring.mk'_eq_div, div_eq_one_iff_eq hy] at hxy,
    exact is_fraction_ring.injective A K hxy }
end

open function

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : injective g) : K →+* L :=
lift $ λ (y : non_zero_divisors A), is_unit_map_of_injective hg y

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp] lemma lift_algebra_map (hg : injective g) (x) :
  lift hg (algebra_map A K x) = g x :=
lift_eq _ _

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ non_zero_divisors A`. -/
lemma lift_mk' (hg : injective g) (x) (y : non_zero_divisors A) :
  lift hg (mk' K x y) = g x / g y :=
by simp only [mk'_eq_div, map_div₀, lift_algebra_map]

/-- Given integral domains `A, B` with fields of fractions `K`, `L`
and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map {A B K L : Type*} [comm_ring A] [comm_ring B] [is_domain B]
  [comm_ring K] [algebra A K] [is_fraction_ring A K] [comm_ring L] [algebra B L]
  [is_fraction_ring B L] {j : A →+* B} (hj : injective j) :
  K →+* L :=
map L j (show non_zero_divisors A ≤ (non_zero_divisors B).comap j,
         from non_zero_divisors_le_comap_non_zero_divisors_of_injective j hj)

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
noncomputable def field_equiv_of_ring_equiv [algebra B L] [is_fraction_ring B L] (h : A ≃+* B) :
  K ≃+* L :=
ring_equiv_of_ring_equiv K L h
begin
  ext b,
  show b ∈ h.to_equiv '' _ ↔ _,
  erw [h.to_equiv.image_eq_preimage, set.preimage, set.mem_set_of_eq,
       mem_non_zero_divisors_iff_ne_zero, mem_non_zero_divisors_iff_ne_zero],
  exact h.symm.map_ne_zero_iff
end

variables (S)

lemma is_fraction_ring_iff_of_base_ring_equiv (h : R ≃+* P) :
  is_fraction_ring R S ↔
    @@is_fraction_ring P _ S _ ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  delta is_fraction_ring,
  convert is_localization_iff_of_base_ring_equiv _ _ h,
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

protected
lemma nontrivial (R S : Type*) [comm_ring R] [nontrivial R] [comm_ring S] [algebra R S]
  [is_fraction_ring R S] : nontrivial S :=
begin
  apply nontrivial_of_ne,
  intro h,
  apply @zero_ne_one R,
  exact is_localization.injective S (le_of_eq rfl)
    (((algebra_map R S).map_zero.trans h).trans (algebra_map R S).map_one.symm),
end

end is_fraction_ring

variables (R A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.
-/
@[reducible] def fraction_ring := localization (non_zero_divisors R)

namespace fraction_ring

instance unique [subsingleton R] : unique (fraction_ring R) :=
localization.unique

instance [nontrivial R] : nontrivial (fraction_ring R) :=
⟨⟨(algebra_map R _) 0, (algebra_map _ _) 1,
  λ H, zero_ne_one (is_localization.injective _ le_rfl H)⟩⟩

variables {A}

noncomputable instance : field (fraction_ring A) :=
{ add := (+),
  mul := (*),
  neg := has_neg.neg,
  sub := has_sub.sub,
  one := 1,
  zero := 0,
  nsmul := add_monoid.nsmul,
  zsmul := sub_neg_monoid.zsmul,
  npow := localization.npow _,
  .. localization.comm_ring,
  .. is_fraction_ring.to_field A }

@[simp] lemma mk_eq_div {r s} : (localization.mk r s : fraction_ring A) =
  (algebra_map _ _ r / algebra_map A _ s : fraction_ring A) :=
by rw [localization.mk_eq_mk', is_fraction_ring.mk'_eq_div]

noncomputable instance [is_domain R] [field K] [algebra R K] [no_zero_smul_divisors R K] :
  algebra (fraction_ring R) K :=
ring_hom.to_algebra (is_fraction_ring.lift (no_zero_smul_divisors.algebra_map_injective R _))

instance [is_domain R] [field K] [algebra R K] [no_zero_smul_divisors R K] :
  is_scalar_tower R (fraction_ring R) K :=
is_scalar_tower.of_algebra_map_eq (λ x, (is_fraction_ring.lift_algebra_map _ x).symm)

variables (A)

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def alg_equiv (K : Type*) [field K] [algebra A K] [is_fraction_ring A K] :
  fraction_ring A ≃ₐ[A] K :=
localization.alg_equiv (non_zero_divisors A) K

instance [algebra R A] [no_zero_smul_divisors R A] : no_zero_smul_divisors R (fraction_ring A) :=
no_zero_smul_divisors.of_algebra_map_injective
  begin
    rw [is_scalar_tower.algebra_map_eq R A],
    exact function.injective.comp
      (no_zero_smul_divisors.algebra_map_injective _ _)
      (no_zero_smul_divisors.algebra_map_injective _ _)
  end

end fraction_ring
