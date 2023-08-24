/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.ideal.local_ring
import ring_theory.localization.ideal

/-!
# Localizations of commutative rings at the complement of a prime ideal

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

 * `is_localization.at_prime (I : ideal R) [is_prime I] (S : Type*)` expresses that `S` is a
   localization at (the complement of) a prime ideal `I`, as an abbreviation of
   `is_localization I.prime_compl S`

## Main results

 * `is_localization.at_prime.local_ring`: a theorem (not an instance) stating a localization at the
   complement of a prime ideal is a local ring

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_semiring R] (M : submonoid R) (S : Type*) [comm_semiring S]
variables [algebra R S] {P : Type*} [comm_semiring P]

section at_prime

variables (I : ideal R) [hp : I.is_prime]
include hp
namespace ideal

/-- The complement of a prime ideal `I ⊆ R` is a submonoid of `R`. -/
def prime_compl :
  submonoid R :=
{ carrier := (Iᶜ : set R),
  one_mem' := by convert I.ne_top_iff_one.1 hp.1; refl,
  mul_mem' := λ x y hnx hny hxy, or.cases_on (hp.mem_or_mem hxy) hnx hny }

lemma prime_compl_le_non_zero_divisors [no_zero_divisors R] : I.prime_compl ≤ non_zero_divisors R :=
le_non_zero_divisors_of_no_zero_divisors $ not_not_intro I.zero_mem

end ideal

variables (S)

/-- Given a prime ideal `P`, the typeclass `is_localization.at_prime S P` states that `S` is
isomorphic to the localization of `R` at the complement of `P`. -/
protected abbreviation is_localization.at_prime := is_localization I.prime_compl S

/-- Given a prime ideal `P`, `localization.at_prime S P` is a localization of
`R` at the complement of `P`, as a quotient type. -/
protected abbreviation localization.at_prime := localization I.prime_compl

namespace is_localization

lemma at_prime.nontrivial [is_localization.at_prime S I] : nontrivial S :=
nontrivial_of_ne (0 : S) 1 $ λ hze,
begin
  rw [←(algebra_map R S).map_one, ←(algebra_map R S).map_zero] at hze,
  obtain ⟨t, ht⟩ := (eq_iff_exists I.prime_compl S).1 hze,
  have htz : (t : R) = 0, by simpa using ht.symm,
  exact t.2 (htz.symm ▸ I.zero_mem : ↑t ∈ I)
end

local attribute [instance] at_prime.nontrivial

theorem at_prime.local_ring [is_localization.at_prime S I] : local_ring S :=
local_ring.of_nonunits_add
begin
  intros x y hx hy hu,
  cases is_unit_iff_exists_inv.1 hu with z hxyz,
  have : ∀ {r : R} {s : I.prime_compl}, mk' S r s ∈ nonunits S → r ∈ I, from
    λ (r : R) (s : I.prime_compl), not_imp_comm.1
      (λ nr, is_unit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : I.prime_compl),
        mk'_mul_mk'_eq_one' _ _ nr⟩),
  rcases mk'_surjective I.prime_compl x with ⟨rx, sx, hrx⟩,
  rcases mk'_surjective I.prime_compl y with ⟨ry, sy, hry⟩,
  rcases mk'_surjective I.prime_compl z with ⟨rz, sz, hrz⟩,
  rw [←hrx, ←hry, ←hrz, ←mk'_add, ←mk'_mul,
      ←mk'_self S I.prime_compl.one_mem] at hxyz,
  rw ←hrx at hx, rw ←hry at hy,
  obtain ⟨t, ht⟩ := is_localization.eq.1 hxyz,
  simp only [mul_one, one_mul, submonoid.coe_mul, subtype.coe_mk] at ht,
  suffices : ↑t * (↑sx * ↑sy * ↑sz) ∈ I, from
    not_or (mt hp.mem_or_mem $ not_or sx.2 sy.2) sz.2
      (hp.mem_or_mem $ (hp.mem_or_mem this).resolve_left t.2),
  rw [←ht],
  exact I.mul_mem_left _ (I.mul_mem_right _ (I.add_mem (I.mul_mem_right _ $ this hx)
                                                       (I.mul_mem_right _ $ this hy))),
end

end is_localization

namespace localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
instance at_prime.local_ring : local_ring (localization I.prime_compl) :=
is_localization.at_prime.local_ring (localization I.prime_compl) I

end localization

end at_prime

namespace is_localization

variables {A : Type*} [comm_ring A] [is_domain A]

/--
The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
instance is_domain_of_local_at_prime {P : ideal A} (hp : P.is_prime) :
  is_domain (localization.at_prime P) :=
is_domain_localization P.prime_compl_le_non_zero_divisors

namespace at_prime

variables (I : ideal R) [hI : I.is_prime] [is_localization.at_prime S I]
include hI

lemma is_unit_to_map_iff (x : R) :
  is_unit ((algebra_map R S) x) ↔ x ∈ I.prime_compl :=
⟨λ h hx, (is_prime_of_is_prime_disjoint I.prime_compl S I hI disjoint_compl_left).ne_top $
  (ideal.map (algebra_map R S) I).eq_top_of_is_unit_mem (ideal.mem_map_of_mem _ hx) h,
λ h, map_units S ⟨x, h⟩⟩

-- Can't use typeclasses to infer the `local_ring` instance, so use an `opt_param` instead
-- (since `local_ring` is a `Prop`, there should be no unification issues.)
lemma to_map_mem_maximal_iff (x : R) (h : _root_.local_ring S := local_ring S I) :
  algebra_map R S x ∈ local_ring.maximal_ideal S ↔ x ∈ I :=
not_iff_not.mp $ by
simpa only [local_ring.mem_maximal_ideal, mem_nonunits_iff, not_not]
  using is_unit_to_map_iff S I x

lemma comap_maximal_ideal (h : _root_.local_ring S := local_ring S I) :
  (local_ring.maximal_ideal S).comap (algebra_map R S) = I :=
ideal.ext $ λ x, by simpa only [ideal.mem_comap] using to_map_mem_maximal_iff _ I x

lemma is_unit_mk'_iff (x : R) (y : I.prime_compl) :
  is_unit (mk' S x y) ↔ x ∈ I.prime_compl :=
⟨λ h hx, mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h,
λ h, is_unit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

lemma mk'_mem_maximal_iff (x : R) (y : I.prime_compl) (h : _root_.local_ring S := local_ring S I) :
  mk' S x y ∈ local_ring.maximal_ideal S ↔ x ∈ I :=
not_iff_not.mp $ by
simpa only [local_ring.mem_maximal_ideal, mem_nonunits_iff, not_not]
  using is_unit_mk'_iff S I x y

end at_prime

end is_localization

namespace localization

open is_localization

local attribute [instance] classical.prop_decidable

variables (I : ideal R) [hI : I.is_prime]
include hI

variables {I}
/-- The unique maximal ideal of the localization at `I.prime_compl` lies over the ideal `I`. -/
lemma at_prime.comap_maximal_ideal :
  ideal.comap (algebra_map R (localization.at_prime I))
    (local_ring.maximal_ideal (localization I.prime_compl)) = I :=
at_prime.comap_maximal_ideal _ _

/-- The image of `I` in the localization at `I.prime_compl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `at_prime.local_ring` -/
lemma at_prime.map_eq_maximal_ideal :
  ideal.map (algebra_map R (localization.at_prime I)) I =
    (local_ring.maximal_ideal (localization I.prime_compl)) :=
begin
  convert congr_arg (ideal.map _) at_prime.comap_maximal_ideal.symm,
  rw map_comap I.prime_compl
end

lemma le_comap_prime_compl_iff {J : ideal P} [hJ : J.is_prime] {f : R →+* P} :
  I.prime_compl ≤ J.prime_compl.comap f ↔ J.comap f ≤ I :=
⟨λ h x hx, by { contrapose! hx, exact h hx },
 λ h x hx hfxJ, hx (h hfxJ)⟩

variables (I)

/--
For a ring hom `f : R →+* S` and a prime ideal `J` in `S`, the induced ring hom from the
localization of `R` at `J.comap f` to the localization of `S` at `J`.

To make this definition more flexible, we allow any ideal `I` of `R` as input, together with a proof
that `I = J.comap f`. This can be useful when `I` is not definitionally equal to `J.comap f`.
 -/
noncomputable def local_ring_hom (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) :
  localization.at_prime I →+* localization.at_prime J :=
is_localization.map (localization.at_prime J) f (le_comap_prime_compl_iff.mpr (ge_of_eq hIJ))

lemma local_ring_hom_to_map (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) (x : R) :
  local_ring_hom I J f hIJ (algebra_map _ _ x) = algebra_map _ _ (f x) :=
map_eq _ _

lemma local_ring_hom_mk' (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) (x : R) (y : I.prime_compl) :
  local_ring_hom I J f hIJ (is_localization.mk' _ x y) =
    is_localization.mk' (localization.at_prime J) (f x)
      (⟨f y, le_comap_prime_compl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.prime_compl) :=
map_mk' _ _ _

instance is_local_ring_hom_local_ring_hom (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) :
  is_local_ring_hom (local_ring_hom I J f hIJ) :=
is_local_ring_hom.mk $ λ x hx,
begin
  rcases is_localization.mk'_surjective I.prime_compl x with ⟨r, s, rfl⟩,
  rw local_ring_hom_mk' at hx,
  rw at_prime.is_unit_mk'_iff at hx ⊢,
  exact λ hr, hx ((set_like.ext_iff.mp hIJ r).mp hr),
end

lemma local_ring_hom_unique (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) {j : localization.at_prime I →+* localization.at_prime J}
  (hj : ∀ x : R, j (algebra_map _ _ x) = algebra_map _ _ (f x)) :
  local_ring_hom I J f hIJ = j :=
map_unique _ _ hj

@[simp] lemma local_ring_hom_id :
  local_ring_hom I I (ring_hom.id R) (ideal.comap_id I).symm = ring_hom.id _ :=
local_ring_hom_unique _ _ _ _ (λ x, rfl)

@[simp] lemma local_ring_hom_comp {S : Type*} [comm_semiring S]
  (J : ideal S) [hJ : J.is_prime] (K : ideal P) [hK : K.is_prime]
  (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* P) (hJK : J = K.comap g) :
  local_ring_hom I K (g.comp f) (by rw [hIJ, hJK, ideal.comap_comap f g]) =
  (local_ring_hom J K g hJK).comp (local_ring_hom I J f hIJ) :=
local_ring_hom_unique _ _ _ _
  (λ r, by simp only [function.comp_app, ring_hom.coe_comp, local_ring_hom_to_map])

end localization
