/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import ring_theory.integral_closure
import data.polynomial.field_division
import ring_theory.polynomial.gauss_lemma

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element x of an A-algebra B,
under the assumption that x is integral over A.

After stating the defining property we specialize to the setting of field extensions
and derive some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

universes u v w

open_locale classical
open polynomial set function

variables {α : Type u} {β : Type v}

section min_poly_def
variables [comm_ring α] [ring β] [algebra α β]

/-- Let `B` be an `A`-algebra, and `x` an element of `B` that is integral over `A`
so we have some term `hx : is_integral A x`.
The minimal polynomial `minimal_polynomial hx` of `x` is a monic polynomial of smallest degree
that has `x` as its root.
For instance, if `V` is a `K`-vector space for some field `K`, and `f : V →ₗ[K] V` then
the minimal polynomial of `f` is `minimal_polynomial f.is_integral`. -/
noncomputable def minimal_polynomial {x : β} (hx : is_integral α x) : polynomial α :=
well_founded.min degree_lt_wf _ hx

end min_poly_def

namespace minimal_polynomial

section ring
variables [comm_ring α] [ring β] [algebra α β]
variables {x : β} (hx : is_integral α x)

/--A minimal polynomial is monic.-/
lemma monic : monic (minimal_polynomial hx) :=
(well_founded.min_mem degree_lt_wf _ hx).1

/--An element is a root of its minimal polynomial.-/
@[simp] lemma aeval : aeval x (minimal_polynomial hx) = 0 :=
(well_founded.min_mem degree_lt_wf _ hx).2

/--The defining property of the minimal polynomial of an element x:
it is the monic polynomial with smallest degree that has x as its root.-/
lemma min {p : polynomial α} (pmonic : p.monic) (hp : polynomial.aeval x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
le_of_not_lt $ well_founded.not_lt_min degree_lt_wf _ hx ⟨pmonic, hp⟩

/-- A minimal polynomial is nonzero. -/
lemma ne_zero [nontrivial α] : (minimal_polynomial hx) ≠ 0 :=
ne_zero_of_monic (monic hx)

/-- If an element `x` is a root of a nonzero monic polynomial `p`,
then the degree of `p` is at least the degree of the minimal polynomial of `x`. -/
lemma degree_le_of_monic
  {p : polynomial α} (hmonic : p.monic) (hp : polynomial.aeval x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
min _ hmonic (by simp [hp])

end ring

section integral_domain

variables [integral_domain α]

section ring

variables [ring β] [algebra α β] [nontrivial β]
variables {x : β} (hx : is_integral α x)

/--The degree of a minimal polynomial is positive. -/
lemma degree_pos [nontrivial α] : 0 < degree (minimal_polynomial hx) :=
begin
  apply lt_of_le_of_ne,
  { simpa only [zero_le_degree_iff] using ne_zero hx },
  assume deg_eq_zero,
  rw eq_comm at deg_eq_zero,
  have ndeg_eq_zero : nat_degree (minimal_polynomial hx) = 0,
  { simpa using congr_arg nat_degree (eq_C_of_degree_eq_zero deg_eq_zero) },
  have eq_one : minimal_polynomial hx = 1,
  { rw eq_C_of_degree_eq_zero deg_eq_zero, convert C_1,
    simpa only [ndeg_eq_zero.symm] using (monic hx).leading_coeff },
  simpa only [eq_one, alg_hom.map_one, one_ne_zero] using aeval hx
end

/-- If `L/K` is a ring extension, and `x` is an element of `L` in the image of `K`,
then the minimal polynomial of `x` is `X - C x`. -/
lemma eq_X_sub_C_of_algebra_map_inj [nontrivial α] (a : α) (hf : function.injective (algebra_map α β)) :
  minimal_polynomial (@is_integral_algebra_map α β _ _ _ a) = X - C a :=
begin
  have hdegle : (minimal_polynomial (@is_integral_algebra_map α β _ _ _ a)).nat_degree ≤ 1,
  { apply with_bot.coe_le_coe.1,
    rw [←degree_eq_nat_degree (ne_zero (@is_integral_algebra_map α β _ _ _ a)),
      with_top.coe_one, ←degree_X_sub_C a],
    refine degree_le_of_monic (@is_integral_algebra_map α β _ _ _ a) (monic_X_sub_C a) _,
    simp only [aeval_C, aeval_X, alg_hom.map_sub, sub_self] },
  have hdeg : (minimal_polynomial (@is_integral_algebra_map α β _ _ _ a)).degree = 1,
  { apply (degree_eq_iff_nat_degree_eq (ne_zero (@is_integral_algebra_map α β _ _ _ a))).2,
    exact (has_le.le.antisymm hdegle (nat.succ_le_of_lt (with_bot.coe_lt_coe.1
    (lt_of_lt_of_le (degree_pos (@is_integral_algebra_map α β _ _ _ a)) degree_le_nat_degree)))) },
  have hrw := eq_X_add_C_of_degree_eq_one hdeg,
  simp only [monic (@is_integral_algebra_map α β _ _ _ a), one_mul,
    monic.leading_coeff, ring_hom.map_one] at hrw,
  have h0 : (minimal_polynomial (@is_integral_algebra_map α β _ _ _ a)).coeff 0 = -a,
  { have hroot := aeval (@is_integral_algebra_map α β _ _ _ a),
    rw [hrw, add_comm] at hroot,
    simp only [aeval_C, aeval_X, aeval_add] at hroot,
    replace hroot := eq_neg_of_add_eq_zero hroot,
    rw [←ring_hom.map_neg _ a] at hroot,
    exact (hf hroot) },
  rw hrw,
  simp only [h0, ring_hom.map_neg, sub_eq_add_neg],
end

/-- A minimal polynomial is not a unit. -/
lemma not_is_unit : ¬ is_unit (minimal_polynomial hx) :=
assume H, (ne_of_lt (degree_pos hx)).symm $ degree_eq_zero_of_is_unit H

end ring

section domain

variables [domain β] [algebra α β]
variables {x : β} (hx : is_integral α x)

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
lemma aeval_ne_zero_of_dvd_not_unit_minimal_polynomial {a : polynomial α}
  (hamonic : a.monic) (hdvd : dvd_not_unit a (minimal_polynomial hx)) :
  polynomial.aeval x a ≠ 0 :=
begin
  intro ha,
  refine not_lt_of_ge (minimal_polynomial.min hx hamonic ha) _,
  obtain ⟨hzeroa, b, hb_nunit, prod⟩ := hdvd,
  have hbmonic : b.monic,
  { rw monic.def,
    have := monic hx,
    rwa [monic.def, prod, leading_coeff_mul, monic.def.mp hamonic, one_mul] at this },
  have hzerob : b ≠ 0 := hbmonic.ne_zero,
  have degbzero : 0 < b.nat_degree,
  { apply nat.pos_of_ne_zero,
    intro h,
    have h₁ := eq_C_of_nat_degree_eq_zero h,
    rw [←h, ←leading_coeff, monic.def.1 hbmonic, C_1] at h₁,
    rw h₁ at hb_nunit,
    have := is_unit_one,
    contradiction },
  rw [prod, degree_mul, degree_eq_nat_degree hzeroa, degree_eq_nat_degree hzerob],
  exact_mod_cast lt_add_of_pos_right _ degbzero,
end

/--A minimal polynomial is irreducible.-/
lemma irreducible : irreducible (minimal_polynomial hx) :=
begin
  cases irreducible_or_factor (minimal_polynomial hx) (not_is_unit hx) with hirr hred,
  { exact hirr },
  exfalso,
  obtain ⟨a, b, ha_nunit, hb_nunit, hab_eq⟩ := hred,
  have coeff_prod : a.leading_coeff * b.leading_coeff = 1,
  { rw [←monic.def.1 (monic hx), ←hab_eq],
    simp only [leading_coeff_mul] },
  have hamonic : (a * C b.leading_coeff).monic,
  { rw monic.def,
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C] },
  have hbmonic : (b * C a.leading_coeff).monic,
  { rw [monic.def, mul_comm],
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C] },
  have prod : minimal_polynomial hx = (a * C b.leading_coeff) * (b * C a.leading_coeff),
  { symmetry,
    calc a * C b.leading_coeff * (b * C a.leading_coeff)
        = a * b * (C a.leading_coeff * C b.leading_coeff) : by ring
    ... = a * b * (C (a.leading_coeff * b.leading_coeff)) : by simp only [ring_hom.map_mul]
    ... = a * b : by rw [coeff_prod, C_1, mul_one]
    ... = minimal_polynomial hx : hab_eq },
  have hzero := aeval hx,
  rw [prod, aeval_mul, mul_eq_zero] at hzero,
  cases hzero,
  { refine aeval_ne_zero_of_dvd_not_unit_minimal_polynomial hx hamonic _ hzero,
    exact ⟨hamonic.ne_zero, _, mt is_unit_of_mul_is_unit_left hb_nunit, prod⟩ },
  { refine aeval_ne_zero_of_dvd_not_unit_minimal_polynomial hx hbmonic _ hzero,
    rw mul_comm at prod,
    exact ⟨hbmonic.ne_zero, _, mt is_unit_of_mul_is_unit_left ha_nunit, prod⟩ },
end

end domain

end integral_domain

section field
variables [field α]

section ring
variables [ring β] [algebra α β]
variables {x : β} (hx : is_integral α x)

/--If an element x is a root of a nonzero polynomial p,
then the degree of p is at least the degree of the minimal polynomial of x.-/
lemma degree_le_of_ne_zero
  {p : polynomial α} (pnz : p ≠ 0) (hp : polynomial.aeval x p = 0) :
  degree (minimal_polynomial hx) ≤ degree p :=
calc degree (minimal_polynomial hx) ≤ degree (p * C (leading_coeff p)⁻¹) :
    min _ (monic_mul_leading_coeff_inv pnz) (by simp [hp])
  ... = degree p : degree_mul_leading_coeff_inv p pnz

/--The minimal polynomial of an element x is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has x as a root,
then this polynomial is equal to the minimal polynomial of x.-/
lemma unique {p : polynomial α} (pmonic : p.monic) (hp : polynomial.aeval x p = 0)
  (pmin : ∀ q : polynomial α, q.monic → polynomial.aeval x q = 0 → degree p ≤ degree q) :
  p = minimal_polynomial hx :=
begin
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := degree_le_of_ne_zero hx hnz (by simp [hp]),
  contrapose! this,
  apply degree_sub_lt _ (ne_zero hx),
  { rw [(monic hx).leading_coeff, pmonic.leading_coeff] },
  { exact le_antisymm (min hx pmonic hp)
      (pmin (minimal_polynomial hx) (monic hx) (aeval hx)) },
end

/--If an element x is a root of a polynomial p, then the minimal polynomial of x divides p.-/
lemma dvd {p : polynomial α} (hp : polynomial.aeval x p = 0) :
  minimal_polynomial hx ∣ p :=
begin
  rw ← dvd_iff_mod_by_monic_eq_zero (monic hx),
  by_contra hnz,
  have := degree_le_of_ne_zero hx hnz _,
  { contrapose! this,
    exact degree_mod_by_monic_lt _ (monic hx) (ne_zero hx) },
  { rw ← mod_by_monic_add_div p (monic hx) at hp,
    simpa using hp }
end

lemma dvd_map_of_is_scalar_tower {α γ : Type*} (β : Type*) [comm_ring α] [field β] [comm_ring γ]
  [algebra α β] [algebra α γ] [algebra β γ] [is_scalar_tower α β γ] {x : γ} (hx : is_integral α x) :
  minimal_polynomial (is_integral_of_is_scalar_tower x hx) ∣ (minimal_polynomial hx).map (algebra_map α β) :=
by { apply minimal_polynomial.dvd, rw [← is_scalar_tower.aeval_apply, minimal_polynomial.aeval] }

variables [nontrivial β]

theorem unique' {p : polynomial α} (hp1 : _root_.irreducible p) (hp2 : polynomial.aeval x p = 0)
  (hp3 : p.monic) : p = minimal_polynomial hx :=
let ⟨q, hq⟩ := dvd hx hp2 in
eq_of_monic_of_associated hp3 (monic hx) $
mul_one (minimal_polynomial hx) ▸ hq.symm ▸ associated_mul_mul (associated.refl _) $
associated_one_iff_is_unit.2 $ (hp1.is_unit_or_is_unit hq).resolve_left $ not_is_unit hx

lemma gcd_domain_eq_field_fractions {α : Type u} {β : Type v} {γ : Type w} [integral_domain α]
  [gcd_monoid α] [field β] [integral_domain γ] (f : fraction_map α β) [algebra f.codomain γ]
  [algebra α γ] [is_scalar_tower α f.codomain γ] {x : γ} (hx : is_integral α x) :
  minimal_polynomial (@is_integral_of_is_scalar_tower α f.codomain γ _ _ _ _ _ _ _ x hx) =
    ((minimal_polynomial hx).map (localization_map.to_ring_hom f)) :=
begin
  refine (unique' (@is_integral_of_is_scalar_tower α f.codomain γ _ _ _ _ _ _ _ x hx) _ _ _).symm,
  { exact (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map f
  (polynomial.monic.is_primitive (monic hx))).1 (irreducible hx) },
  { have htower := is_scalar_tower.aeval_apply α f.codomain γ x (minimal_polynomial hx),
    simp only [localization_map.algebra_map_eq, aeval] at htower,
    exact htower.symm },
  { exact monic_map _ (monic hx) }
end

variable (β)
/--If L/K is a field extension, and x is an element of L in the image of K,
then the minimal polynomial of x is X - C x.-/
lemma eq_X_sub_C (a : α) :
  minimal_polynomial (@is_integral_algebra_map α β _ _ _ a) =
  X - C a :=
eq.symm $ unique' (@is_integral_algebra_map α β _ _ _ a) (irreducible_X_sub_C a)
  (by rw [alg_hom.map_sub, aeval_X, aeval_C, sub_self]) (monic_X_sub_C a)
variable {β}

/--The minimal polynomial of 0 is X.-/
@[simp] lemma zero {h₀ : is_integral α (0:β)} :
  minimal_polynomial h₀ = X :=
by simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, ring_hom.map_zero]
  using eq_X_sub_C β (0:α)

/--The minimal polynomial of 1 is X - 1.-/
@[simp] lemma one {h₁ : is_integral α (1:β)} :
  minimal_polynomial h₁ = X - 1 :=
by simpa only [ring_hom.map_one, C_1, sub_eq_add_neg]
  using eq_X_sub_C β (1:α)

end ring

section domain
variables [domain β] [algebra α β]
variables {x : β} (hx : is_integral α x)

/--A minimal polynomial is prime.-/
lemma prime : prime (minimal_polynomial hx) :=
begin
  refine ⟨ne_zero hx, not_is_unit hx, _⟩,
  rintros p q ⟨d, h⟩,
  have :    polynomial.aeval x (p*q) = 0 := by simp [h, aeval hx],
  replace : polynomial.aeval x p = 0 ∨ polynomial.aeval x q = 0 := by simpa,
  exact or.imp (dvd hx) (dvd hx) this
end

/--If L/K is a field extension and an element y of K is a root of the minimal polynomial
of an element x ∈ L, then y maps to x under the field embedding.-/
lemma root {x : β} (hx : is_integral α x) {y : α}
  (h : is_root (minimal_polynomial hx) y) : algebra_map α β y = x :=
have key : minimal_polynomial hx = X - C y :=
eq_of_monic_of_associated (monic hx) (monic_X_sub_C y) (associated_of_dvd_dvd
  (dvd_symm_of_irreducible (irreducible_X_sub_C y) (irreducible hx) (dvd_iff_is_root.2 h))
  (dvd_iff_is_root.2 h)),
by { have := aeval hx, rwa [key, alg_hom.map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this }

/--The constant coefficient of the minimal polynomial of x is 0
if and only if x = 0.-/
@[simp] lemma coeff_zero_eq_zero : coeff (minimal_polynomial hx) 0 = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have zero_root := zero_is_root_of_coeff_zero_eq_zero h,
    rw ← root hx zero_root,
    exact ring_hom.map_zero _ },
  { rintro rfl, simp }
end

/--The minimal polynomial of a nonzero element has nonzero constant coefficient.-/
lemma coeff_zero_ne_zero (h : x ≠ 0) : coeff (minimal_polynomial hx) 0 ≠ 0 :=
by { contrapose! h, simpa using h }

end domain

end field

end minimal_polynomial
