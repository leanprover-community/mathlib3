/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.localization.at_prime
import ring_theory.localization.basic
import ring_theory.localization.fraction_ring

/-!
# Localizations of localizations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) {S : Type*} [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

open function
open_locale big_operators

namespace is_localization

section localization_localization

variable (M)

variables (N : submonoid S) (T : Type*) [comm_ring T] [algebra R T]

section

variables [algebra S T] [is_scalar_tower R S T]

/--
Localizing wrt `M ⊆ R` and then wrt `N ⊆ S = M⁻¹R` is equal to the localization of `R` wrt this
module. See `localization_localization_is_localization`.
-/
-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
@[nolint unused_arguments]
def localization_localization_submodule : submonoid R :=
(N ⊔ M.map (algebra_map R S)).comap (algebra_map R S)

variables {M N}
@[simp]
lemma mem_localization_localization_submodule {x : R} :
  x ∈ localization_localization_submodule M N ↔
    ∃ (y : N) (z : M), algebra_map R S x = y * algebra_map R S z :=
begin
  rw [localization_localization_submodule, submonoid.mem_comap, submonoid.mem_sup],
  split,
  { rintros ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩, exact ⟨⟨y, hy⟩, ⟨z, hz⟩ ,e.symm⟩ },
  { rintros ⟨y, z, e⟩, exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩ }
end

variables (M N) [is_localization M S]

lemma localization_localization_map_units [is_localization N T]
  (y : localization_localization_submodule M N) : is_unit (algebra_map R T y) :=
begin
  obtain ⟨y', z, eq⟩ := mem_localization_localization_submodule.mp y.prop,
  rw [is_scalar_tower.algebra_map_apply R S T, eq, ring_hom.map_mul, is_unit.mul_iff],
  exact ⟨is_localization.map_units T y',
    (is_localization.map_units _ z).map (algebra_map S T)⟩,
end

lemma localization_localization_surj [is_localization N T] (x : T) :
  ∃ (y : R × localization_localization_submodule M N),
    x * (algebra_map R T y.2) = algebra_map R T y.1 :=
begin
  rcases is_localization.surj N x with ⟨⟨y, s⟩, eq₁⟩, -- x = y / s
  rcases is_localization.surj M y with ⟨⟨z, t⟩, eq₂⟩, -- y = z / t
  rcases is_localization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩, -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃,
  use z * t', use z' * t, -- x = y / s = (z * t') / (z' * t)
  { rw mem_localization_localization_submodule,
    refine ⟨s, t * t', _⟩,
    rw [ring_hom.map_mul, ← eq₃, mul_assoc, ← ring_hom.map_mul, mul_comm t, submonoid.coe_mul] },
  { simp only [subtype.coe_mk, ring_hom.map_mul, is_scalar_tower.algebra_map_apply R S T,
      ← eq₃, ← eq₂, ← eq₁],
    ring },
end

lemma localization_localization_eq_iff_exists [is_localization N T] (x y : R) :
  algebra_map R T x = algebra_map R T y ↔
    ∃ (c : localization_localization_submodule M N), ↑c * x = ↑c * y :=
begin
  rw [is_scalar_tower.algebra_map_apply R S T, is_scalar_tower.algebra_map_apply R S T,
      is_localization.eq_iff_exists N T],
  split,
  { rintros ⟨z, eq₁⟩,
    rcases is_localization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩,
    dsimp only at eq₂,
    obtain ⟨c, eq₃ :  ↑c * (x * z') = ↑c * (y * z')⟩ := (is_localization.eq_iff_exists M S).mp _,
    swap,
    { rw [map_mul, map_mul, ←eq₂, ←mul_assoc, ←mul_assoc, mul_comm _ ↑z, eq₁, mul_comm _ ↑z] },
    use c * z',
    { rw mem_localization_localization_submodule,
      refine ⟨z, c * s, _⟩,
      rw [map_mul, ← eq₂, submonoid.coe_mul, map_mul, mul_left_comm] },
    { rwa [mul_comm _ z', mul_comm _ z', ←mul_assoc, ←mul_assoc] at eq₃ } },
  { rintro ⟨⟨c, hc⟩, eq₁ : c * x = c * y⟩,
    rw mem_localization_localization_submodule at hc,
    rcases hc with ⟨z₁, z, eq₂⟩,
    use z₁,
    refine (is_localization.map_units S z).mul_right_inj.mp _,
    rw [←mul_assoc, mul_comm _ ↑z₁, ←eq₂, ←map_mul, eq₁, map_mul, eq₂, ←mul_assoc, mul_comm _ ↑z₁] }
end

/--
Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization is a localization.
-/
lemma localization_localization_is_localization [is_localization N T] :
  is_localization (localization_localization_submodule M N) T :=
{ map_units := localization_localization_map_units M N T,
  surj := localization_localization_surj M N T,
  eq_iff_exists := localization_localization_eq_iff_exists M N T }

include M

/--
Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the localization of a
localization is a localization.
-/
lemma localization_localization_is_localization_of_has_all_units
  [is_localization N T] (H : ∀ (x : S), is_unit x → x ∈ N) :
  is_localization (N.comap (algebra_map R S)) T :=
begin
  convert localization_localization_is_localization M N T,
  symmetry,
  rw sup_eq_left,
  rintros _ ⟨x, hx, rfl⟩,
  exact H _ (is_localization.map_units _ ⟨x, hx⟩),
end

/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
lemma is_localization_is_localization_at_prime_is_localization (p : ideal S) [Hp : p.is_prime]
  [is_localization.at_prime T p] :
  is_localization.at_prime T (p.comap (algebra_map R S)) :=
begin
  apply localization_localization_is_localization_of_has_all_units M p.prime_compl T,
  intros x hx hx',
  exact (Hp.1 : ¬ _) (p.eq_top_of_is_unit_mem hx' hx),
end

instance (p : ideal (localization M)) [p.is_prime] : algebra R (localization.at_prime p) :=
localization.algebra

instance (p : ideal (localization M)) [p.is_prime] :
  is_scalar_tower R (localization M) (localization.at_prime p) :=
is_scalar_tower.of_algebra_map_eq' rfl

instance localization_localization_at_prime_is_localization (p : ideal (localization M))
  [p.is_prime] : is_localization.at_prime (localization.at_prime p) (p.comap (algebra_map R _)) :=
is_localization_is_localization_at_prime_is_localization M _ _

/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` the localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R` at `f⁻¹(p)`.
-/
noncomputable
def localization_localization_at_prime_iso_localization (p : ideal (localization M)) [p.is_prime] :
  localization.at_prime (p.comap (algebra_map R (localization M))) ≃ₐ[R] localization.at_prime p :=
is_localization.alg_equiv (p.comap (algebra_map R (localization M))).prime_compl _ _

end

variables (S)

/-- Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`. -/
noncomputable
def localization_algebra_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T] :
  algebra S T :=
(is_localization.lift (λ y, (map_units T ⟨↑y, h y.prop⟩ : _)) : S →+* T).to_algebra

/-- If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes with the
localization maps -/
lemma localization_is_scalar_tower_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T] :
  @@is_scalar_tower R S T _ (localization_algebra_of_submonoid_le S T M N h).to_has_smul _ :=
begin
  letI := localization_algebra_of_submonoid_le S T M N h,
  exact is_scalar_tower.of_algebra_map_eq' (is_localization.lift_comp _).symm
end

noncomputable
instance (x : ideal R) [H : x.is_prime] [is_domain R] :
  algebra (localization.at_prime x) (localization (non_zero_divisors R)) :=
localization_algebra_of_submonoid_le _ _ x.prime_compl (non_zero_divisors R)
  (by { intros a ha, rw mem_non_zero_divisors_iff_ne_zero, exact λ h, ha (h.symm ▸ x.zero_mem) })

/-- If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S` at `N`. -/
lemma is_localization_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T]
  [algebra S T] [is_scalar_tower R S T] :
  is_localization (N.map (algebra_map R S)) T :=
{ map_units := begin
    rintro ⟨_, ⟨y, hy, rfl⟩⟩,
    convert is_localization.map_units T ⟨y, hy⟩,
    exact (is_scalar_tower.algebra_map_apply _ _ _ _).symm
  end,
  surj := λ y, begin
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj N y,
    refine ⟨⟨algebra_map _ _ x, _, _, s.prop, rfl⟩, _⟩,
    simpa [← is_scalar_tower.algebra_map_apply] using e
  end,
  eq_iff_exists := λ x₁ x₂, begin
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := is_localization.surj M x₁,
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := is_localization.surj M x₂,
    refine iff.trans _ (set.exists_image_iff (algebra_map R S) N (λ c, c * x₁ = c * x₂)).symm,
    dsimp only at e₁ e₂ ⊢,
    suffices : algebra_map R T (y₁ * s₂) = algebra_map R T (y₂ * s₁) ↔
      ∃ (a : N), algebra_map R S (a * (y₁ * s₂)) = algebra_map R S (a * (y₂ * s₁)),
    { have h₁ := (is_localization.map_units T ⟨_, h s₁.prop⟩).mul_left_inj,
      have h₂ := (is_localization.map_units T ⟨_, h s₂.prop⟩).mul_left_inj,
      simp only [is_scalar_tower.algebra_map_apply R S T, subtype.coe_mk] at h₁ h₂,
      simp only [is_scalar_tower.algebra_map_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebra_map R S s₂),
        mul_right_comm _ (algebra_map S T (algebra_map R S s₂)),
        (is_localization.map_units S s₁).mul_left_inj,
        (is_localization.map_units S s₂).mul_left_inj] at this,
      rw [h₂, h₁] at this,
      simpa only [mul_comm] using this },
    simp_rw [is_localization.eq_iff_exists N T, is_localization.eq_iff_exists M S],
    split,
    { rintro ⟨a, e⟩, exact ⟨a, 1, by { convert e using 1; simp; ring }⟩ },
    { rintro ⟨a, b, e⟩, exact ⟨a * (⟨_, h b.prop⟩ : N), by { convert e using 1; simp; ring }⟩ }
  end }

/-- If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then the
localization at `N` is equal to the localizaton of `M`. -/
lemma is_localization_of_is_exists_mul_mem (M N : submonoid R) [is_localization M S] (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : is_localization N S :=
{ map_units := λ y, begin
    obtain ⟨m, hm⟩ := h' y,
    have := is_localization.map_units S ⟨_, hm⟩,
    erw map_mul at this,
    exact (is_unit.mul_iff.mp this).2
  end,
  surj := λ z, by { obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M z, exact ⟨⟨y, _, h s.prop⟩, e⟩ },
  eq_iff_exists := λ x₁ x₂, begin
    rw is_localization.eq_iff_exists M,
    refine ⟨λ ⟨x, hx⟩, ⟨⟨_, h x.prop⟩, hx⟩, _⟩,
    rintros ⟨x, h⟩,
    obtain ⟨m, hm⟩ := h' x,
    refine ⟨⟨_, hm⟩, _⟩,
    simp [h, mul_assoc],
  end }

end localization_localization

end is_localization

namespace is_fraction_ring

open is_localization

variable (M)

lemma is_fraction_ring_of_is_localization (S T : Type*) [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] [algebra S T] [is_scalar_tower R S T]
  [is_localization M S] [is_fraction_ring R T] (hM : M ≤ non_zero_divisors R) :
  is_fraction_ring S T :=
begin
  have := is_localization_of_submonoid_le S T M (non_zero_divisors R) _,
  refine @@is_localization_of_is_exists_mul_mem _ _ _ _ _ _ this _ _,
  { exact map_non_zero_divisors_le M S },
  { rintro ⟨x, hx⟩,
    obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M x,
    use algebra_map R S s,
    rw [mul_comm, subtype.coe_mk, e],
    refine set.mem_image_of_mem (algebra_map R S) _,
    intros z hz,
    apply is_localization.injective S hM,
    rw map_zero,
    apply hx,
    rw [← (map_units S s).mul_left_inj, mul_assoc, e, ← map_mul, hz, map_zero, zero_mul] },
  { exact hM }
end

lemma is_fraction_ring_of_is_domain_of_is_localization [is_domain R] (S T : Type*)
  [comm_ring S] [comm_ring T] [algebra R S] [algebra R T] [algebra S T]
  [is_scalar_tower R S T] [is_localization M S] [is_fraction_ring R T] : is_fraction_ring S T :=
begin
  haveI := is_fraction_ring.nontrivial R T,
  haveI := (algebra_map S T).domain_nontrivial,
  apply is_fraction_ring_of_is_localization M S T,
  intros x hx,
  rw mem_non_zero_divisors_iff_ne_zero,
  intro hx',
  apply @zero_ne_one S,
  rw [← (algebra_map R S).map_one, ← @mk'_one R _ M, @comm _ eq, mk'_eq_zero_iff],
  exact ⟨⟨x, hx⟩, by simp [hx'] ⟩,
end

end is_fraction_ring
