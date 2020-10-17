/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

TODO: Provide a GCD monoid instance for `ℕ`, port GCD facts about nats
TODO: Generalize normalization monoids commutative (cancellative) monoids with or without zero
TODO: Generalize GCD monoid to not require normalization in all cases
-/
import algebra.associated

/-!

# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `comm_cancel_monoid_with_zero`s, including `integral_domain`s.

## Main Definitions

* `normalization_monoid`
* `gcd_monoid`

## Implementation Notes

* `normalization_monoid` is defined by assigning to each element a `norm_unit` such that multiplying
by that unit normalizes the monoid, and `normalize` is an idempotent monoid homomorphism. This
definition as currently implemented does casework on `0`.

* `gcd_monoid` extends `normalization_monoid`, so the `gcd` and `lcm` are always normalized.
This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains, and monoids
without zero.

## TODO

* Provide a GCD monoid instance for `ℕ`, port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero
* Generalize GCD monoid to not require normalization in all cases


## Tags

divisibility, gcd, lcm, normalize

-/

variables {α : Type*}

set_option old_structure_cmd true



/-- Normalization monoid: multiplying with `norm_unit` gives a normal form for associated elements. -/
@[protect_proj] class normalization_monoid (α : Type*) [nontrivial α]
  [comm_cancel_monoid_with_zero α] :=
(norm_unit : α → units α)
(norm_unit_zero      : norm_unit 0 = 1)
(norm_unit_mul       : ∀{a b}, a ≠ 0 → b ≠ 0 → norm_unit (a * b) = norm_unit a * norm_unit b)
(norm_unit_coe_units : ∀(u : units α), norm_unit u = u⁻¹)

export normalization_monoid (norm_unit norm_unit_zero norm_unit_mul norm_unit_coe_units)

attribute [simp] norm_unit_coe_units norm_unit_zero norm_unit_mul

section normalization_monoid
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α]

@[simp] theorem norm_unit_one : norm_unit (1:α) = 1 :=
norm_unit_coe_units 1

/-- Chooses an element of each associate class, by multiplying by `norm_unit` -/
def normalize : α →* α :=
{ to_fun := λ x, x * norm_unit x,
  map_one' := by rw [norm_unit_one, units.coe_one, mul_one],
  map_mul' := λ x y,
  classical.by_cases (λ hx : x = 0, by rw [hx, zero_mul, zero_mul, zero_mul]) $ λ hx,
  classical.by_cases (λ hy : y = 0, by rw [hy, mul_zero, zero_mul, mul_zero]) $ λ hy,
  by simp only [norm_unit_mul hx hy, units.coe_mul]; simp only [mul_assoc, mul_left_comm y], }

theorem associated_normalize {x : α} : associated x (normalize x) :=
⟨_, rfl⟩

theorem normalize_associated {x : α} : associated (normalize x) x :=
associated_normalize.symm

lemma associates.mk_normalize {x : α} : associates.mk (normalize x) = associates.mk x :=
associates.mk_eq_mk_iff_associated.2 normalize_associated

@[simp] lemma normalize_apply {x : α} : normalize x = x * norm_unit x := rfl

@[simp] lemma normalize_zero : normalize (0 : α) = 0 := by simp

@[simp] lemma normalize_one : normalize (1 : α) = 1 := normalize.map_one

lemma normalize_coe_units (u : units α) : normalize (u : α) = 1 := by simp

lemma normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
⟨λ hx, (associated_zero_iff_eq_zero x).1 $ hx ▸ associated_normalize, by rintro rfl; exact normalize_zero⟩

lemma normalize_eq_one {x : α} : normalize x = 1 ↔ is_unit x :=
⟨λ hx, is_unit_iff_exists_inv.2 ⟨_, hx⟩, λ ⟨u, hu⟩, hu ▸ normalize_coe_units u⟩

@[simp] theorem norm_unit_mul_norm_unit (a : α) : norm_unit (a * norm_unit a) = 1 :=
classical.by_cases (assume : a = 0, by simp only [this, norm_unit_zero, zero_mul]) $
  assume h, by rw [norm_unit_mul h (units.ne_zero _), norm_unit_coe_units, mul_inv_eq_one]

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp

theorem normalize_eq_normalize {a b : α}
  (hab : a ∣ b) (hba : b ∣ a) : normalize a = normalize b :=
begin
  rcases associated_of_dvd_dvd hab hba with ⟨u, rfl⟩,
  refine classical.by_cases (by rintro rfl; simp only [zero_mul]) (assume ha : a ≠ 0, _),
  suffices : a * ↑(norm_unit a) = a * ↑u * ↑(norm_unit a) * ↑u⁻¹,
    by simpa only [normalize_apply, mul_assoc, norm_unit_mul ha u.ne_zero, norm_unit_coe_units],
  calc a * ↑(norm_unit a) = a * ↑(norm_unit a) * ↑u * ↑u⁻¹:
      (units.mul_inv_cancel_right _ _).symm
    ... = a * ↑u * ↑(norm_unit a) * ↑u⁻¹ : by rw mul_right_comm a
end

lemma normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x :=
⟨λ h, ⟨units.dvd_mul_right.1 ⟨_, h.symm⟩, units.dvd_mul_right.1 ⟨_, h⟩⟩,
λ ⟨hxy, hyx⟩, normalize_eq_normalize hxy hyx⟩

theorem dvd_antisymm_of_normalize_eq {a b : α}
  (ha : normalize a = a) (hb : normalize b = b) (hab : a ∣ b) (hba : b ∣ a) :
  a = b :=
ha ▸ hb ▸ normalize_eq_normalize hab hba

--can be proven by simp
lemma dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
units.dvd_mul_right

--can be proven by simp
lemma normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
units.mul_right_dvd

end normalization_monoid

namespace comm_group_with_zero
variables [decidable_eq α] [comm_group_with_zero α]

@[priority 100] -- see Note [lower instance priority]
instance : normalization_monoid α :=
{ norm_unit := λ x, if h : x = 0 then 1 else (units.mk0 x h)⁻¹,
  norm_unit_zero := dif_pos rfl,
  norm_unit_mul := λ x y x0 y0, units.eq_iff.1 (by simp [x0, y0, mul_inv']),
  norm_unit_coe_units := λ u, by { rw [dif_neg (units.ne_zero _), units.mk0_coe], apply_instance } }

@[simp]
lemma coe_norm_unit {a : α} (h0 : a ≠ 0) : (↑(norm_unit a) : α) = a⁻¹ :=
by simp [norm_unit, h0]

end comm_group_with_zero

namespace associates
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [normalization_monoid α]

local attribute [instance] associated.setoid

/-- Maps an element of `associates` back to the normalized element of its associate class -/
protected def out : associates α → α :=
quotient.lift (normalize : α → α) $ λ a b ⟨u, hu⟩, hu ▸
normalize_eq_normalize ⟨_, rfl⟩ (units.mul_right_dvd.2 $ dvd_refl a)

lemma out_mk (a : α) : (associates.mk a).out = normalize a := rfl

@[simp] lemma out_one : (1 : associates α).out = 1 :=
normalize_one

lemma out_mul (a b : associates α) : (a * b).out = a.out * b.out :=
quotient.induction_on₂ a b $ assume a b,
by simp only [associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize.map_mul]

lemma dvd_out_iff (a : α) (b : associates α) : a ∣ b.out ↔ associates.mk a ≤ b :=
quotient.induction_on b $ by simp [associates.out_mk, associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

lemma out_dvd_iff (a : α) (b : associates α) : b.out ∣ a ↔ b ≤ associates.mk a :=
quotient.induction_on b $ by simp [associates.out_mk, associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

@[simp] lemma out_top : (⊤ : associates α).out = 0 :=
normalize_zero

@[simp] lemma normalize_out (a : associates α) : normalize a.out = a.out :=
quotient.induction_on a normalize_idem

end associates

/-- GCD monoid: a `comm_cancel_monoid_with_zero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`.
-/
@[protect_proj] class gcd_monoid (α : Type*) [comm_cancel_monoid_with_zero α] [nontrivial α]
  extends normalization_monoid α :=
(gcd : α → α → α)
(lcm : α → α → α)
(gcd_dvd_left   : ∀a b, gcd a b ∣ a)
(gcd_dvd_right  : ∀a b, gcd a b ∣ b)
(dvd_gcd        : ∀{a b c}, a ∣ c → a ∣ b → a ∣ gcd c b)
(normalize_gcd  : ∀a b, normalize (gcd a b) = gcd a b)
(gcd_mul_lcm    : ∀a b, gcd a b * lcm a b = normalize (a * b))
(lcm_zero_left  : ∀a, lcm 0 a = 0)
(lcm_zero_right : ∀a, lcm a 0 = 0)

export gcd_monoid (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd  lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

section gcd_monoid
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]

@[simp] theorem normalize_gcd : ∀a b:α, normalize (gcd a b) = gcd a b :=
gcd_monoid.normalize_gcd

@[simp] theorem gcd_mul_lcm : ∀a b:α, gcd a b * lcm a b = normalize (a * b) :=
gcd_monoid.gcd_mul_lcm

section gcd

theorem dvd_gcd_iff (a b c : α) : a ∣ gcd b c ↔ (a ∣ b ∧ a ∣ c) :=
iff.intro
  (assume h, ⟨dvd_trans h (gcd_dvd_left _ _), dvd_trans h (gcd_dvd_right _ _)⟩)
  (assume ⟨hab, hac⟩, dvd_gcd hab hac)

theorem gcd_comm (a b : α) : gcd a b = gcd b a :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
  (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_assoc (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (dvd_gcd
    (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
    (dvd_gcd (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
  (dvd_gcd
    (dvd_gcd (gcd_dvd_left m (gcd n k)) (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
    (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

instance : is_commutative α gcd := ⟨gcd_comm⟩
instance : is_associative α gcd := ⟨gcd_assoc⟩

theorem gcd_eq_normalize {a b c : α} (habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) :
  gcd a b = normalize c :=
normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp] theorem gcd_zero_left (a : α) : gcd 0 a = normalize a :=
gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp] theorem gcd_zero_right (a : α) : gcd a 0 = normalize a :=
gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp] theorem gcd_eq_zero_iff (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume h, let ⟨ca, ha⟩ := gcd_dvd_left a b, ⟨cb, hb⟩ := gcd_dvd_right a b in
    by rw [h, zero_mul] at ha hb; exact ⟨ha, hb⟩)
  (assume ⟨ha, hb⟩, by rw [ha, hb, gcd_zero_left, normalize_zero])

@[simp] theorem gcd_one_left (a : α) : gcd 1 a = 1 :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp] theorem gcd_one_right (a : α) : gcd a 1 = 1 :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

theorem gcd_dvd_gcd {a b c d: α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
dvd_gcd (dvd.trans (gcd_dvd_left _ _) hab) (dvd.trans (gcd_dvd_right _ _) hcd)

@[simp] theorem gcd_same (a : α) : gcd a a = normalize a :=
gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp] theorem gcd_mul_left (a b c : α) : gcd (a * b) (a * c) = normalize a * gcd b c :=
classical.by_cases (by rintro rfl; simp only [zero_mul, gcd_zero_left, normalize_zero]) $ assume ha : a ≠ 0,
suffices gcd (a * b) (a * c) = normalize (a * gcd b c),
  by simpa only [normalize.map_mul, normalize_gcd],
let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c) in
gcd_eq_normalize
  (eq.symm ▸ mul_dvd_mul_left a $ show d ∣ gcd b c, from
    dvd_gcd
      ((mul_dvd_mul_iff_left ha).1 $ eq ▸ gcd_dvd_left _ _)
      ((mul_dvd_mul_iff_left ha).1 $ eq ▸ gcd_dvd_right _ _))
  (dvd_gcd
    (mul_dvd_mul_left a $ gcd_dvd_left _ _)
    (mul_dvd_mul_left a $ gcd_dvd_right _ _))

@[simp] theorem gcd_mul_right (a b c : α) : gcd (b * a) (c * a) = gcd b c * normalize a :=
by simp only [mul_comm, gcd_mul_left]

theorem gcd_eq_left_iff (a b : α) (h : normalize a = a) : gcd a b = a ↔ a ∣ b :=
iff.intro (assume eq, eq ▸ gcd_dvd_right _ _) $
  assume hab, dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

theorem gcd_eq_right_iff (a b : α) (h : normalize b = b) : gcd a b = b ↔ b ∣ a :=
by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

theorem gcd_dvd_gcd_mul_left (m n k : α) : gcd m n ∣ gcd (k * m) n :=
gcd_dvd_gcd (dvd_mul_left _ _) (dvd_refl _)

theorem gcd_dvd_gcd_mul_right (m n k : α) : gcd m n ∣ gcd (m * k) n :=
gcd_dvd_gcd (dvd_mul_right _ _) (dvd_refl _)

theorem gcd_dvd_gcd_mul_left_right (m n k : α) : gcd m n ∣ gcd m (k * n) :=
gcd_dvd_gcd (dvd_refl _) (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : α) : gcd m n ∣ gcd m (n * k) :=
gcd_dvd_gcd (dvd_refl _) (dvd_mul_right _ _)

theorem gcd_eq_of_associated_left {m n : α} (h : associated m n) (k : α) : gcd m k = gcd n k :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (gcd_dvd_gcd (dvd_of_associated h) (dvd_refl _))
  (gcd_dvd_gcd (dvd_of_associated h.symm) (dvd_refl _))

theorem gcd_eq_of_associated_right {m n : α} (h : associated m n) (k : α) : gcd k m = gcd k n :=
dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  (gcd_dvd_gcd (dvd_refl _) (dvd_of_associated h))
  (gcd_dvd_gcd (dvd_refl _) (dvd_of_associated h.symm))

lemma dvd_gcd_mul_of_dvd_mul {m n k : α} (H : k ∣ m * n) : k ∣ (gcd k m) * n :=
begin
  transitivity gcd k m * normalize n,
  { rw ← gcd_mul_right,
    exact dvd_gcd (dvd_mul_right _ _) H },
  { apply dvd.intro ↑(norm_unit n)⁻¹,
    rw [normalize_apply, mul_assoc, mul_assoc, ← units.coe_mul],
    simp }
end

lemma dvd_mul_gcd_of_dvd_mul {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n :=
by { rw mul_comm at H ⊢, exact dvd_gcd_mul_of_dvd_mul H }

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

 Note: In general, this representation is highly non-unique. -/
lemma exists_dvd_and_dvd_of_dvd_mul {m n k : α} (H : k ∣ m * n) :
  ∃ d₁ (hd₁ : d₁ ∣ m) d₂ (hd₂ : d₂ ∣ n), k = d₁ * d₂ :=
begin
  by_cases h0 : gcd k m = 0,
  { rw gcd_eq_zero_iff at h0,
    rcases h0 with ⟨rfl, rfl⟩,
    refine ⟨0, dvd_refl 0, n, dvd_refl n, _⟩,
    simp },
  { obtain ⟨a, ha⟩ := gcd_dvd_left k m,
    refine ⟨gcd k m, gcd_dvd_right _ _, a, _, ha⟩,
    suffices h : gcd k m * a ∣ gcd k m * n,
    { cases h with b hb,
      use b,
      rw mul_assoc at hb,
      apply mul_left_cancel' h0 hb },
    rw ← ha,
    exact dvd_gcd_mul_of_dvd_mul H }
end

theorem gcd_mul_dvd_mul_gcd (k m n : α) : gcd k (m * n) ∣ gcd k m * gcd k n :=
begin
  obtain ⟨m', hm', n', hn', h⟩ := (exists_dvd_and_dvd_of_dvd_mul $ gcd_dvd_right k (m * n)),
  replace h : gcd k (m * n) = m' * n' := h,
  rw h,
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _,
  apply mul_dvd_mul,
  { have hm'k : m' ∣ k := dvd_trans (dvd_mul_right m' n') hm'n',
    exact dvd_gcd hm'k hm' },
  { have hn'k : n' ∣ k := dvd_trans (dvd_mul_left n' m') hm'n',
    exact dvd_gcd hn'k hn' }
end

theorem gcd_pow_right_dvd_pow_gcd {a b : α} {k : ℕ} : gcd a (b ^ k) ∣ (gcd a b) ^ k :=
begin
  by_cases hg : gcd a b = 0,
  { rw gcd_eq_zero_iff at hg,
    rcases hg with ⟨rfl, rfl⟩,
    simp },
  { induction k with k hk, simp,
    rw [pow_succ, pow_succ],
    transitivity gcd a b * gcd a (b ^ k),
    apply gcd_mul_dvd_mul_gcd a b (b ^ k),
    refine (mul_dvd_mul_iff_left hg).mpr hk }
end

theorem gcd_pow_left_dvd_pow_gcd {a b : α} {k : ℕ} : gcd (a ^ k) b ∣ (gcd a b) ^ k :=
by { rw [gcd_comm, gcd_comm a b], exact gcd_pow_right_dvd_pow_gcd }

theorem pow_dvd_of_mul_eq_pow {a b c d₁ d₂ : α} (ha : a ≠ 0)
  (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) (hc : c = d₁ * d₂)
  (hd₁ : d₁ ∣ a) : d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a :=
begin
  have h1 : gcd (d₁ ^ k) b = 1,
  { rw ← normalize_gcd (d₁ ^ k) b, rw normalize_eq_one,
    apply is_unit_of_dvd_one,
    transitivity (gcd d₁ b) ^ k,
    { exact gcd_pow_left_dvd_pow_gcd },
    { apply is_unit.dvd, apply is_unit.pow, apply is_unit_of_dvd_one,
      rw ← hab, apply gcd_dvd_gcd hd₁ (dvd_refl b) } },
  have h2 : d₁ ^ k ∣ a * b, { use d₂ ^ k, rw [h, hc], exact mul_pow d₁ d₂ k },
  rw mul_comm at h2,
  have h3 : d₁ ^ k ∣ a, { rw [← one_mul a, ← h1], apply dvd_gcd_mul_of_dvd_mul h2 },
  have h4 : d₁ ^ k ≠ 0,
  { intro hdk, rw hdk at h3, apply absurd (zero_dvd_iff.mp h3) ha },
  tauto
end

theorem exists_associated_pow_of_mul_eq_pow {a b c : α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : gcd a b = 1) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : α), associated (d ^ k) a :=
begin
  by_cases hk : k = 0,
  { use 1, rw [hk, pow_zero] at h ⊢, use units.mk_of_mul_eq_one _ _ h,
    rw [units.coe_mk_of_mul_eq_one, one_mul] },
  have hc : c ∣ a * b, { rw h, refine dvd_pow (dvd_refl c) hk },
  obtain ⟨d₁, hd₁, d₂, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc,
  use d₁,
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁,
  rw [mul_comm] at h hc, rw [gcd_comm] at hab,
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂,
  rw [ha', hb', hc, mul_pow] at h,
  have h' : a' * b' = 1,
  { apply (mul_right_inj' h0₁).mp, rw mul_one,
    apply (mul_right_inj' h0₂).mp, rw ← h,
    rw [mul_assoc, mul_comm a', ← mul_assoc (d₁ ^ k), ← mul_assoc _ (d₁ ^ k), mul_comm b'] },
  use units.mk_of_mul_eq_one _ _ h',
  rw [units.coe_mk_of_mul_eq_one, ha']
end

end gcd

section lcm

lemma lcm_dvd_iff {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c :=
classical.by_cases
  (assume : a = 0 ∨ b = 0, by rcases this with rfl | rfl;
    simp only [iff_def, lcm_zero_left, lcm_zero_right, zero_dvd_iff, dvd_zero,
      eq_self_iff_true, and_true, imp_true_iff] {contextual:=tt})
  (assume this : ¬ (a = 0 ∨ b = 0),
    let ⟨h1, h2⟩ := not_or_distrib.1 this in
    have h : gcd a b ≠ 0, from λ H, h1 ((gcd_eq_zero_iff _ _).1 H).1,
    by rw [← mul_dvd_mul_iff_left h, gcd_mul_lcm, normalize_dvd_iff, ← dvd_normalize_iff,
        normalize.map_mul, normalize_gcd, ← gcd_mul_right, dvd_gcd_iff,
        mul_comm b c, mul_dvd_mul_iff_left h1, mul_dvd_mul_iff_right h2, and_comm])

lemma dvd_lcm_left (a b : α) : a ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl _)).1

lemma dvd_lcm_right (a b : α) : b ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl _)).2

lemma lcm_dvd {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp] theorem lcm_eq_zero_iff (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
iff.intro
  (assume h : lcm a b = 0,
    have normalize (a * b) = 0,
      by rw [← gcd_mul_lcm _ _, h, mul_zero],
    by simpa only [normalize_eq_zero, mul_eq_zero, units.ne_zero, or_false])
  (by rintro (rfl | rfl); [apply lcm_zero_left, apply lcm_zero_right])

@[simp] lemma normalize_lcm (a b : α) : normalize (lcm a b) = lcm a b :=
classical.by_cases (assume : lcm a b = 0, by rw [this, normalize_zero]) $
  assume h_lcm : lcm a b ≠ 0,
  have h1 : gcd a b ≠ 0, from mt (by rw [gcd_eq_zero_iff, lcm_eq_zero_iff];
    rintros ⟨rfl, rfl⟩; left; refl) h_lcm,
  have h2 : normalize (gcd a b * lcm a b) = gcd a b * lcm a b,
    by rw [gcd_mul_lcm, normalize_idem],
  by simpa only [normalize.map_mul, normalize_gcd, one_mul, mul_right_inj' h1] using h2

theorem lcm_comm (a b : α) : lcm a b = lcm b a :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
  (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_assoc (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left _ _) (dvd.trans (dvd_lcm_left _ _) (dvd_lcm_right _ _)))
    (dvd.trans (dvd_lcm_right _ _) (dvd_lcm_right _ _)))
  (lcm_dvd
    (dvd.trans (dvd_lcm_left _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd.trans (dvd_lcm_right _ _) (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

instance : is_commutative α lcm := ⟨lcm_comm⟩
instance : is_associative α lcm := ⟨lcm_assoc⟩

lemma lcm_eq_normalize {a b c : α} (habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) :
  lcm a b = normalize c :=
normalize_lcm a b ▸ normalize_eq_normalize habc hcab

theorem lcm_dvd_lcm {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
lcm_dvd (dvd.trans hab (dvd_lcm_left _ _)) (dvd.trans hcd (dvd_lcm_right _ _))

@[simp] theorem lcm_units_coe_left (u : units α) (a : α) : lcm ↑u a = normalize a :=
lcm_eq_normalize (lcm_dvd units.coe_dvd (dvd_refl _)) (dvd_lcm_right _ _)

@[simp] theorem lcm_units_coe_right (a : α) (u : units α) : lcm a ↑u = normalize a :=
(lcm_comm a u).trans $ lcm_units_coe_left _ _

@[simp] theorem lcm_one_left (a : α) : lcm 1 a = normalize a :=
lcm_units_coe_left 1 a

@[simp] theorem lcm_one_right (a : α) : lcm a 1 = normalize a :=
lcm_units_coe_right a 1

@[simp] theorem lcm_same (a : α) : lcm a a = normalize a :=
lcm_eq_normalize (lcm_dvd (dvd_refl _) (dvd_refl _)) (dvd_lcm_left _ _)

@[simp] theorem lcm_eq_one_iff (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
iff.intro
  (assume eq, eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩)
  (assume ⟨⟨c, hc⟩, ⟨d, hd⟩⟩,
    show lcm (units.mk_of_mul_eq_one a c hc.symm : α) (units.mk_of_mul_eq_one b d hd.symm) = 1,
      by rw [lcm_units_coe_left, normalize_coe_units])

@[simp] theorem lcm_mul_left (a b c : α) : lcm (a * b) (a * c) = normalize a * lcm b c :=
classical.by_cases (by rintro rfl; simp only [zero_mul, lcm_zero_left, normalize_zero]) $ assume ha : a ≠ 0,
suffices lcm (a * b) (a * c) = normalize (a * lcm b c),
  by simpa only [normalize.map_mul, normalize_lcm],
have a ∣ lcm (a * b) (a * c), from dvd.trans (dvd_mul_right _ _) (dvd_lcm_left _ _),
let ⟨d, eq⟩ := this in
lcm_eq_normalize
  (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
  (eq.symm ▸ (mul_dvd_mul_left a $ lcm_dvd
    ((mul_dvd_mul_iff_left ha).1 $ eq ▸ dvd_lcm_left _ _)
    ((mul_dvd_mul_iff_left ha).1 $ eq ▸ dvd_lcm_right _ _)))

@[simp] theorem lcm_mul_right (a b c : α) : lcm (b * a) (c * a) = lcm b c * normalize a :=
by simp only [mul_comm, lcm_mul_left]

theorem lcm_eq_left_iff (a b : α) (h : normalize a = a) : lcm a b = a ↔ b ∣ a :=
iff.intro (assume eq, eq ▸ dvd_lcm_right _ _) $
  assume hab, dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

theorem lcm_eq_right_iff (a b : α) (h : normalize b = b) : lcm a b = b ↔ a ∣ b :=
by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

theorem lcm_dvd_lcm_mul_left (m n k : α) : lcm m n ∣ lcm (k * m) n :=
lcm_dvd_lcm (dvd_mul_left _ _) (dvd_refl _)

theorem lcm_dvd_lcm_mul_right (m n k : α) : lcm m n ∣ lcm (m * k) n :=
lcm_dvd_lcm (dvd_mul_right _ _) (dvd_refl _)

theorem lcm_dvd_lcm_mul_left_right (m n k : α) : lcm m n ∣ lcm m (k * n) :=
lcm_dvd_lcm (dvd_refl _) (dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right (m n k : α) : lcm m n ∣ lcm m (n * k) :=
lcm_dvd_lcm (dvd_refl _) (dvd_mul_right _ _)

theorem lcm_eq_of_associated_left {m n : α} (h : associated m n) (k : α) : lcm m k = lcm n k :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd_lcm (dvd_of_associated h) (dvd_refl _))
  (lcm_dvd_lcm (dvd_of_associated h.symm) (dvd_refl _))

theorem lcm_eq_of_associated_right {m n : α} (h : associated m n) (k : α) : lcm k m = lcm k n :=
dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
  (lcm_dvd_lcm (dvd_refl _) (dvd_of_associated h))
  (lcm_dvd_lcm (dvd_refl _) (dvd_of_associated h.symm))

end lcm

namespace gcd_monoid
theorem prime_of_irreducible {x : α} (hi: irreducible x) : prime x :=
⟨hi.ne_zero, ⟨hi.1, λ a b h,
begin
  cases gcd_dvd_left x a with y hy,
  cases hi.2 _ _ hy with hu hu; cases hu with u hu,
  { right, transitivity (gcd (x * b) (a * b)), apply dvd_gcd (dvd_mul_right x b) h,
    rw gcd_mul_right, rw ← hu,
    apply dvd_of_associated, transitivity (normalize b), symmetry, use u, apply mul_comm,
    apply normalize_associated, },
  { left, rw [hy, ← hu],
    transitivity, {apply dvd_of_associated, symmetry, use u}, apply gcd_dvd_right, }
end ⟩⟩

theorem irreducible_iff_prime {p : α} : irreducible p ↔ prime p :=
⟨prime_of_irreducible, irreducible_of_prime⟩

end gcd_monoid
end gcd_monoid

section unique_unit

variables [comm_cancel_monoid_with_zero α] [unique (units α)]

lemma units_eq_one (u : units α) : u = 1 := subsingleton.elim u 1

variable [nontrivial α]

@[priority 100] -- see Note [lower instance priority]
instance normalization_monoid_of_unique_units : normalization_monoid α :=
{ norm_unit := λ x, 1,
  norm_unit_zero := rfl,
  norm_unit_mul := λ x y hx hy, (mul_one 1).symm,
  norm_unit_coe_units := λ u, subsingleton.elim _ _ }

@[simp] lemma norm_unit_eq_one (x : α) : norm_unit x = 1 := rfl

@[simp] lemma normalize_eq (x : α) : normalize x = x := mul_one x

end unique_unit

section integral_domain

variables [integral_domain α] [gcd_monoid α]

lemma gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c :=
begin
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _);
  rw dvd_gcd_iff; refine ⟨gcd_dvd_left _ _, _⟩,
  { rcases h with ⟨d, hd⟩,
    rcases gcd_dvd_right a b with ⟨e, he⟩,
    rcases gcd_dvd_left a b with ⟨f, hf⟩,
    use e - f * d,
    rw [mul_sub, ← he, ← mul_assoc, ← hf, ← hd, sub_sub_cancel] },
  { rcases h with ⟨d, hd⟩,
    rcases gcd_dvd_right a c with ⟨e, he⟩,
    rcases gcd_dvd_left a c with ⟨f, hf⟩,
    use e + f * d,
    rw [mul_add, ← he, ← mul_assoc, ← hf, ← hd, ← add_sub_assoc, add_comm c b, add_sub_cancel] }
end

lemma gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a :=
by rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]

end integral_domain
