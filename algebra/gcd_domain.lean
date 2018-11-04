/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

GCD domain and integral domains with normalization functions

TODO: abstract the domains to to semi domains (i.e. domains on semirings) to include ℕ and ℕ[X] etc.
-/
import algebra.ring

variables {α : Type*}

set_option old_structure_cmd true

/-- Normalization domain: multiplying with `norm_unit` gives a normal form for associated elements. -/
class normalization_domain (α : Type*) extends integral_domain α :=
(norm_unit : α → units α)
(norm_unit_zero      : norm_unit 0 = 1)
(norm_unit_mul       : ∀a b, a ≠ 0 → b ≠ 0 → norm_unit (a * b) = norm_unit a * norm_unit b)
(norm_unit_coe_units : ∀(u : units α), norm_unit u = u⁻¹)

export normalization_domain (norm_unit norm_unit_zero norm_unit_mul norm_unit_coe_units)

attribute [simp] norm_unit_coe_units norm_unit_zero norm_unit_mul

section normalization_domain
variable [normalization_domain α]

@[simp] theorem norm_unit_one : norm_unit (1:α) = 1 :=
norm_unit_coe_units 1

theorem norm_unit_mul_norm_unit (a : α) : norm_unit (a * norm_unit a) = 1 :=
classical.by_cases (assume : a = 0, by simp only [this, norm_unit_zero, zero_mul]) $
  assume h, by rw [norm_unit_mul _ _ h (units.ne_zero _), norm_unit_coe_units, mul_inv_eq_one]

theorem associated_of_dvd_of_dvd : ∀{a b : α}, a ∣ b → b ∣ a → ∃u:units α, a * u = b
| a b ⟨c, rfl⟩ ⟨d, hd⟩ :=
  classical.by_cases (assume : c = 0, ⟨1, by simp only [zero_mul, mul_zero, *] at *⟩) $ assume hc : c ≠ 0,
  classical.by_cases (assume : a = 0, ⟨1, by simp only [zero_mul, *] at *⟩) $ assume ha : a ≠ 0,
  have a * 1 = a * (c * d), by rwa [mul_one, ← mul_assoc],
  have 1 = c * d, from eq_of_mul_eq_mul_left ha this,
  ⟨units.mk_of_mul_eq_one c d this.symm, rfl⟩

theorem mul_norm_unit_eq_mul_norm_unit {a b : α}
  (hab : a ∣ b) (hba : b ∣ a) : a * norm_unit a = b * norm_unit b :=
begin
  rcases associated_of_dvd_of_dvd hab hba with ⟨u, rfl⟩,
  refine classical.by_cases (by rintro rfl; simp only [zero_mul]) (assume ha : a ≠ 0, _),
  suffices : a * ↑(norm_unit a) = a * ↑u * ↑(norm_unit a) * ↑u⁻¹,
    by simpa only [mul_assoc, norm_unit_mul a u ha (units.ne_zero _), norm_unit_coe_units],
  calc a * ↑(norm_unit a) = a * ↑(norm_unit a) * ↑u * ↑u⁻¹:
      (units.mul_inv_cancel_right _ _).symm
    ... = a * ↑u * ↑(norm_unit a) * ↑u⁻¹ : by rw mul_right_comm a
end

theorem dvd_antisymm_of_norm {a b : α}
  (ha : norm_unit a = 1) (hb : norm_unit b = 1) (hab : a ∣ b) (hba : b ∣ a) :
  a = b :=
have a * norm_unit a = b * norm_unit b, from mul_norm_unit_eq_mul_norm_unit hab hba,
by simpa only [ha, hb, units.coe_one, mul_one]

end normalization_domain

/-- GCD domain: an integral domain with normalization and `gcd` (greatest common divisor) and
`lcm` (least common multiple) operations. In this setting `gcd` and `lcm` form a bounded lattice on
the associated elements where `gcd` is the infimum, `lcm` is the supremum, `1` is bottom, and
`0` is top. The type class focuses on `gcd` and we derive the correpsonding `lcm` facts from `gcd`.
-/
class gcd_domain (α : Type*) extends normalization_domain α :=
(gcd : α → α → α)
(lcm : α → α → α)
(gcd_dvd_left   : ∀a b, gcd a b ∣ a)
(gcd_dvd_right  : ∀a b, gcd a b ∣ b)
(dvd_gcd        : ∀{a b c}, a ∣ c → a ∣ b → a ∣ gcd c b)
(norm_unit_gcd  : ∀a b, norm_unit (gcd a b) = 1)
(gcd_mul_lcm    : ∀a b, gcd a b * lcm a b = a * b * norm_unit (a * b))
(lcm_zero_left  : ∀a, lcm 0 a = 0)
(lcm_zero_right : ∀a, lcm a 0 = 0)

export gcd_domain (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd  lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

section gcd_domain
variables [gcd_domain α]

@[simp] theorem norm_unit_gcd : ∀a b:α, norm_unit (gcd a b) = 1 :=
gcd_domain.norm_unit_gcd

@[simp] theorem gcd_mul_lcm : ∀a b:α, gcd a b * lcm a b = a * b * norm_unit (a * b) :=
gcd_domain.gcd_mul_lcm

section gcd

theorem dvd_gcd_iff (a b c : α) : a ∣ gcd b c ↔ (a ∣ b ∧ a ∣ c) :=
iff.intro
  (assume h, ⟨dvd_trans h (gcd_dvd_left _ _), dvd_trans h (gcd_dvd_right _ _)⟩)
  (assume ⟨hab, hac⟩, dvd_gcd hab hac)

theorem gcd_comm (a b : α) : gcd a b = gcd b a :=
dvd_antisymm_of_norm (norm_unit_gcd _ _) (norm_unit_gcd _ _)
  (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
  (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_assoc (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd_antisymm_of_norm (norm_unit_gcd _ _) (norm_unit_gcd _ _)
  (dvd_gcd
    (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
    (dvd_gcd (dvd.trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
  (dvd_gcd
    (dvd_gcd (gcd_dvd_left m (gcd n k)) (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
    (dvd.trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

instance : is_commutative α gcd := ⟨gcd_comm⟩
instance : is_associative α gcd := ⟨gcd_assoc⟩

theorem gcd_eq_mul_norm_unit {a b c : α} (habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) :
  gcd a b = c * norm_unit c :=
suffices gcd a b * norm_unit (gcd a b) = c * norm_unit c,
  by rwa [norm_unit_gcd, units.coe_one, mul_one] at this,
mul_norm_unit_eq_mul_norm_unit habc hcab

@[simp] theorem gcd_zero_left (a : α) : gcd 0 a = a * norm_unit a :=
gcd_eq_mul_norm_unit (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp] theorem gcd_zero_right (a : α) : gcd a 0 = a * norm_unit a :=
gcd_eq_mul_norm_unit (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp] theorem gcd_eq_zero_iff (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume h, let ⟨ca, ha⟩ := gcd_dvd_left a b, ⟨cb, hb⟩ := gcd_dvd_right a b in
    by rw [h, zero_mul] at ha hb; exact ⟨ha, hb⟩)
  (assume ⟨ha, hb⟩, by rw [ha, hb, gcd_zero_left, zero_mul])

@[simp] theorem gcd_one_left (a : α) : gcd 1 a = 1 :=
dvd_antisymm_of_norm (norm_unit_gcd _ _) norm_unit_one (gcd_dvd_left _ _)
  (dvd_gcd (dvd_refl 1) (one_dvd _))

@[simp] theorem gcd_one_right (a : α) : gcd a 1 = 1 :=
dvd_antisymm_of_norm (norm_unit_gcd _ _) norm_unit_one (gcd_dvd_right _ _)
  (dvd_gcd (one_dvd _) (dvd_refl 1))

theorem gcd_dvd_gcd {a b c d: α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
dvd_gcd (dvd.trans (gcd_dvd_left _ _) hab) (dvd.trans (gcd_dvd_right _ _) hcd)

@[simp] theorem gcd_same (a : α) : gcd a a = a * norm_unit a :=
gcd_eq_mul_norm_unit (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp] theorem gcd_mul_left (a b c : α) : gcd (a * b) (a * c) = (a * norm_unit a) * gcd b c :=
classical.by_cases (by rintro rfl; simp only [zero_mul, gcd_zero_left]) $ assume ha : a ≠ 0,
classical.by_cases (assume h : gcd b c = 0, by rw [h, mul_zero]; rw gcd_eq_zero_iff at h ⊢;
    rcases h with ⟨rfl, rfl⟩; split; apply mul_zero) $ assume hbc : gcd b c ≠ 0,
  suffices gcd (a * b) (a * c) = a * gcd b c * norm_unit (a * gcd b c),
    by simpa only [norm_unit_mul a _ ha hbc, norm_unit_gcd, mul_one, mul_right_comm],
  let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c) in
  gcd_eq_mul_norm_unit
    (eq.symm ▸ mul_dvd_mul_left a $ show d ∣ gcd b c, from
      dvd_gcd
        ((mul_dvd_mul_iff_left ha).1 $ eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 $ eq ▸ gcd_dvd_right _ _))
    (dvd_gcd
      (mul_dvd_mul_left a $ gcd_dvd_left _ _)
      (mul_dvd_mul_left a $ gcd_dvd_right _ _))

@[simp] theorem gcd_mul_right (a b c : α) : gcd (b * a) (c * a) = gcd b c * (a * norm_unit a) :=
by simp only [mul_comm, gcd_mul_left]

theorem gcd_eq_left_iff (a b : α) (h : norm_unit a = 1) : gcd a b = a ↔ a ∣ b :=
iff.intro (assume eq, eq ▸ gcd_dvd_right _ _) $
  assume hab, dvd_antisymm_of_norm (norm_unit_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

theorem gcd_eq_right_iff (a b : α) (h : norm_unit b = 1) : gcd a b = b ↔ b ∣ a :=
by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

theorem gcd_dvd_gcd_mul_left (m n k : α) : gcd m n ∣ gcd (k * m) n :=
gcd_dvd_gcd (dvd_mul_left _ _) (dvd_refl _)

theorem gcd_dvd_gcd_mul_right (m n k : α) : gcd m n ∣ gcd (m * k) n :=
gcd_dvd_gcd (dvd_mul_right _ _) (dvd_refl _)

theorem gcd_dvd_gcd_mul_left_right (m n k : α) : gcd m n ∣ gcd m (k * n) :=
gcd_dvd_gcd (dvd_refl _) (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : α) : gcd m n ∣ gcd m (n * k) :=
gcd_dvd_gcd (dvd_refl _) (dvd_mul_right _ _)

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
    by rw [← mul_dvd_mul_iff_left h, gcd_mul_lcm, units.coe_mul_dvd,
        ← units.dvd_coe_mul _ _ (norm_unit c), mul_assoc, mul_comm (gcd a b),
        ← gcd_mul_left, dvd_gcd_iff, mul_comm c a, mul_dvd_mul_iff_left h1,
        mul_dvd_mul_iff_right h2, and_comm])

lemma dvd_lcm_left (a b : α) : a ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl _)).1

lemma dvd_lcm_right (a b : α) : b ∣ lcm a b := (lcm_dvd_iff.1 (dvd_refl _)).2

lemma lcm_dvd {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp] theorem lcm_eq_zero_iff (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
iff.intro
  (assume h : lcm a b = 0,
    have a * b * norm_unit (a * b) = 0,
      by rw [← gcd_mul_lcm _ _, h, mul_zero],
    by simpa only [mul_eq_zero, units.ne_zero, or_false])
  (by rintro (rfl | rfl); [apply lcm_zero_left, apply lcm_zero_right])

@[simp] lemma norm_unit_lcm (a b : α) : norm_unit (lcm a b) = 1 :=
classical.by_cases (assume : lcm a b = 0, by rw [this, norm_unit_zero]) $
  assume h_lcm : lcm a b ≠ 0,
  have h1 : gcd a b ≠ 0, from mt (by rw [gcd_eq_zero_iff, lcm_eq_zero_iff];
    rintros ⟨rfl, rfl⟩; left; refl) h_lcm,
  have h2 : norm_unit (gcd a b * lcm a b) = 1,
    by rw [gcd_mul_lcm, norm_unit_mul_norm_unit],
  by simpa only [norm_unit_mul _ _ h1 h_lcm, norm_unit_gcd, one_mul] using h2

theorem lcm_comm (a b : α) : lcm a b = lcm b a :=
dvd_antisymm_of_norm (norm_unit_lcm _ _) (norm_unit_lcm _ _)
  (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
  (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_assoc (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd_antisymm_of_norm (norm_unit_lcm _ _) (norm_unit_lcm _ _)
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left _ _) (dvd.trans (dvd_lcm_left _ _) (dvd_lcm_right _ _)))
    (dvd.trans (dvd_lcm_right _ _) (dvd_lcm_right _ _)))
  (lcm_dvd
    (dvd.trans (dvd_lcm_left _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd.trans (dvd_lcm_right _ _) (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

instance : is_commutative α lcm := ⟨lcm_comm⟩
instance : is_associative α lcm := ⟨lcm_assoc⟩

lemma lcm_eq_mul_norm_unit {a b c : α} (habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) :
  lcm a b = c * norm_unit c :=
dvd_antisymm_of_norm (norm_unit_lcm _ _) (norm_unit_mul_norm_unit _)
  ((units.dvd_coe_mul _ _ _).2 $ habc)
  ((units.coe_mul_dvd _ _ _).2 $ hcab)

theorem lcm_dvd_lcm {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
lcm_dvd (dvd.trans hab (dvd_lcm_left _ _)) (dvd.trans hcd (dvd_lcm_right _ _))

@[simp] theorem lcm_units_coe_left (u : units α) (a : α) : lcm ↑u a = a * norm_unit a :=
lcm_eq_mul_norm_unit (lcm_dvd (units.coe_dvd _ _) (dvd_refl _)) (dvd_lcm_right _ _)

@[simp] theorem lcm_units_coe_right (a : α) (u : units α) : lcm a ↑u = a * norm_unit a :=
(lcm_comm a u).trans $ lcm_units_coe_left _ _

@[simp] theorem lcm_one_left (a : α) : lcm 1 a = a * norm_unit a :=
lcm_units_coe_left 1 a

@[simp] theorem lcm_one_right (a : α) : lcm a 1 = a * norm_unit a :=
lcm_units_coe_right a 1

@[simp] theorem lcm_same (a : α) : lcm a a = a * norm_unit a :=
lcm_eq_mul_norm_unit (lcm_dvd (dvd_refl _) (dvd_refl _)) (dvd_lcm_left _ _)

@[simp] theorem lcm_eq_one_iff (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
iff.intro
  (assume eq, eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩)
  (assume ⟨⟨c, hc⟩, ⟨d, hd⟩⟩,
    show lcm (units.mk_of_mul_eq_one a c hc.symm : α) (units.mk_of_mul_eq_one b d hd.symm) = 1,
      by rw [lcm_units_coe_left, norm_unit_coe_units, units.mul_inv])

@[simp] theorem lcm_mul_left (a b c : α) : lcm (a * b) (a * c) = (a * norm_unit a) * lcm b c :=
classical.by_cases (by rintro rfl; simp only [zero_mul, lcm_zero_left]) $ assume ha : a ≠ 0,
classical.by_cases (assume : lcm b c = 0, by rw [this, mul_zero]; rw lcm_eq_zero_iff at this ⊢;
    rcases this with rfl | rfl; [left, right]; simp only [mul_zero]) $ assume hbc : lcm b c ≠ 0,
  suffices lcm (a * b) (a * c) = a * lcm b c * norm_unit (a * lcm b c),
    by simpa only [norm_unit_mul _ _ ha hbc, norm_unit_lcm, mul_one, mul_right_comm],
  have a ∣ lcm (a * b) (a * c), from dvd.trans (dvd_mul_right _ _) (dvd_lcm_left _ _),
  let ⟨d, eq⟩ := this in
  lcm_eq_mul_norm_unit
    (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
    (eq.symm ▸ (mul_dvd_mul_left a $ lcm_dvd
      ((mul_dvd_mul_iff_left ha).1 $ eq ▸ dvd_lcm_left _ _)
      ((mul_dvd_mul_iff_left ha).1 $ eq ▸ dvd_lcm_right _ _)))

@[simp] theorem lcm_mul_right (a b c : α) : lcm (b * a) (c * a) = lcm b c * (a * norm_unit a) :=
by simp only [mul_comm, lcm_mul_left]

theorem lcm_eq_left_iff (a b : α) (h : norm_unit a = 1) : lcm a b = a ↔ b ∣ a :=
iff.intro (assume eq, eq ▸ dvd_lcm_right _ _) $
  assume hab, dvd_antisymm_of_norm (norm_unit_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

theorem lcm_eq_right_iff (a b : α) (h : norm_unit b = 1) : lcm a b = b ↔ a ∣ b :=
by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

theorem lcm_dvd_lcm_mul_left (m n k : α) : lcm m n ∣ lcm (k * m) n :=
lcm_dvd_lcm (dvd_mul_left _ _) (dvd_refl _)

theorem lcm_dvd_lcm_mul_right (m n k : α) : lcm m n ∣ lcm (m * k) n :=
lcm_dvd_lcm (dvd_mul_right _ _) (dvd_refl _)

theorem lcm_dvd_lcm_mul_left_right (m n k : α) : lcm m n ∣ lcm m (k * n) :=
lcm_dvd_lcm (dvd_refl _) (dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right (m n k : α) : lcm m n ∣ lcm m (n * k) :=
lcm_dvd_lcm (dvd_refl _) (dvd_mul_right _ _)

end lcm

end gcd_domain
