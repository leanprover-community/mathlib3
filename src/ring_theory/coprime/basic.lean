/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import tactic.ring
import algebra.ring.basic

/-!
# Coprime elements of a ring

## Main definitions

* `is_coprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.

See also `ring_theory.coprime.lemmas` for further development of coprime elements.
-/

open_locale classical

universes u v

section comm_semiring

variables {R : Type u} [comm_semiring R] (x y z : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[simp] def is_coprime : Prop :=
∃ a b, a * x + b * y = 1

variables {x y z}

theorem is_coprime.symm (H : is_coprime x y) : is_coprime y x :=
let ⟨a, b, H⟩ := H in ⟨b, a, by rw [add_comm, H]⟩

theorem is_coprime_comm : is_coprime x y ↔ is_coprime y x :=
⟨is_coprime.symm, is_coprime.symm⟩

theorem is_coprime_self : is_coprime x x ↔ is_unit x :=
⟨λ ⟨a, b, h⟩, is_unit_of_mul_eq_one x (a + b) $ by rwa [mul_comm, add_mul],
λ h, let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 h in ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

theorem is_coprime_zero_left : is_coprime 0 x ↔ is_unit x :=
⟨λ ⟨a, b, H⟩, is_unit_of_mul_eq_one x b $ by rwa [mul_zero, zero_add, mul_comm] at H,
λ H, let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 H in ⟨1, b, by rwa [one_mul, zero_add]⟩⟩

theorem is_coprime_zero_right : is_coprime x 0 ↔ is_unit x :=
is_coprime_comm.trans is_coprime_zero_left

lemma not_coprime_zero_zero [nontrivial R] : ¬ is_coprime (0 : R) 0 :=
mt is_coprime_zero_right.mp not_is_unit_zero

theorem is_coprime_one_left : is_coprime 1 x :=
⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩

theorem is_coprime_one_right : is_coprime x 1 :=
⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩

theorem is_coprime.dvd_of_dvd_mul_right (H1 : is_coprime x z) (H2 : x ∣ y * z) : x ∣ y :=
let ⟨a, b, H⟩ := H1 in by { rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm],
exact dvd_add (dvd_mul_left _ _) (H2.mul_left _) }

theorem is_coprime.dvd_of_dvd_mul_left (H1 : is_coprime x y) (H2 : x ∣ y * z) : x ∣ z :=
let ⟨a, b, H⟩ := H1 in by { rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b],
exact dvd_add (dvd_mul_left _ _) (H2.mul_left _) }

theorem is_coprime.mul_left (H1 : is_coprime x z) (H2 : is_coprime y z) : is_coprime (x * y) z :=
let ⟨a, b, h1⟩ := H1, ⟨c, d, h2⟩ := H2 in
⟨a * c, a * x * d + b * c * y + b * d * z,
calc  a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
    = (a * x + b * z) * (c * y + d * z) : by ring
... = 1 : by rw [h1, h2, mul_one]⟩

theorem is_coprime.mul_right (H1 : is_coprime x y) (H2 : is_coprime x z) : is_coprime x (y * z) :=
by { rw is_coprime_comm at H1 H2 ⊢, exact H1.mul_left H2 }

theorem is_coprime.mul_dvd (H : is_coprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
begin
  obtain ⟨a, b, h⟩ := H,
  rw [← mul_one z, ← h, mul_add],
  apply dvd_add,
  { rw [mul_comm z, mul_assoc],
    exact (mul_dvd_mul_left _ H2).mul_left _ },
  { rw [mul_comm b, ← mul_assoc],
    exact (mul_dvd_mul_right H1 _).mul_right _ }
end


theorem is_coprime.of_mul_left_left (H : is_coprime (x * y) z) : is_coprime x z :=
let ⟨a, b, h⟩ := H in ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩

theorem is_coprime.of_mul_left_right (H : is_coprime (x * y) z) : is_coprime y z :=
by { rw mul_comm at H, exact H.of_mul_left_left }

theorem is_coprime.of_mul_right_left (H : is_coprime x (y * z)) : is_coprime x y :=
by { rw is_coprime_comm at H ⊢, exact H.of_mul_left_left }

theorem is_coprime.of_mul_right_right (H : is_coprime x (y * z)) : is_coprime x z :=
by { rw mul_comm at H, exact H.of_mul_right_left }

theorem is_coprime.mul_left_iff : is_coprime (x * y) z ↔ is_coprime x z ∧ is_coprime y z :=
⟨λ H, ⟨H.of_mul_left_left, H.of_mul_left_right⟩, λ ⟨H1, H2⟩, H1.mul_left H2⟩

theorem is_coprime.mul_right_iff : is_coprime x (y * z) ↔ is_coprime x y ∧ is_coprime x z :=
by rw [is_coprime_comm, is_coprime.mul_left_iff, is_coprime_comm, @is_coprime_comm _ _ z]

theorem is_coprime.of_coprime_of_dvd_left (h : is_coprime y z) (hdvd : x ∣ y) : is_coprime x z :=
begin
  obtain ⟨d, rfl⟩ := hdvd,
  exact is_coprime.of_mul_left_left h
end

theorem is_coprime.of_coprime_of_dvd_right (h : is_coprime z y) (hdvd : x ∣ y) : is_coprime z x :=
(h.symm.of_coprime_of_dvd_left hdvd).symm

theorem is_coprime.is_unit_of_dvd (H : is_coprime x y) (d : x ∣ y) : is_unit x :=
let ⟨k, hk⟩ := d in is_coprime_self.1 $ is_coprime.of_mul_right_left $
show is_coprime x (x * k), from hk ▸ H

theorem is_coprime.is_unit_of_dvd' {a b x : R} (h : is_coprime a b) (ha : x ∣ a) (hb : x ∣ b) :
  is_unit x :=
(h.of_coprime_of_dvd_left ha).is_unit_of_dvd hb

theorem is_coprime.map (H : is_coprime x y) {S : Type v} [comm_semiring S] (f : R →+* S) :
  is_coprime (f x) (f y) :=
let ⟨a, b, h⟩ := H in ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

variables {x y z}

lemma is_coprime.of_add_mul_left_left (h : is_coprime (x + y * z) y) : is_coprime x y :=
let ⟨a, b, H⟩ := h in ⟨a, a * z + b, by simpa only [add_mul, mul_add,
    add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using H⟩

lemma is_coprime.of_add_mul_right_left (h : is_coprime (x + z * y) y) : is_coprime x y :=
by { rw mul_comm at h, exact h.of_add_mul_left_left }

lemma is_coprime.of_add_mul_left_right (h : is_coprime x (y + x * z)) : is_coprime x y :=
by { rw is_coprime_comm at h ⊢, exact h.of_add_mul_left_left }

lemma is_coprime.of_add_mul_right_right (h : is_coprime x (y + z * x)) : is_coprime x y :=
by { rw mul_comm at h, exact h.of_add_mul_left_right }

lemma is_coprime.of_mul_add_left_left (h : is_coprime (y * z + x) y) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_left_left }

lemma is_coprime.of_mul_add_right_left (h : is_coprime (z * y + x) y) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_right_left }

lemma is_coprime.of_mul_add_left_right (h : is_coprime x (x * z + y)) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_left_right }

lemma is_coprime.of_mul_add_right_right (h : is_coprime x (z * x + y)) : is_coprime x y :=
by { rw add_comm at h, exact h.of_add_mul_right_right }

end comm_semiring

namespace is_coprime

section comm_ring

variables {R : Type u} [comm_ring R]

lemma add_mul_left_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (x + y * z) y :=
@of_add_mul_left_left R _ _ _ (-z) $
by simpa only [mul_neg_eq_neg_mul_symm, add_neg_cancel_right] using h

lemma add_mul_right_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (x + z * y) y :=
by { rw mul_comm, exact h.add_mul_left_left z }

lemma add_mul_left_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (y + x * z) :=
by { rw is_coprime_comm, exact h.symm.add_mul_left_left z }

lemma add_mul_right_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (y + z * x) :=
by { rw is_coprime_comm, exact h.symm.add_mul_right_left z }

lemma mul_add_left_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (y * z + x) y :=
by { rw add_comm, exact h.add_mul_left_left z }

lemma mul_add_right_left {x y : R} (h : is_coprime x y) (z : R) : is_coprime (z * y + x) y :=
by { rw add_comm, exact h.add_mul_right_left z }

lemma mul_add_left_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (x * z + y) :=
by { rw add_comm, exact h.add_mul_left_right z }

lemma mul_add_right_right {x y : R} (h : is_coprime x y) (z : R) : is_coprime x (z * x + y) :=
by { rw add_comm, exact h.add_mul_right_right z }

lemma add_mul_left_left_iff {x y z : R} : is_coprime (x + y * z) y ↔ is_coprime x y :=
⟨of_add_mul_left_left, λ h, h.add_mul_left_left z⟩

lemma add_mul_right_left_iff {x y z : R} : is_coprime (x + z * y) y ↔ is_coprime x y :=
⟨of_add_mul_right_left, λ h, h.add_mul_right_left z⟩

lemma add_mul_left_right_iff {x y z : R} : is_coprime x (y + x * z) ↔ is_coprime x y :=
⟨of_add_mul_left_right, λ h, h.add_mul_left_right z⟩

lemma add_mul_right_right_iff {x y z : R} : is_coprime x (y + z * x) ↔ is_coprime x y :=
⟨of_add_mul_right_right, λ h, h.add_mul_right_right z⟩

lemma mul_add_left_left_iff {x y z : R} : is_coprime (y * z + x) y ↔ is_coprime x y :=
⟨of_mul_add_left_left, λ h, h.mul_add_left_left z⟩

lemma mul_add_right_left_iff {x y z : R} : is_coprime (z * y + x) y ↔ is_coprime x y :=
⟨of_mul_add_right_left, λ h, h.mul_add_right_left z⟩

lemma mul_add_left_right_iff {x y z : R} : is_coprime x (x * z + y) ↔ is_coprime x y :=
⟨of_mul_add_left_right, λ h, h.mul_add_left_right z⟩

lemma mul_add_right_right_iff {x y z : R} : is_coprime x (z * x + y) ↔ is_coprime x y :=
⟨of_mul_add_right_right, λ h, h.mul_add_right_right z⟩

lemma neg_left {x y : R} (h : is_coprime x y) : is_coprime (-x) y :=
begin
  obtain ⟨a, b, h⟩ := h,
  use [-a, b],
  rwa neg_mul_neg,
end

lemma neg_left_iff (x y : R) : is_coprime (-x) y ↔ is_coprime x y :=
⟨λ h, neg_neg x ▸ h.neg_left, neg_left⟩

lemma neg_right {x y : R} (h : is_coprime x y) : is_coprime x (-y) :=
h.symm.neg_left.symm

lemma neg_right_iff (x y : R) : is_coprime x (-y) ↔ is_coprime x y :=
⟨λ h, neg_neg y ▸ h.neg_right, neg_right⟩

lemma neg_neg {x y : R} (h : is_coprime x y) : is_coprime (-x) (-y) :=
h.neg_left.neg_right

lemma neg_neg_iff (x y : R) : is_coprime (-x) (-y) ↔ is_coprime x y :=
(neg_left_iff _ _).trans (neg_right_iff _ _)

end comm_ring

end is_coprime
