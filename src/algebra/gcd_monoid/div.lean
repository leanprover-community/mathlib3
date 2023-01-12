/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import algebra.gcd_monoid.finset
import algebra.gcd_monoid.basic
import ring_theory.int.basic
import ring_theory.polynomial.content

/-!
# Basic results about setwise gcds on normalized gcd monoid with a division.

## Main results

* `finset.nat.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from `s` to
  `ℕ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `finset.int.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from `s` to
  `ℤ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `finset.polynomial.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from
  `s` to `K[X]`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.

## TODO
Add a typeclass to state these results uniformly.

-/

namespace finset

namespace nat

/-- Given a nonempty finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type*} {f : β → ℕ} (s : finset β) {x : β} (hx : x ∈ s)
  (hfz : f x ≠ 0) : s.gcd (λ b, f b / s.gcd f) = 1 :=
begin
  obtain ⟨g, he, hg⟩ := finset.extract_gcd f ⟨x, hx⟩,
  refine (finset.gcd_congr rfl $ λ a ha, _).trans hg,
  rw [he a ha, nat.mul_div_cancel_left],
  exact nat.pos_of_ne_zero (mt finset.gcd_eq_zero_iff.1 (λ h, hfz $ h x hx)),
end

theorem gcd_div_id_eq_one {s : finset ℕ} {x : ℕ} (hx : x ∈ s) (hnz : x ≠ 0) :
  s.gcd (λ b, b / s.gcd id) = 1 :=
gcd_div_eq_one s hx hnz

end nat

namespace int

/-- Given a nonempty finset `s` and a function `f` from `s` to `ℤ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type*} {f : β → ℤ} (s : finset β) {x : β} (hx : x ∈ s)
  (hfz : f x ≠ 0) : s.gcd (λ b, f b / s.gcd f) = 1 :=
begin
  obtain ⟨g, he, hg⟩ := finset.extract_gcd f ⟨x, hx⟩,
  refine (finset.gcd_congr rfl $ λ a ha, _).trans hg,
  rw [he a ha, int.mul_div_cancel_left],
  exact mt finset.gcd_eq_zero_iff.1 (λ h, hfz $ h x hx),
end

theorem gcd_div_id_eq_one {s : finset ℤ} {x : ℤ} (hx : x ∈ s) (hnz : x ≠ 0) :
  s.gcd (λ b, b / s.gcd id) = 1 :=
gcd_div_eq_one s hx hnz

end int

namespace polynomial

open_locale polynomial classical

noncomputable theory

variables {K : Type*} [field K]

/-- Given a nonempty finset `s` and a function `f` from `s` to `K[X]`, if `d = s.gcd f`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type*} {f : β → K[X]} (s : finset β) {x : β} (hx : x ∈ s)
  (hfz : f x ≠ 0) : s.gcd (λ b, f b / s.gcd f) = 1 :=
begin
  obtain ⟨g, he, hg⟩ := finset.extract_gcd f ⟨x, hx⟩,
  refine (finset.gcd_congr rfl $ λ a ha, _).trans hg,
  rw [he a ha, euclidean_domain.mul_div_cancel_left],
  exact mt finset.gcd_eq_zero_iff.1 (λ h, hfz $ h x hx),
end

theorem gcd_div_id_eq_one {s : finset K[X]} {x : K[X]} (hx : x ∈ s) (hnz : x ≠ 0) :
  s.gcd (λ b, b / s.gcd id) = 1 :=
gcd_div_eq_one s hx hnz

end polynomial

end finset
