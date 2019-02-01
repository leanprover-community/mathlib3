/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import algebra.associated algebra.euclidean_domain ring_theory.ideals
noncomputable theory
local attribute [instance] classical.dec
open euclidean_domain set ideal

theorem span_gcd {α} [euclidean_domain α] (x y : α) :
  span ({gcd x y} : set α) = span ({x, y} : set α) :=
begin
  apply le_antisymm; refine span_le.1 _,
  { simp [submodule.span_span, mem_span_pair, submodule.le_def', mem_span_singleton'],
    assume a b ha,
    exact ⟨b * gcd_a x y, b * gcd_b x y, by rw [← ha, gcd_eq_gcd_ab x y];
      simp [mul_add, mul_comm, mul_left_comm]⟩ },
  { assume z ,
    simp [mem_span_singleton, euclidean_domain.gcd_dvd_left, mem_span_pair,
      @eq_comm _ _ z] {contextual := tt},
    assume a b h,
    exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _) }
end

theorem gcd_is_unit_iff {α} [euclidean_domain α] {x y : α} :
  is_unit (gcd x y) ↔ is_coprime x y :=
by rw [← span_singleton_eq_top, span_gcd, is_coprime]

theorem is_coprime_of_dvd {α} [euclidean_domain α] {x y : α}
  (z : ¬ (x = 0 ∧ y = 0)) (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  rw [← gcd_is_unit_iff],
  by_contra h,
  refine H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _),
  rwa [ne, euclidean_domain.gcd_eq_zero_iff]
end

theorem dvd_or_coprime {α} [euclidean_domain α] (x y : α)
  (h : irreducible x) : x ∣ y ∨ is_coprime x y :=
begin
  refine or_iff_not_imp_left.2 (λ h', _),
  unfreezeI, apply is_coprime_of_dvd,
  { rintro ⟨rfl, rfl⟩, simpa using h },
  { rintro z nu nz ⟨w, rfl⟩ dy,
    refine h' (dvd.trans _ dy),
    simpa using mul_dvd_mul_left z (is_unit_iff_dvd_one.1 $
      (of_irreducible_mul h).resolve_left nu) }
end
