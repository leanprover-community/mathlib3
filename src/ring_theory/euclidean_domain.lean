/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import ring_theory.coprime
import ring_theory.ideal.basic

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

noncomputable theory
open_locale classical
open euclidean_domain set ideal

-- TODO -- this should surely be proved for PIDs instead?

theorem span_gcd {α} [euclidean_domain α] (x y : α) :
  span ({gcd x y} : set α) = span ({x, y} : set α) :=
begin
  apply le_antisymm,
  { refine span_le.2 (λ x, _),
    simp only [set.mem_singleton_iff, set_like.mem_coe, mem_span_pair],
    rintro rfl,
    exact ⟨gcd_a x y, gcd_b x y, by simp [gcd_eq_gcd_ab, mul_comm]⟩ },
  { assume z ,
    simp [mem_span_singleton, euclidean_domain.gcd_dvd_left, mem_span_pair,
      @eq_comm _ _ z] {contextual := tt},
    exact λ a b _, dvd_add ((gcd_dvd_left x y).mul_left _)
      ((gcd_dvd_right x y).mul_left _) }
end
-- this should be proved for PIDs?
theorem gcd_is_unit_iff {α} [euclidean_domain α] {x y : α} :
  is_unit (gcd x y) ↔ is_coprime x y :=
⟨λ h, let ⟨b, hb⟩ := is_unit_iff_exists_inv'.1 h in ⟨b * gcd_a x y, b * gcd_b x y,
  by rw [← hb, gcd_eq_gcd_ab, mul_comm x, mul_comm y, mul_add, mul_assoc, mul_assoc]⟩,
λ ⟨a, b, h⟩, is_unit_iff_dvd_one.2 $ h ▸ dvd_add ((gcd_dvd_left x y).mul_left _)
  ((gcd_dvd_right x y).mul_left _)⟩

-- this should be proved for UFDs surely?
theorem is_coprime_of_dvd {α} [euclidean_domain α] {x y : α}
  (z : ¬ (x = 0 ∧ y = 0)) (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  rw [← gcd_is_unit_iff],
  by_contra h,
  refine H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _),
  rwa [ne, euclidean_domain.gcd_eq_zero_iff]
end

-- this should be proved for UFDs surely?
theorem dvd_or_coprime {α} [euclidean_domain α] (x y : α)
  (h : irreducible x) : x ∣ y ∨ is_coprime x y :=
begin
  refine or_iff_not_imp_left.2 (λ h', _),
  apply is_coprime_of_dvd,
  { unfreezingI { rintro ⟨rfl, rfl⟩ }, simpa using h },
  { unfreezingI { rintro z nu nz ⟨w, rfl⟩ dy },
    refine h' (dvd_trans _ dy),
    simpa using mul_dvd_mul_left z (is_unit_iff_dvd_one.1 $
      (of_irreducible_mul h).resolve_left nu) }
end
