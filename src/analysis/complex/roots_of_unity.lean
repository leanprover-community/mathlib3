/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.roots_of_unity
import analysis.special_functions.trigonometric
import analysis.special_functions.pow

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/

namespace complex

open polynomial real

lemma is_primitive_root (n : ℕ) (h0 : n ≠ 0) : is_primitive_root (exp (2 * pi * I / n)) n :=
begin
  rw is_primitive_root.iff_def,
  simp only [← exp_nat_mul, exp_eq_one_iff],
  have hn0 : (n : ℂ) ≠ 0, by exact_mod_cast h0,
  split,
  { use 1,
    field_simp [hn0, mul_comm (n : ℂ)] },
  { simp only [hn0, mul_right_comm _ _ ↑n, mul_left_inj' two_pi_I_ne_zero, ne.def, not_false_iff,
      exists_imp_distrib] with field_simps,
    norm_cast,
    rintro l k hk,
    rw ← int.coe_nat_dvd,
    rw mul_comm at hk,
    exact ⟨k, hk⟩ }
end

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
lemma mem_roots_of_unity (n : ℕ+) (x : units ℂ) :
  x ∈ roots_of_unity n ℂ ↔ (∃ i < (n : ℕ), exp (2 * pi * I * (i / n)) = x) :=
begin
  rw [mem_roots_of_unity, units.ext_iff, units.coe_pow, units.coe_one],
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (nat.pos_iff_ne_zero.mp n.pos),
  split,
  { intro h,
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * pi * I / n) ^ i = x,
    { simpa only using (is_primitive_root n n.ne_zero).eq_pow_of_pow_eq_one h n.pos },
    refine ⟨i, hi, _⟩,
    rw [← H, ← exp_nat_mul],
    congr' 1,
    field_simp [hn0, mul_comm (i : ℂ)] },
  { rintro ⟨i, hi, H⟩,
    rw [← H, ← exp_nat_mul, exp_eq_one_iff],
    use i,
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)] }
end

lemma card_roots_of_unity (n : ℕ+) : fintype.card (roots_of_unity n ℂ) = n :=
begin
  have h := is_primitive_root n n.ne_zero,
  obtain ⟨ζ, hζ⟩ := h.is_unit n.pos,
  rw [← hζ, is_primitive_root.coe_units_iff] at h,
  haveI : fact (0 < ↑n) := n.pos,
  let e := h.zmod_equiv_gpowers,
  haveI F : fintype (subgroup.gpowers ζ) := fintype.of_equiv _ e.to_equiv,
  calc fintype.card (roots_of_unity n ℂ)
      = fintype.card (subgroup.gpowers ζ) : fintype.card_congr $ by rw h.gpowers_eq
  ... = fintype.card (zmod n)             : fintype.card_congr e.to_equiv.symm
  ... = n                                 : zmod.card n
end

end complex
