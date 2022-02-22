/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/

import ring_theory.witt_vector.domain
import ring_theory.witt_vector.mul_coeff
import tactic.linear_combination

/-!

# Witt vectors over a perfect ring

This file establishes a basic result about Witt vectors over perfect rings.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `witt_vector.exists_eq_pow_p_mul`: the theorem over a perfect ring
* `witt_vector.exists_eq_pow_p_mul'`: the theorem over a perfect field

-/

noncomputable theory

namespace witt_vector

variables (p : ℕ) [hp : fact p.prime]
include hp
local notation `𝕎` := witt_vector p

section perfect_ring
variables {k : Type*} [comm_ring k] [char_p k p] [perfect_ring k p]

/-- This is basically the same as `𝕎 k` being a DVR. -/
lemma exists_eq_pow_p_mul (a : 𝕎 k) (ha : a ≠ 0) :
  ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = p ^ m * b :=
begin
  obtain ⟨m, c, hc, hcm⟩ := witt_vector.verschiebung_nonzero ha,
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c,
  rw witt_vector.iterate_frobenius_coeff at hc,
  have := congr_fun (witt_vector.verschiebung_frobenius_comm.comp_iterate m) b,
  simp only [function.comp_app] at this,
  rw ← this at hcm,
  refine ⟨m, b, _, _⟩,
  { contrapose! hc,
    have : 0 < p ^ m := pow_pos (nat.prime.pos (fact.out _)) _,
    simp [hc, zero_pow this] },
  { rw ← mul_left_iterate (p : 𝕎 k) m,
    convert hcm,
    ext1 x,
    rw [mul_comm, ← witt_vector.verschiebung_frobenius x] },
end

end perfect_ring

section comm_ring
variables {k :Type*} [comm_ring k] [char_p k p]
variables {p}

/-- This is the `n+1`st coefficient of our inverse. -/
def succ_nth_val_units (n : ℕ) (a : units k) (A : 𝕎 k) (bs : fin (n+1) → k) : k :=
- ↑(a⁻¹ ^ (p^(n+1)))
* (A.coeff (n + 1) * ↑(a⁻¹ ^ (p^(n+1))) + nth_remainder p n (truncate_fun (n+1) A) bs)

/--
Recursively defines the sequence of coefficients for the inverse to a Witt vector whose first entry
is a unit.
-/
noncomputable def inverse_coeff (a : units k) (A : 𝕎 k) : ℕ → k
| 0       := ↑a⁻¹
| (n + 1) := succ_nth_val_units n a A (λ i, inverse_coeff i.val)
              using_well_founded { dec_tac := `[apply fin.is_lt] }

/--
Upgrade a Witt vector `A` whose first entry `A.coeff 0` is a unit to be, itself, a unit in `𝕎 k`.
-/
def mk_unit {a : units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : units (𝕎 k) :=
units.mk_of_mul_eq_one
  A
  (witt_vector.mk p (inverse_coeff a A))
  begin
    ext n,
    induction n with n ih,
    { simp [witt_vector.mul_coeff_zero, inverse_coeff, hA] },
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1))
      + nth_remainder p n (truncate_fun (n + 1) A) (λ (i : fin (n + 1)), inverse_coeff a A i),
    have H := units.mul_inv (a ^ p ^ (n + 1)),
    linear_combination (H, -H_coeff) { normalize := ff },
    have ha : (a:k) ^ (p ^ (n + 1)) = ↑(a ^ (p ^ (n + 1))) := by norm_cast,
    have ha_inv : (↑(a⁻¹):k) ^ (p ^ (n + 1)) = ↑(a ^ (p ^ (n + 1)))⁻¹ :=
      by exact_mod_cast inv_pow _ _,
    simp only [nth_remainder_spec, inverse_coeff, succ_nth_val_units, hA, fin.val_eq_coe,
      one_coeff_eq_of_pos, nat.succ_pos', H_coeff, ha_inv, ha, inv_pow],
    ring!,
  end

@[simp] lemma coe_mk_unit {a : units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mk_unit hA : 𝕎 k) = A :=
rfl

end comm_ring

section perfect_field
variables {k : Type*} [field k] [char_p k p] [perfect_ring k p]

/-- This is basically the same as `𝕎 k` being a DVR. -/
lemma exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) :
  ∃ (m : ℕ) (b : units (𝕎 k)), a = p ^ m * b :=
begin
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul p a ha,
  let b₀ := units.mk0 (b.coeff 0) h₁,
  have hb₀ : b.coeff 0 = b₀ := rfl,
  exact ⟨m, mk_unit hb₀, h₂⟩,
end

end perfect_field
end witt_vector
