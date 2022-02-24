/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth, Johan Commelin
-/

import ring_theory.witt_vector.domain
import ring_theory.witt_vector.mul_coeff
import ring_theory.discrete_valuation_ring
import tactic.linear_combination

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `witt_vector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `witt_vector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `witt_vector.discrete_valuation_ring`: `𝕎 k` is a discrete valuation ring if `k` is a perfect
    field

-/

noncomputable theory

namespace witt_vector

variables {p : ℕ} [hp : fact p.prime]
include hp
local notation `𝕎` := witt_vector p

section comm_ring
variables {k : Type*} [comm_ring k] [char_p k p]

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
units.mk_of_mul_eq_one A (witt_vector.mk p (inverse_coeff a A))
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

section field
variables {k : Type*} [field k] [char_p k p]

lemma is_unit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 ≠ 0) : is_unit x :=
begin
  let y : kˣ := units.mk0 (x.coeff 0) hx,
  have hy : x.coeff 0 = y := rfl,
  exact (mk_unit hy).is_unit
end

variables (p)
lemma irreducible : irreducible (p : 𝕎 k) :=
begin
  have hp : ¬ is_unit (p : 𝕎 k),
  { intro hp,
    simpa only [constant_coeff_apply, coeff_p_zero, not_is_unit_zero]
      using constant_coeff.is_unit_map hp, },
  refine ⟨hp, λ a b hab, _⟩,
  obtain ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0,
  { rw ← mul_ne_zero_iff, intro h, rw h at hab, exact p_nonzero p k hab },
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0,
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0,
  cases m, { exact or.inl (is_unit_of_coeff_zero_ne_zero a ha) },
  cases n, { exact or.inr (is_unit_of_coeff_zero_ne_zero b hb) },
  rw iterate_verschiebung_mul at hab,
  apply_fun (λ x, coeff x 1) at hab,
  simp only [coeff_p_one, nat.add_succ, add_comm _ n, function.iterate_succ', function.comp_app,
    verschiebung_coeff_add_one, verschiebung_coeff_zero] at hab,
  exact (one_ne_zero hab).elim
end

end field

section perfect_ring
variables {k : Type*} [comm_ring k] [char_p k p] [perfect_ring k p]

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

section perfect_field
variables {k : Type*} [field k] [char_p k p] [perfect_ring k p]

lemma exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) :
  ∃ (m : ℕ) (b : units (𝕎 k)), a = p ^ m * b :=
begin
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha,
  let b₀ := units.mk0 (b.coeff 0) h₁,
  have hb₀ : b.coeff 0 = b₀ := rfl,
  exact ⟨m, mk_unit hb₀, h₂⟩,
end

instance : discrete_valuation_ring (𝕎 k) :=
discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
begin
  refine ⟨p, irreducible p, λ x hx, _⟩,
  obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx,
  exact ⟨n, b, hb.symm⟩,
end

end perfect_field
end witt_vector
