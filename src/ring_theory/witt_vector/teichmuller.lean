/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.basic

/-!

# Teichmüller lifts

This file defines `witt_vector.teichmuller`, a monoid hom `R → 𝕎 R`, which embeds `r : R` as the
0th component of a Witt vector whose other coefficients are 0.

`teichmuller` is a natural transformation; the `n`th ghost component of `teichmuller p r`
is `r ^ p ^ n`.

-/

namespace witt_vector

open mv_polynomial
variables (p : ℕ) {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

/--
The underlying function of the monoid hom `witt_vector.teichmuller`.
The 0th coefficient of `teichmuller_fun p r` is `r`, and all others are 0.
-/
def teichmuller_fun (r : R) : 𝕎 R
| 0 := r
| (n+1) := 0

include hp

private lemma ghost_component_teichmuller_fun (r : R) (n : ℕ) :
  ghost_component n (teichmuller_fun p r) = r ^ p ^ n :=
begin
  rw [ghost_component_apply, aeval_witt_polynomial, finset.sum_eq_single 0,
      pow_zero, one_mul, nat.sub_zero],
  { refl },
  { intros i hi h0,
    convert mul_zero _, convert zero_pow _,
    { cases i, { contradiction }, { refl } },
    { apply pow_pos, apply nat.prime.pos, assumption } },
  { rw finset.mem_range, intro h, exact (h (nat.succ_pos n)).elim }
end

/-- teichmuller is a natural transformation -/
private lemma map_teichmuller_fun (f : R →+* S) (r : R) :
  map f (teichmuller_fun p r) = teichmuller_fun p (f r) :=
by { ext n, cases n, { refl }, { exact f.map_zero } }

private lemma teichmuller_mul_aux₁ (x y : mv_polynomial R ℚ) :
  teichmuller_fun p (x * y) = teichmuller_fun p x * teichmuller_fun p y :=
begin
  apply (ghost_map.bijective_of_invertible p (mv_polynomial R ℚ)).1,
  rw ring_hom.map_mul,
  ext1 n,
  simp only [pi.mul_apply, ghost_map_apply, ghost_component_teichmuller_fun, mul_pow],
end

private lemma teichmuller_mul_aux₂ (x y : mv_polynomial R ℤ) :
  teichmuller_fun p (x * y) = teichmuller_fun p x * teichmuller_fun p y :=
begin
  refine map_injective (mv_polynomial.map (int.cast_ring_hom ℚ))
    (mv_polynomial.map_injective _ int.cast_injective) _,
  simp only [teichmuller_mul_aux₁, map_teichmuller_fun, ring_hom.map_mul]
end

/--
`witt_vector.teichmuller_fun` is a ring hom.
The 0th coefficient of `teichmuller p r` is `r`, and all others are 0.
-/
noncomputable def teichmuller : R →* 𝕎 R :=
{ to_fun := teichmuller_fun p,
  map_one' :=
  begin
    ext ⟨⟩,
    { rw one_coeff_zero, refl },
    { rw one_coeff_pos _ _ (nat.succ_pos n), refl }
  end,
  map_mul' :=
  begin
    intros x y,
    rcases counit_surjective R x with ⟨x, rfl⟩,
    rcases counit_surjective R y with ⟨y, rfl⟩,
    simp only [← map_teichmuller_fun, ← ring_hom.map_mul, teichmuller_mul_aux₂],
  end }

@[simp] lemma teichmuller_coeff_zero (r : R) :
  (teichmuller p r).coeff 0 = r := rfl

@[simp] lemma teichmuller_coeff_pos (r : R) :
  ∀ (n : ℕ) (hn : 0 < n), (teichmuller p r).coeff n = 0
| (n+1) _ := rfl.

@[simp] lemma teichmuller_zero : teichmuller p (0:R) = 0 :=
by ext ⟨⟩; { rw zero_coeff, refl }

/-- teichmuller is a natural transformation -/
@[simp] lemma map_teichmuller (f : R →+* S) (r : R) :
  map f (teichmuller p r) = teichmuller p (f r) :=
map_teichmuller_fun _ _ _

@[simp] lemma ghost_component_teichmuller (r : R) (n : ℕ) :
  ghost_component n (teichmuller p r) = r ^ p ^ n :=
ghost_component_teichmuller_fun _ _ _

end witt_vector
