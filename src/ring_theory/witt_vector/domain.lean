/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import ring_theory.witt_vector.identities

/-!

# Witt vectors over a domain

This file builds to the proof `witt_vector.domain`,
an instance that says if `R` is an integral domain, then so is `𝕎 R`.
Most of the file develops an API around iterated applications
of `witt_vector.verschiebung` and `witt_vector.frobenius`.

The [proof sketch](https://tinyurl.com/2p8cwrn7) goes as follows:
any nonzero $$x$$ is an iterated application of $$V$$
to some vector $$w_x$$ whose 0th component is zero (`witt_vector.verschiebung_nonzero`).
Known identities (`witt_vector.iterate_verschiebung_mul`) allow us to transform
the product of two such $$x$$ and $$y$$
to the form $$V^{m+n}\left(F^n(w_x) \cdot F^m(w_y)\right)$$,
the 0th component of which must be nonzero.

## Main declarations

* `witt_vector.iterate_verschiebung_mul_coeff` : an identity from [Haze09]
* `witt_vector.domain`

-/

open function


lemma function.iterate_comm_aux {α : Type*} (op1 op2 : α → α) (h_comm : ∀ v, op1 (op2 v) = op2 (op1 v)) (a : α) (j : ℕ) :
  op1 (nat.iterate op2 j a) = nat.iterate op2 j (op1 a) :=
begin
  induction j with j jh,
  { refl },
  { rw [iterate_succ_apply', h_comm, jh, iterate_succ_apply'], }
end
lemma function.iterate_comm_apply {α : Type*} (op1 op2 : α → α) (h_comm : ∀ v, op1 (op2 v) = op2 (op1 v)) (a : α) (i j : ℕ) :
  nat.iterate op1 i (nat.iterate op2 j a) = nat.iterate op2 j (nat.iterate op1 i a) :=
begin
  induction i with i ih generalizing a,
  { refl },
  { rw [iterate_succ_apply', ih, function.iterate_comm_aux op1 op2 h_comm, iterate_succ_apply'], }
end

noncomputable theory
open_locale classical

namespace witt_vector
open function

variables {p : ℕ} {R : Type*}

local notation `𝕎` := witt_vector p -- type as `\bbW`


/-!
## The `shift` operator
-/

/--
`witt_vector.verschiebung` translates the entries of a Witt vector upward, inserting 0s in the gaps.
`witt_vector.shift` does the opposite, removing the first entries.
This is mainly useful as an auxiliary construction for `witt_vector.verschiebung_nonzero`.
-/
def shift (x : 𝕎 R) (n : ℕ) : 𝕎 R := mk p (λ i, x.coeff (n + i))

lemma shift_coeff (x : 𝕎 R) (n k : ℕ) : (x.shift n).coeff k = x.coeff (n + k) :=
rfl

variables [hp : fact p.prime] [comm_ring R]
include hp

lemma verschiebung_shift (x : 𝕎 R) (k : ℕ) (h : ∀ i < k+1, x.coeff i = 0) :
  verschiebung (x.shift k.succ) = x.shift k :=
begin
  ext ⟨j⟩,
  { rw [verschiebung_coeff_zero, shift_coeff, h],
    apply nat.lt_succ_self },
  { simp only [verschiebung_coeff_succ, shift],
    congr' 1,
    rw [nat.add_succ, add_comm, nat.add_succ, add_comm] }
end

lemma eq_iterate_verschiebung {x : 𝕎 R} {n : ℕ} (h : ∀ i < n, x.coeff i = 0) :
  x = (verschiebung^[n] (x.shift n)) :=
begin
  induction n with k ih,
  { cases x; simp [shift] },
  { dsimp, rw verschiebung_shift,
    { exact ih (λ i hi, h _ (hi.trans (nat.lt_succ_self _))), },
    { exact h } }
end

lemma verschiebung_nonzero {x : 𝕎 R} (hx : x ≠ 0) :
  ∃ n : ℕ, ∃ x' : 𝕎 R, x'.coeff 0 ≠ 0 ∧ x = (verschiebung^[n] x') :=
begin
  have hex : ∃ k : ℕ, x.coeff k ≠ 0,
  { by_contradiction hall,
    push_neg at hall,
    apply hx,
    ext i,
    simp only [hall, zero_coeff] },
  let n := nat.find hex,
  use [n, x.shift n],
  refine ⟨nat.find_spec hex, eq_iterate_verschiebung (λ i hi, not_not.mp _)⟩,
  exact nat.find_min hex hi,
end

/-!
## Iteration lemmas

This construction involves iterated applications of `verschiebung` and `frobenius`.
Here we prove some useful lemmas about these.
Auxiliary lemmas are used to simplify double inductions.
-/

lemma iterate_verschiebung_coeff (x : 𝕎 R) (n k : ℕ) :
  (verschiebung^[n] x).coeff (k + n) = x.coeff k :=
begin
  induction n with k ih,
  { simp },
  { rw [iterate_succ_apply', nat.add_succ, verschiebung_coeff_succ],
    exact ih }
end

lemma iterate_verschiebung_mul_left (x y : 𝕎 R) (i : ℕ) :
  (verschiebung^[i] x) * y = (verschiebung^[i] (x * (frobenius^[i] y))) :=
begin
  induction i with i ih generalizing y,
  { simp },
  { rw [iterate_succ_apply', ← verschiebung_mul_frobenius, ih, iterate_succ_apply'], refl }
end

/-!
From this point on, we assume `R` is of characteristic `p`.
-/

section char_p

variable [char_p R p]

lemma iterate_verschiebung_mul_frobenius (x : 𝕎 R) (i j : ℕ) :
  (frobenius^[i] : 𝕎 R → 𝕎 R) (verschiebung^[j] x) =
    (verschiebung^[j] ((frobenius^[i] x))) :=
iterate_comm_apply _ _ (λ _, (verschiebung_frobenius_comm _).symm) _ _ _

lemma iterate_verschiebung_mul (x y : 𝕎 R) (i j : ℕ) :
  (verschiebung^[i] x) * (verschiebung^[j] y) =
    (verschiebung^[i + j] ((frobenius^[j] x) * (frobenius^[i] y))) :=
begin
  calc
  _ = (verschiebung^[i] (x * (frobenius^[i] ((verschiebung^[j] y))))) : _
... = (verschiebung^[i] (x * (verschiebung^[j] ((frobenius^[i] y))))) : _
... = (verschiebung^[i] ((verschiebung^[j] ((frobenius^[i] y)) * x))) : _
... = (verschiebung^[i] ((verschiebung^[j] ((frobenius^[i] y) * (frobenius^[j] x))))) : _
... = (verschiebung^[i + j] ((frobenius^[i] y) * (frobenius^[j] x))) : _
... = _ : _,
  { apply iterate_verschiebung_mul_left },
  { rw iterate_verschiebung_mul_frobenius },
  { rw mul_comm },
  { rw iterate_verschiebung_mul_left },
  { rw iterate_add_apply },
  { rw mul_comm }
end

lemma iter_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
  ((frobenius^[i] x)).coeff k = (x.coeff k)^(p^i) :=
begin
  induction i with i ih,
  { simp },
  { rw [iterate_succ_apply', coeff_frobenius_char_p, ih],
    ring_exp }
end

/-- This is a slightly specialized form of [Hazewinkel, *Witt Vectors*][Haze09] 6.2 equation 5. -/
lemma iterate_verschiebung_mul_coeff (x y : 𝕎 R) (i j : ℕ) :
  ((verschiebung^[i] x) * (verschiebung^[j] y)).coeff (i + j) =
    (x.coeff 0)^(p ^ j) * (y.coeff 0)^(p ^ i) :=
begin
  calc
  _ = (verschiebung^[i + j] ((frobenius^[j] x) * (frobenius^[i] y))).coeff (i + j) : _
... = ((frobenius^[j] x) * (frobenius^[i] y)).coeff 0 : _
... = (frobenius^[j] x).coeff 0 * ((frobenius^[i] y)).coeff 0 : _
... = _ : _,
  { rw iterate_verschiebung_mul },
  { convert iterate_verschiebung_coeff _ _ _ using 2,
    rw zero_add },
  { apply coeff_mul_zero },
  { simp only [iter_frobenius_coeff] }
end

/-!
## Witt vectors over a domain

If `R` is an integral domain, then so is `𝕎 R`.
This argument is adapted from <https://tinyurl.com/2p8cwrn7>.
-/

variable  [is_domain R]

lemma nonzeros (x y : 𝕎 R) : x * y = 0 → x = 0 ∨ y = 0 :=
begin
  contrapose!,
  rintros ⟨ha, hb⟩,
  rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, hwaeq⟩,
  rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, hwbeq⟩,
  have : (x * y).coeff (na + nb) = (wa.coeff 0) ^ (p ^ nb) * (wb.coeff 0) ^ (p ^ na),
  { rw [← iterate_verschiebung_mul_coeff, hwaeq, hwbeq], },
  have : (x * y).coeff (na + nb) ≠ 0,
  { rw this,
    apply mul_ne_zero; apply pow_ne_zero; assumption },
  contrapose! this,
  simp [this]
end

instance : is_domain (𝕎 R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := nonzeros,
  exists_pair_ne := witt_vector.nontrivial.exists_pair_ne }

end char_p

end witt_vector
