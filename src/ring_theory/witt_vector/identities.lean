/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.frobenius
import ring_theory.witt_vector.verschiebung
import ring_theory.witt_vector.mul_p

/-!
## Identities between operations on the ring of Witt vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
* `iterate_verschiebung_mul_coeff`: an identity from [Haze09] 6.2

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace witt_vector

variables {p : ℕ} {R : Type*} [hp : fact p.prime] [comm_ring R]
local notation `𝕎` := witt_vector p -- type as `\bbW`
include hp
noncomputable theory

/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
lemma frobenius_verschiebung (x : 𝕎 R) :
  frobenius (verschiebung x) = x * p :=
by { ghost_calc x, ghost_simp [mul_comm] }

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `zmod p`. -/
lemma verschiebung_zmod (x : 𝕎 (zmod p)) :
  verschiebung x = x * p :=
by rw [← frobenius_verschiebung, frobenius_zmodp]

variables (p R)

lemma coeff_p_pow [char_p R p] (i : ℕ) : (p ^ i : 𝕎 R).coeff i = 1 :=
begin
  induction i with i h,
  { simp only [one_coeff_zero, ne.def, pow_zero] },
  { rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p,
        verschiebung_coeff_succ, h, one_pow], }
end

lemma coeff_p_pow_eq_zero [char_p R p] {i j : ℕ} (hj : j ≠ i) : (p ^ i : 𝕎 R).coeff j = 0 :=
begin
  induction i with i hi generalizing j,
  { rw [pow_zero, one_coeff_eq_of_pos],
    exact nat.pos_of_ne_zero hj },
  { rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p],
    cases j,
    { rw [verschiebung_coeff_zero, zero_pow],
      exact nat.prime.pos hp.out },
    { rw [verschiebung_coeff_succ, hi, zero_pow],
      { exact nat.prime.pos hp.out },
      { exact ne_of_apply_ne (λ (j : ℕ), j.succ) hj } } }
end

lemma coeff_p [char_p R p] (i : ℕ) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 :=
begin
  split_ifs with hi,
  { simpa only [hi, pow_one] using coeff_p_pow p R 1, },
  { simpa only [pow_one] using coeff_p_pow_eq_zero p R hi, }
end

@[simp] lemma coeff_p_zero [char_p R p] : (p : 𝕎 R).coeff 0 = 0 :=
by { rw [coeff_p, if_neg], exact zero_ne_one }

@[simp] lemma coeff_p_one [char_p R p] : (p : 𝕎 R).coeff 1 = 1 :=
by rw [coeff_p, if_pos rfl]

lemma p_nonzero [nontrivial R] [char_p R p] : (p : 𝕎 R) ≠ 0 :=
by { intros h, simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R }

lemma fraction_ring.p_nonzero [nontrivial R] [char_p R p] :
  (p : fraction_ring (𝕎 R)) ≠ 0 :=
by simpa using (is_fraction_ring.injective (𝕎 R) (fraction_ring (𝕎 R))).ne (p_nonzero _ _)

variables {p R}

/-- The “projection formula” for Frobenius and Verschiebung. -/
lemma verschiebung_mul_frobenius (x y : 𝕎 R) :
  verschiebung (x * frobenius y) = verschiebung x * y :=
by { ghost_calc x y, rintro ⟨⟩; ghost_simp [mul_assoc] }

lemma mul_char_p_coeff_zero [char_p R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 :=
begin
  rw [← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_zero, zero_pow],
  exact nat.prime.pos hp.out
end

lemma mul_char_p_coeff_succ [char_p R p] (x : 𝕎 R) (i : ℕ) :
  (x * p).coeff (i + 1) = (x.coeff i)^p :=
by rw [← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_succ]

lemma verschiebung_frobenius [char_p R p] (x : 𝕎 R) :
  verschiebung (frobenius x) = x * p :=
begin
  ext ⟨i⟩,
  { rw [mul_char_p_coeff_zero, verschiebung_coeff_zero], },
  { rw [mul_char_p_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_char_p], }
end

lemma verschiebung_frobenius_comm [char_p R p] :
  function.commute (verschiebung : 𝕎 R → 𝕎 R) frobenius :=
λ x, by rw [verschiebung_frobenius, frobenius_verschiebung]


/-!
## Iteration lemmas
-/

open function

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

section char_p

variable [char_p R p]

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
  { rw verschiebung_frobenius_comm.iterate_iterate; apply_instance },
  { rw mul_comm },
  { rw iterate_verschiebung_mul_left },
  { rw iterate_add_apply },
  { rw mul_comm }
end

lemma iterate_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
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
  { apply mul_coeff_zero },
  { simp only [iterate_frobenius_coeff] }
end

end char_p

end witt_vector
