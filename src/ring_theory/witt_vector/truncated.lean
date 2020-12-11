/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.init_tail
import tactic.equiv_rw

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.
We prove this in future work.

## Main declarations

- `truncated_witt_vector`: the underlying type of the ring of truncated Witt vectors
- `witt_vector.truncate_fun`: the truncation map that truncates a Witt vector,
                              to obtain a truncated Witt vector
                              (in future work, this will be bundled into a homomorphism)
- `truncated_witt_vector.comm_ring`: the ring structure on truncated Witt vectors

## TODO

Show that `witt_vector p R` is the projective limit of the system
`truncated_witt_vector p n R` as `n` varies.

-/

open function (injective surjective)

noncomputable theory

variables {p : ℕ} [hp : fact p.prime] (n : ℕ) (R : Type*)

local notation `𝕎` := witt_vector p -- type as `\bbW`

/--
A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`truncated_witt_vector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `truncated_witt_vector p n R`.
(`truncated_witt_vector p₁ n R` and `truncated_witt_vector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
@[nolint unused_arguments]
def truncated_witt_vector (p : ℕ) (n : ℕ) (R : Type*) := fin n → R

instance (p n : ℕ) (R : Type*) [inhabited R] : inhabited (truncated_witt_vector p n R) :=
⟨λ _, default R⟩

variables {n R}

namespace truncated_witt_vector

variables (p)

/-- Create a `truncated_witt_vector` from a vector `x`. -/
def mk (x : fin n → R) : truncated_witt_vector p n R := x

variables {p}

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff (i : fin n) (x : truncated_witt_vector p n R) : R := x i

@[ext]
lemma ext {x y : truncated_witt_vector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
funext h

lemma ext_iff {x y : truncated_witt_vector p n R} : x = y ↔ ∀ i, x.coeff i = y.coeff i :=
⟨λ h i, by rw h, ext⟩

@[simp] lemma coeff_mk (x : fin n → R) (i : fin n) :
  (mk p x).coeff i = x i := rfl

@[simp] lemma mk_coeff (x : truncated_witt_vector p n R) :
  mk p (λ i, x.coeff i) = x :=
by { ext i, rw [coeff_mk] }

variable [comm_ring R]

/--
We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out (x : truncated_witt_vector p n R) : 𝕎 R :=
witt_vector.mk p $ λ i, if h : i < n then x.coeff ⟨i, h⟩ else 0

@[simp]
lemma coeff_out (x : truncated_witt_vector p n R) (i : fin n) :
  x.out.coeff i = x.coeff i :=
by rw [out, witt_vector.coeff_mk, dif_pos i.is_lt, fin.eta]

lemma out_injective : injective (@out p n R _) :=
begin
  intros x y h,
  ext i,
  rw [witt_vector.ext_iff] at h,
  simpa only [coeff_out] using h ↑i
end

end truncated_witt_vector

namespace witt_vector

variables {p} (n)

section

local attribute [semireducible] witt_vector

/-- `truncate_fun n x` uses the first `n` entries of `x` to construct a `truncated_witt_vector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `witt_vector.truncate` -/
def truncate_fun (x : 𝕎 R) : truncated_witt_vector p n R :=
truncated_witt_vector.mk p $ λ i, x.coeff i

end

variables {n}

@[simp] lemma coeff_truncate_fun (x : 𝕎 R) (i : fin n) :
  (truncate_fun n x).coeff i = x.coeff i :=
by rw [truncate_fun, truncated_witt_vector.coeff_mk]

variable [comm_ring R]

@[simp] lemma out_truncate_fun (x : 𝕎 R) :
  (truncate_fun n x).out = init n x :=
begin
  ext i,
  dsimp [truncated_witt_vector.out, init, select],
  split_ifs with hi, swap, { refl },
  rw [coeff_truncate_fun, fin.coe_mk],
end

end witt_vector

namespace truncated_witt_vector

variable [comm_ring R]

@[simp] lemma truncate_fun_out (x : truncated_witt_vector p n R) :
  x.out.truncate_fun n = x :=
by simp only [witt_vector.truncate_fun, coeff_out, mk_coeff]

open witt_vector
variables (p n R)

include hp

instance : has_zero (truncated_witt_vector p n R) :=
⟨truncate_fun n 0⟩

instance : has_one (truncated_witt_vector p n R) :=
⟨truncate_fun n 1⟩

instance : has_add (truncated_witt_vector p n R) :=
⟨λ x y, truncate_fun n (x.out + y.out)⟩

instance : has_mul (truncated_witt_vector p n R) :=
⟨λ x y, truncate_fun n (x.out * y.out)⟩

instance : has_neg (truncated_witt_vector p n R) :=
⟨λ x, truncate_fun n (- x.out)⟩

@[simp] lemma coeff_zero (i : fin n) :
  (0 : truncated_witt_vector p n R).coeff i = 0 :=
begin
  show coeff i (truncate_fun _ 0 : truncated_witt_vector p n R) = 0,
  rw [coeff_truncate_fun, witt_vector.zero_coeff],
end

end truncated_witt_vector

/-- A macro tactic used to prove that `truncate_fun` respects ring operations. -/
meta def tactic.interactive.witt_truncate_fun_tac : tactic unit :=
`[show _ = truncate_fun n _,
  apply truncated_witt_vector.out_injective,
  iterate { rw [out_truncate_fun] },
  rw init_add <|> rw init_mul <|> rw init_neg]

namespace witt_vector

variables (p n R)
variable [comm_ring R]

lemma truncate_fun_surjective :
  surjective (@truncate_fun p n R) :=
λ x, ⟨x.out, truncated_witt_vector.truncate_fun_out x⟩

include hp

@[simp]
lemma truncate_fun_zero : truncate_fun n (0 : 𝕎 R) = 0 := rfl

@[simp]
lemma truncate_fun_one : truncate_fun n (1 : 𝕎 R) = 1 := rfl

variables {p R}

@[simp]
lemma truncate_fun_add (x y : 𝕎 R) :
  truncate_fun n (x + y) = truncate_fun n x + truncate_fun n y :=
by witt_truncate_fun_tac

@[simp]
lemma truncate_fun_mul (x y : 𝕎 R) :
  truncate_fun n (x * y) = truncate_fun n x * truncate_fun n y :=
by witt_truncate_fun_tac

lemma truncate_fun_neg (x : 𝕎 R) :
  truncate_fun n (-x) = -truncate_fun n x :=
by witt_truncate_fun_tac

end witt_vector

namespace truncated_witt_vector
open witt_vector
variables (p n R)
variable [comm_ring R]
include hp

instance : comm_ring (truncated_witt_vector p n R) :=
(truncate_fun_surjective p n R).comm_ring _
  (truncate_fun_zero p n R)
  (truncate_fun_one p n R)
  (truncate_fun_add n)
  (truncate_fun_mul n)
  (truncate_fun_neg n)

end truncated_witt_vector
