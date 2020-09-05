/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.basic

/-!

# Truncated Witt vectors

-/

noncomputable theory

def truncated_witt_vectors (p : ℕ) (n : ℕ) (R : Type*) :=
fin n → R

namespace truncated_witt_vectors

section basics
variables (p : ℕ) (n : ℕ) (R : Type*)

instance [fintype R] : fintype (truncated_witt_vectors p n R) :=
pi.fintype

lemma card [fintype R] :
  fintype.card (truncated_witt_vectors p n R) = fintype.card R ^ n :=
sorry

end basics

end truncated_witt_vectors

namespace witt_vectors

variables (p : ℕ) [fact p.prime] (n : ℕ) (R : Type*) [comm_ring R]

local notation `𝕎` := witt_vectors p -- type as `\bbW`

-- huh, what's wrong here?
def truncate_fun : 𝕎 R → truncated_witt_vectors p n R :=
λ x i, x.coeff i

end witt_vectors

namespace truncated_witt_vectors

variables (p : ℕ) [fact p.prime] (n : ℕ) (R : Type*) [comm_ring R]

local notation `𝕎` := witt_vectors p -- type as `\bbW`

-- the "kernel" of `truncate_fun` is `witt_vectors.ideal n`
instance : comm_ring (truncated_witt_vectors p n R) := sorry

end truncated_witt_vectors
