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


section defs

variables (p : ℕ) [fact p.prime] (n : ℕ) (R : Type*) [comm_ring R]

local notation `𝕎` := witt_vectors p -- type as `\bbW`

@[derive comm_ring]
def truncated_witt_vectors :=
(witt_vectors.ideal p R n).quotient

def witt_vectors.truncate : 𝕎 R →+* truncated_witt_vectors p n R :=
ideal.quotient.mk _

end defs

namespace truncated_witt_vectors

section basics
variables (p : ℕ) [fact p.prime] (n : ℕ) (R : Type*) [comm_ring R]

instance [fintype R] : fintype (truncated_witt_vectors p n R) :=
_

lemma card [fintype R] :
  fintype.card (truncated_witt_vectors p n R) = fintype.card R ^ n :=
sorry

end basics

end truncated_witt_vectors
