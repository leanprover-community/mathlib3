/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.verschiebung

/-! ## Multiplication by `p` -/

namespace witt_vector

variables (p : ℕ) (R : Type*) [hp : fact p.prime] [comm_ring R]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial

include hp

lemma coeff_p_pow [nontrivial R] (i : ℕ) : (p ^ i : 𝕎 R).coeff i ≠ 0 :=
begin

end

end witt_vector
