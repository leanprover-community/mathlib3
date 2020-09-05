import ring_theory.witt_vector.truncated
import data.padics.ring_homs

/-!

# Comparison isomorphism between `witt_vector (zmod p)` and `ℤ_[p]`

-/

noncomputable theory

namespace witt_vectors

variables (p : ℕ) [hp : fact p.prime]
include hp

local notation `𝕎` := witt_vectors p -- type as `\bbW`

def to_zmod_pow (n : ℕ) : 𝕎 (zmod p) →+* zmod (p ^ n) :=
ring_hom.comp (iso_to_zmod _ _ _).to_ring_hom
  (witt_vectors.truncate p n)

def to_padic_int : 𝕎 (zmod p) →+* ℤ_[p] :=
padic_int.lift _

end witt_vectors
