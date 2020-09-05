import ring_theory.witt_vector.truncated
import data.padics.ring_homs

/-!

# Comparison isomorphism between `witt_vector (zmod p)` and `ℤ_[p]`

-/

noncomputable theory

namespace truncated_witt_vectors

variables (p : ℕ) [hp : fact p.prime] (n : ℕ)
include hp

instance char_p_zmod : char_p (truncated_witt_vectors p n (zmod p)) (p ^ n) :=
sorry

end truncated_witt_vectors

namespace witt_vectors

variables (p : ℕ) [hp : fact p.prime]
include hp

local notation `𝕎` := witt_vectors p -- type as `\bbW`

def to_zmod_pow (n : ℕ) : 𝕎 (zmod p) →+* zmod (p ^ n) :=
(iso_to_zmod (truncated_witt_vectors p n (zmod p)) (p ^ n)
  (by rw [truncated_witt_vectors.card, zmod.card])).to_ring_hom.comp
(witt_vectors.truncate p n)

lemma to_zmod_pow_compat (k1 k2 : ℕ) (hk : k1 ≤ k2) :
ring_hom.comp
  (zmod.cast_hom (pow_dvd_pow p hk) (zmod (p ^ k1)))
  (to_zmod_pow p k2) = to_zmod_pow p k1 :=
begin
  sorry
end

def to_padic_int : 𝕎 (zmod p) →+* ℤ_[p] :=
padic_int.lift (to_zmod_pow_compat p)

end witt_vectors
