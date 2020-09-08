import ring_theory.witt_vector.truncated
import data.padics.ring_homs

/-!

# Comparison isomorphism between `witt_vector (zmod p)` and `ℤ_[p]`

-/

noncomputable theory

namespace witt_vector
open truncated_witt_vector

variables (p : ℕ) [hp : fact p.prime]
include hp

local notation `𝕎` := witt_vector p -- type as `\bbW`

def to_zmod_pow (k : ℕ) : 𝕎 (zmod p) →+* zmod (p ^ k) :=
(zmod_equiv_trunc p k).symm.to_ring_hom.comp (truncate p k)

lemma to_zmod_pow_compat (m n : ℕ) (h : m ≤ n) :
  (zmod.cast_hom (show p ^ m ∣ p ^ n, by { simpa using pow_dvd_pow p h }) (zmod (p ^ m))).comp ((λ (k : ℕ), to_zmod_pow p k) n) =
    (λ (k : ℕ), to_zmod_pow p k) m :=
begin
  unfold to_zmod_pow,
  rw [← ring_hom.comp_assoc, ← commutes_symm p _ h],
  refl
end

def to_padic_int : 𝕎 (zmod p) →+* ℤ_[p] :=
-- I think the family should be an explicit argument of `lift`,
-- for increased readability.
padic_int.lift (λ m n h, to_zmod_pow_compat p m n h)

lemma zmod_equiv_trunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (truncated_witt_vector.truncate p (zmod p) hk).comp
        ((zmod_equiv_trunc p k₂).to_ring_hom.comp
           (padic_int.to_zmod_pow k₂)) =
      (zmod_equiv_trunc p k₁).to_ring_hom.comp (padic_int.to_zmod_pow k₁) :=
begin
  rw [← ring_hom.comp_assoc, commutes, ring_hom.comp_assoc, padic_int.zmod_cast_comp_to_zmod_pow],
  assumption
end


def from_padic_int : ℤ_[p] →+* 𝕎 (zmod p) :=
truncated_witt_vector.lift (λ k, (zmod_equiv_trunc p k).to_ring_hom.comp (padic_int.to_zmod_pow k)) $
  zmod_equiv_trunc_compat _

lemma to_padic_int_comp_from_padic_int :
  (to_padic_int p).comp (from_padic_int p) = ring_hom.id ℤ_[p] :=
begin
  rw ← padic_int.to_zmod_pow_eq_iff_ext,
  intro n,
  sorry
end
-- we might want a `hom_eq_hom` for `ℤ_[p]` like we have for `𝕎 R` in the truncated file

lemma from_padic_int_comp_to_padic_int :
  (from_padic_int p).comp (to_padic_int p) = ring_hom.id (𝕎 (zmod p)) :=
begin
  apply witt_vector.hom_ext,
  intro n,
  sorry
end

--sorry -- use `hom_eq_hom`

def equiv : 𝕎 (zmod p) ≃+* ℤ_[p] := sorry

end witt_vector
