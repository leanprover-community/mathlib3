/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.truncated
import data.padics.ring_homs

/-!

# Comparison isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`

-/

noncomputable theory

namespace witt_vector
open truncated_witt_vector

variables (p : ℕ) [hp : fact p.prime]
include hp

local notation `𝕎` := witt_vector p -- type as `\bbW`

def to_zmod_pow (k : ℕ) : 𝕎 (zmod p) →+* zmod (p ^ k) :=
(zmod_equiv_trunc p k).symm.to_ring_hom.comp (truncate k)

lemma to_zmod_pow_compat (m n : ℕ) (h : m ≤ n) :
  (zmod.cast_hom (show p ^ m ∣ p ^ n, by { simpa using pow_dvd_pow p h }) (zmod (p ^ m))).comp ((λ (k : ℕ), to_zmod_pow p k) n) =
    (λ (k : ℕ), to_zmod_pow p k) m :=
calc (zmod.cast_hom _ (zmod (p ^ m))).comp ((zmod_equiv_trunc p n).symm.to_ring_hom.comp (truncate n)) =
  ((zmod_equiv_trunc p m).symm.to_ring_hom.comp (truncated_witt_vector.truncate h)).comp (truncate n) :
  by rw [commutes_symm, ring_hom.comp_assoc]
... = (zmod_equiv_trunc p m).symm.to_ring_hom.comp (truncate m) :
  by rw [ring_hom.comp_assoc, truncate_comp_witt_vector_truncate]

def to_padic_int : 𝕎 (zmod p) →+* ℤ_[p] :=
-- I think the family should be an explicit argument of `lift`,
-- for increased readability.
padic_int.lift (λ m n h, to_zmod_pow_compat p m n h)

lemma zmod_equiv_trunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (truncated_witt_vector.truncate hk).comp
        ((zmod_equiv_trunc p k₂).to_ring_hom.comp
           (padic_int.to_zmod_pow k₂)) =
      (zmod_equiv_trunc p k₁).to_ring_hom.comp (padic_int.to_zmod_pow k₁) :=
begin
  rw [← ring_hom.comp_assoc, commutes, ring_hom.comp_assoc, padic_int.zmod_cast_comp_to_zmod_pow],
  assumption
end

def from_padic_int : ℤ_[p] →+* 𝕎 (zmod p) :=
witt_vector.lift (λ k, (zmod_equiv_trunc p k).to_ring_hom.comp (padic_int.to_zmod_pow k)) $
  zmod_equiv_trunc_compat _

lemma to_padic_int_comp_from_padic_int :
  (to_padic_int p).comp (from_padic_int p) = ring_hom.id ℤ_[p] :=
begin
  rw ← padic_int.to_zmod_pow_eq_iff_ext,
  intro n,
  rw [← ring_hom.comp_assoc, to_padic_int, padic_int.lift_spec],
  simp only [from_padic_int, to_zmod_pow, ring_hom.comp_id],
  rw [ring_hom.comp_assoc, truncate_comp_lift, ← ring_hom.comp_assoc],
  convert ring_hom.id_comp _,
end

lemma from_padic_int_comp_to_padic_int :
  (from_padic_int p).comp (to_padic_int p) = ring_hom.id (𝕎 (zmod p)) :=
begin
  apply witt_vector.hom_ext,
  intro n,
  rw [from_padic_int, ← ring_hom.comp_assoc, truncate_comp_lift, ring_hom.comp_assoc],
  simp only [to_padic_int, to_zmod_pow, ring_hom.comp_id],
  rw [padic_int.lift_spec, ← ring_hom.comp_assoc],
  convert ring_hom.id_comp _,
  ext1, simp
end

def equiv : 𝕎 (zmod p) ≃+* ℤ_[p] :=
{ to_fun := to_padic_int p,
  inv_fun := from_padic_int p,
  left_inv := λ x, show (from_padic_int p).comp (to_padic_int p) x = _,
              by rw from_padic_int_comp_to_padic_int; refl,
  right_inv := λ x, show (to_padic_int p).comp (from_padic_int p) x = _,
              by rw to_padic_int_comp_from_padic_int; refl,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _ }

end witt_vector
