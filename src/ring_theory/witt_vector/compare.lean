/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/

import ring_theory.witt_vector.truncated
import ring_theory.witt_vector.identities
import number_theory.padics.ring_homs

/-!

# Comparison isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`

We construct a ring isomorphism between `witt_vector p (zmod p)` and `ℤ_[p]`.
This isomorphism follows from the fact that both satisfy the universal property
of the inverse limit of `zmod (p^n)`.

## Main declarations

* `witt_vector.to_zmod_pow`: a family of compatible ring homs `𝕎 (zmod p) → zmod (p^k)`
* `witt_vector.equiv`: the isomorphism

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

noncomputable theory

variables {p : ℕ} [hp : fact p.prime]

local notation `𝕎` := witt_vector p

include hp

namespace truncated_witt_vector

variables (p) (n : ℕ) (R : Type*) [comm_ring R]

lemma eq_of_le_of_cast_pow_eq_zero [char_p R p] (i : ℕ) (hin : i ≤ n)
  (hpi : (p ^ i : truncated_witt_vector p n R) = 0) :
  i = n :=
begin
  contrapose! hpi,
  replace hin := lt_of_le_of_ne hin hpi, clear hpi,
  have : (↑p ^ i : truncated_witt_vector p n R) = witt_vector.truncate n (↑p ^ i),
  { rw [ring_hom.map_pow, ring_hom.map_nat_cast] },
  rw [this, ext_iff, not_forall], clear this,
  use ⟨i, hin⟩,
  rw [witt_vector.coeff_truncate, coeff_zero, fin.coe_mk, witt_vector.coeff_p_pow],
  haveI : nontrivial R := char_p.nontrivial_of_char_ne_one hp.1.ne_one,
  exact one_ne_zero
end

section iso

variables (p n) {R}

lemma card_zmod : fintype.card (truncated_witt_vector p n (zmod p)) = p ^ n :=
by rw [card, zmod.card]

lemma char_p_zmod : char_p (truncated_witt_vector p n (zmod p)) (p ^ n) :=
char_p_of_prime_pow_injective _ _ _ (card_zmod _ _)
    (eq_of_le_of_cast_pow_eq_zero p n (zmod p))

local attribute [instance] char_p_zmod

/--
The unique isomorphism between `zmod p^n` and `truncated_witt_vector p n (zmod p)`.

This isomorphism exists, because `truncated_witt_vector p n (zmod p)` is a finite ring
with characteristic and cardinality `p^n`.
-/
def zmod_equiv_trunc : zmod (p^n) ≃+* truncated_witt_vector p n (zmod p) :=
zmod.ring_equiv (truncated_witt_vector p n (zmod p)) (card_zmod _ _)

lemma zmod_equiv_trunc_apply {x : zmod (p^n)} :
  zmod_equiv_trunc p n x = zmod.cast_hom (by refl) (truncated_witt_vector p n (zmod p)) x :=
rfl

/--
The following diagram commutes:
```text
          zmod (p^n) ----------------------------> zmod (p^m)
            |                                        |
            |                                        |
            v                                        v
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
```
Here the vertical arrows are `truncated_witt_vector.zmod_equiv_trunc`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
lemma commutes {m : ℕ} (hm : n ≤ m) :
  (truncate hm).comp (zmod_equiv_trunc p m).to_ring_hom =
    (zmod_equiv_trunc p n).to_ring_hom.comp (zmod.cast_hom (pow_dvd_pow p hm) _) :=
ring_hom.ext_zmod _ _

lemma commutes' {m : ℕ} (hm : n ≤ m) (x : zmod (p^m)) :
  truncate hm (zmod_equiv_trunc p m x) =
    zmod_equiv_trunc p n (zmod.cast_hom (pow_dvd_pow p hm) _ x) :=
show (truncate hm).comp (zmod_equiv_trunc p m).to_ring_hom x = _,
by rw commutes _ _ hm; refl

lemma commutes_symm' {m : ℕ} (hm : n ≤ m) (x : truncated_witt_vector p m (zmod p)) :
  (zmod_equiv_trunc p n).symm (truncate hm x) =
    zmod.cast_hom (pow_dvd_pow p hm) _ ((zmod_equiv_trunc p m).symm x) :=
begin
  apply (zmod_equiv_trunc p n).injective,
  rw ← commutes',
  simp
end

/--
The following diagram commutes:
```text
truncated_witt_vector p n (zmod p) ----> truncated_witt_vector p m (zmod p)
            |                                        |
            |                                        |
            v                                        v
          zmod (p^n) ----------------------------> zmod (p^m)
```
Here the vertical arrows are `(truncated_witt_vector.zmod_equiv_trunc p _).symm`,
the horizontal arrow at the top is `zmod.cast_hom`,
and the horizontal arrow at the bottom is `truncated_witt_vector.truncate`.
-/
lemma commutes_symm {m : ℕ} (hm : n ≤ m) :
  (zmod_equiv_trunc p n).symm.to_ring_hom.comp (truncate hm) =
    (zmod.cast_hom (pow_dvd_pow p hm) _).comp (zmod_equiv_trunc p m).symm.to_ring_hom :=
by ext; apply commutes_symm'

end iso

end truncated_witt_vector

namespace witt_vector
open truncated_witt_vector

variables (p)

/--
`to_zmod_pow` is a family of compatible ring homs. We get this family by composing
`truncated_witt_vector.zmod_equiv_trunc` (in right-to-left direction)
with `witt_vector.truncate`.
-/
def to_zmod_pow (k : ℕ) : 𝕎 (zmod p) →+* zmod (p ^ k) :=
(zmod_equiv_trunc p k).symm.to_ring_hom.comp (truncate k)

lemma to_zmod_pow_compat (m n : ℕ) (h : m ≤ n) :
  (zmod.cast_hom (pow_dvd_pow p h) (zmod (p ^ m))).comp (to_zmod_pow p n) = to_zmod_pow p m :=
calc (zmod.cast_hom _ (zmod (p ^ m))).comp
      ((zmod_equiv_trunc p n).symm.to_ring_hom.comp (truncate n)) =
  ((zmod_equiv_trunc p m).symm.to_ring_hom.comp
    (truncated_witt_vector.truncate h)).comp (truncate n) :
  by rw [commutes_symm, ring_hom.comp_assoc]
... = (zmod_equiv_trunc p m).symm.to_ring_hom.comp (truncate m) :
  by rw [ring_hom.comp_assoc, truncate_comp_witt_vector_truncate]

/--
`to_padic_int` lifts `to_zmod_pow : 𝕎 (zmod p) →+* zmod (p ^ k)` to a ring hom to `ℤ_[p]`
using `padic_int.lift`, the universal property of `ℤ_[p]`.
-/
def to_padic_int : 𝕎 (zmod p) →+* ℤ_[p] := padic_int.lift $ to_zmod_pow_compat p

lemma zmod_equiv_trunc_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (truncated_witt_vector.truncate hk).comp
        ((zmod_equiv_trunc p k₂).to_ring_hom.comp
           (padic_int.to_zmod_pow k₂)) =
      (zmod_equiv_trunc p k₁).to_ring_hom.comp (padic_int.to_zmod_pow k₁) :=
by rw [← ring_hom.comp_assoc, commutes, ring_hom.comp_assoc, padic_int.zmod_cast_comp_to_zmod_pow]

/--
`from_padic_int` uses `witt_vector.lift` to lift `truncated_witt_vector.zmod_equiv_trunc`
composed with `padic_int.to_zmod_pow` to a ring hom `ℤ_[p] →+* 𝕎 (zmod p)`.
-/
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
  simp only [ring_equiv.symm_to_ring_hom_comp_to_ring_hom, ring_hom.id_comp]
end

lemma to_padic_int_comp_from_padic_int_ext (x) :
  (to_padic_int p).comp (from_padic_int p) x = ring_hom.id ℤ_[p] x :=
by rw to_padic_int_comp_from_padic_int

lemma from_padic_int_comp_to_padic_int :
  (from_padic_int p).comp (to_padic_int p) = ring_hom.id (𝕎 (zmod p)) :=
begin
  apply witt_vector.hom_ext,
  intro n,
  rw [from_padic_int, ← ring_hom.comp_assoc, truncate_comp_lift, ring_hom.comp_assoc],
  simp only [to_padic_int, to_zmod_pow, ring_hom.comp_id, padic_int.lift_spec, ring_hom.id_comp,
    ← ring_hom.comp_assoc, ring_equiv.to_ring_hom_comp_symm_to_ring_hom]
end

lemma from_padic_int_comp_to_padic_int_ext (x) :
  (from_padic_int p).comp (to_padic_int p) x = ring_hom.id (𝕎 (zmod p)) x :=
by rw from_padic_int_comp_to_padic_int

/--
The ring of Witt vectors over `zmod p` is isomorphic to the ring of `p`-adic integers. This
equivalence is witnessed by `witt_vector.to_padic_int` with inverse `witt_vector.from_padic_int`.
-/
def equiv : 𝕎 (zmod p) ≃+* ℤ_[p] :=
{ to_fun := to_padic_int p,
  inv_fun := from_padic_int p,
  left_inv := from_padic_int_comp_to_padic_int_ext _,
  right_inv := to_padic_int_comp_from_padic_int_ext _,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _ }

end witt_vector
