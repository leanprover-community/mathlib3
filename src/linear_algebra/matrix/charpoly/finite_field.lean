/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import linear_algebra.matrix.charpoly.coeff
import field_theory.finite.basic
import data.matrix.char_p


/-!
# Results on characteristic polynomials and traces over finite fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

noncomputable theory

open polynomial matrix
open_locale polynomial

variables {n : Type*} [decidable_eq n] [fintype n]

@[simp] lemma finite_field.matrix.charpoly_pow_card {K : Type*} [field K] [fintype K]
  (M : matrix n n K) : (M ^ (fintype.card K)).charpoly = M.charpoly :=
begin
  casesI (is_empty_or_nonempty n).symm,
  { cases char_p.exists K with p hp, letI := hp,
    rcases finite_field.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩,
    haveI : fact p.prime := ⟨hp⟩,
    dsimp at hk, rw hk at *,
    apply (frobenius_inj K[X] p).iterate k,
    repeat { rw iterate_frobenius, rw ← hk },
    rw ← finite_field.expand_card,
    unfold charpoly, rw [alg_hom.map_det, ← coe_det_monoid_hom,
      ← (det_monoid_hom : matrix n n K[X] →* K[X]).map_pow],
    apply congr_arg det,
    refine mat_poly_equiv.injective _,
    rw [alg_equiv.map_pow, mat_poly_equiv_charmatrix, hk, sub_pow_char_pow_of_commute, ← C_pow],
    { exact (id (mat_poly_equiv_eq_X_pow_sub_C (p ^ k) M) : _) },
    { exact (C M).commute_X } },
  { exact congr_arg _ (subsingleton.elim _ _), },
end

@[simp] lemma zmod.charpoly_pow_card {p : ℕ} [fact p.prime] (M : matrix n n (zmod p)) :
  (M ^ p).charpoly = M.charpoly :=
by { have h := finite_field.matrix.charpoly_pow_card M, rwa zmod.card at h, }

lemma finite_field.trace_pow_card {K : Type*} [field K] [fintype K]
  (M : matrix n n K) : trace (M ^ (fintype.card K)) = trace M ^ (fintype.card K) :=
begin
  casesI is_empty_or_nonempty n,
  { simp [zero_pow fintype.card_pos, matrix.trace], },
  rw [matrix.trace_eq_neg_charpoly_coeff, matrix.trace_eq_neg_charpoly_coeff,
       finite_field.matrix.charpoly_pow_card, finite_field.pow_card]
end

lemma zmod.trace_pow_card {p : ℕ} [fact p.prime] (M : matrix n n (zmod p)) :
  trace (M ^ p) = (trace M)^p :=
by { have h := finite_field.trace_pow_card M, rwa zmod.card at h, }
