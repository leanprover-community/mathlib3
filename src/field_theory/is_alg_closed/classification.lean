/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import ring_theory.algebraic_independent
import field_theory.is_alg_closed.basic
import data.polynomial.cardinal
import data.mv_polynomial.cardinal
import data.zmod.algebra
/-!
# Classification of Algebraically closed fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results related to classifying algebraically closed fields.

## Main statements

* `is_alg_closed.equiv_of_transcendence_basis` Two fields with the same characteristic and the same
  cardinality of transcendence basis are isomorphic.
* `is_alg_closed.ring_equiv_of_cardinal_eq_of_char_eq` Two uncountable algebraically closed fields
  are isomorphic if they have the same characteristic and the same cardinality.
-/
universe u

open_locale cardinal polynomial
open cardinal

section algebraic_closure

namespace algebra.is_algebraic

variables (R L : Type u) [comm_ring R] [comm_ring L] [is_domain L] [algebra R L]
variables [no_zero_smul_divisors R L] (halg : algebra.is_algebraic R L)

lemma cardinal_mk_le_sigma_polynomial :
  #L ≤ #(Σ p : R[X], { x : L // x ∈ (p.map (algebra_map R L)).roots }) :=
@mk_le_of_injective L (Σ p : R[X], { x : L | x ∈ (p.map (algebra_map R L)).roots })
  (λ x : L, let p := classical.indefinite_description _ (halg x) in
    ⟨p.1, x,
      begin
      dsimp,
      have h : p.1.map (algebra_map R L) ≠ 0,
      { rw [ne.def, ← polynomial.degree_eq_bot, polynomial.degree_map_eq_of_injective
          (no_zero_smul_divisors.algebra_map_injective R L), polynomial.degree_eq_bot],
        exact p.2.1 },
      erw [polynomial.mem_roots h, polynomial.is_root, polynomial.eval_map,
        ← polynomial.aeval_def, p.2.2],
      end⟩) (λ x y, begin
    intro h,
    simp only at h,
    refine (subtype.heq_iff_coe_eq _).1 h.2,
    simp only [h.1, iff_self, forall_true_iff]
  end)

/--The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀` -/
lemma cardinal_mk_le_max : #L ≤ max (#R) ℵ₀ :=
calc #L ≤ #(Σ p : R[X], { x : L // x ∈ (p.map (algebra_map R L)).roots }) :
  cardinal_mk_le_sigma_polynomial R L halg
... = cardinal.sum (λ p : R[X], #{ x : L | x ∈ (p.map (algebra_map R L)).roots }) :
  by rw ← mk_sigma; refl
... ≤ cardinal.sum.{u u} (λ p : R[X], ℵ₀) :
  sum_le_sum _ _ $ λ p, (multiset.finite_to_set _).lt_aleph_0.le
... = #R[X] * ℵ₀ : sum_const' _ _
... ≤ max (max (#R[X]) ℵ₀) ℵ₀ : mul_le_max _ _
... ≤ max (max (max (#R) ℵ₀) ℵ₀) ℵ₀ :
  max_le_max (max_le_max polynomial.cardinal_mk_le_max le_rfl) le_rfl
... = max (#R) ℵ₀ : by simp only [max_assoc, max_comm ℵ₀, max_left_comm ℵ₀, max_self]

end algebra.is_algebraic

end algebraic_closure

namespace is_alg_closed

section classification

noncomputable theory

variables {R L K : Type*} [comm_ring R]
variables [field K] [algebra R K]
variables [field L] [algebra R L]
variables {ι : Type*} (v : ι → K)
variables {κ : Type*} (w : κ → L)

variables (hv : algebraic_independent R v)

lemma is_alg_closure_of_transcendence_basis [is_alg_closed K] (hv : is_transcendence_basis R v) :
  is_alg_closure (algebra.adjoin R (set.range v)) K :=
by letI := ring_hom.domain_nontrivial (algebra_map R K); exact
{ alg_closed := by apply_instance,
  algebraic := hv.is_algebraic }

variables (hw : algebraic_independent R w)

/-- setting `R` to be `zmod (ring_char R)` this result shows that if two algebraically
closed fields have equipotent transcendence bases and the same characteristic then they are
isomorphic. -/
def equiv_of_transcendence_basis [is_alg_closed K] [is_alg_closed L] (e : ι ≃ κ)
  (hv : is_transcendence_basis R v) (hw : is_transcendence_basis R w) : K ≃+* L :=
begin
  letI := is_alg_closure_of_transcendence_basis v hv;
  letI := is_alg_closure_of_transcendence_basis w hw;
  have e : algebra.adjoin R (set.range v) ≃+* algebra.adjoin R (set.range w),
  { refine hv.1.aeval_equiv.symm.to_ring_equiv.trans _,
    refine (alg_equiv.of_alg_hom
      (mv_polynomial.rename e)
      (mv_polynomial.rename e.symm)
      _ _).to_ring_equiv.trans _,
    { ext, simp },
    { ext, simp },
    exact hw.1.aeval_equiv.to_ring_equiv },
  exact is_alg_closure.equiv_of_equiv K L e
end

end classification

section cardinal

variables {R L K : Type u} [comm_ring R]
variables [field K] [algebra R K] [is_alg_closed K]
variables {ι : Type u} (v : ι → K)
variable (hv : is_transcendence_basis R v)

lemma cardinal_le_max_transcendence_basis (hv : is_transcendence_basis R v) :
  #K ≤ max (max (#R) (#ι)) ℵ₀ :=
calc #K ≤ max (#(algebra.adjoin R (set.range v))) ℵ₀ :
  by letI := is_alg_closure_of_transcendence_basis v hv;
   exact algebra.is_algebraic.cardinal_mk_le_max _ _ is_alg_closure.algebraic
... = max (#(mv_polynomial ι R)) ℵ₀ : by rw [cardinal.eq.2 ⟨(hv.1.aeval_equiv).to_equiv⟩]
... ≤ max (max (max (#R) (#ι)) ℵ₀) ℵ₀ : max_le_max mv_polynomial.cardinal_mk_le_max le_rfl
... = _ : by simp [max_assoc]

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis. -/
lemma cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt [nontrivial R]
  (hv : is_transcendence_basis R v) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) : #K = #ι :=
have ℵ₀ ≤ #ι,
  from le_of_not_lt (λ h,
    not_le_of_gt hK $ calc
      #K ≤ max (max (#R) (#ι)) ℵ₀ : cardinal_le_max_transcendence_basis v hv
     ... ≤ _ : max_le (max_le hR (le_of_lt h)) le_rfl),
le_antisymm
  (calc #K ≤ max (max (#R) (#ι)) ℵ₀ : cardinal_le_max_transcendence_basis v hv
       ... = #ι : begin
         rw [max_eq_left, max_eq_right],
         { exact le_trans hR this },
         { exact le_max_of_le_right this }
       end)
  (mk_le_of_injective (show function.injective v, from hv.1.injective))

end cardinal

variables {K L : Type} [field K] [field L] [is_alg_closed K] [is_alg_closed L]

/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
@[nolint def_lemma] lemma ring_equiv_of_cardinal_eq_of_char_zero [char_zero K] [char_zero L]
  (hK : ℵ₀ < #K) (hKL : #K = #L) : K ≃+* L :=
begin
  apply classical.choice,
  cases exists_is_transcendence_basis ℤ
    (show function.injective (algebra_map ℤ K),
      from int.cast_injective) with s hs,
  cases exists_is_transcendence_basis ℤ
    (show function.injective (algebra_map ℤ L),
      from int.cast_injective) with t ht,
  have : #s = #t,
  { rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ hs (le_of_eq mk_int) hK,
        ← cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ ht (le_of_eq mk_int), hKL],
    rwa ← hKL },
  cases cardinal.eq.1 this with e,
  exact ⟨equiv_of_transcendence_basis _ _ e hs ht⟩
end

private lemma ring_equiv_of_cardinal_eq_of_char_p (p : ℕ) [fact p.prime]
  [char_p K p] [char_p L p] (hK : ℵ₀ < #K) (hKL : #K = #L) : K ≃+* L :=
begin
  apply classical.choice,
  cases exists_is_transcendence_basis (zmod p)
    (show function.injective (algebra_map (zmod p) K),
      from ring_hom.injective _) with s hs,
  cases exists_is_transcendence_basis (zmod p)
    (show function.injective (algebra_map (zmod p) L),
      from ring_hom.injective _) with t ht,
  have : #s = #t,
  { rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ hs
      (lt_aleph_0_of_finite (zmod p)).le hK,
        ← cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ ht
      (lt_aleph_0_of_finite (zmod p)).le, hKL],
    rwa ← hKL },
  cases cardinal.eq.1 this with e,
  exact ⟨equiv_of_transcendence_basis _ _ e hs ht⟩
end

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
@[nolint def_lemma] lemma ring_equiv_of_cardinal_eq_of_char_eq (p : ℕ) [char_p K p] [char_p L p]
  (hK : ℵ₀ < #K) (hKL : #K = #L) : K ≃+* L :=
begin
  apply classical.choice,
  rcases char_p.char_is_prime_or_zero K p with hp | hp,
  { haveI : fact p.prime := ⟨hp⟩,
    exact ⟨ring_equiv_of_cardinal_eq_of_char_p p hK hKL⟩ },
  { rw [hp] at *,
    resetI,
    letI : char_zero K := char_p.char_p_to_char_zero K,
    letI : char_zero L := char_p.char_p_to_char_zero L,
    exact ⟨ring_equiv_of_cardinal_eq_of_char_zero hK hKL⟩ }
end

end is_alg_closed
