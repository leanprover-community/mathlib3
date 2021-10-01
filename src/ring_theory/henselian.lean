/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.taylor
import ring_theory.ideal.local_ring
import linear_algebra.adic_completion

/-!
# Henselian rings

In this file we set up the basic theory of Henselian (local) rings.
A ring `R` is *Henselian* at an ideal `I` if the following conditions hold:
* `I` is contained in the Jacobson radical of `R`
* for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
  there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.)

A local ring `R` is *Henselian* if it is Henselian at its maximal ideal.
In this case the first condition is automatic, and in the second condition we may ask for
`f.derivative.eval a ≠ 0`, since the quotient ring `R/I` is a field in this case.

## Main declarations

* `henselian_ring`: a typeclass on commutative rings,
  asserting that the ring is Henselian at the ideal `I`.
* `henselian_local_ring`: a typeclass on commutative rings,
   asserting that the ring is local Henselian.
* `field.henselian`: fields are Henselian local rings
* `henselian.tfae`: equivalent ways of expressing the Henselian property for local rings
* `is_adic_complete.henselian`:
  a ring `R` with ideal `I` that is `I`-adically complete is Henselian at `I`

## References

https://stacks.math.columbia.edu/tag/04GE

## Todo

After a good API for etale ring homomorphisms has been developed,
we can give more equivalent characterization os Henselian rings.

In particular, this can give a proof that factorizations into coprime polynomials can be lifted
from the residue field to the Henselian ring.

The following gist contains some code sketches in that direction.
https://gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598

-/



noncomputable theory

universe variables u v

open_locale big_operators

open local_ring polynomial function

lemma is_local_ring_hom_of_le_jacobson_bot {R : Type*} [comm_ring R]
  (I : ideal R) (h : I ≤ ideal.jacobson ⊥) :
  is_local_ring_hom (ideal.quotient.mk I) :=
begin
  constructor,
  intros a h,
  have : is_unit (ideal.quotient.mk (ideal.jacobson ⊥) a),
  { rw [is_unit_iff_exists_inv] at *,
    obtain ⟨b, hb⟩ := h,
    obtain ⟨b, rfl⟩ := ideal.quotient.mk_surjective b,
    use ideal.quotient.mk _ b,
    rw [←(ideal.quotient.mk _).map_one, ←(ideal.quotient.mk _).map_mul, ideal.quotient.eq] at ⊢ hb,
    exact h hb },
  obtain ⟨⟨x, y, h1, h2⟩, rfl : x = _⟩ := this,
  obtain ⟨y, rfl⟩ := ideal.quotient.mk_surjective y,
  rw [← (ideal.quotient.mk _).map_mul, ← (ideal.quotient.mk _).map_one, ideal.quotient.eq,
    ideal.mem_jacobson_bot] at h1 h2,
  specialize h1 1,
  simp at h1,
  exact h1.1,
end

/-- A ring `R` is *Henselian* at an ideal `I` if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the quotient ring `R/I`,
there exists a lift `a : R` of `a₀` that is a root of `f`.

(Here, saying that a root `b` of a polynomial `g` is *simple* means that `g.derivative.eval b` is a
unit. Warning: if `R/I` is not a field then it is not enough to assume that `g` has a factorization
into monic linear factors in which `X - b` shows up only once; for example `1` is not a simple root
of `X^2-1` over `ℤ/4ℤ`.) -/
class henselian_ring (R : Type*) [comm_ring R] (I : ideal R) : Prop :=
(jac : I ≤ ideal.jacobson ⊥)
(is_henselian : ∀ (f : polynomial R) (hf : f.monic) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
  (h₂ : is_unit (ideal.quotient.mk I (f.derivative.eval a₀))),
  ∃ a : R, f.is_root a ∧ (a - a₀ ∈ I))

/-- A local ring `R` is *Henselian* if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the residue field,
there exists a lift `a : R` of `a₀` that is a root of `f`.
(Recall that a root `b` of a polynomial `g` is *simple* if it is not a double root, so if
`g.derivative.eval b ≠ 0`.)

In other words, `R` is local Henselian if it is Henselian at the ideal `I`,
in the sense of `henselian_ring`. -/
class henselian_local_ring (R : Type*) [comm_ring R] extends local_ring R : Prop :=
(is_henselian : ∀ (f : polynomial R) (hf : f.monic) (a₀ : R) (h₁ : f.eval a₀ ∈ maximal_ideal R)
  (h₂ : is_unit (f.derivative.eval a₀)),
  ∃ a : R, f.is_root a ∧ (a - a₀ ∈ maximal_ideal R))

@[priority 100] -- see Note [lower instance priority]
instance field.henselian (K : Type*) [field K] : henselian_local_ring K :=
{ is_henselian := λ f hf a₀ h₁ h₂,
  begin
    refine ⟨a₀, _, _⟩;
    rwa [(maximal_ideal K).eq_bot_of_prime, ideal.mem_bot] at *,
    rw sub_self,
  end }

lemma henselian_local_ring.tfae (R : Type u) [comm_ring R] [local_ring R] :
  tfae [
  henselian_local_ring R,
  ∀ (f : polynomial R) (hf : f.monic) (a₀ : residue_field R) (h₁ : aeval a₀ f = 0)
    (h₂ : aeval a₀ f.derivative ≠ 0),
    ∃ a : R, f.is_root a ∧ (residue R a = a₀),
  ∀ {K : Type u} [field K], by exactI ∀ (φ : R →+* K) (hφ : surjective φ)
    (f : polynomial R) (hf : f.monic) (a₀ : K) (h₁ : f.eval₂ φ a₀ = 0)
    (h₂ : f.derivative.eval₂ φ a₀ ≠ 0),
    ∃ a : R, f.is_root a ∧ (φ a = a₀)] :=
begin
  tfae_have _3_2 : 3 → 2, { intro H, exact H (residue R) ideal.quotient.mk_surjective, },
  tfae_have _2_1 : 2 → 1,
  { intros H, constructor, intros f hf a₀ h₁ h₂,
    specialize H f hf (residue R a₀),
    have aux := flip mem_nonunits_iff.mp h₂,
    simp only [aeval_def, ring_hom.algebra_map_to_algebra, eval₂_at_apply,
      ← ideal.quotient.eq_zero_iff_mem, ← local_ring.mem_maximal_ideal] at H h₁ aux,
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ aux,
    refine ⟨a, ha₁, _⟩,
    rw ← ideal.quotient.eq_zero_iff_mem,
    rwa [← sub_eq_zero, ← ring_hom.map_sub] at ha₂, },
  tfae_have _1_3 : 1 → 3,
  { introsI hR K _K φ hφ f hf a₀ h₁ h₂,
    obtain ⟨a₀, rfl⟩ := hφ a₀,
    have H := henselian_local_ring.is_henselian f hf a₀,
    simp only [← ker_eq_maximal_ideal φ hφ, eval₂_at_apply, φ.mem_ker] at H h₁ h₂,
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ _,
    { refine ⟨a, ha₁, _⟩, rwa [φ.map_sub, sub_eq_zero] at ha₂, },
    { contrapose! h₂,
      rwa [← mem_nonunits_iff, ← local_ring.mem_maximal_ideal,
        ← local_ring.ker_eq_maximal_ideal φ hφ, φ.mem_ker] at h₂, } },
  tfae_finish,
end

instance (R : Type*) [comm_ring R] [hR : henselian_local_ring R] :
  henselian_ring R (maximal_ideal R) :=
{ jac := by { rw [ideal.jacobson, le_Inf_iff], rintro I ⟨-, hI⟩, exact (eq_maximal_ideal hI).ge },
  is_henselian :=
  begin
    intros f hf a₀ h₁ h₂,
    refine henselian_local_ring.is_henselian f hf a₀ h₁ _,
    contrapose! h₂,
    rw [← mem_nonunits_iff, ← local_ring.mem_maximal_ideal, ← ideal.quotient.eq_zero_iff_mem] at h₂,
    rw h₂,
    exact not_is_unit_zero
  end }

/-- A ring `R` that is `I`-adically complete is Henselian at `I`. -/
@[priority 100] -- see Note [lower instance priority]
instance is_adic_complete.henselian_ring
  (R : Type*) [comm_ring R] (I : ideal R) [is_adic_complete I R] :
  henselian_ring R I :=
{ jac := is_adic_complete.le_jacobson_bot _,
  is_henselian :=
  begin
    intros f hf a₀ h₁ h₂,
    classical,
    let f' := f.derivative,
    -- we define a sequence `c n` by starting at `a₀` and then continually
    -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
    -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
    let c : ℕ → R := λ n, nat.rec_on n a₀ (λ _ b, b - f.eval b * ring.inverse (f'.eval b)),
    have hc : ∀ n, c (n+1) = c n - f.eval (c n) * ring.inverse (f'.eval (c n)),
    { intro n, dsimp only [c, nat.rec_add_one], refl, },
    -- we now spend some time determining properties of the sequence `c : ℕ → R`
    -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
    -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
    -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
    have hc_mod : ∀ n, c n ≡ a₀ [SMOD I],
    { intro n, induction n with n ih, { refl },
      rw [nat.succ_eq_add_one, hc, sub_eq_add_neg, ← add_zero a₀],
      refine ih.add _,
      rw [smodeq.zero, ideal.neg_mem_iff],
      refine I.mul_mem_right _ _,
      rw [← smodeq.zero] at h₁ ⊢,
      exact (ih.eval f).trans h₁, },
    have hf'c : ∀ n, is_unit (f'.eval (c n)),
    { intro n,
      haveI := is_local_ring_hom_of_le_jacobson_bot I (is_adic_complete.le_jacobson_bot I),
      apply is_unit_of_map_unit (ideal.quotient.mk I),
      convert h₂ using 1,
      exact smodeq.def.mp ((hc_mod n).eval _), },
    have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n+1),
    { intro n,
      induction n with n ih, { simpa only [pow_one] },
      simp only [nat.succ_eq_add_one],
      rw [← taylor_eval_sub (c n), hc],
      simp only [sub_eq_add_neg, add_neg_cancel_comm],
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
        ← finset.sum_range_add_sum_Ico _ (nat.le_add_left _ _)],
      swap, { intro i, rw zero_mul },
      refine ideal.add_mem _ _ _,
      { simp only [finset.sum_range_succ, taylor_coeff_one, mul_one, pow_one, taylor_coeff_zero,
          mul_neg_eq_neg_mul_symm, finset.sum_singleton, finset.range_one, pow_zero],
        rw [mul_left_comm, ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_self],
        exact ideal.zero_mem _ },
      { refine submodule.sum_mem _ _, simp only [finset.Ico.mem],
        rintro i ⟨h2i, hi⟩,
        have aux : n + 2 ≤ i * (n + 1), { transitivity 2 * (n + 1); nlinarith only [h2i], },
        refine ideal.mul_mem_left _ _ (ideal.pow_le_pow aux _),
        rw [pow_mul'],
        refine ideal.pow_mem_pow ((ideal.neg_mem_iff _).2 $ ideal.mul_mem_right _ _ ih) _, } },
    -- we are now in the position to show that `c : ℕ → R` is a Cauchy sequence
    have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : ideal R)],
    { intros m n hmn,
      rw [← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one],
      obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hmn, clear hmn,
      induction k with k ih, { rw add_zero, },
      rw [nat.succ_eq_add_one, ← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg],
      refine ih.add _, symmetry,
      rw [smodeq.zero, ideal.neg_mem_iff],
      refine ideal.mul_mem_right _ _ (ideal.pow_le_pow _ (hfcI _)),
      rw [add_assoc], exact le_self_add },
    -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
    obtain ⟨a, ha⟩ := is_precomplete.prec' c aux,
    refine ⟨a, _, _⟩,
    { show f.is_root a,
      suffices : ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : ideal R)], { from is_Hausdorff.haus' _ this },
      intro n, specialize ha n,
      rw [← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one] at ha ⊢,
      refine (ha.symm.eval f).trans _,
      rw [smodeq.zero],
      exact ideal.pow_le_pow le_self_add (hfcI _), },
    { show a - a₀ ∈ I,
      specialize ha 1,
      rw [hc, pow_one, ← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one, sub_eq_add_neg] at ha,
      rw [← smodeq.sub_mem, ← add_zero a₀],
      refine ha.symm.trans (smodeq.refl.add _),
      rw [smodeq.zero, ideal.neg_mem_iff],
      exact ideal.mul_mem_right _ _ h₁, }
  end }
