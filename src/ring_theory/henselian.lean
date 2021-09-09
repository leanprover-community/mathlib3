/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.taylor
import ring_theory.ideal.local_ring
import linear_algebra.adic_completion

/-!
# Henselian local rings

In this file we set up the basic theory of Henselian local rings.
A local ring `R` is *Henselian* if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the residue field,
there exists a lift `a : R` of `a₀` that is a root of `f`.
(Recall that a root `a` is *simple* if it is not a double root, so `f.derivative.eval a ≠ 0`.)

## Main declarations

* `henselian`: a typeclass on commutative rings, asserting that the ring is local Henselian.
* `field.henselian`: fields are Henselian local rings
* `henselian.tfae`: equivalent ways of expressing the Henselian property
* `is_adic_complete.henselian`:
  a local ring `R` with maximal ideal `I` that is `I`-adically complete is Henselian

## References

https://stacks.math.columbia.edu/tag/04GE
-/

noncomputable theory

universe variables u v

open_locale big_operators

open local_ring polynomial function

/-- A local ring `R` is *Henselian* if the following condition holds:
for every polynomial `f` over `R`, with a *simple* root `a₀` over the residue field,
there exists a lift `a : R` of `a₀` that is a root of `f`.
(Recall that a root `a` is *simple* if it is not a double root, so `f.derivative.eval a ≠ 0`.) -/
class henselian (R : Type*) [comm_ring R] extends local_ring R : Prop :=
(is_henselian : ∀ (f : polynomial R) (hf : f.monic) (a₀ : R) (h₁ : f.eval a₀ ∈ maximal_ideal R)
  (h₂ : is_unit (f.derivative.eval a₀)),
  ∃ a : R, f.is_root a ∧ (a - a₀ ∈ maximal_ideal R))

@[priority 100] -- see Note [lower instance priority]
instance field.henselian (K : Type*) [field K] : henselian K :=
{ is_henselian := λ f hf a₀ h₁ h₂,
  begin
    refine ⟨a₀, _, _⟩;
    rwa [(maximal_ideal K).eq_bot_of_prime, ideal.mem_bot] at *,
    rw sub_self,
  end }

lemma henselian.tfae (R : Type u) [comm_ring R] [local_ring R] :
  tfae [
  henselian R,
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
    have H := henselian.is_henselian f hf a₀,
    simp only [← ker_eq_maximal_ideal φ hφ, eval₂_at_apply, φ.mem_ker] at H h₁ h₂,
    obtain ⟨a, ha₁, ha₂⟩ := H h₁ _,
    { refine ⟨a, ha₁, _⟩, rwa [φ.map_sub, sub_eq_zero] at ha₂, },
    { contrapose! h₂,
      rwa [← mem_nonunits_iff, ← local_ring.mem_maximal_ideal,
        ← local_ring.ker_eq_maximal_ideal φ hφ, φ.mem_ker] at h₂, } },
  tfae_finish,
end

/-- A local ring `R` with maximal ideal `I` that is `I`-adically complete is Henselian. -/
@[priority 100] -- see Note [lower instance priority]
instance is_adic_complete.henselian (R : Type*)
  [comm_ring R] [local_ring R] [is_adic_complete (maximal_ideal R) R] :
  henselian R :=
begin
  constructor,
  intros f hf a₀ h₁ h₂,
  classical,
  let I := maximal_ideal R,
  let f' := f.derivative,
  -- a temporary multiplicative inverse for units in `R`
  let inv : R → R := λ x, if hx : is_unit x then ↑hx.some⁻¹ else 0,
  have hinv : ∀ x, is_unit x → x * inv x = 1,
  { intros x hx, simp only [hx, inv, dif_pos], convert units.mul_inv hx.some, rw hx.some_spec },
  -- in the following line, `f'.eval b` is a unit,
  -- because `b` has the same residue class as `a₀`
  let c : ℕ → R := λ n, nat.rec_on n a₀ (λ k b, b - f.eval b * inv (f'.eval b)),
  have hc : ∀ n, c (n+1) = c n - f.eval (c n) * inv (f'.eval (c n)),
  { intro n, dsimp only [c, nat.rec_add_one], refl, },
  -- we now spend some time determining properties of the sequence `c : ℕ → R`
  -- `hc'`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
  -- `hfc`: for every `n`, `f'.eval (c n)` is a unit
  -- `Hc` : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
  have hc' : ∀ n, c n ≡ a₀ [SMOD I],
  { intro n, induction n with n ih, { refl },
    rw [nat.succ_eq_add_one, hc, sub_eq_add_neg, ← add_zero a₀],
    refine ih.add _,
    rw [smodeq.zero, ideal.neg_mem_iff],
    refine I.mul_mem_right _ _,
    rw [← smodeq.zero] at h₁ ⊢,
    exact (ih.eval f).trans h₁, },
  have hfc : ∀ n, is_unit (f'.eval (c n)),
  { intro n, contrapose! h₂,
    rw [← mem_nonunits_iff, ← local_ring.mem_maximal_ideal, ← smodeq.zero] at h₂ ⊢,
    exact ((hc' n).symm.eval _).trans h₂, },
  have Hc : ∀ n, f.eval (c n) ∈ I ^ (n+1),
  { intro n,
    induction n with n ih, { simpa only [pow_one] },
    simp only [nat.succ_eq_add_one],
    rw [← taylor_eval_sub (c n), hc],
    simp only [sub_eq_add_neg, add_neg_cancel_comm],
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two),
      ← finset.sum_range_add_sum_Ico _ (nat.le_add_left _ _)],
    swap, { intro i, rw zero_mul },
    refine ideal.add_mem _ _ _,
    { simp only [finset.sum_range_succ, taylor_coeff_one, mul_one, pow_one, mul_neg_eq_neg_mul_symm,
        taylor_coeff_zero, finset.sum_singleton, finset.range_one, pow_zero],
      rw [mul_left_comm, hinv _ (hfc n), mul_one, add_neg_self],
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
    refine ideal.mul_mem_right _ _ (ideal.pow_le_pow _ (Hc _)),
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
    exact ideal.pow_le_pow le_self_add (Hc _), },
  { show a - a₀ ∈ maximal_ideal R,
    specialize ha 1,
    rw [hc, pow_one, ← ideal.one_eq_top, algebra.id.smul_eq_mul, mul_one, sub_eq_add_neg] at ha,
    rw [← smodeq.sub_mem, ← add_zero a₀],
    refine ha.symm.trans (smodeq.refl.add _),
    rw [smodeq.zero, ideal.neg_mem_iff],
    exact ideal.mul_mem_right _ _ h₁, }
end

/-
TODO: After a good API for etale ring homomorphisms has been developed,
we can give more equivalent characterization os Henselian rings.

In particular, this can give a proof that factorizations into coprime polynomials can be lifted
from the residue field to the Henselian ring.

The following gist contains some code sketches in that direction.
https://gist.github.com/jcommelin/47d94e4af092641017a97f7f02bf9598
-/
