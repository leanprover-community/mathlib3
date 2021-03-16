import ring_theory.polynomial.symmetric
import ring_theory.polynomial.homogeneous
import data.mv_polynomial.basic
import data.multiset.basic

noncomputable theory

open fintype classical
open_locale big_operators

namespace mv_polynomial
variables {σ : Type*} [fintype σ]  {R : Type*} [comm_semiring R]

instance [nontrivial R] : nontrivial (mv_polynomial σ R) := add_monoid_algebra.nontrivial

lemma is_homogeneous_esymm (n : ℕ) : (esymm σ R n).is_homogeneous n :=
begin
  rw esymm,
  refine is_homogeneous.sum _ _ _ (λ t H, _),
  have : ∑ i in t, 1 = n, { simp [(finset.mem_powerset_len.mp H).2], },
  rw ← this,
  refine is_homogeneous.prod _ _ _ (λ i hi, is_homogeneous_X R i),
end

lemma support_sum {ι : Type*} [fintype ι] [decidable_eq σ] (f : ι → mv_polynomial σ R) :
  (∑ i, f i).support ⊆ finset.bUnion (finset.univ) (λ i, (f i).support) :=
begin
  sorry --convert @finsupp.support_sum _ _ _ (mv_polynomial σ R) _ _,
end

lemma support_esymm (n : ℕ) [decidable_eq σ] :
  (esymm σ R n).support = (finset.powerset_len n (finset.univ : finset σ)).image (λ t, ∑ i in t, finsupp.single i 1) :=
by sorry

lemma degrees_esymm (n : ℕ) [decidable_eq σ] : (esymm σ R n).degrees = (finset.univ : finset σ).val :=
begin
  simp only [degrees, support_esymm],
  convert ← finset.sup_finset_image,
  -- mismatching instances.
  sorry
end

lemma esymm_ne_zero (n : ℕ) (h : n ≤ card σ) [nontrivial R] : esymm σ R n ≠ 0 :=
begin
  induction n with n ih,
  simp,
  sorry,

end

end mv_polynomial
