/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.ideal.cotangent
import ring_theory.dedekind_domain.basic
import ring_theory.valuation.valuation_ring
import ring_theory.nakayama
/-!

# Equivalent conditions for DVR

In `discrete_valuation_ring.tfae`, we show that the following are equivalent for a
noetherian local domain `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

-/


variables (R : Type*) [comm_ring R] (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]

open_locale discrete_valuation
open local_ring

open_locale big_operators

lemma exists_maximal_ideal_pow_eq_of_principal [is_noetherian_ring R] [local_ring R] [is_domain R]
  (h : ¬ is_field R) (h' : (maximal_ideal R).is_principal) (I : ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = (maximal_ideal R) ^ n :=
begin
  classical,
  unfreezingI { obtain ⟨x, hx : _ = ideal.span _⟩ := h' },
  by_cases hI' : I = ⊤, { use 0, rw [pow_zero, hI', ideal.one_eq_top] },
  have H : ∀ r : R, ¬ (is_unit r) ↔ x ∣ r :=
    λ r, (set_like.ext_iff.mp hx r).trans ideal.mem_span_singleton,
  have : x ≠ 0,
  { rintro rfl,
    apply ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h,
    simp [hx] },
  have hx' := discrete_valuation_ring.irreducible_of_span_eq_maximal_ideal x this hx,
  have H' : ∀ r : R, r ≠ 0 → r ∈ nonunits R → ∃ (n : ℕ), associated (x ^ n) r,
  { intros r hr₁ hr₂,
    obtain ⟨f, hf₁, rfl, hf₂⟩ := (wf_dvd_monoid.not_unit_iff_exists_factors_eq r hr₁).mp hr₂,
    have : ∀ b ∈ f, associated x b,
    { intros b hb,
      exact irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1) },
    clear hr₁ hr₂ hf₁,
    induction f using multiset.induction with fa fs fh,
    { exact (hf₂ rfl).elim },
    rcases eq_or_ne fs ∅ with rfl|hf',
    { use 1,
      rw [pow_one, multiset.prod_cons, multiset.empty_eq_zero, multiset.prod_zero, mul_one],
      exact this _ (multiset.mem_cons_self _ _) },
    { obtain ⟨n, hn⟩ := fh hf' (λ b hb, this _ (multiset.mem_cons_of_mem hb)),
      use n + 1,
      rw [pow_add, multiset.prod_cons, mul_comm, pow_one],
      exact associated.mul_mul (this _ (multiset.mem_cons_self _ _)) hn } },
  have : ∃ n : ℕ, x ^ n ∈ I,
  { obtain ⟨r, hr₁, hr₂⟩ : ∃ r : R, r ∈ I ∧ r ≠ 0,
    { by_contra h, push_neg at h, apply hI, rw eq_bot_iff, exact h },
    obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximal_ideal hI' hr₁),
    use n,
    rwa [← I.unit_mul_mem_iff_mem u.is_unit, mul_comm] },
  use nat.find this,
  apply le_antisymm,
  { change ∀ s ∈ I, s ∈ _,
    by_contra hI'',
    push_neg at hI'',
    obtain ⟨s, hs₁, hs₂⟩ := hI'',
    apply hs₂,
    by_cases hs₃ : s = 0, { rw hs₃, exact zero_mem _ },
    obtain ⟨n, u, rfl⟩ := H' s hs₃ (le_maximal_ideal hI' hs₁),
    rw [mul_comm, ideal.unit_mul_mem_iff_mem _ u.is_unit] at ⊢ hs₁,
    apply ideal.pow_le_pow (nat.find_min' this hs₁),
    apply ideal.pow_mem_pow,
    exact (H _).mpr (dvd_refl _) },
  { rw [hx, ideal.span_singleton_pow, ideal.span_le, set.singleton_subset_iff],
    exact nat.find_spec this }
end

lemma maximal_ideal_is_principal_of_is_dedekind_domain
  [local_ring R] [is_domain R] [is_dedekind_domain R] : (maximal_ideal R).is_principal :=
begin
  classical,
  by_cases ne_bot : maximal_ideal R = ⊥,
  { rw ne_bot, apply_instance },
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ maximal_ideal R, a ≠ (0 : R),
  { by_contra h', push_neg at h', apply ne_bot, rwa eq_bot_iff },
  have hle : ideal.span {a} ≤ maximal_ideal R,
  { rwa [ideal.span_le, set.singleton_subset_iff] },
  have : (ideal.span {a}).radical = maximal_ideal R,
  { rw ideal.radical_eq_Inf,
    apply le_antisymm,
    { exact Inf_le ⟨hle, infer_instance⟩ },
    { refine le_Inf (λ I hI, (eq_maximal_ideal $
        is_dedekind_domain.dimension_le_one _ (λ e, ha₂ _) hI.2).ge),
      rw [← ideal.span_singleton_eq_bot, eq_bot_iff, ← e], exact hI.1 } },
  have : ∃ n, maximal_ideal R ^ n ≤ ideal.span {a},
  { rw ← this, apply ideal.exists_radical_pow_le_of_fg, exact is_noetherian.noetherian _ },
  cases hn : nat.find this,
  { have := nat.find_spec this,
    rw [hn, pow_zero, ideal.one_eq_top] at this,
    exact (ideal.is_maximal.ne_top infer_instance (eq_top_iff.mpr $ this.trans hle)).elim },
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ maximal_ideal R ^ n, ¬ b ∈ ideal.span {a},
  { by_contra h', push_neg at h', rw nat.find_eq_iff at hn,
    exact hn.2 n n.lt_succ_self (λ x hx, not_not.mp (h' x hx)) },
  have hb₃ : ∀ m ∈ maximal_ideal R, ∃ k : R, k * a = b * m,
  { intros m hm, rw ← ideal.mem_span_singleton', apply nat.find_spec this,
    rw [hn, pow_succ'], exact ideal.mul_mem_mul hb₁ hm },
  have hb₄ : b ≠ 0,
  { rintro rfl, apply hb₂, exact zero_mem _ },
  let K := fraction_ring R,
  let x : K := algebra_map R K b / algebra_map R K a,
  let M := submodule.map (algebra.of_id R K).to_linear_map (maximal_ideal R),
  have ha₃ : algebra_map R K a ≠ 0 := is_fraction_ring.to_map_eq_zero_iff.not.mpr ha₂,
  by_cases hx : ∀ y ∈ M, x * y ∈ M,
  { have := is_integral_of_smul_mem_submodule M _ _ x hx,
    { obtain ⟨y, e⟩ := is_integrally_closed.algebra_map_eq_of_integral this,
      refine (hb₂ (ideal.mem_span_singleton'.mpr ⟨y, _⟩)).elim,
      apply is_fraction_ring.injective R K,
      rw [map_mul, e, div_mul_cancel _ ha₃] },
    { rw submodule.ne_bot_iff, refine ⟨_, ⟨a, ha₁, rfl⟩, _⟩,
      exact is_fraction_ring.to_map_eq_zero_iff.not.mpr ha₂ },
    { apply submodule.fg.map, exact is_noetherian.noetherian _ } },
  { have : (M.map (distrib_mul_action.to_linear_map R K x)).comap
      (algebra.of_id R K).to_linear_map = ⊤,
    { by_contra h, apply hx,
      rintros m' ⟨m, hm, (rfl : algebra_map R K m = m')⟩,
      obtain ⟨k, hk⟩ := hb₃ m hm,
      have hk' : x * algebra_map R K m = algebra_map R K k,
      { rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel _ ha₃] },
      exact ⟨k, le_maximal_ideal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩ },
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximal_ideal R, b * y = a,
    { rw [ideal.eq_top_iff_one, submodule.mem_comap] at this,
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebra_map R K y = algebra_map R K 1⟩ := this,
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy',
      exact ⟨y, hy, is_fraction_ring.injective R K hy'⟩ },
    refine ⟨⟨y, _⟩⟩,
    apply le_antisymm,
    { intros m hm, obtain ⟨k, hk⟩ := hb₃ m hm, rw [← hy₂, mul_comm, mul_assoc] at hk,
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm], exact ideal.mem_span_singleton'.mpr ⟨_, rfl⟩ },
    { rwa [submodule.span_le, set.singleton_subset_iff] } }
end

lemma discrete_valuation_ring.tfae [is_noetherian_ring R] [local_ring R] [is_domain R]
  (h : ¬ is_field R) :
  tfae [discrete_valuation_ring R,
    valuation_ring R,
    is_dedekind_domain R,
    is_integrally_closed R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ P.is_prime,
    (maximal_ideal R).is_principal,
    finite_dimensional.finrank (residue_field R) (cotangent_space R) = 1,
    ∀ I ≠ ⊥, ∃ n : ℕ, I = (maximal_ideal R) ^ n] :=
begin
  have ne_bot := ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h,
  classical,
  rw finrank_eq_one_iff',
  tfae_have : 1 → 2,
  { introI _, apply_instance },
  tfae_have : 2 → 1,
  { introI _,
    haveI := is_bezout.to_gcd_domain R,
    haveI : unique_factorization_monoid R := ufm_of_gcd_of_wf_dvd_monoid,
    apply discrete_valuation_ring.of_ufd_of_unique_irreducible,
    { obtain ⟨x, hx₁, hx₂⟩ := ring.exists_not_is_unit_of_not_is_field h,
      obtain ⟨p, hp₁, hp₂⟩ := wf_dvd_monoid.exists_irreducible_factor hx₂ hx₁,
      exact ⟨p, hp₁⟩ },
    { exact valuation_ring.unique_irreducible } },
  tfae_have : 1 → 4,
  { introI H,
    exact ⟨infer_instance, ((discrete_valuation_ring.iff_pid_with_one_nonzero_prime R).mp H).2⟩ },
  tfae_have : 4 → 3,
  { rintros ⟨h₁, h₂⟩, exact ⟨infer_instance, λ I hI hI', unique_of_exists_unique h₂
      ⟨ne_bot, infer_instance⟩ ⟨hI, hI'⟩ ▸ maximal_ideal.is_maximal R, h₁⟩ },
  tfae_have : 3 → 5,
  { introI h, exact maximal_ideal_is_principal_of_is_dedekind_domain R },
  tfae_have : 5 → 6,
  { rintro ⟨x, hx⟩,
    have : x ∈ maximal_ideal R := by { rw hx, exact submodule.subset_span (set.mem_singleton x) },
    let x' : maximal_ideal R := ⟨x, this⟩,
    use submodule.quotient.mk x',
    split,
    { intro e,
      rw submodule.quotient.mk_eq_zero at e,
      apply ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h,
      apply submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximal_ideal R),
      { exact ⟨{x}, (finset.coe_singleton x).symm ▸ hx.symm⟩ },
      { conv_lhs { rw hx },
        rw submodule.mem_smul_top_iff at e,
        rwa [submodule.span_le, set.singleton_subset_iff] },
      { rw local_ring.jacobson_eq_maximal_ideal (⊥ : ideal R) bot_ne_top, exact le_refl _ } },
    { refine λ w, quotient.induction_on' w $ λ y, _,
      obtain ⟨y, hy⟩ := y,
      rw [hx, submodule.mem_span_singleton] at hy,
      obtain ⟨a, rfl⟩ := hy,
      exact ⟨ideal.quotient.mk _ a, rfl⟩ } },
  tfae_have : 6 → 5,
  { rintro ⟨x, hx, hx'⟩,
    induction x using quotient.induction_on',
    use x,
    apply le_antisymm,
    swap, { rw [submodule.span_le, set.singleton_subset_iff], exact x.prop },
    have h₁ : (ideal.span {x} : ideal R) ⊔ maximal_ideal R ≤
      ideal.span {x} ⊔ (maximal_ideal R) • (maximal_ideal R),
    { refine sup_le le_sup_left _,
      rintros m hm,
      obtain ⟨c, hc⟩ := hx' (submodule.quotient.mk ⟨m, hm⟩),
      induction c using quotient.induction_on',
      rw ← sub_sub_cancel (c * x) m,
      apply sub_mem _ _,
      { apply_instance },
      { refine ideal.mem_sup_left (ideal.mem_span_singleton'.mpr ⟨c, rfl⟩) },
      { have := (submodule.quotient.eq _).mp hc,
        rw [submodule.mem_smul_top_iff] at this,
        exact ideal.mem_sup_right this } },
    have h₂ : maximal_ideal R ≤ (⊥ : ideal R).jacobson,
    { rw local_ring.jacobson_eq_maximal_ideal, exacts [le_refl _, bot_ne_top] },
    have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
      (is_noetherian.noetherian _) h₂ h₁,
    rw [submodule.bot_smul, sup_bot_eq] at this,
    rw [← sup_eq_left, eq_comm],
    exact le_sup_left.antisymm (h₁.trans $ le_of_eq this) },
  tfae_have : 5 → 7,
  { exact exists_maximal_ideal_pow_eq_of_principal R h },
  tfae_have : 7 → 2,
  { rw valuation_ring.iff_ideal_total,
    intro H,
    constructor,
    intros I J,
    by_cases hI : I = ⊥, { subst hI,  left, exact bot_le },
    by_cases hJ : J = ⊥, { subst hJ, right, exact bot_le },
    obtain ⟨n, rfl⟩ := H I hI,
    obtain ⟨m, rfl⟩ := H J hJ,
    cases le_total m n with h' h',
    {  left, exact ideal.pow_le_pow h' },
    { right, exact ideal.pow_le_pow h' } },
  tfae_finish,
end
