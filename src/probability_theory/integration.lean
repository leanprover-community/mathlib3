/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import measure_theory.measure_space
import measure_theory.borel_space
import data.indicator_function
import data.support
import measure_theory.integration
import probability_theory.independence
import tactic.split_ifs

/-!
  Integration results for independent random variables. Specifically, for two
  independent random variables X and Y over the extended non-negative
  reals, E[X * Y] = E[X] * E[Y], and similar results.
-/

noncomputable theory
open set (hiding restrict restrict_apply) filter ennreal probability_theory
open_locale classical topological_space big_operators nnreal ennreal

#check 42
namespace measurable
open measure_theory
open measure_theory.simple_func
universe u
/- A way to prove symmetric properties over ennreal measurable functions by induction.
   Many properties we want to prove are obviously symmetric. For example,
   lintegral μ (f + g) = (lintegral μ f) + (integral μ g) if and only if
     lintegral μ (g + f) = (lintegral μ g) + (integral μ f).
   Or:
   lintegral μ (f * g) = (lintegral μ f) * (integral μ g) if and only if
     lintegral μ (g * f) = (lintegral μ g) * (integral μ f).
   A straightforward application of measurable.ennreal_induction would be:
   Prove something via ennreal_induction on g.
   1. For the base case, use ennreal_induction on f.
   1A. Prove the true base case, where f and g are indicator functions.
   1B. Prove the sum case, where f is the sum of two functions, and
       g is an indicator function.
   1C. Prove the supremum case, where f is the supremum of a sequence of functions, and
       g is an indicator function.
   2. Prove the sum case, where f is a function and g is the sum of two functions.
   3. Prove the supremum case, where f is a function, and g is the supremum of a 
      sequence of functions.

   Notice that, if the property is symmetric, then 1B is a special case of 2, and
   1C is a special case of 3.

   Thus, instead, this theorem allows us to use the symmetric properties of
   our goal and prove 1A, 2, and 3, and let the result follow.

   There are three variants of this proof. In the first variant, the two functions
   can have different domains. In the second variant, the two functions have the 
   same domains, but are measurable according to different functions (useful for
   independent random variables). In the third variant, the functions have the
   same domains and measurability (could be used for lintegral_add).

   In the first two variants, we allow for constraints on the types and
   measurable spaces. These have to be symmetric too. For example, the integral of the
   product equals the product of the integral if the measurable spaces are
   independent. -/ 
theorem ennreal_induction_symm 
  {Q : Π ⦃α β : Type u⦄, (measurable_space α) → (measurable_space β) → Prop}
  (Q_symm : Π ⦃α β: Type u⦄  ⦃M1 : measurable_space α⦄ ⦃M2 : measurable_space β⦄,
   Q M1 M2 → Q M2 M1)
  {P : Π ⦃α β : Type u⦄, (α → ℝ≥0∞) → (β → ℝ≥0∞) → Prop}
  (h_symm :  Π ⦃α β : Type u⦄ ⦃M1 : measurable_space α⦄ ⦃M2 : measurable_space β⦄
    (hQ : Q M1 M2), ∀ ⦃f1 : α → ℝ≥0∞⦄ ⦃f2 : β →  ℝ≥0∞⦄ (hf1 : @measurable _ _ M1 _ f1) 
     (hf2 : @measurable _ _ M2 _ f2), P f1 f2 → P f2 f1)
  (h_ind : ∀ ⦃α β : Type u⦄ ⦃M1 : measurable_space α⦄ ⦃M2 : measurable_space β⦄ (hQ : Q M1 M2) 
  (c1 c2 : ℝ≥0∞) ⦃s1 : set α⦄ ⦃s2 : set β⦄, M1.measurable_set' s1 → M2.measurable_set' s2 →
   P (set.indicator s1 (λ _, c1)) (set.indicator s2 (λ _, c2)))
  (h_sum : ∀ ⦃α β : Type u⦄ ⦃M1:measurable_space α⦄ ⦃M2:measurable_space β⦄ (hQ : Q M1 M2)
   ⦃f1 g1 : α → ℝ≥0∞⦄ ⦃f2 : β → ℝ≥0∞⦄, set.univ ⊆ f1 ⁻¹' {0} ∪ g1 ⁻¹' {0} → 
   (@measurable _ _ M1 _ f1) → (@measurable _ _ M1 _ g1) → (@measurable _ _ M2 _ f2) →
   P f1 f2 → P g1 f2 → P (f1 + g1) f2)
  (h_supr : ∀  ⦃α β : Type u⦄ ⦃M1:measurable_space α⦄ ⦃M2:measurable_space β⦄ (hQ : Q M1 M2)
   ⦃f1 : ℕ → α → ℝ≥0∞⦄ ⦃f2 : β → ℝ≥0∞⦄ (hf : ∀n, @measurable _ _ M1 _ (f1 n)) (h_mono : monotone f1) (hf2: @measurable _ _ M2 _ f2) 
    (hP : ∀ n, P (f1 n) (f2)), P (λ x, ⨆ n, f1 n x) (f2))
  ⦃α β : Type u⦄ ⦃M1:measurable_space α⦄ ⦃M2:measurable_space β⦄ (hQ : Q M1 M2)
  ⦃f1 : α → ℝ≥0∞⦄ (hf : measurable f1)  ⦃f2 : β → ℝ≥0∞⦄ (hf2 : measurable f2) : P f1 f2 :=
begin
  have hQ' : Q M2 M1 := Q_symm hQ,
  apply measurable.ennreal_induction,
  { intros c2 s2 h_meas_s2, 
    have h_meas_indicator:measurable (s2.indicator (λ _, c2)),
    { apply measurable.indicator measurable_const h_meas_s2,  },
    apply @measurable.ennreal_induction α M1 (λ f1, P f1 (s2.indicator (λ _, c2))),
    { intros c1 s1 h_meas_s1, apply h_ind hQ c1 c2 h_meas_s1 h_meas_s2 },
    { intros f1 g1 h_univ h_meas_f1 h_meas_g1, apply h_sum hQ, apply h_univ,
      apply h_meas_f1, apply h_meas_g1, apply h_meas_indicator },
    { intros f1 h_meas_f1 h_mono, apply h_supr hQ, apply h_meas_f1,
      apply h_mono, apply h_meas_indicator },
    apply hf,
  },
  { intros f2 g2 h_univ h_meas_f2 h_meas_g2 h_P_f2 h_P_g2,
    apply h_symm hQ' (measurable.add h_meas_f2 h_meas_g2) hf,
    apply h_sum hQ' h_univ h_meas_f2 h_meas_g2 hf,
    apply h_symm hQ hf h_meas_f2 h_P_f2,
    apply h_symm hQ hf h_meas_g2 h_P_g2,
      },
  { intros f2' h_meas_f2' h_mono h_P_f2',
    apply h_symm hQ',
    apply measurable_supr h_meas_f2',
    apply hf,
    apply h_supr hQ' h_meas_f2' h_mono hf,
    intros n, apply h_symm hQ, apply hf, apply h_meas_f2',
    apply h_P_f2' },
  apply hf2,
end

theorem ennreal_induction_symm' {α:Type u}
  {Q : (measurable_space α) → (measurable_space α) → Prop}
  (h_symmQ : ∀ ⦃M1 M2 : measurable_space α⦄, Q M1 M2 → Q M2 M1)
  {P : (α → ℝ≥0∞) → (α → ℝ≥0∞) → Prop}
  (h_symm :  Π  ⦃M1 M2 : measurable_space α⦄, Q M1 M2 →
   ∀ ⦃f1 : α → ℝ≥0∞⦄ ⦃f2 : α →  ℝ≥0∞⦄ (hf1 : @measurable _ _ M1 _ f1) 
     (hf2 : @measurable _ _ M2 _ f2), P f1 f2 → P f2 f1)
  (h_ind : ∀  ⦃M1 M2 : measurable_space α⦄ (hQ: Q M1 M2)
  (c1 c2 : ℝ≥0∞) ⦃s1 : set α⦄ ⦃s2 : set α⦄, M1.measurable_set' s1 → M2.measurable_set' s2 →
   P (set.indicator s1 (λ _, c1)) (set.indicator s2 (λ _, c2)))
  (h_sum : ∀  ⦃M1 M2:measurable_space α⦄ (hQ : Q M1 M2)
   ⦃f1 g1 : α → ℝ≥0∞⦄ ⦃f2 : α → ℝ≥0∞⦄, set.univ ⊆ f1 ⁻¹' {0} ∪ g1 ⁻¹' {0} → 
   (@measurable _ _ M1 _ f1) → (@measurable _ _ M1 _ g1) → (@measurable _ _ M2 _ f2) →
   P f1 f2 → P g1 f2 → P (f1 + g1) f2)
  (h_supr : ∀   ⦃M1 M2:measurable_space α⦄ (hQ : Q M1 M2)
   ⦃f1 : ℕ → α → ℝ≥0∞⦄ ⦃f2 : α → ℝ≥0∞⦄ (hf : ∀n, @measurable _ _ M1 _ (f1 n)) (h_mono : monotone f1) (hf2: @measurable _ _ M2 _ f2) 
    (hP : ∀ n, P (f1 n) (f2)), P (λ x, ⨆ n, f1 n x) (f2))
   ⦃M1 M2:measurable_space α⦄ (hQ: Q M1 M2)
  ⦃f1 : α → ℝ≥0∞⦄ (hf :  @measurable _ _ M1 _ f1)  ⦃f2 : α → ℝ≥0∞⦄ (hf2 : @measurable _ _ M2 _ f2) : P f1 f2 :=
begin
  -- This may be easier to prove directly.
  let Q' : Π  ⦃α β : Type u⦄, (measurable_space α) → (measurable_space β) → Prop :=
    (λ α' β M1 M2, α' = α ∧ β = α ∧ Π (h:α' = α) (h2:β = α), Q (cast begin rw h end M1) (cast begin rw h2 end M2)),
  let P' : Π  ⦃α β : Type u⦄,  (α → ℝ≥0∞) → (β → ℝ≥0∞) → Prop :=
    (λ α' β f1 f2, α' = α ∧ β = α ∧ Π (h:α' = α) (h2:β = α), P (cast begin rw h end f1) (cast begin rw h2 end f2)),
  begin
    have h1: ∀ ⦃f1' f2'⦄, P' f1' f2' → P f1' f2',
    { intros f1' f2' h1', apply h1'.right.right, refl, refl },
    have h2: ∀ ⦃f1' f2'⦄, Q' f1' f2' → Q f1' f2',
    { intros f1' f2' h1', apply h1'.right.right, refl, refl },
    apply h1,
    apply @ennreal_induction_symm Q' _ P',
    { intros α' β M1' M2' hQ' hf1 hf2 h_meas1 h_meas2 hP',
      split, apply hP'.right.left,
      split, apply hP'.left,
      intros h1 h2,
      subst α', subst β,
      apply h_symm (h2 hQ') h_meas1 h_meas2 (h1 hP') },
   { intros α' β M1 M2 hQ' c1 c2 s1 s2 h_meas_s1 h_meas_s2,
     split,
     apply hQ'.left,
     split,
     apply hQ'.right.left,
     intros h1 h2,
     subst α', subst β,
     apply h_ind (h2 hQ') _ _ h_meas_s1 h_meas_s2 },
   { intros α' β M1 M2 hQ' f1 g1 f2 h_univ h_meas_f1 h_meas_g1 h_meas_f2 h_P'_f1_f2
     h_P'_g1_f2,
     split,
     apply hQ'.left,
     split,
     apply hQ'.right.left,
     intros h1 h2,
     subst α', subst β,
     apply h_sum (h2 hQ') h_univ h_meas_f1 h_meas_g1 h_meas_f2,
     apply (h1 h_P'_f1_f2),
     apply (h1 h_P'_g1_f2),
   },
  { intros α' β M1 M2 hQ' f1 f2 h_meas_f1 h_mono_f1 h_meas_f2 h_P'_f1_f2,
    split,
    apply hQ'.left,
    split,
    apply hQ'.right.left,
    intros h h2,
    subst α', subst β,
    apply h_supr (h2 hQ') h_meas_f1 h_mono_f1 h_meas_f2 (λ n, h1 (h_P'_f1_f2 n)),
   },
   split,
   refl,
   split,
   refl,
   intros α' β,
   apply hQ,
   apply hf,
   apply hf2,
   intros α' β M1' M2' hQ',
   { split, apply hQ'.right.left, split,
     apply hQ'.left, intros h h2, subst α', subst β,
     apply h_symmQ (h2 hQ') },
  end
end


theorem ennreal_induction_symm'' {α : Type u} [M : measurable_space α]
  {P : (α → ℝ≥0∞) → (α → ℝ≥0∞) → Prop}
  (h_symm : ∀ ⦃f1 f2 : α →  ℝ≥0∞⦄ (hf1 : measurable f1) 
    (hf2 : measurable f2), P f1 f2 → P f2 f1)
  (h_ind : ∀ (c1 c2 : ℝ≥0∞) ⦃s1 s2:set α⦄, measurable_set s1 → measurable_set s2 →
    P (set.indicator s1 (λ _, c1)) (set.indicator s2 (λ _, c2)))
  (h_sum : ∀ ⦃f1 g1 f2 : α → ℝ≥0∞⦄, set.univ ⊆ f1 ⁻¹' {0} ∪ g1 ⁻¹' {0} → 
    (measurable f1) → (measurable g1) → (measurable f2) →
    P f1 f2 → P g1 f2 → P (f1 + g1) f2)
  (h_supr : ∀ ⦃f1 : ℕ → α → ℝ≥0∞⦄ ⦃f2 : α → ℝ≥0∞⦄ (hf : ∀n, measurable (f1 n))
    (h_mono : monotone f1) (hf2: measurable f2) 
    (hP : ∀ n, P (f1 n) (f2)), P (λ x, ⨆ n, f1 n x) (f2))
  ⦃f1 : α → ℝ≥0∞⦄ (hf : measurable f1)  ⦃f2 : α → ℝ≥0∞⦄ (hf2 : measurable f2) : P f1 f2 :=
begin
  let Q := (λ  (M1 M2 : measurable_space α), M1 = M ∧ M2 = M),
  begin
    apply @ennreal_induction_symm' α Q _ P,
    { intros M1 M2 hQ, cases hQ, substs M1 M2, apply h_symm },
    { intros M1 M2 hQ, cases hQ, substs M1 M2, apply h_ind },
    { intros M1 M2 hQ, cases hQ, substs M1 M2, apply h_sum },
    { intros M1 M2 hQ, cases hQ, substs M1 M2, apply h_supr },
    { split; refl },
    { apply hf },
    { apply hf2 },
    { intros M1 M2 hQ, cases hQ, substs M1 M2, split; refl },
  end
end

end measurable

lemma set.indicator_mul_indicator_eq_inter {α:Type*} {t1 t2:set α} {c1 c2:ennreal}:
  (t1.indicator (λ (x : α), c1) * t2.indicator (λ (x : α), c2)) =
       (t1 ∩ t2).indicator (λ (x : α), c1 * c2) := begin
  funext a,
  simp only [zero_mul, pi.mul_apply, ite_mul, mul_ite, mul_zero, set.indicator],
  split_ifs;
  try { refl }; exfalso,
  { simp at h_2, apply h_2 h_1 h },
  { simp at h_2, apply h_1 h_2.left },
  { simp at h_1, apply h h_1.right },
end


namespace measure_theory
open measure_theory measure_theory.simple_func



/-- This (roughly) proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn` for
   a more common variant of the product of independent variables. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  {α : Type*} {Mf : measurable_space α} {Mg : measurable_space α} [M : measurable_space α]
  {μ : measure α} (hMf : Mf ≤ M) (hMg : Mg ≤ M)
  (h_ind : indep Mf Mg μ)
  (f g : α → ℝ≥0∞) (h_meas_f : @measurable α ℝ≥0∞ Mf _ f)
  (h_meas_g : @measurable α ℝ≥0∞ Mg _ g):
  ∫⁻ a, (f * g) a ∂μ = (∫⁻ a, f a ∂μ) * (∫⁻ a, g a ∂μ) :=
begin
  let Q := (λ (Mf Mg : measurable_space α), Mf ≤ M ∧ Mg ≤ M ∧ @indep α Mf Mg M μ),
  let P := (λ (f g  : α → ℝ≥0∞),   ∫⁻ a, (f * g) a ∂μ = (∫⁻ a, f a ∂μ) * (∫⁻ a, g a ∂μ)),
  begin
    have hP_apply : ∀ ⦃f1 f2⦄,
      (P f1 f2 → ∫⁻ a, (f1 a) * (f2 a) ∂μ = (∫⁻ a, f1 a ∂μ) * (∫⁻ a, f2 a ∂μ)),
    { intros f1  f2, intros hP, simp only [P] at hP, apply hP },
    have hP : P f g,
    { apply @measurable.ennreal_induction_symm' _ Q _ P _ _ _ _ _ _ 
      (and.intro hMf (and.intro hMg h_ind)) _ h_meas_f _ h_meas_g,
      { -- Independence of measurable spaces is symmetric.
        apply (λ M1 M2 (hQ : Q M1 M2), and.intro hQ.right.left (and.intro hQ.left 
        hQ.right.right.symm )) },
      { -- The goal is symmetric.
        intros M1 M2 hQ f1 f2 h_meas_f1 h_meas_f2 h_P_f1_f2,
        simp only [P],
        rw [mul_comm f2 f1, mul_comm (lintegral μ f2)], 
        apply h_P_f1_f2 },
      { -- Base case: the property holds for two indicator functions. Want to prove:
        -- lintegral μ (s1.indicator c1) * s2.indicator c2)) =
        --   lintegral μ (s1.indicator c1)) * lintegral μ (s2.indicator (λ (_x : α), c2))
        -- c1 * c2 * μ (s1 ∩ s2) = c1 * μ s1 * c2 * μ s2
        -- The rest follows from the independence of s1 and s2.
        intros M1 M2 hQ c1 c2 s1 s2 h_meas_s1 h_meas_s2,
        simp only [P],
        rw [@set.indicator_mul_indicator_eq_inter],
        rw [lintegral_indicator, lintegral_indicator, lintegral_indicator],
        simp,
        rw hQ.right.right,
        ring,
        apply h_meas_s1, apply h_meas_s2,
        apply hQ.right.left _ h_meas_s2, apply hQ.left _ h_meas_s1,
        apply measurable_set.inter (hQ.left _ h_meas_s1) (hQ.right.left _ h_meas_s2) },
      { -- inductive case over sum. Want to prove:
        -- lintegral μ ((f1 + g1) * f2) = lintegral μ (f1 + g1) * lintegral μ f2
        -- Using right_distrib and lintegral_add, can rewrite as:
        -- lintegral μ (f1 * f2) * lintegral μ (f1 * f2) = 
        --   lintegral μ f1 * lintegral μ f2 = lintegral μ g1 * lintegral μ f2
        -- The rest follows by induction.
        intros M1 M2 hQ f1 g1 f2 h_univ h_meas_f1 h_meas_g1 h_meas_f2 h_P_f1_f2
          h_P_g1_f2,
        have h_measM_f1 := measurable.mono h_meas_f1 hQ.left (le_refl _),
        have h_measM_g1 := measurable.mono h_meas_g1 hQ.left (le_refl _),
        have h_measM_f2 := measurable.mono h_meas_f2 hQ.right.left (le_refl _),
        simp only [P],
        have h2 : (f1 + g1) * f2 = (λ a, (λ a', f1 a' * f2 a') a + (λ a', g1 a' * f2 a') a),
        { ext1 a, rw right_distrib, refl },
        have h3 : (f1 + g1)  = (λ a, f1 a + g1 a),
        { refl },
        rw [h2, lintegral_add (measurable.ennreal_mul h_measM_f1 h_measM_f2)
            (measurable.ennreal_mul h_measM_g1 h_measM_f2), h3, 
            lintegral_add h_measM_f1 h_measM_g1, hP_apply h_P_f1_f2, hP_apply h_P_g1_f2,
            right_distrib] },
      { -- inductive case over supremum. Want to prove:
        -- lintegral μ ((λ x, ⨆ n, f1 n x) * f2) =
        --   lintegral μ (λ x, ⨆ n, f1 n x) * lintegral μ f2
        -- By ennreal.supr_mul and lintegral_supr, can rewrite as:
        -- (⨆ (n : ℕ), lintegral μ (f1 n * f2) =
        --   lintegral μ (λ x, ⨆ (n : ℕ), f1 n x) * lintegral μ f2
        -- We can apply induction to rewrite as:
        -- (⨆ (n : ℕ), lintegral μ (f1 n) * lintegral μ f2) =
        --   lintegral μ (λ x, ⨆ (n : ℕ), f1 n x) * lintegral μ f2
        -- Using ennreal.supr_mul and lintegral_supr again completes the proof.
        intros M1 M2 hQ f1 f2 h_meas_f1 h_mono_f1 h_meas_f2 h_P_f1_f2,
        have h_measM_f1 := λ n, measurable.mono (h_meas_f1 n) hQ.left (le_refl _),
        have h_measM_f2 := measurable.mono h_meas_f2 hQ.right.left (le_refl _),
        simp only [P],
        have h_mul : ((λ (x : α), ⨆ (n : ℕ), f1 n x) * f2) =
          (λ (a : α), ⨆ (n : ℕ), (λ (x:α), f1 n x * f2 x) a),
        { ext1 a, simp only [pi.mul_apply], rw ennreal.supr_mul },
        have h_mul2 : (λ (n : ℕ), ∫⁻ (x : α), f1 n x * f2 x ∂μ) =
          (λ n, (∫⁻ x, f1 n x ∂μ) *  ∫⁻ x, f2 x ∂μ),
        { ext1 n, simp only [P] at h_P_f1_f2, rw ← h_P_f1_f2 n, refl },
        rw [h_mul, lintegral_supr,
            lintegral_supr h_measM_f1 h_mono_f1, ennreal.supr_mul, h_mul2],
        { apply (λ (n : ℕ), measurable.ennreal_mul (h_measM_f1 n) h_measM_f2) }, 
        { apply (λ (n : ℕ) (m : ℕ) (h_le : n ≤ m) a, ennreal.mul_le_mul 
          (h_mono_f1 h_le a) (le_refl _)) } } },
    apply hP,
  end
end

/-- This proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun {α : Type*} [M : measurable_space α]
  (μ : measure α) (f g : α → ℝ≥0∞) (h_meas_f : measurable f) (h_meas_g : measurable g)
  (h_indep_fun : indep_fun (borel ennreal) (borel ennreal) f g μ):
  ∫⁻ (a : α), (f * g) a ∂μ = (∫⁻ (a : α), f a ∂μ) * (∫⁻ (a : α), g a ∂μ) :=
begin
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g),
  apply h_indep_fun,
  repeat { apply measurable.of_comap_le (le_refl _) },
end

end measure_theory
