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
theorem measurable.ennreal_induction_symm 
  {P : Π ⦃α β : Type u⦄, (α → ℝ≥0∞) → (β → ℝ≥0∞) → Prop}
  (h_symm :  Π ⦃α β : Type u⦄ ⦃M1 : measurable_space α⦄ ⦃M2 : measurable_space β⦄,
   ∀ ⦃f1 : α → ℝ≥0∞⦄ ⦃f2 : β →  ℝ≥0∞⦄ (hf1 : @measurable _ _ M1 _ f1) 
     (hf2 : @measurable _ _ M2 _ f2), P f1 f2 → P f2 f1)
  (h_ind : ∀ ⦃α β : Type u⦄ ⦃M1 : measurable_space α⦄ ⦃M2 : measurable_space β⦄
  (c1 c2 : ℝ≥0∞) ⦃s1 : set α⦄ ⦃s2 : set β⦄, M1.measurable_set' s1 → M2.measurable_set' s2 →
   P (set.indicator s1 (λ _, c1)) (set.indicator s2 (λ _, c2)))
  (h_sum : ∀ ⦃α β : Type u⦄ ⦃M1:measurable_space α⦄ ⦃M2:measurable_space β⦄
   ⦃f1 g1 : α → ℝ≥0∞⦄ ⦃f2 : β → ℝ≥0∞⦄, set.univ ⊆ f1 ⁻¹' {0} ∪ g1 ⁻¹' {0} → 
   (@measurable _ _ M1 _ f1) → (@measurable _ _ M1 _ g1) → (@measurable _ _ M2 _ f2) →
   P f1 f2 → P g1 f2 → P (f1 + g1) f2)
  (h_supr : ∀  ⦃α β : Type u⦄ ⦃M1:measurable_space α⦄ ⦃M2:measurable_space β⦄
   ⦃f1 : ℕ → α → ℝ≥0∞⦄ ⦃f2 : β → ℝ≥0∞⦄ (hf : ∀n, @measurable _ _ M1 _ (f1 n)) (h_mono : monotone f1) (hf2: @measurable _ _ M2 _ f2) 
    (hP : ∀ n, P (f1 n) (f2)), P (λ x, ⨆ n, f1 n x) (f2))
  ⦃α β : Type u⦄ ⦃M1:measurable_space α⦄ ⦃M2:measurable_space β⦄
  ⦃f1 : α → ℝ≥0∞⦄ (hf : measurable f1)  ⦃f2 : β → ℝ≥0∞⦄ (hf2 : measurable f2) : P f1 f2 :=
begin
  apply measurable.ennreal_induction,
  { intros c2 s2 h_meas_s2, 
    have h_meas_indicator:measurable (s2.indicator (λ _, c2)),
    { apply measurable.indicator measurable_const h_meas_s2,  },
    apply @measurable.ennreal_induction α M1 (λ f1, P f1 (s2.indicator (λ _, c2))),
    { intros c1 s1 h_meas_s1, apply h_ind c1 c2 h_meas_s1 h_meas_s2 },
    { intros f1 g1 h_univ h_meas_f1 h_meas_g1, apply h_sum, apply h_univ,
      apply h_meas_f1, apply h_meas_g1, apply h_meas_indicator },
    { intros f1 h_meas_f1 h_mono, apply h_supr, apply h_meas_f1,
      apply h_mono, apply h_meas_indicator },
    --{ intros s1 h_meas_s1, apply h_supr, apply h_meas_f1,
     -- apply h_mono, apply h_meas_indicator },
    apply hf,
  },
  { intros f2 g2 h_univ h_meas_f2 h_meas_g2 h_P_f2 h_P_g2,
    apply h_symm (measurable.add h_meas_f2 h_meas_g2) hf,
    apply h_sum h_univ h_meas_f2 h_meas_g2 hf,
    apply h_symm hf h_meas_f2 h_P_f2,
    apply h_symm hf h_meas_g2 h_P_g2,
      },
  { intros f2' h_meas_f2' h_mono h_P_f2',
    apply h_symm,
    apply measurable_supr h_meas_f2',
    apply hf,
    apply h_supr h_meas_f2' h_mono hf,
    intros n, apply h_symm, apply hf, apply h_meas_f2',
    apply h_P_f2' },
  apply hf2,
end

theorem measurable.ennreal_induction_symm2 
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
    --{ intros s1 h_meas_s1, apply h_supr, apply h_meas_f1,
     -- apply h_mono, apply h_meas_indicator },
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

theorem measurable.ennreal_induction_symm' {α:Type u}
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
    apply @measurable.ennreal_induction_symm2 Q' _ P',
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


theorem measurable.ennreal_induction_symm'' {α : Type u} [M : measurable_space α]
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
    apply @measurable.ennreal_induction_symm' α Q _ P,
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
  (λ a, (t1.indicator (λ (x : α), c1) * t2.indicator (λ (x : α), c2)) a) =
      (λ a, (t1 ∩ t2).indicator (λ (x : α), c1 * c2) a) := begin
  simp only [zero_mul, pi.mul_apply, ite_mul, mul_ite, mul_zero],
  repeat {rw ← set.indicator}, rw [set.indicator_indicator, set.inter_comm],
end


namespace measure_theory
open measure_theory measure_theory.simple_func

/-- This (roughly) proves that if a random variable `f` is independent of an event `T`,
   then if you restrict the random variable to `T`, then
   `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
   `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space`. -/
lemma lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
  {α : Type*} {Mf : measurable_space α} [M : measurable_space α] {μ : measure α} 
  (hMf : Mf ≤ M) (c : ℝ≥0∞) {T : set α} (h_meas_T : M.measurable_set' T)
  (h_ind : indep_sets Mf.measurable_set' {T} μ )
  {f : α → ℝ≥0∞} (h_meas_f : @measurable α ℝ≥0∞ Mf _ f):
   ∫⁻ a, (f * (T.indicator (λ (x : α), c))) a ∂μ =
  ∫⁻ a, f a ∂μ *
  ∫⁻ a, (T.indicator (λ (x : α), c)) a ∂μ :=
begin
  revert f,
  have h_mul_indicator : ∀ g, @measurable α ℝ≥0∞ M _ g →
    @measurable α ℝ≥0∞ M _ (g * (λ (a : α), T.indicator (λ (_x : α), c) a)) :=
  (λ g h_mg, measurable.ennreal_mul h_mg (measurable.indicator measurable_const h_meas_T)),
  apply measurable.ennreal_induction,
  { intros c' s' h_meas_s',
    rw [set.indicator_mul_indicator_eq_inter, lintegral_indicator _
        (measurable_set.inter (hMf _ h_meas_s') (h_meas_T)),
        lintegral_indicator _  (hMf _ h_meas_s'),
        lintegral_indicator _ h_meas_T],
    simp only [measurable_const, lintegral_const, set.univ_inter, lintegral_const_mul,
        measurable_set.univ, measure.restrict_apply],
    rw h_ind, ring, apply h_meas_s', simp },
  { intros f' g h_univ h_meas_f' h_meas_g h_ind_f' h_ind_g,
    have h_measM_f' := measurable.mono h_meas_f' hMf (le_refl _),
    have h_measM_g := measurable.mono h_meas_g hMf (le_refl _),
    have h_indicator : @measurable α ℝ≥0∞ M _ (λ (a : α), T.indicator (λ (_x : α), c) a),
    { apply measurable.indicator (measurable_const) h_meas_T },
    have h8 : (f' + g) * T.indicator (λ (x : α), c) =
             (λ a, (f' * (T.indicator (λ _, c))) a + (g * (T.indicator (λ _, c))) a),
    { ext1 a, simp [right_distrib] },
    rw h8,
    have h_add : (f' + g) = (λ a, (f' a + g a)),
   { refl },
   rw [h_add, lintegral_add (h_mul_indicator _ h_measM_f')
       (h_mul_indicator _ h_measM_g),
       lintegral_add h_measM_f' h_measM_g, right_distrib, h_ind_f',
       h_ind_g] },
  { intros f h_meas_f h_mono_f h_ind_f,
    have h_measM_f := (λ n, measurable.mono (h_meas_f n) hMf (le_refl _)),
    have h_mul : (λ a, ((λ (x : α), ⨆ (n : ℕ), f n x) * T.indicator (λ (x : α), c)) a) =
      (λ (a : α), ⨆ (n : ℕ), (λ (x : α), f n x * (T.indicator (λ (x : α), c) x)) a),
    { ext1 a, rw @pi.mul_apply, rw ennreal.supr_mul, },
    have h_mul2 : (λ n, ∫⁻ x, f n x * T.indicator (λ (x : α), c) x ∂μ)  =
        (λ n, (∫⁻ x, (f n x) ∂μ) * (∫⁻ x, T.indicator (λ (x : α), c) x ∂μ)),
    { ext1 n, rw ← h_ind_f n, refl },
    rw [h_mul, lintegral_supr h_measM_f h_mono_f, lintegral_supr, ennreal.supr_mul, h_mul2],
    { apply (λ n, h_mul_indicator _ (h_measM_f n)) },
    { intros m n h_le a, apply ennreal.mul_le_mul _ (le_refl _), apply h_mono_f h_le } },
end

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
  revert g,
  have h_meas_Mg : ∀ ⦃f : α → ℝ≥0∞⦄, (@measurable α ℝ≥0∞ Mg _ f) → (measurable f),
  { intros f' h_meas_f', apply measurable.mono h_meas_f' hMg (le_refl _) },
  have h_measM_f := measurable.mono h_meas_f hMf (le_refl _),
  apply measurable.ennreal_induction,
  { intros c s h_s,
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator 
       hMf _ (hMg _ h_s) _ h_meas_f,
    apply probability_theory.indep_sets_of_indep_sets_of_le_right h_ind,
    rw singleton_subset_iff, apply h_s },
  { intros f' g h_univ h_measMg_f' h_measMg_g h_ind_f' h_ind_g',
    have h_measM_f' := h_meas_Mg h_measMg_f',
    have h_measM_g := h_meas_Mg h_measMg_g,
    have h_add : (f' + g) = (λ a, (f' a + g a)) := rfl,
    have h8 : (λ a, (f * λ a', (f' a' + g a')) a ) = (λ a, (f a * f' a) + (f a * g a)),
    { ext1 a, simp [left_distrib] },
    have h9 : (λ a, (f * f') a) = (λ a, f a * f' a),
    { ext1 a, refl },
    have h10 : (λ a, (f * g) a) = (λ a, f a * g a),
    { ext1 a, refl },
    rw [h_add, lintegral_add h_measM_f' h_measM_g, h8,
        lintegral_add (measurable.ennreal_mul h_measM_f h_measM_f')
          (measurable.ennreal_mul h_measM_f h_measM_g),
        left_distrib, ← h9, h_ind_f', ← h10, h_ind_g'] },
  { intros f' h_meas_f' h_mono_f' h_ind_f',
    have h_measM_f' := (λ n, h_meas_Mg (h_meas_f' n)),
    have h_mul : (λ (a : α), (f * λ (x : α), ⨆ (n : ℕ), f' n x) a) =
      (λ (a : α), ⨆ (n : ℕ), (λ (x:α), (f x * f' n x)) a),
    { ext1 a, simp only [pi.mul_apply], rw ennreal.mul_supr },
    have h_mul2 : (λ (n:ℕ), ∫⁻ (x : α), f x * f' n x ∂μ) =
        (λ n, (∫⁻ x, f x ∂μ) * ∫⁻ x, f' n x ∂μ),
    { ext1 n, rw ← h_ind_f' n, refl },
    rw [h_mul, lintegral_supr,
        lintegral_supr h_measM_f' h_mono_f', ennreal.mul_supr, h_mul2],
    { apply (λ (n : ℕ), measurable.ennreal_mul h_measM_f (h_measM_f' n)) }, 
    { apply (λ (n : ℕ) (m : ℕ) (h_le : n ≤ m) a, ennreal.mul_le_mul (le_refl _)
      (h_mono_f' h_le a)) } }
end

/-- This proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. Note that this will only apply to probability
   measures, because `μ (f ⁻¹' univ) * μ (g ⁻¹' univ) = μ ((f ⁻¹' univ) ∩ (g ⁻¹' univ)))`
   implies μ univ * μ univ = μ univ, i.e. μ univ = 1. -/
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
