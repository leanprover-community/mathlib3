/-
Copyright (c) 2022 Ian Jauslin and Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Jauslin, Alex Kontorovich
-/

import measure_theory.measure.probability_measure

/-!
# Bell's Inequality

This file proves Bell's Inequality as a probabilitstic statement in several
forms. (TODO: Add other forms.)

A star-algebra version of Bell's inequality has already been proved in
  `algebra.star.chsh.CHSH_inequality_of_comm`
Here, the inequality is formulated in terms of probabilities.

Bell's inequality is the cornerstone of Bell's theorem, which states that
quantum mechanics is a non-local theory. The proof of Bell's theorem,
established by J.S. Bell in 1964, first uses the Einstein-Podolsky-Rosen
argument to establish that either quantum mechanics is non-local, or all
quantum observables simultaneously have values (in other words, quantum
mechanics is a non-contextual hidden variable theory). Bell's inequality is a
necessary condition for all the observables in an abstract probabilistic theory
to simultaneously have values. By showing that, in quantum mechanics, Bell's
inequality is violated, Bell proved that quantum mechanics is non-local.

The violation of Bell's inequality has also been verified experimentally in
many different setups.


## Bell's 1964 inequality

We first prove Bell's original statement of the inequality, which was published
in 1964, and will thus be called `bells_inequality_1964` in this file.

Consider two observers, A and B, performing measurements that take values in
{-1,+1}.

Let `ℙ` be a probability measure, and let `Za i` and `Zb i` for i∈{1,2,3} be
random variables taking values in {-1,+1}. For convenience, we identify {-1,+1}
with ℤˣ. `Za i` represent the outcomes of measurements done by A, and `Zb i`
those done by B. We assume perfect anticorrelation between the outcomes of A
and B: 𝔼[(Za i) (Zb i)] = -1. Bell's inequality states that
  `𝔼[(Za 1) (Zb 2)] - 𝔼[(Za 1) (Zb 2)] ≤ 1 + 𝔼[(Za 2) (Zb 3)]`.


## Future work

J.S. Bell generalized the inequality in 1975 to include more probabilistic
theories. In particular, the 1975 statement does not require observables to
simultaneously have values. Instead, it is solely based on the requirement of
locality. The 1975 inequality thus gives a more direct proof of Bell's theorem.


## References

* [J.S. Bell, *On the Einstein Podolsky Rosen Paradox*, 1964][MR3790629]

* [J.S. Bell, *The theory of local beables*, 1975,
  reproduced in chapter 7 of *Speakable and unspeakable in quantum mechanics*][MR915338]



-/

noncomputable theory

open measure_theory

section preliminaries

lemma pm_one_space_vals (r : ℤˣ) :
  (r : ℝ) = 1 ∨ (r : ℝ) = -1 := by cases int.units_eq_one_or r with hh hh; rw hh; simp

lemma pm_one_space_abs_le (r : ℤˣ) :
  |(r : ℝ)| ≤ 1 := by cases int.units_eq_one_or r with hh hh; rw hh; simp

/-- The CHSH inequality in `ℤˣ`. -/
lemma CHSH_inequality_of_int_units (A₀ A₁ B₀ B₁ : ℤˣ) :
  (A₀ : ℝ) * B₀ + A₀ * B₁ + A₁ * B₀ + (-A₁) * B₁ + -2 ≤ 0 :=
  by cases pm_one_space_vals A₀ with hA0 hA0;
    cases pm_one_space_vals A₁ with hA1 hA1;
    cases pm_one_space_vals B₀ with hB0 hB0;
    cases pm_one_space_vals B₁ with hB1 hB1;
    rw [hA0, hA1, hB0, hB1]; ring_nf; simp

end preliminaries

variables {Ω : Type*} [measurable_space Ω] (ℙ : probability_measure Ω)

lemma integrable_mul_of_units_int {Za Zb : Ω → ℤˣ} (sm_a : strongly_measurable (λ ω, (Za ω : ℝ)))
  (sm_b : strongly_measurable (λ ω, (Zb ω : ℝ))) :
  integrable (λ ω, (Za ω : ℝ) * Zb ω) (ℙ : measure Ω) :=
begin
  refine ⟨strongly_measurable.ae_strongly_measurable (strongly_measurable.mul sm_a sm_b), _⟩,
  refine @has_finite_integral_of_bounded _ _ _ _ _ _ _ (1 : ℝ) _,
  filter_upwards with x,
  convert pm_one_space_abs_le (Za x * Zb x),
  simp,
end

lemma integrable_mul_of_units_int_neg {Za Zb : Ω → ℤˣ}
  (sm_a : strongly_measurable (λ ω, (Za ω : ℝ)))
  (sm_b : strongly_measurable (λ ω, (Zb ω : ℝ))) :
  integrable (λ ω : Ω , -(Za ω :ℝ) * Zb ω) (ℙ : measure Ω) :=
begin
  convert @integrable_mul_of_units_int _ _ _ (λ x, -Za x) Zb _ sm_b,
  { ext1 x,
    simp, },
  { convert strongly_measurable.neg sm_a,
    ext1 x,
    simp, },
end

/-- **Bell's inequality (1964 version)** Given six random variables `Za Zb : fin 3 → Ω → ℤˣ` taking
  values in `±1`, and assuming perfect anticorrelation on the diagonal (that is,
  `𝔼[(Za i) (Zb i)] = -1` for all `i`), we have that
  `𝔼[(Za 1) (Zb 2)] - 𝔼[(Za 1) (Zb 2)] ≤ 1 + 𝔼[(Za 2) (Zb 3)]`. -/
theorem bells_inequality_1964 {Za Zb : fin 3 → Ω → ℤˣ}
  (Za_measurable : ∀ i, strongly_measurable (λ ω, (Za i ω : ℝ)))
  (Zb_measurable : ∀ i, strongly_measurable (λ ω, (Zb i ω : ℝ)))
  (anticorrelation : ∀ i, ∫ ω, (Za i ω : ℝ) * (Zb i ω) ∂(ℙ:measure Ω) = -1) :
  (∫ ω, (Za 1 ω : ℝ) * (Zb 2 ω) ∂(ℙ : measure Ω)) - (∫ ω, (Za 1 ω : ℝ) * (Zb 3 ω) ∂(ℙ : measure Ω))
    ≤ 1 + (∫ ω, (Za 2 ω : ℝ) * (Zb 3 ω) ∂(ℙ : measure Ω)) :=
begin
  let integrable_muls :=
    λ i j, integrable_mul_of_units_int ℙ (Za_measurable i) (Zb_measurable j),
  let integrable_mul_negs :=
    λ i j, integrable_mul_of_units_int_neg ℙ (Za_measurable i) (Zb_measurable j),
  rw sub_eq_add_neg,
  apply sub_nonpos.mp,
  rw [sub_add_eq_sub_sub, sub_eq_add_neg, sub_eq_add_neg],
  have : ∀ ω, (-Za 2 ω : ℝ) * (Zb 2 ω) + (-Za 2 ω) * (Zb 3 ω) + (Za 1 ω) * (Zb 2 ω)
                  + -(Za 1 ω) * (Zb 3 ω) + -2 ≤ 0 ,
  { intro ω,
    convert CHSH_inequality_of_int_units (-(Za 2 ω)) (Za 1 ω) (Zb 2 ω) (Zb 3 ω);
    simp, },
  have int_chsh := @integral_nonpos _ _ (ℙ : measure Ω) _ (λ x, this x),
  rw [integral_add, integral_add, integral_add, integral_add] at int_chsh,
  { have : ∫ ω, -(Za 2 ω : ℝ) * (Zb 2 ω) ∂(ℙ:measure Ω) = 1,
    { convert neg_inj.mpr (anticorrelation 2),
      { rw ← measure_theory.integral_neg,
        rw integral_congr_ae,
        filter_upwards with x,
        simp, },
      { simp, }, },
    rw [this, (by simp : ∫ ω, (-2 : ℝ) ∂(ℙ : measure Ω) = -2)] at int_chsh,
    convert int_chsh using 1,
    ring_nf,
    congr' 1,
    rw add_sub_left_comm,
    congr' 1,
    { rw integral_neg,
      congr' 2,
      ext1 x,
      ring, },
    { congr' 1,
      rw integral_neg,
      congr' 2,
      ext1 x,
      ring, }, },
  { exact integrable_mul_negs 2 2, },
  { exact integrable_mul_negs 2 3, },
  { exact integrable.add (integrable_mul_negs 2 2) (integrable_mul_negs 2 3), },
  { exact integrable_muls 1 2, },
  { refine integrable.add (integrable.add (integrable_mul_negs 2 2) (integrable_mul_negs 2 3)) _,
    exact integrable_muls 1 2, },
  { exact integrable_mul_negs 1 3, },
  { refine integrable.add _ (integrable_mul_negs 1 3),
    refine integrable.add _ (integrable_muls 1 2),
    exact integrable.add (integrable_mul_negs 2 2) (integrable_mul_negs 2 3), },
  { apply integrable_const, },
  { exact has_add.to_covariant_class_right ℝ, },
end

#exit

-- Bell's inequality: 1975 version
theorem bells_inequality_1975 {Ω : Type u} {m : measurable_space Ω}
  -- parameter space for experiments
  {Aa Ab : Type u}
  -- shared variable space
  {Λ : Type u}
  {mm : measurable_space Λ}

  -- random variables
  (Xa : Ω → ℤˣ)
  (Xb : Ω → ℤˣ)
  (Xa_measurable : measurable Xa)
  (Xb_measurable : measurable Xb)

  -- probability distribution on outcomes of experiments that depends on two parameters α∈Aa and β∈Ab
  (ℙ : Aa → Ab → (probability_measure Ω))
  -- factorized probabilities
  (ℙa : Aa → (probability_measure Ω))
  (ℙb : Ab → (probability_measure Ω))
  -- probability distribution on shared variable
  (P_lam : probability_measure Ω)

  -- shared variable
  (lam : Ω → Λ)
  (lam_measurable : measurable lam)

  -- locality assumption
  (locality : ∀ lam_val:Λ, ∀ α:Aa, ∀ β:Ab , ∀ ω : set Ω ,
    ((probability_theory.cond ((ℙ α β):measure Ω) (lam ⁻¹' {lam_val})) ω) =
      ((probability_theory.cond ((ℙa α):measure Ω) (lam ⁻¹' {lam_val})) ω)*
      ((probability_theory.cond ((ℙb β):measure Ω) (lam ⁻¹' {lam_val})) ω )
  )
  :
  ∀ α : Aa , ∀ α' : Aa, ∀ β : Ab , ∀ β' : Ab ,
  | (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂((ℙ α β):measure Ω) )
    - (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂((ℙ α β'):measure Ω) ) |
  + | (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂((ℙ α' β):measure Ω) )
    - (∫ ω, (Xa ω : ℝ) * (Xb ω) ∂((ℙ α' β'):measure Ω) ) |
    ≤ 2
  :=

begin
  sorry,
end

#exit

def pm_one_space := ℤˣ

lemma pm_one_space_vals (r : ℤˣ) :
  (r : ℝ) = 1 ∨ (r : ℝ) = -1 :=
begin
  cases int.units_eq_one_or r with hh hh;
  rw hh; simp,
end

instance int.units.measurable_space : measurable_space ℤˣ := ⊤
-- units.measurable_space


section preliminaries

lemma pm_one_func_vals_ℝ (Za : Ω → ℤˣ) (ω : Ω) :
  ((Za ω) : ℝ) = 1 ∨ ((Za ω) : ℝ)  = -1 :=
begin
  apply pm_one_space_vals,
end

lemma pm_one_func_vals (Za : Ω → ℤˣ) (ω : Ω) :
  Za ω = 1 ∨ Za ω  = -1 := int.units_eq_one_or _

lemma neq_one_pm_one_space_ℝ {Za : Ω → ℤˣ} {ω : Ω} (hω : (Za ω : ℝ) ≠ 1) :
  (Za ω : ℝ)  = -1 :=
begin
  cases pm_one_func_vals_ℝ Za ω,
  { exfalso,
    exact hω h, },
  { exact h, },
end

lemma one_ne_neg_one_Z_units : (1 : ℤˣ) ≠ -1 .

lemma neq_one_pm_one_space {Za : Ω → ℤˣ} {ω : Ω} (hω : Za ω = 1) :
  ¬ Za ω = -1 :=
begin
  cases pm_one_func_vals Za ω,
  { rw h,
    exact one_ne_neg_one_Z_units, },
  { exfalso,
    rw hω at h,
    exact one_ne_neg_one_Z_units h, },
end

lemma correlation_to_probability [has_union (Type u)]
 (Za Zb : Ω → ℤˣ)
  (Za_measurable : measurable Za) (Zb_measurable : measurable Zb) :
  ∫ ω, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) = 1 - 2 * (ℙ {ω | (Za ω : ℝ) ≠ Zb ω }) :=
begin
--  let Ωp := {ω : Ω | (Za ω : ℝ) = 1},
--  let Ωm := {ω : Ω | (Za ω : ℝ) = -1},
  let Ωp := Za ⁻¹' {1},
  let Ωm := Za ⁻¹' {-1},

  have pm_univ : Ωp ∪ Ωm = set.univ,
  { ext x,
    split,
    { intros,
      simp, },
    { intros,
      rw set.union_def,
      simp only [set.mem_set_of_eq, set.mem_preimage, set.mem_singleton_iff],
      --have := pm_one_func_vals,
      exact_mod_cast pm_one_func_vals Za x, }, },

  have pm_disjoint : disjoint Ωp Ωm,
  { rw disjoint_iff,
    ext x,
    simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_preimage, set.mem_singleton_iff,
      set.bot_eq_empty, set.mem_empty_iff_false, iff_false, not_and],
    apply neq_one_pm_one_space, },

  have Ωp_measurable : measurable_set Ωp ,
  { convert measurable_set_preimage Za_measurable _,
    simp, },

  have Ωm_measurable : measurable_set Ωm ,
  { convert measurable_set_preimage Za_measurable _,
    simp, },

  have : ∫ ω, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) =
    ∫ ω in Ωp, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) +
    ∫ ω in Ωm, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω),
    --∫ ω in Ωm, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω),
  { convert measure_theory.integral_union pm_disjoint _ _ _,
    { rw pm_univ,
      exact measure.restrict_univ.symm, },
    { exact Ωm_measurable, },
    {

    },
    repeat {sorry},
    -- have : Ωp ∪ Ωm = set.univ := sorry,
  },
  rw this, clear this,
  let Ωpp := {ω : Ω | (Za ω : ℝ) = 1 ∧ (Zb ω : ℝ) = 1},
  let Ωpm := {ω : Ω | (Za ω : ℝ) = 1 ∧ (Zb ω : ℝ) = -1},
  have : ∫ ω in Ωp, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) =
    ∫ ω in Ωpp, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) +
    ∫ ω in Ωpm, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω),
  { convert measure_theory.integral_union _ _ _ _,
    repeat {sorry}, },
  rw this, clear this,
  let Ωmp := {ω : Ω | (Za ω : ℝ) = -1 ∧ (Zb ω : ℝ) = 1},
  let Ωmm := {ω : Ω | (Za ω : ℝ) = -1 ∧ (Zb ω : ℝ) = -1},
  have : ∫ ω in Ωm, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) =
    ∫ ω in Ωmp, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω) +
    ∫ ω in Ωmm, (Za ω : ℝ) * (Zb ω) ∂(ℙ:measure Ω),
  { convert measure_theory.integral_union _ _ _ _,
    repeat {sorry}, },
  rw this, clear this,


  set s := {ω : Ω | (Za ω : ℝ) ≠ Zb ω},
  have : ∀ ω ∈ s, (Za ω : ℝ) * (Zb ω) = -1,
  { intros ω hω,
    have Za_neq_Zb : (Za ω : ℝ) ≠ Zb ω := set.mem_def.mp hω,
    by_cases ha : (Za ω : ℝ) = 1;
    by_cases hb : (Zb ω : ℝ) = 1,
    { exfalso,
      rw ← hb at ha,
      exact Za_neq_Zb ha, },
    { rw [ha, neq_one_pm_one_space hb],
      ring, },
    { rw [hb, neq_one_pm_one_space ha],
      ring, },
    { exfalso,
      have := neq_one_pm_one_space ha,
      rw ← neq_one_pm_one_space hb at this,
      exact Za_neq_Zb this, }, },

  sorry,
end

/- prove that s.indicator f a = s.indicator 1 a when f a = 1 on s
lemma indicator_eq_indicator_one [α : Type*] (f : Ω → α) (h : ∀ x : α , x∈ s → f x = c):
  s.indicator f = s.indicator (λ x , c) :=
  begin
    --have : s.indicator f a = 0 ∨ s.indicator f a = f a := set.indicator_eq_zero_or_self s f a,
    have : a ∈ s ∨ a ∉ s:= sorry,

    -- go through both cases
    cases this with zero nonzero , {
      have : s.indicator f a = f a := set.indicator_of_mem zero f,
      have eq1 : s.indicator f a = c := eq.trans this ((h a) zero),
      have eq2 : s.indicator (λ x , c) a = c := set.indicator_of_mem zero (λ x , c),
      exact eq.trans eq1 (eq.symm eq2),
    },
    {
      have eq1 : s.indicator f a = 0 := set.indicator_of_not_mem nonzero f,
      have eq2 : s.indicator (λ x , c) a = 0 := set.indicator_of_not_mem nonzero (λ x , c),
      exact eq.trans eq1 (eq.symm eq2),
    },
  end
-/

/-
-- Prove that C(i,j)=1-2*P(Zi≠ Zj)
lemma correlation_to_probability [Ω : Type] [has_mem Ω Type] [measurable_space Ω]
  (Za : Ω → ℤ )
  (Zb : Ω → ℤ )
  (P : measure_theory.probability_measure Ω)
  -- restrict values to ± 1
  (ha: ∀ ω : Ω , Za ω = 1 ∨ Za ω = -1)
  (hb: ∀ ω : Ω , Zb ω = 1 ∨ Zb ω = -1)
  -- I have no clue why this does not work
  : ∫ ω , (Za ω :ℝ)*(Zb ω :ℝ) ∂↑P = 1-2*(P {ω | Za ω ≠ Zb ω })
  :=
  begin
    let Cij:=∫ ω , (Za ω : ℝ)*(Zb ω : ℝ) ∂↑P,

    -- first step: prove that C(i,j)=P(Zi*Zj=1)-P(Zi*Zj=-1)
    have : Cij = (P {ω | Za ω * Zb ω =1}) - (P {ω | Za ω * Zb ω =-1}) ,
    {
      -- set Za = Zb
      let eqs := {ω | Za ω = Zb ω},

      -- prove that Za Zb=1 in eqs
      have in_eq : ∀ ω ∈ eqs , Za ω * Zb ω =1  , {
        intros ω hω,
        -- prove that Za = Zb
        have equal : Za ω = Zb ω := set.mem_set_of.mp hω,

        -- split cases for Za = ± 1
        cases ha ω with ap1 am1 , {
          have eq1 : Zb ω = 1 := eq.trans (eq.symm equal) ap1,
          -- this should be trivial
          sorry,
        },
        {
          have eq1 : Zb ω = -1 := eq.trans (eq.symm equal) am1,
          -- this should be trivial
          sorry,
        },
      },

      -- prove that Za Zb=-1 in complement of eqs
      have in_compl : ∀ ω ∈ eqsᶜ , Za ω * Zb ω =-1  , {
        intros ω hω,
        -- prove that Za ≠ Zb
        have : ω ∈ {ω | Za ω ≠ Zb ω } ,{
          have : eqsᶜ = {ω | Za ω ≠ Zb ω }:= set.compl_set_of (λ ω , Za ω = Zb ω),
          exact hω,
        },
        have different : Za ω ≠ Zb ω := set.mem_set_of.mp this,

        -- split cases for Za = ± 1
        cases ha ω with ap1 am1 , {
          have neq1 : Zb ω ≠ 1 := ne.trans_eq (ne.symm different) ap1,
          have : Zb ω = 1 ∨ Zb ω = -1 := hb ω,
          have : Zb ω = -1 := or.resolve_left this neq1,
          -- this should be trivial
          sorry,
        },
        {
          have neq1 : Zb ω ≠ -1 := ne.trans_eq (ne.symm different) am1,
          have : Zb ω = 1 ∨ Zb ω = -1 := hb ω,
          have : Zb ω = 1 := or.resolve_right this neq1,
          -- this should be trivial
          sorry,
        },
      },

      -- split integral
      let int1:=∫ ω in eqs, (Za ω : ℝ)*(Zb ω : ℝ) ∂↑P,
      let int2:=∫ ω in eqsᶜ, (Za ω : ℝ)*(Zb ω : ℝ) ∂↑P,


      -- assumptions to split integral
      have hfs : measure_theory.integrable (λ ω , (Za ω : ℝ)*(Zb ω : ℝ)) ↑P:= sorry,
      have measurable_eqs : measurable_set eqs := sorry,

      -- split
      have : Cij=int1+int2 := eq.symm (measure_theory.integral_add_compl measurable_eqs hfs),

      have : int1=P eqs , {
        have : int1 = ∫ ω in eqs, 1 ∂↑P , {
          have int_ind : int1 = ∫ ω , eqs.indicator (λ ω , (Za ω : ℝ)*(Zb ω : ℝ)) ω  ∂↑P := eq.symm (measure_theory.integral_indicator measurable_eqs),
          have : ∀ ω : Ω , eqs.indicator (λ ω , Za ω*Zb ω) ω = eqs.indicator (λ ω , 1) ω , {
            intro ω,
            -- ???????????????
            have : eqs.indicator (λ ω , Za ω*Zb ω) ω = eqs.indicator (λ x , 1) ω := indicator_eq_indicator_one eqs (λ ω , Za ω*Zb ω) (ω:Ω) (1:ℤ) in_eq,
          },
        },
        exact measure_theory.set_integral_const 1,
        sorry,
      },

      sorry,
    },
    sorry,
  end

-/
end preliminaries

/-- **Bell's Inequality** -/
theorem bells_inequality : true :=
begin
  exact trivial,
end


end probability_theory
