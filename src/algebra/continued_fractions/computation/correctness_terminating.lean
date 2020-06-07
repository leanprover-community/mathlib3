/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.translations
import algebra.continued_fractions.terminated_stable
import algebra.continued_fractions.continuants_recurrence
/-!
# Correctness of Terminating Continued Fraction Computations (`gcf.of`)

## Summary

Let us write `gcf` for `generalized_continued_fraction`. We show the correctness of the
algorithm computing continued fractions (`gcf.of`) in case of termination in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the
convergent `(gcf.of v).convergents n`. The residual term will be zero exactly when the continued
fraction terminated; otherwise, the residual term will be given by the fractional part stored in
`gcf.int_fract_pair.stream v n`.

For an example, refer to `gcf.comp_exact_value` and for more information
about the computation process, refer to `algebra.continued_fraction.computation.basic`.

## Main definitions

- `gcf.comp_exact_value` returns the exact value approximated by the continued fraction `gcf.of v`
  by adding a residual term as described in the summary.

## Main Theorems

- `gcf.comp_exact_value_correctness_of_stream_eq_some` shows that `gcf.comp_exact_value` indeed
  returns the value `v` when given the convergent and fractional part as described in the summary.
- `gcf.of_correctness_of_terminated_at` shows the equality `v = (gcf.of v).convergents n`
  if `gcf.of v` terminated at position `n`.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

variables {K : Type*} [discrete_linear_ordered_field K] {v : K} {n : ℕ}

/--
Given two successive continuants (at positions `n + 1` and `n`) of a continued fraction
`generalized_continued_fraction.of v` and the fractional part at `int_fract_pair.stream n`,
this function returns the exact value approximated by the continued fraction, that is `v`.

For example, let `(v : ℚ) := 3.4`. We have
- `gcf.int_fract_pair.stream v 0 = some ⟨3, 0.4⟩`, and
- `gcf.int_fract_pair.stream v 1 = some ⟨2, 0.5⟩`.

Now `(gcf.of v).convergents 1 = 3 + 1/2`, and our fractional term (the residual) at position `2` is
`0.5`. We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`.
-/
protected def comp_exact_value (pred_conts conts : gcf.pair K) (fr : K) : K :=
-- if the fractional part is zero, we exactly approximated the value by the last continuants
if fr = 0 then conts.a / conts.b
-- otherwise, we have to include the fractional part in a final continuants step.
else let exact_conts := next_continuants 1 fr⁻¹ pred_conts conts in
  exact_conts.a / exact_conts.b

variable [floor_ring K]

/-- Just a computational lemma we need for the next main proof. -/
protected lemma comp_exact_value_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
  (fract_a_ne_zero : fract a ≠ 0) :
  ((⌊a⌋ : K) * b + c) / (fract a) + b = (b * a + c) / fract a :=
begin
  have : ((⌊a⌋ : K) * b + c) / (fract a) + b = ((b * (fract a) + b * ⌊a⌋ + c) / fract a), by
  { field_simp [fract_a_ne_zero], ac_refl },
  simpa [←left_distrib] using this
end

open generalized_continued_fraction as gcf

/--
Shows the correctness of `comp_exact_value` in case the continued fraction did not terminate.
That is, at every step of the computation of a continued fraction `gcf.of v`, we obtain the value
`v` if we compute the continuant at position `n` and add the residual term given by the fractional
part stored in `int_fract_pair.stream v n`.
-/
lemma comp_exact_value_correctness_of_stream_eq_some :
  ∀ {ifp_n : int_fract_pair K}, int_fract_pair.stream v n = some ifp_n →
    v = gcf.comp_exact_value
          ((gcf.of v).continuants_aux  n)
          ((gcf.of v).continuants_aux $ n + 1)
          ifp_n.fr :=
begin
  let g := gcf.of v,
  induction n with n IH,
  { assume ifp_zero stream_zero_eq, -- nat.zero
    have : int_fract_pair.of v = ifp_zero, by
    { have : int_fract_pair.stream v 0 = some (int_fract_pair.of v), from rfl,
      simpa only [this] using stream_zero_eq },
    cases this,
    cases decidable.em (fract v = 0) with fract_eq_zero fract_ne_zero,
    -- fract v = 0; we must then have `v = ⌊v⌋`
    { suffices : v = ⌊v⌋, by simpa [continuants_aux, fract_eq_zero, gcf.comp_exact_value],
      calc
          v = fract v + ⌊v⌋ : by rw fract_add_floor
        ... = ⌊v⌋           : by simp [fract_eq_zero] },
    -- fract v ≠ 0; the claim then easily follows by unfolding a single computation step
    { field_simp [continuants_aux, next_continuants, next_numerator, next_denominator,
        gcf.of_h_eq_floor, gcf.comp_exact_value, fract_ne_zero] } },
  { assume ifp_succ_n succ_nth_stream_eq,  -- nat.succ
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, _⟩ :
      ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
      ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
        int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
    -- introduce some notation
    let conts := g.continuants_aux (n + 2),
    set pred_conts := g.continuants_aux (n + 1) with pred_conts_eq,
    set ppred_conts := g.continuants_aux n with ppred_conts_eq,
    cases decidable.em (ifp_succ_n.fr = 0) with ifp_succ_n_fr_eq_zero ifp_succ_n_fr_ne_zero,
    -- ifp_succ_n.fr = 0
    { suffices : v = conts.a / conts.b, by
        simpa [gcf.comp_exact_value, ifp_succ_n_fr_eq_zero],
      -- use the IH and the fact that ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ to prove this case
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_inv_eq_floor⟩ :
        ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋, from
          int_fract_pair.obtain_succ_nth_stream_of_fr_zero succ_nth_stream_eq ifp_succ_n_fr_eq_zero,
      have : ifp_n' = ifp_n, by injection (eq.trans (nth_stream_eq').symm nth_stream_eq),
      cases this,
      have s_nth_eq : g.s.nth n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩, from
        gcf.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero,
      rw [←ifp_n_fract_inv_eq_floor] at s_nth_eq,
      suffices : v = gcf.comp_exact_value ppred_conts pred_conts ifp_n.fr, by
        simpa [conts, continuants_aux, s_nth_eq,gcf.comp_exact_value, nth_fract_ne_zero] using this,
      exact (IH nth_stream_eq) },
    -- ifp_succ_n.fr ≠ 0
    { -- use the IH to show that the following equality suffices
      suffices : gcf.comp_exact_value ppred_conts pred_conts ifp_n.fr
               = gcf.comp_exact_value pred_conts conts ifp_succ_n.fr, by
      { have : v = gcf.comp_exact_value ppred_conts pred_conts ifp_n.fr, from IH nth_stream_eq,
        conv_lhs { rw this }, assumption },
      -- get the correspondence between ifp_n and ifp_succ_n
      obtain ⟨ifp_n', nth_stream_eq', ifp_n_fract_ne_zero, ⟨refl⟩⟩ :
        ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
        ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
          int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
      have : ifp_n' = ifp_n, by injection (eq.trans (nth_stream_eq').symm nth_stream_eq),
      cases this,
      -- get the correspondence between ifp_n and g.s.nth n
      have s_nth_eq : g.s.nth n = some ⟨1, (⌊ifp_n.fr⁻¹⌋ : K)⟩, from
        gcf.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero nth_stream_eq ifp_n_fract_ne_zero,
      -- the claim now follows by unfolding the definitions and tedious calculations
      -- some shorthand notation
      let ppA := ppred_conts.a, let ppB := ppred_conts.b,
      let pA := pred_conts.a, let pB := pred_conts.b,
      have : gcf.comp_exact_value ppred_conts pred_conts ifp_n.fr
          = (ppA + ifp_n.fr⁻¹ * pA) / (ppB + ifp_n.fr⁻¹ * pB), by
        -- unfold comp_exact_value and the convergent computation once
        { field_simp [ifp_n_fract_ne_zero, gcf.comp_exact_value, next_continuants, next_numerator,
          next_denominator], ac_refl },
      rw this,
      -- two calculations needed to show the claim
      have tmp_calc := gcf.comp_exact_value_correctness_of_stream_eq_some_aux_comp
        pA ppA ifp_succ_n_fr_ne_zero,
      have tmp_calc' := gcf.comp_exact_value_correctness_of_stream_eq_some_aux_comp
        pB ppB ifp_succ_n_fr_ne_zero,
      rw inv_eq_one_div at tmp_calc tmp_calc',
      have : fract (1 / ifp_n.fr) ≠ 0, by simpa using ifp_succ_n_fr_ne_zero,
      -- now unfold the recurrence one step and simplify both sides to arrive at the conclusion
      field_simp [conts, gcf.comp_exact_value,
        (gcf.continuants_aux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq), next_continuants,
        next_numerator, next_denominator, this, tmp_calc, tmp_calc'],
      ac_refl } }
end

/--
Shows the correctness of `comp_exact_value` in case the `int_fract_pair.stream` of the corresponding
to the continued fraction terminated.
-/
lemma comp_exact_value_correctness_of_stream_eq_none
  (nth_stream_eq_none : int_fract_pair.stream v n = none) :
  v = (gcf.of v).convergents (n - 1) :=
begin
  induction n with n IH,
  case nat.zero { contradiction }, -- int_fract_pair.stream v 0 ≠ none
  case nat.succ
  { rename nth_stream_eq_none succ_nth_stream_eq_none,
    let g := gcf.of v,
    change v = g.convergents n,
    have : int_fract_pair.stream v n = none
      ∨ ∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0, from
      int_fract_pair.succ_nth_stream_eq_none_iff.elim_left succ_nth_stream_eq_none,
    rcases this with ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩,
    { cases n with n',
      { contradiction }, -- int_fract_pair.stream v 0 ≠ none
      { have : g.terminated_at n', from
          gcf.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_right
          nth_stream_eq_none,
        have : g.convergents (n' + 1) = g.convergents n', from
          gcf.convergents_stable_of_terminated n'.le_succ this,
        rw this,
        exact (IH nth_stream_eq_none) } },
    { simpa [nth_stream_fr_eq_zero, gcf.comp_exact_value] using
      (comp_exact_value_correctness_of_stream_eq_some nth_stream_eq) } }
end

/-- If `generalized_continued_fraction.of v` terminated at step `n`, then the `n`th convergent is
exactly `v`. -/
theorem of_correctness_of_terminated_at (terminated_at_n : (gcf.of v).terminated_at n) :
  v = (gcf.of v).convergents n :=
have int_fract_pair.stream v (n + 1) = none, from
  gcf.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_left terminated_at_n,
comp_exact_value_correctness_of_stream_eq_none this

/-- If `generalized_continued_fraction.of v` terminates, then its convergent will eventually be
exactly `v`. -/
lemma of_correctness_of_terminates (terminates : (gcf.of v).terminates) :
  ∃ (n : ℕ), v = (gcf.of v).convergents n :=
exists.elim terminates
( assume n terminated_at_n,
  exists.intro n (of_correctness_of_terminated_at terminated_at_n) )

end generalized_continued_fraction
