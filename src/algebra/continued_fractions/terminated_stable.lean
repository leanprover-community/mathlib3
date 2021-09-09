/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.translations
/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf
variables {K : Type*} {g : gcf K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`.-/
lemma terminated_stable (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.terminated_at m :=
g.s.terminated_stable n_le_m terminated_at_n

variable [division_ring K]

lemma continuants_aux_stable_step_of_terminated (terminated_at_n : g.terminated_at n) :
  g.continuants_aux (n + 2) = g.continuants_aux (n + 1) :=
by { rw [terminated_at_iff_s_none] at terminated_at_n,
     simp only [terminated_at_n, continuants_aux] }

lemma continuants_aux_stable_of_terminated (succ_n_le_m : (n + 1) ≤ m)
  (terminated_at_n : g.terminated_at n) :
  g.continuants_aux m = g.continuants_aux (n + 1) :=
begin
  induction succ_n_le_m with m succ_n_le_m IH,
  { refl },
  { have : g.continuants_aux (m + 1) = g.continuants_aux m, by
    { have : n ≤ m - 1, from nat.le_pred_of_lt succ_n_le_m,
      have : g.terminated_at (m - 1), from terminated_stable this terminated_at_n,
      have stable_step : g.continuants_aux (m - 1 + 2) = g.continuants_aux (m - 1 + 1), from
        continuants_aux_stable_step_of_terminated this,
      have one_le_m : 1 ≤ m, from nat.one_le_of_lt succ_n_le_m,
      have : m - 1 + 2 = m + 2 - 1, from (nat.sub_add_comm one_le_m).symm,
      have : m - 1 + 1 = m + 1 - 1, from (nat.sub_add_comm one_le_m).symm,
      simpa [*] using stable_step },
    exact (eq.trans this IH) }
end

lemma convergents'_aux_stable_step_of_terminated {s : seq $ gcf.pair K}
  (terminated_at_n : s.terminated_at n) :
  convergents'_aux s (n + 1) = convergents'_aux s n :=
begin
  change s.nth n = none at terminated_at_n,
  induction n with n IH generalizing s,
  case nat.zero
  { simp only [convergents'_aux, terminated_at_n, seq.head] },
  case nat.succ
  { cases s_head_eq : s.head with gp_head,
    case option.none { simp only [convergents'_aux, s_head_eq] },
    case option.some
    { have : s.tail.terminated_at n, by simp only [seq.terminated_at, s.nth_tail, terminated_at_n],
      simp only [convergents'_aux, s_head_eq, (IH this)] } }
end

lemma convergents'_aux_stable_of_terminated {s : seq $ gcf.pair K} (n_le_m : n ≤ m)
  (terminated_at_n : s.terminated_at n) :
  convergents'_aux s m = convergents'_aux s n :=
begin
  induction n_le_m with m n_le_m IH generalizing s,
  { refl },
  { cases s_head_eq : s.head with gp_head,
    case option.none { cases n; simp only [convergents'_aux, s_head_eq] },
    case option.some
    { have : convergents'_aux s (n + 1) = convergents'_aux s n, from
        convergents'_aux_stable_step_of_terminated terminated_at_n,
      rw [←this],
      have : s.tail.terminated_at n, by
        simpa only [seq.terminated_at, seq.nth_tail] using (s.le_stable n.le_succ terminated_at_n),
      have : convergents'_aux s.tail m = convergents'_aux s.tail n, from IH this,
      simp only [convergents'_aux, s_head_eq, this] } }
end

lemma continuants_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.continuants m = g.continuants n :=
by simp only [nth_cont_eq_succ_nth_cont_aux,
  (continuants_aux_stable_of_terminated (nat.pred_le_iff.elim_left n_le_m) terminated_at_n)]

lemma numerators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.numerators m = g.numerators n :=
by simp only [num_eq_conts_a, (continuants_stable_of_terminated n_le_m terminated_at_n)]

lemma denominators_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.denominators m = g.denominators n :=
by simp only [denom_eq_conts_b, (continuants_stable_of_terminated n_le_m terminated_at_n)]

lemma convergents_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.convergents m = g.convergents n :=
by simp only [convergents, (denominators_stable_of_terminated n_le_m terminated_at_n),
  (numerators_stable_of_terminated n_le_m terminated_at_n)]

lemma convergents'_stable_of_terminated (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.convergents' m = g.convergents' n :=
by simp only [convergents', (convergents'_aux_stable_of_terminated n_le_m terminated_at_n)]

end generalized_continued_fraction
