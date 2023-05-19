/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.translations
/-!
# Stabilisation of gcf Computations Under Termination

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/

namespace generalized_continued_fraction
open stream.seq as seq

variables {K : Type*} {g : generalized_continued_fraction K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`.-/
lemma terminated_stable (n_le_m : n ≤ m) (terminated_at_n : g.terminated_at n) :
  g.terminated_at m :=
g.s.terminated_stable n_le_m terminated_at_n

variable [division_ring K]

lemma continuants_aux_stable_step_of_terminated (terminated_at_n : g.terminated_at n) :
  g.continuants_aux (n + 2) = g.continuants_aux (n + 1) :=
by { rw [terminated_at_iff_s_none] at terminated_at_n,
     simp only [terminated_at_n, continuants_aux] }

lemma continuants_aux_stable_of_terminated (n_lt_m : n < m)
  (terminated_at_n : g.terminated_at n) :
  g.continuants_aux m = g.continuants_aux (n + 1) :=
begin
  refine nat.le_induction rfl (λ k hnk hk, _) _ n_lt_m,
  rcases nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩,
  refine (continuants_aux_stable_step_of_terminated _).trans hk,
  exact terminated_stable (nat.le_add_right _ _) terminated_at_n
end

lemma convergents'_aux_stable_step_of_terminated {s : seq $ pair K}
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

lemma convergents'_aux_stable_of_terminated
  {s : seq $ pair K} (n_le_m : n ≤ m)
  (terminated_at_n : s.terminated_at n) :
  convergents'_aux s m = convergents'_aux s n :=
begin
  induction n_le_m with m n_le_m IH,
  { refl },
  { refine (convergents'_aux_stable_step_of_terminated _).trans IH,
    exact s.terminated_stable n_le_m terminated_at_n }
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
