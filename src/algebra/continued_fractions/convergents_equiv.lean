/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.continuants_recurrence
import algebra.continued_fractions.terminated_stable
import tactic.field_simp
import tactic.ring

/-!
# Equivalence of Recursive and Direct Computations of `gcf` Convergents

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convergents`) vs.
direct evaluation (`convergents'`)) for `gcf`s on linear ordered fields. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
$$
  c = h + \dfrac{a_0}
                {b_0 + \dfrac{a_1}
                             {b_1 + \dfrac{a_2}
                                          {b_2 + \dfrac{a_3}
                                                       {b_3 + \dots}}}}
$$
One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convergents'`)
2. Using the recurrence (`convergents`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`convergents_eq_convergents'`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁), (aₙ, bₙ + aₙ₊₁ / bₙ₊₁), (aₙ₊₁, bₙ₊₁),...]`.
This squashing process is formalised in section `squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_convergent'_eq_squash_gcf_nth_convergent'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and and `c'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `succ_nth_convergent_eq_squash_gcf_nth_convergent`.

## Main Theorems

- `generalized_continued_fraction.convergents_eq_convergents'` shows the equivalence under a strict
positivity restriction on the sequence.
- `continued_fractions.convergents_eq_convergents'` shows the equivalence for (regular) continued
fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/

variables {K : Type*} {n : ℕ}
namespace generalized_continued_fraction
open stream.seq as seq

variables {g : generalized_continued_fraction K} {s : seq $ pair K}

section squash
/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/

section with_division_ring
variable [division_ring K]

/--
Given a sequence of gcf.pairs `s = [(a₀, bₒ), (a₁, b₁), ...]`, `squash_seq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squash_seq s 0 = [(a₀, bₒ + a₁ / b₁), (a₁, b₁),...]`.
If `s.terminated_at (n + 1)`, then `squash_seq s n = s`.
-/
def squash_seq (s : seq $ pair K) (n : ℕ) : seq (pair K) :=
match prod.mk (s.nth n) (s.nth (n + 1)) with
| ⟨some gp_n, some gp_succ_n⟩ := seq.nats.zip_with
    -- return the squashed value at position `n`; otherwise, do nothing.
    (λ n' gp, if n' = n then ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ else gp) s
| _ := s
end

/-! We now prove some simple lemmas about the squashed sequence -/

/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
lemma squash_seq_eq_self_of_terminated (terminated_at_succ_n : s.terminated_at (n + 1)) :
  squash_seq s n = s :=
begin
  change s.nth (n + 1) = none at terminated_at_succ_n,
  cases s_nth_eq : (s.nth n);
  simp only [*, squash_seq]
end

/-- If the sequence has not terminated before position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
lemma squash_seq_nth_of_not_terminated {gp_n gp_succ_n : pair K}
  (s_nth_eq : s.nth n = some gp_n) (s_succ_nth_eq : s.nth (n + 1) = some gp_succ_n) :
  (squash_seq s n).nth n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ :=
by simp [*, squash_seq]

/-- The values before the squashed position stay the same. -/
lemma squash_seq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squash_seq s n).nth m = s.nth m :=
begin
  cases s_succ_nth_eq : s.nth (n + 1),
  case option.none { rw (squash_seq_eq_self_of_terminated s_succ_nth_eq) },
  case option.some
  { obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.nth n = some gp_n, from
      s.ge_stable n.le_succ s_succ_nth_eq,
    obtain ⟨gp_m, s_mth_eq⟩ : ∃ gp_m, s.nth m = some gp_m, from
      s.ge_stable (le_of_lt m_lt_n) s_nth_eq,
    simp [*, squash_seq, m_lt_n.ne] }
end

/-- Squashing at position `n + 1` and taking the tail is the same as squashing the tail of the
sequence at position `n`. -/
lemma squash_seq_succ_n_tail_eq_squash_seq_tail_n :
  (squash_seq s (n + 1)).tail = squash_seq s.tail n :=
begin
  cases s_succ_succ_nth_eq : s.nth (n + 2) with gp_succ_succ_n,
  case option.none
  { have : squash_seq s (n + 1) = s, from squash_seq_eq_self_of_terminated s_succ_succ_nth_eq,
    cases s_succ_nth_eq : (s.nth (n + 1));
    simp only [squash_seq, seq.nth_tail, s_succ_nth_eq, s_succ_succ_nth_eq] },
  case option.some
  { obtain ⟨gp_succ_n, s_succ_nth_eq⟩ : ∃ gp_succ_n, s.nth (n + 1) = some gp_succ_n, from
      s.ge_stable (n + 1).le_succ s_succ_succ_nth_eq,
    -- apply extensionality with `m` and continue by cases `m = n`.
    ext1 m,
    cases decidable.em (m = n) with m_eq_n m_ne_n,
    { have : s.tail.nth n = some gp_succ_n, from (s.nth_tail n).trans s_succ_nth_eq,
      simp [*, squash_seq] },
    { have : s.tail.nth m = s.nth (m + 1), from s.nth_tail m,
      cases s_succ_mth_eq : s.nth (m + 1),
      all_goals { have s_tail_mth_eq, from this.trans s_succ_mth_eq },
      { simp only [*, squash_seq, seq.nth_tail, seq.nth_zip_with, option.map₂_none_right] },
      { simp [*, squash_seq] } } }
end

/-- The auxiliary function `convergents'_aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
lemma succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq :
  convergents'_aux s (n + 2) = convergents'_aux (squash_seq s n) (n + 1) :=
begin
  cases s_succ_nth_eq : (s.nth $ n + 1) with gp_succ_n,
  case option.none
  { rw [(squash_seq_eq_self_of_terminated s_succ_nth_eq),
        (convergents'_aux_stable_step_of_terminated s_succ_nth_eq)] },
  case option.some
  { induction n with m IH generalizing s gp_succ_n,
    case nat.zero
    { obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head, from
        s.ge_stable zero_le_one s_succ_nth_eq,
      have : (squash_seq s 0).head = some ⟨gp_head.a, gp_head.b + gp_succ_n.a / gp_succ_n.b⟩,
        from squash_seq_nth_of_not_terminated s_head_eq s_succ_nth_eq,
      simp [*, convergents'_aux, seq.head, seq.nth_tail] },
    case nat.succ
    { obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head, from
        s.ge_stable (m + 2).zero_le s_succ_nth_eq,
      suffices : gp_head.a / (gp_head.b + convergents'_aux s.tail (m + 2))
               = convergents'_aux (squash_seq s (m + 1)) (m + 2), by
        simpa only [convergents'_aux, s_head_eq],
      have : convergents'_aux s.tail (m + 2) = convergents'_aux (squash_seq s.tail m) (m + 1), by
      { refine (IH gp_succ_n _),
        simpa [seq.nth_tail] using s_succ_nth_eq },
      have : (squash_seq s (m + 1)).head = some gp_head, from
        (squash_seq_nth_of_lt m.succ_pos).trans s_head_eq,
      simp only [*, convergents'_aux, squash_seq_succ_n_tail_eq_squash_seq_tail_n] } }
end

/-! Let us now lift the squashing operation to gcfs. -/

/--
Given a gcf `g = [h; (a₀, bₒ), (a₁, b₁), ...]`, we have
- `squash_nth.gcf g 0 = [h + a₀ / b₀); (a₀, bₒ), ...]`,
- `squash_nth.gcf g (n + 1) = ⟨g.h, squash_seq g.s n⟩`
-/
def squash_gcf (g : generalized_continued_fraction K) : ℕ → generalized_continued_fraction K
| 0 := match g.s.nth 0 with
  | none := g
  | some gp := ⟨g.h + gp.a / gp.b, g.s⟩
  end
| (n + 1) := ⟨g.h, squash_seq g.s n⟩

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/

/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
lemma squash_gcf_eq_self_of_terminated (terminated_at_n : terminated_at g n) :
  squash_gcf g n = g :=
begin
  cases n,
  case nat.zero
  { change g.s.nth 0 = none at terminated_at_n,
    simp only [convergents', squash_gcf, convergents'_aux, terminated_at_n] },
  case nat.succ
  { cases g, simp [(squash_seq_eq_self_of_terminated terminated_at_n), squash_gcf] }
end

/-- The values before the squashed position stay the same. -/
lemma squash_gcf_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
  (squash_gcf g (n + 1)).s.nth m = g.s.nth m :=
by simp only [squash_gcf, (squash_seq_nth_of_lt m_lt_n)]

/-- `convergents'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
lemma succ_nth_convergent'_eq_squash_gcf_nth_convergent' :
  g.convergents' (n + 1) = (squash_gcf g n).convergents' n :=
begin
  cases n,
  case nat.zero
  { cases g_s_head_eq : (g.s.nth 0);
    simp [g_s_head_eq, squash_gcf, convergents', convergents'_aux, seq.head] },
  case nat.succ
  { simp only [succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq,
      convergents', squash_gcf] }
end

/-- The auxiliary continuants before the squashed position stay the same. -/
lemma continuants_aux_eq_continuants_aux_squash_gcf_of_le {m : ℕ} :
  m ≤ n → continuants_aux g m = (squash_gcf g n).continuants_aux m :=
nat.strong_induction_on m
(begin
  clear m,
  assume m IH m_le_n,
  cases m with m',
  { refl },
  { cases n with n',
    { exact (m'.not_succ_le_zero m_le_n).elim }, -- 1 ≰ 0
    { cases m' with m'',
      { refl },
      { -- get some inequalities to instantiate the IH for m'' and m'' + 1
        have m'_lt_n : m'' + 1 < n' + 1 := m_le_n,
        have succ_m''th_conts_aux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le,
        have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two,
        have m''th_conts_aux_eq := IH m'' this (le_trans this.le m_le_n),
        have : (squash_gcf g (n' + 1)).s.nth m'' = g.s.nth m'', from
          squash_gcf_nth_of_lt (nat.succ_lt_succ_iff.mp m'_lt_n),
        simp [continuants_aux, succ_m''th_conts_aux_eq, m''th_conts_aux_eq, this] } } }
end)

end with_division_ring

/-- The convergents coincide in the expected way at the squashed position if the partial denominator
at the squashed position is not zero. -/
lemma succ_nth_convergent_eq_squash_gcf_nth_convergent [field K]
  (nth_part_denom_ne_zero : ∀ {b : K}, g.partial_denominators.nth n = some b → b ≠ 0) :
  g.convergents (n + 1) = (squash_gcf g n).convergents n :=
begin
  cases decidable.em (g.terminated_at n) with terminated_at_n not_terminated_at_n,
  { have : squash_gcf g n = g, from squash_gcf_eq_self_of_terminated terminated_at_n,
    simp only [this, (convergents_stable_of_terminated n.le_succ terminated_at_n)] },
  { obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.nth n = some gp_n, from
      option.ne_none_iff_exists'.mp not_terminated_at_n,
    have b_ne_zero : b ≠ 0, from nth_part_denom_ne_zero (part_denom_eq_s_b s_nth_eq),
    cases n with n',
    case nat.zero
    { suffices : (b * g.h + a) / b = g.h + a / b, by
        simpa [squash_gcf, s_nth_eq, convergent_eq_conts_a_div_conts_b,
          (continuants_recurrence_aux s_nth_eq zeroth_continuant_aux_eq_one_zero
          first_continuant_aux_eq_h_one)],
      calc
        (b * g.h + a) / b = b * g.h / b + a / b  : by ring -- requires `field`, not `division_ring`
                      ... = g.h + a / b          : by rw (mul_div_cancel_left _ b_ne_zero) },
    case nat.succ
    { obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.nth n' = some gp_n' :=
        g.s.ge_stable n'.le_succ s_nth_eq,
      -- Notations
      let g' := squash_gcf g (n' + 1),
      set pred_conts := g.continuants_aux (n' + 1) with succ_n'th_conts_aux_eq,
      set ppred_conts := g.continuants_aux n' with n'th_conts_aux_eq,
      let pA := pred_conts.a, let pB := pred_conts.b,
      let ppA := ppred_conts.a, let ppB := ppred_conts.b,
      set pred_conts' := g'.continuants_aux (n' + 1) with succ_n'th_conts_aux_eq',
      set ppred_conts' := g'.continuants_aux n' with n'th_conts_aux_eq',
      let pA' := pred_conts'.a, let pB' := pred_conts'.b, let ppA' := ppred_conts'.a,
      let ppB' := ppred_conts'.b,
      -- first compute the convergent of the squashed gcf
      have : g'.convergents (n' + 1)
           = ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB'),
      { have : g'.s.nth n' = some ⟨pa, pb + a / b⟩ :=
          squash_seq_nth_of_not_terminated s_n'th_eq s_nth_eq,
        rw [convergent_eq_conts_a_div_conts_b,
          continuants_recurrence_aux this n'th_conts_aux_eq'.symm succ_n'th_conts_aux_eq'.symm], },
      rw this,
      -- then compute the convergent of the original gcf by recursively unfolding the continuants
      -- computation twice
      have : g.convergents (n' + 2)
           = (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB),
      { -- use the recurrence once
        have : g.continuants_aux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩ :=
          continuants_aux_recurrence s_n'th_eq n'th_conts_aux_eq.symm succ_n'th_conts_aux_eq.symm,
        -- and a second time
        rw [convergent_eq_conts_a_div_conts_b,
          continuants_recurrence_aux s_nth_eq succ_n'th_conts_aux_eq.symm this] },
      rw this,
      suffices : ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB)
               = (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB),
      { obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB,
        { simp [*, (continuants_aux_eq_continuants_aux_squash_gcf_of_le $ le_refl $ n' + 1).symm,
            (continuants_aux_eq_continuants_aux_squash_gcf_of_le n'.le_succ).symm] },
        symmetry,
        simpa only [eq1, eq2, eq3, eq4, mul_div_cancel _  b_ne_zero] },
      field_simp,
      congr' 1; ring } }
end

end squash

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of the
gcf coincide at position `n` if the sequence of fractions contains strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this result.
For example, the dual - sequences with strictly negative values only - would also work.

In practice, one most commonly deals with (regular) continued fractions, which satisfy the
positivity criterion required here. The analogous result for them
(see `continued_fractions.convergents_eq_convergents`) hence follows directly from this theorem.
-/
theorem convergents_eq_convergents' [linear_ordered_field K]
  (s_pos : ∀ {gp : pair K} {m : ℕ}, m < n → g.s.nth m = some gp → 0 < gp.a ∧ 0 < gp.b) :
  g.convergents n = g.convergents' n :=
begin
  induction n with n IH generalizing g,
  case nat.zero { simp },
  case nat.succ
  { let g' := squash_gcf g n, -- first replace the rhs with the squashed computation
    suffices : g.convergents (n + 1) = g'.convergents' n, by
      rwa [succ_nth_convergent'_eq_squash_gcf_nth_convergent'],
    cases decidable.em (terminated_at g n) with terminated_at_n not_terminated_at_n,
    { have g'_eq_g : g' = g, from squash_gcf_eq_self_of_terminated terminated_at_n,
      rw [(convergents_stable_of_terminated n.le_succ terminated_at_n), g'_eq_g, (IH _)],
      assume _ _ m_lt_n s_mth_eq, exact (s_pos (nat.lt.step m_lt_n) s_mth_eq) },
    { suffices : g.convergents (n + 1) = g'.convergents n, by -- invoke the IH for the squashed gcf
      { rwa ← IH,
        assume gp' m m_lt_n s_mth_eq',
        -- case distinction on m + 1 = n or m + 1 < n
        cases m_lt_n with n succ_m_lt_n,
        { -- the difficult case at the squashed position: we first obtain the values from
          -- the sequence
          obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.nth (m + 1) = some gp_succ_m, from
            option.ne_none_iff_exists'.mp not_terminated_at_n,
          obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.nth m = some gp_m, from
            g.s.ge_stable m.le_succ s_succ_mth_eq,
          -- we then plug them into the recurrence
          suffices : 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b, by
          { have ot : g'.s.nth m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩, from
              squash_seq_nth_of_not_terminated mth_s_eq s_succ_mth_eq,
            have : gp' = ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩, by cc,
            rwa this },
          refine ⟨(s_pos (nat.lt.step m_lt_n) mth_s_eq).left, _⟩,
          refine add_pos (s_pos (nat.lt.step m_lt_n) mth_s_eq).right _,
          have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b := s_pos (lt_add_one $ m + 1) s_succ_mth_eq,
          exact (div_pos this.left this.right) },
        { -- the easy case: before the squashed position, nothing changes
          refine s_pos (nat.lt.step $ nat.lt.step succ_m_lt_n) _,
          exact eq.trans (squash_gcf_nth_of_lt succ_m_lt_n).symm s_mth_eq' } },
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `succ_nth_convergent_eq_squash_gcf_nth_convergent`.
      have : ∀ ⦃b⦄, g.partial_denominators.nth n = some b → b ≠ 0, by
      { assume b nth_part_denom_eq,
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.nth n = some gp ∧ gp.b = b, from
          exists_s_b_of_part_denom nth_part_denom_eq,
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm },
      exact succ_nth_convergent_eq_squash_gcf_nth_convergent this } }
end

end generalized_continued_fraction

open generalized_continued_fraction

namespace continued_fraction

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of a
(regular) continued fraction coincide. -/
theorem convergents_eq_convergents' [linear_ordered_field K] {c : continued_fraction K} :
  (↑c : generalized_continued_fraction K).convergents =
    (↑c : generalized_continued_fraction K).convergents' :=
begin
  ext n,
  apply convergents_eq_convergents',
  assume gp m m_lt_n s_nth_eq,
  exact ⟨zero_lt_one.trans_le ((c : simple_continued_fraction K).property m gp.a
      (part_num_eq_s_a s_nth_eq)).symm.le,
    c.property m gp.b $ part_denom_eq_s_b s_nth_eq⟩
end

end continued_fraction
