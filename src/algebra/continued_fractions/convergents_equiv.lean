/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.continuants_recurrence
import algebra.continued_fractions.terminated_stable
import tactic.linarith
/-!
# Equivalence of Convergent Computations for gcfs

## Summary

We show the equivalence of the convergents computations (recurrence relation (`convergents`) vs.
direct evaluation (`convergents'`)) for `gcf`s on linear ordered fields. We follow the proof from
[hardy1979introduction], Chapter 10.

## Main Theorems

- `generalized_continued_fraction.convergents_eq_convergents'` shows the equivalence under a strict
positivity restriction on the sequence.
- `continued_fractions.convergents_eq_convergents'` shows the equivalence for (regular) continued
fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [Hardy, Godfrey Harold and Wright, Edward Maitland, and others,
*An introduction to the theory of numbers*][hardy1979introduction]

## Tags

fractions, recurrence, equivalence
-/

variables {α : Type*} {n : ℕ}
namespace generalized_continued_fraction
open generalized_continued_fraction as gcf
variables {g : gcf α} {s : seq $ gcf.pair α}

/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. We hence keep them `private`.
-/

section squash
section with_division_ring
variable [division_ring α]

/--
Given a sequence of gcf.pairs `s = [(a₀, bₒ), (a₁, b₁), ...]`, `squash_seq s n`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squash_seq s 0 = [(a₀, bₒ + a₁ / b₁), (a₁, b₁),...]`.
If `s.terminated_at (n + 1)`, then `squash_seq s n = s`.
-/
private def squash_seq (s : seq $ gcf.pair α) (n : ℕ) : seq (gcf.pair α) :=
match prod.mk (s.nth n) (s.nth (n + 1)) with
| ⟨some gp_n, some gp_succ_n⟩ := seq.nats.zip_with
    -- return the squashed value at position `n`; otherwise, do nothing.
    (λ n' gp, if n' = n then ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ else gp) s
| _ := s
end

/-! We now prove some simple lemmas about the squashed sequence -/

/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
private lemma squash_seq_eq_self_of_terminated
(terminated_at_succ_n : s.terminated_at (n + 1)) :
  squash_seq s n = s :=
begin
  change s.nth (n + 1) = none at terminated_at_succ_n,
  cases s_nth_eq : (s.nth n);
  simp only [*, squash_seq]
end

/-- If the sequence already did not terminate position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
private lemma squash_seq_nth_of_not_terminated {gp_n gp_succ_n : gcf.pair α}
(s_nth_eq : s.nth n = some gp_n) (s_succ_nth_eq : s.nth (n + 1) = some gp_succ_n) :
  (squash_seq s n).nth n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ :=
by simp [*, squash_seq, (seq.zip_with_nth_some (seq.nats_nth n) s_nth_eq _)]

/-- The values below the squashed position stay the same. -/
private lemma squash_seq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squash_seq s n).nth m = s.nth m :=
begin
  cases s_succ_nth_eq : s.nth (n + 1),
  case option.none { rw (squash_seq_eq_self_of_terminated s_succ_nth_eq) },
  case option.some
  { obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.nth n = some gp_n, from
      s.ge_stable n.le_succ s_succ_nth_eq,
    obtain ⟨gp_m, s_mth_eq⟩ : ∃ gp_m, s.nth m = some gp_m, from
      s.ge_stable (le_of_lt m_lt_n) s_nth_eq,
    simp [*, squash_seq, (seq.zip_with_nth_some (seq.nats_nth m) s_mth_eq _),
      (ne_of_lt m_lt_n)] }
end

/-- Squashing at position `n + 1` and taking the tail is the same as sqashing the tail of the
sequence at position `n`. -/
private lemma squash_seq_succ_n_tail_eq_squash_seq_tail_n :
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
    ext m,
    cases decidable.em (m = n) with m_eq_n m_ne_n,
    { have : s.tail.nth n = some gp_succ_n, from (s.nth_tail n).trans s_succ_nth_eq,
      simp [*, squash_seq, seq.nth_tail, (seq.zip_with_nth_some (seq.nats_nth n) this),
        (seq.zip_with_nth_some (seq.nats_nth (n + 1)) s_succ_nth_eq)] },
    { have : s.tail.nth m = s.nth (m + 1), from s.nth_tail m,
      cases s_succ_mth_eq : s.nth (m + 1),
      all_goals { have s_tail_mth_eq, from this.trans s_succ_mth_eq },
      { simp only [*, squash_seq, seq.nth_tail, (seq.zip_with_nth_none' s_succ_mth_eq),
          (seq.zip_with_nth_none' s_tail_mth_eq)] },
      { simp [*, squash_seq, seq.nth_tail,
          (seq.zip_with_nth_some (seq.nats_nth (m + 1)) s_succ_mth_eq),
          (seq.zip_with_nth_some (seq.nats_nth m) s_tail_mth_eq)] }}}
end

/-- The auxiliary function `convergents'_aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
private lemma succ_succ_nth_convergent'_aux_eq_succ_nth_convergent'_aux_squash_seq :
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
      have : convergents'_aux s.tail (m + 2) = convergents'_aux (squash_seq s.tail m) (m + 1),by
      { have : s.tail.nth (m + 1) = some gp_succ_n, by simpa [seq.nth_tail] using s_succ_nth_eq,
        exact (IH _ this) },
      have : (squash_seq s (m + 1)).head = some gp_head, from
        (squash_seq_nth_of_lt m.succ_pos).trans s_head_eq,
      simp only [*, convergents'_aux, squash_seq_succ_n_tail_eq_squash_seq_tail_n] }}
end

/-! Let us now lift the squashing operation to gcfs. -/

/--
Given a gcf `g = [h; (a₀, bₒ), (a₁, b₁), ...]`, we have
- `squash_nth.gcf g 0 = [h + a₀ / b₀); (a₀, bₒ), ...]`,
- `squash_nth.gcf g (n + 1) = ⟨g.h, squash_seq g.s n⟩`
-/
private def squash_gcf (g : gcf α) : ℕ → gcf α
| 0 := match g.s.nth 0 with
  | none := g
  | some gp := ⟨g.h + gp.a / gp.b, g.s⟩
  end
| (n + 1) := ⟨g.h, squash_seq g.s n⟩

/-! Again, we derive some simple lemmas that are not really of interrest. This time for the
squashed gcf. -/

/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
private lemma squash_gcf_eq_self_of_terminated (terminated_at_n : terminated_at g n) :
  squash_gcf g n = g :=
begin
  cases n,
  case nat.zero
  { change g.s.nth 0 = none at terminated_at_n,
    simp only [convergents', squash_gcf, convergents'_aux, terminated_at_n] },
  case nat.succ
  { cases g, simp [(squash_seq_eq_self_of_terminated terminated_at_n), squash_gcf] }
end

/-- The values below the squashed position stay the same. -/
private lemma squash_gcf_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
  (squash_gcf g (n + 1)).s.nth m = g.s.nth m :=
by simp only [squash_gcf, (squash_seq_nth_of_lt m_lt_n)]

/-- `convergents'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
private lemma succ_nth_convergent'_eq_squash_gcf_nth_convergent' :
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
private lemma continuants_aux_eq_continuants_aux_squash_gcf_of_le {m : ℕ} :
  m ≤ n → continuants_aux g m = (squash_gcf g n).continuants_aux m :=
nat.strong_induction_on m
(begin
  clear m,
  assume m IH m_le_n,
  cases m with m',
  { refl },
  { cases n with n',
    { have : false, from m'.not_succ_le_zero m_le_n, contradiction }, -- 1 ≰ 0
    { cases m' with m'',
      { refl },
      { -- get some inequalities to instantiate the IH for m'' and m'' + 1
        have m'_lt_n : m'' + 1 < n' + 1, from m_le_n,
        have : m'' + 1 < m'' + 2, by linarith,
        have succ_m''th_conts_aux_eq := IH (m'' + 1) this (le_of_lt m'_lt_n),
        have : m'' < m'' + 2, by linarith,
        have m''th_conts_aux_eq := IH m'' this (le_of_lt $ lt_of_lt_of_le (by linarith) n'.le_succ),
        have : (squash_gcf g (n' + 1)).s.nth m'' = g.s.nth m'', from
          squash_gcf_nth_of_lt (by linarith),
        simp [continuants_aux, succ_m''th_conts_aux_eq, m''th_conts_aux_eq, this] }}}
end)

end with_division_ring

/-- The convergents coincide in the expected way at the squashed position if the parital denominator
at the squashed position is not zero. -/
private lemma succ_nth_convergent_eq_squash_gcf_nth_convergent [field α]
(nth_part_denom_ne_zero : ∀ {b : α}, g.partial_denominators.nth n = some b → b ≠ 0) :
  g.convergents (n + 1) = (squash_gcf g n).convergents n :=
begin
cases decidable.em (g.terminated_at n) with terminated_at_n not_terminated_at_n,
{ have : squash_gcf g n = g, from squash_gcf_eq_self_of_terminated terminated_at_n,
  simp only [this, (convergents_stable_of_terminated n.le_succ terminated_at_n)] },
{ obtain ⟨⟨a, b⟩, s_nth_eq⟩ : ∃ gp_n, g.s.nth n = some gp_n, from
    with_one.ne_one_iff_exists.elim_left not_terminated_at_n,
  have b_ne_zero : b ≠ 0, from nth_part_denom_ne_zero (part_denom_eq_s_b s_nth_eq),
  cases n with n',
  case nat.zero
  { suffices : (b * g.h + a) / b = g.h + a / b, by
      simpa [squash_gcf, s_nth_eq, convergent_eq_conts_a_div_conts_b,
        (continuants_recurrence_aux s_nth_eq zeroth_continuant_aux_eq_one_zero
        first_continuant_aux_eq_h_one)],
    calc
      (b * g.h + a) / b = b * g.h / b + a / b  : by ring -- requires `field` rather than `division_ring`
                    ... = g.h + a / b          : by rw (mul_div_cancel_left _ b_ne_zero) },
  case nat.succ
  { obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.nth n' = some gp_n', from
      g.s.ge_stable n'.le_succ s_nth_eq,
    -- Notations
    let g' := squash_gcf g (n' + 1),
    set predConts := g.continuants_aux (n' + 1) with succ_n'th_conts_aux_eq,
    set ppredConts := g.continuants_aux n' with n'th_conts_aux_eq,
    let pA := predConts.a, let pB := predConts.b, let ppA := ppredConts.a, let ppB := ppredConts.b,
    set predConts' := g'.continuants_aux (n' + 1) with succ_n'th_conts_aux_eq',
    set ppredConts' := g'.continuants_aux n' with n'th_conts_aux_eq',
    let pA' := predConts'.a, let pB' := predConts'.b, let ppA' := ppredConts'.a,
    let ppB' := ppredConts'.b,
    -- first compute the convergent of the squashed gcf
    have : g'.convergents (n' + 1)
         = ((pb + a / b) * pA' + pa * ppA') / ((pb + a / b) * pB' + pa * ppB'), by
    { have : g'.s.nth n' = some ⟨pa, pb + a / b⟩, by
        simpa only [squash_nth_gcf] using
          (squash_seq_nth_of_not_terminated s_n'th_eq s_nth_eq),
      rw [convergent_eq_conts_a_div_conts_b,
        (continuants_recurrence_aux this n'th_conts_aux_eq'.symm succ_n'th_conts_aux_eq'.symm)], },
    rw this,
    -- then compute the convergent of the original gcf by recursively unfolding the continuants
    -- computatin twice
    have : g.convergents (n' + 2)
         = (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB), by
    {
      -- use the recurrence once
      have : g.continuants_aux (n' + 2) = ⟨pb * pA + pa * ppA, pb * pB + pa * ppB⟩, from
        continuants_aux_recurrence s_n'th_eq n'th_conts_aux_eq.symm succ_n'th_conts_aux_eq.symm,
      -- and a second time
      rw [convergent_eq_conts_a_div_conts_b,
        (continuants_recurrence_aux s_nth_eq succ_n'th_conts_aux_eq.symm this)] },
    rw this,
    -- now use the fact that the continuants before position n are equal.
    suffices : ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB)
             = (b * (pb * pA + pa * ppA) + a * pA) / (b * (pb * pB + pa * ppB) + a * pB), by
    { obtain ⟨eq1, eq2, eq3, eq4⟩ : pA' = pA ∧ pB' = pB ∧ ppA' = ppA ∧ ppB' = ppB, by
        simp [*, (continuants_aux_eq_continuants_aux_squash_gcf_of_le $ le_refl $ n' + 1).symm,
          (continuants_aux_eq_continuants_aux_squash_gcf_of_le n'.le_succ).symm],
      symmetry,
      simpa only [eq1, eq2, eq3, eq4] },
    calc
          ((pb + a / b) * pA + pa * ppA) / ((pb + a / b) * pB + pa * ppB)
        = (pa * ppA + (pb + a / b) * pA) / (pa * ppB + (pb + a / b) * pB) : by ac_refl
    ... = (pa * ppA + (pb * b + a) / b * pA) /
          (pa * ppB + (pb * b + a) / b * pB)           : by simp only [add_div_eq_mul_add_div
                                                                       _ _ b_ne_zero]
    ... = (pa * ppA + (pb * b + a) * pA / b) /
          (pa * ppB + (pb * b + a) * pB / b)           : by simp only [div_mul_eq_mul_div]
    ... = ((pa * ppA * b + (pb * b + a) * pA) / b) /
          ((pa * ppB * b + (pb * b + a) * pB) / b)     : by simp only [add_div_eq_mul_add_div
                                                                           _ _ b_ne_zero]
    ... = ((pa * ppA * b + (pb * b + a) * pA) * b) /
          ((pa * ppB * b + (pb * b + a) * pB) * b)     : by rw [div_div_div_div_eq, (mul_comm b)]
    ... = (pa * ppA * b + (pb * b + a) * pA) /
          (pa * ppB * b + (pb * b + a) * pB)           : by rw (mul_div_mul_right' _ _ b_ne_zero)
    ... = (pa * ppA * b + pb * b * pA + a * pA) /
          (pa * ppB * b + pb * b * pB + a * pB)        : by simp only [add_mul, add_assoc]
    ... = (b * (pb * pA) + b * (pa * ppA) + a * pA) /
          (b * (pb * pB) + b * (pa * ppB) + a * pB)    : by simp only [(mul_comm _ b), mul_assoc b,
                                                            add_comm (b * (pa * _))]
    ... = (b * (pb * pA + pa * ppA) + a * pA) /
          (b * (pb * pB + pa * ppB) + a * pB)          : by simp only [
                                                            (mul_add b (pb * _) (pa * _))] }}
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
theorem convergents_eq_convergents' [linear_ordered_field α]
(s_pos : ∀ {gp : gcf.pair α} {m : ℕ}, m < n → g.s.nth m = some gp → 0 < gp.a ∧ 0 < gp.b) :
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
      have : ∀ ⦃gp m⦄, m < n → g.s.nth m = some gp → 0 < gp.a ∧ 0 < gp.b, by
        { assume _ _ m_lt_n s_mth_eq, exact (s_pos (nat.lt.step m_lt_n) s_mth_eq) },
      rw [(convergents_stable_of_terminated n.le_succ terminated_at_n), g'_eq_g, (IH this)] },
    { suffices : g.convergents (n + 1) = g'.convergents n, by -- invoke the IH for the squashed gcf
      { have : ∀ ⦃gp' m⦄, m < n → g'.s.nth m = some gp' → 0 < gp'.a ∧ 0 < gp'.b, by
        { assume gp' m m_lt_n s_mth_eq',
          -- case distinction on m + 1 = n or m + 1 < n
          cases m_lt_n with n succ_m_lt_n,
          { -- the difficult case at the squashed position: we first obtain the values from
            -- the sequence
            obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.nth (m + 1) = some gp_succ_m, from
              with_one.ne_one_iff_exists.elim_left not_terminated_at_n,
            obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.nth m = some gp_m, from
              g.s.ge_stable m.le_succ s_succ_mth_eq,
            -- we then plug them into the recurrence
            suffices : 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b, by {
              have : g'.s.nth m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩, from
                squash_seq_nth_of_not_terminated mth_s_eq s_succ_mth_eq,
              have : gp' = ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩, by cc,
              rwa this },
            split,
            { exact (s_pos (nat.lt.step m_lt_n) mth_s_eq).left },
            { have : 0 < gp_m.b, from (s_pos (nat.lt.step m_lt_n) mth_s_eq).right,
              have : 0 < gp_succ_m.a / gp_succ_m.b, by
              { have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b, from
                  s_pos (lt_add_one $ m + 1) s_succ_mth_eq,
                exact (div_pos this.left this.right) },
              linarith }
          },
          { -- the easy case: before the squashed position, nothing changes
            have : g.s.nth m = some gp', by {
              have : g'.s.nth m = g.s.nth m, from squash_gcf_nth_of_lt succ_m_lt_n,
              rwa this at s_mth_eq'
            },
            exact (s_pos (nat.lt.step $ nat.lt.step succ_m_lt_n) this) }},
        rwa [(IH this).symm] },
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `succ_nth_convergent_eq_squash_gcf_nth_convergent`.
      have : ∀ ⦃b⦄, g.partial_denominators.nth n = some b → b ≠ 0, by
      { assume b nth_part_denom_eq,
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.nth n = some gp ∧ gp.b = b, from
          obtain_s_b_of_part_denom nth_part_denom_eq,
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm },
      exact (succ_nth_convergent_eq_squash_gcf_nth_convergent this) }}
end

end generalized_continued_fraction

namespace continued_fraction
open generalized_continued_fraction as gcf
open simple_continued_fraction as scf
open continued_fraction as cf

/-- Shows that the recurrence relation (`convergents`) and direct evaluation (`convergents'`) of a
(regular) continued fraction coincide. -/
theorem convergents_eq_convergents' [linear_ordered_field α] {c : cf α} :
  (↑c : gcf α).convergents = (↑c : gcf α).convergents' :=
begin
  ext n,
  apply gcf.convergents_eq_convergents',
  assume gp m m_lt_n s_nth_eq,
  split,
  { have : gp.a = 1, from (c : scf α).property m gp.a (gcf.part_num_eq_s_a s_nth_eq),
    simp only [zero_lt_one, this] },
  { exact (c.property m gp.b $ gcf.part_denom_eq_s_b s_nth_eq) }
end

end continued_fraction
