/-
Copyright (c) 2022 Russell Emerine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Russell Emerine
-/
import computability.regular_expression_to_NFA.defs
import computability.regular_expression_to_NFA.star

/-!
# Proof That Converting Regular Expressions to NFA's is Correct

Inductively proves that `regular_expression.to_NFA` converts a regular expression to an NFA with
the same accepting language.

TODO: 
 * possibly merge the files into computability/regular_expression? or change filenames?
 * mark things as @simp?
 * clean up things
-/

universe u

variables {α : Type u}

namespace regular_expression

lemma zero_to_NFA_correct : (zero : regular_expression α).matches = zero.to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx, cases hx, },
  { assume hx,
    rcases hx with ⟨q, accept, eval⟩,
    cases accept, },
end

lemma epsilon_to_NFA_correct : (epsilon : regular_expression α).matches = epsilon.to_NFA.accepts :=
begin
  ext,
  split,
  { rintros ⟨⟨⟩⟩, repeat { fconstructor, }, },
  { rintros ⟨q, accept, eval⟩,
    cases accept,
    revert eval,
    rw ← x.reverse_reverse,
    induction x.reverse,
    case nil { simp, },
    case cons : a as ih
    { assume hx,
      rw [list.reverse_cons, NFA.eval_append_singleton, NFA.mem_step_set] at hx,
      rcases hx with ⟨q, mem, step⟩,
      cases step, }, },
end

theorem char_to_NFA_correct {a : α} : (char a).matches = (char a).to_NFA.accepts :=
begin
  ext,
  split,
  { rintros ⟨⟨⟩⟩,
    refine ⟨tt, rfl, _⟩,
    unfold NFA.eval NFA.eval_from list.foldl,
    rw NFA.mem_step_set,
    repeat { fconstructor, }, },
  { rintros ⟨q, accept, eval⟩,
    cases q,
    case ff { contradiction, },
    clear accept,
    revert eval,
    rw ← x.reverse_reverse,
    cases x.reverse with c as,
    case nil { assume hx, contradiction, },
    assume hx,
    unfold NFA.eval NFA.eval_from at hx,
    simp only [
      list.reverse_cons,
      list.foldl_append,
      list.foldl_cons,
      set.mem_singleton_iff,
      regular_expression.matches_char,
      list.foldl_nil] at *,
    rw NFA.mem_step_set at hx,
    rcases hx with ⟨p, mem, step⟩,
    cases p,
    case tt { rcases step with ⟨_, _, _⟩, contradiction, },
    revert mem,
    cases as with b as,
    case nil
    { assume _,
      rcases step with ⟨_, eq, _⟩,
      rw eq,
      exact rfl, },
    assume h,
    simp only [
      list.reverse_cons,
      list.foldl_append,
      list.foldl_cons,
      list.foldl_nil,
      list.append_assoc,
      list.singleton_append] at *,
    rcases h with ⟨S, ⟨q, range⟩, mem⟩,
    rw ← range at mem,
    simp only [exists_prop, set.mem_Union] at mem,
    rcases mem with ⟨_, _, _, _⟩,
    contradiction, },
end

lemma plus_to_NFA_correct
  {r₁ r₂ : regular_expression α}
  (hr₁ : r₁.matches = r₁.to_NFA.accepts)
  (hr₂ : r₂.matches = r₂.to_NFA.accepts)
  : (r₁.plus r₂).matches = (r₁.plus r₂).to_NFA.accepts :=
begin
  ext,
  split,
  { assume hx,
    cases hx,
    case inl
    { rw hr₁ at hx, clear hr₁ hr₂,
      rw set.mem_def at *,
      unfold NFA.accepts NFA.eval NFA.eval_from at *,
      rcases hx with ⟨q, accept, eval⟩,
      refine ⟨sum.inl q, accept, _⟩, clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse with a as ih generalizing q,
      case nil { exact id, },
      assume mem,
      rw [list.reverse_cons, list.foldl_append, list.foldl_cons, list.foldl_nil] at *,
      rcases mem with ⟨S, ⟨p, range⟩, mem⟩,
      rw [← range, set.mem_Union, exists_prop] at mem,
      rcases mem with ⟨mem, step⟩,
      rw NFA.mem_step_set,
      exact ⟨sum.inl p, ih p mem, step⟩, },
    case inr
    { rw hr₂ at hx, clear hr₁ hr₂,
      rw set.mem_def at *,
      unfold NFA.accepts NFA.eval NFA.eval_from at *,
      rcases hx with ⟨q, accept, eval⟩,
      refine ⟨sum.inr q, accept, _⟩, clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse with a as ih generalizing q,
      case nil { exact id, },
      assume mem,
      rw [list.reverse_cons, list.foldl_append, list.foldl_cons, list.foldl_nil] at *,
      rcases mem with ⟨S, ⟨p, range⟩, mem⟩,
      rw [← range, set.mem_Union, exists_prop] at mem,
      rcases mem with ⟨mem, step⟩,
      rw NFA.mem_step_set,
      exact ⟨sum.inr p, ih p mem, step⟩, }, },
  { rintros ⟨q, accept, eval⟩,
    cases q,
    case inl
    { left,
      rw hr₁, clear hr₁ hr₂,
      refine ⟨q, accept, _⟩, clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse with a as ih generalizing q,
      case nil { exact id, },
      assume h,
      unfold NFA.eval NFA.eval_from at *,
      rw [list.reverse_cons, list.foldl_append, list.foldl_cons, list.foldl_nil] at *,
      rcases h with ⟨S, ⟨p, range⟩, mem⟩,
      rw ← range at mem,
      rw [set.mem_Union, exists_prop] at mem,
      rcases mem with ⟨mem, step⟩,
      rw NFA.mem_step_set,
      cases p,
      case inl { exact ⟨p, ih p mem, step⟩, },
      case inr { cases step, }, },
    case inr
    { right,
      rw hr₂, clear hr₁ hr₂,
      refine ⟨q, accept, _⟩, clear accept,
      revert eval,
      rw ← x.reverse_reverse,
      induction x.reverse with a as ih generalizing q,
      case nil { exact id, },
      assume h,
      unfold NFA.eval NFA.eval_from at *,
      rw [list.reverse_cons, list.foldl_append, list.foldl_cons, list.foldl_nil] at *,
      rcases h with ⟨S, ⟨p, range⟩, mem⟩,
      rw ← range at mem,
      rw [set.mem_Union, exists_prop] at mem,
      rcases mem with ⟨mem, step⟩,
      rw NFA.mem_step_set,
      cases p,
      case inl { cases step, },
      case inr { exact ⟨p, ih p mem, step⟩, }, }, },
end

lemma comp_to_NFA_eval₁ {r₁ r₂ : regular_expression α} {x : list α} (q : r₁.state) :
  q ∈ r₁.to_NFA.eval x ↔ sum.inl q ∈ (r₁.comp r₂).to_NFA.eval x :=
begin
  rw ← x.reverse_reverse,
  induction x.reverse with a as ih generalizing q,
  case nil { exact ⟨id, id⟩, },
  split,
  { assume h,
    rw [list.reverse_cons, NFA.eval_append_singleton, NFA.mem_step_set] at *,
    rcases h with ⟨p, eval, step⟩,
    rw ih p at eval,
    exact ⟨sum.inl p, eval, step⟩, },
  { assume h,
    rw [list.reverse_cons, NFA.eval_append_singleton, NFA.mem_step_set] at *,
    rcases h with ⟨p, eval, step⟩,
    cases p,
    case inl { rw ← ih p at eval, exact ⟨p, eval, step⟩, },
    case inr { cases step, }, },
end

lemma comp_to_NFA_eval₂ {r₁ r₂ : regular_expression α} {x y : list α} (q : r₂.state)
(accepts : r₁.to_NFA.accepts x) :
  q ∈ r₂.to_NFA.eval y → sum.inr q ∈ (r₁.comp r₂).to_NFA.eval_from ((r₁.comp r₂).to_NFA.eval x) y :=
begin
  rw ← y.reverse_reverse,
  induction y.reverse generalizing q,
  case nil
  { assume h,
    rcases accepts with ⟨p, accept, eval⟩,
    rw @comp_to_NFA_eval₁ _ _ r₂ _ p at eval,
    revert eval,
    rw ← x.reverse_reverse at *,
    cases x.reverse with a as,
    case nil { assume eval, exact ⟨h, p, accept, eval⟩, },
    assume eval,
    rw [list.reverse_nil, NFA.eval_from_nil],
    rw [list.reverse_cons, NFA.eval_append_singleton, NFA.mem_step_set] at *,
    rcases eval with ⟨r, mem, step⟩,
    refine ⟨r, mem, _⟩,
    cases r,
    case inl { exact ⟨h, p, accept, step⟩, },
    case inr { cases step, }, },
  case cons : b bs ih
  { assume h,
    simp only [
      list.reverse_cons,
      NFA.eval_append_singleton,
      NFA.eval_from_append_singleton,
      NFA.mem_step_set] at *,
    rcases h with ⟨p, mem, step⟩,
    refine ⟨sum.inr p, ih p mem, step⟩, },
end

lemma comp_to_NFA_correct
  {r₁ r₂ : regular_expression α}
  (hr₁ : r₁.matches = r₁.to_NFA.accepts)
  (hr₂ : r₂.matches = r₂.to_NFA.accepts)
  : (r₁.comp r₂).matches = (r₁.comp r₂).to_NFA.accepts :=
begin
  ext,
  split,
  { rintros ⟨y, z, hy, hz, comp⟩,
    rw hr₁ at hy,
    rw hr₂ at hz,
    rw ← comp,
    clear hr₁ hr₂ comp x,
    rw set.mem_def at *,
    rw ← z.reverse_reverse at *,
    cases z.reverse with b bs,
    case nil
    { rcases hy with ⟨q, q_accept, q_eval⟩,
      rcases hz with ⟨p, p_accept, p_eval⟩,
      simp only [list.append_nil, NFA.eval_nil, list.reverse_nil] at *,
      rw comp_to_NFA_eval₁ q at q_eval,
      exact ⟨sum.inl q, ⟨q_accept, p, p_accept, p_eval⟩, q_eval⟩, },
    rcases hz with ⟨q, accept, eval⟩,
    refine ⟨sum.inr q, accept, _⟩,
    rw list.reverse_cons at *,
    rw ← list.append_assoc,
    rw [NFA.eval_append_singleton, NFA.mem_step_set] at *,
    rcases eval with ⟨p, mem, step⟩,
    refine ⟨sum.inr p, _, step⟩,
    unfold NFA.eval NFA.eval_from,
    rw list.foldl_append,
    exact comp_to_NFA_eval₂ p hy mem, },
  { rintros ⟨q, accept, eval⟩,
    cases q,
    case inl
    { rcases accept with ⟨accept, nil⟩,
      refine ⟨x, [], _, _, by simp⟩,
      { rw hr₁,
        refine ⟨q, accept, _⟩, clear accept,
        revert eval,
        rw ← x.reverse_reverse,
        induction x.reverse with a as ih generalizing q,
        case nil { exact id, },
        assume h,
        unfold NFA.eval NFA.eval_from at *,
        rw [
          list.reverse_cons,
          list.foldl_append,
          list.foldl_cons,
          list.foldl_nil,
          NFA.mem_step_set] at *,
        rcases h with ⟨p, mem, step⟩,
        cases p,
        case inl { exact ⟨p, ih p mem, step⟩, },
        case inr { cases step, }, },
      { rw hr₂,
        rcases nil with ⟨q, accept, eval⟩,
        exact ⟨q, accept, eval⟩, }, },
    case inr
    { suffices : ∀ x q,
        sum.inr q ∈ (r₁.comp r₂).to_NFA.eval x
        → ∃ y z,
            y ∈ r₁.to_NFA.accepts
          ∧ q ∈ r₂.to_NFA.eval z
          ∧ y ++ z = x,
      { specialize this x q eval,
        rcases this with ⟨y, z, y_accepts, z_eval, append⟩,
        refine ⟨y, z, by simpa [hr₁], _, by assumption⟩,
        rw hr₂,
        exact ⟨q, accept, z_eval⟩, },
      clear accept eval q hr₁ hr₂,
      assume x q,
      rw ← x.reverse_reverse,
      induction x.reverse with a as ih generalizing q,
      case nil
      { rintros ⟨start, nil⟩,
        refine ⟨[], [], _, start, by simp⟩,
        unfold NFA.accepts at *,
        simpa, },
      assume h,
      unfold NFA.eval NFA.eval_from,
      rw list.reverse_cons at *,
      rw [NFA.eval_append_singleton, NFA.mem_step_set] at h,
      rcases h with ⟨p, mem, step⟩,
      cases p,
      case inl
      { rcases step with ⟨start, r, accept, step⟩,
        refine ⟨as.reverse ++ [a], [], _, start, by simp⟩,
        refine ⟨r, accept, _⟩,
        rw [NFA.eval_append_singleton, NFA.mem_step_set],
        rw ← comp_to_NFA_eval₁ p at mem,
        exact ⟨p, mem, step⟩, },
      case inr
      { rcases ih p mem with ⟨y, z, accepts, eval, append⟩,
        refine ⟨y, z ++ [a], accepts, _, by simp [← append]⟩,
        rw [list.foldl_append, list.foldl_cons, list.foldl_nil, NFA.mem_step_set],
        exact ⟨p, eval, step⟩, }, }, },
end

lemma star_to_NFA_correct {r : regular_expression α} (hr : r.matches = r.to_NFA.accepts)
  : (star r).matches = (star r).to_NFA.accepts :=
begin
  ext,
  rw star_iff_pow,
  split,
  { rintros ⟨n, h⟩,
    cases n,
    case zero
    { cases h,
      refine ⟨none, trivial, trivial⟩, },
    case succ
    { rw r.pow_eval x n hr at h,
      rcases h with ⟨q, accept, t⟩,
      exact ⟨some q, accept, (r.star_eval x q).mpr ⟨n, t⟩⟩, }, },
  { rintros ⟨q, accept, eval⟩,
    cases q,
    case none
    { use 0,
      rw ← x.reverse_reverse at *,
      cases x.reverse with a as,
      case nil { exact rfl, },
      rw [list.reverse_cons, NFA.eval_append_singleton, NFA.mem_step_set] at eval,
      rcases eval with ⟨q, mem, step⟩,
      cases q; cases step, },
    case some
    { rcases (r.star_eval x q).mp eval with ⟨n, t⟩,
      use n.succ,
      exact (r.pow_eval x n hr).mpr ⟨q, accept, t⟩, }, },
end

theorem to_NFA_correct (r : regular_expression α) : r.matches = r.to_NFA.accepts :=
begin
  induction r,
  case zero { exact zero_to_NFA_correct, },
  case epsilon { exact epsilon_to_NFA_correct, },
  case char : a { exact char_to_NFA_correct, },
  case plus : r₁ r₂ hr₁ hr₂ { exact plus_to_NFA_correct hr₁ hr₂, },
  case comp : r₁ r₂ hr₁ hr₂ { exact comp_to_NFA_correct hr₁ hr₂, },
  case star : r hr { exact star_to_NFA_correct hr, },
end

end regular_expression
