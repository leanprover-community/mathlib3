/-
Copyright (c) 2022 Mario Carneiro, Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
import combinatorics.additive.salem_spencer

/-!
# Calculation of small Roth numbers

This file implements an algorithm to calculate small Roth numbers. This

The algorithm we implement is the BASIC2 algorithm from the reference.

## References

* [W. Gasarch, J. Glenn, C. Kruskal, *Finding Large 3-free sets I: The Small `n` Case]
  (https://www.cs.umd.edu/~gasarch/papers/3apI.pdf)
* Sequence [A003002](http://oeis.org/A003002) of the OEIS.

## Tags

Roth, arithmetic progression, average, three-free, algorithm
-/

open list nat

variables {α β : Type*} {l l₁ l₂ : list ℕ} {a b d m n : ℕ}

/-- `three_free a l` returns whether adding `a` to `l` keeps it three-free. -/
def three_free : ℕ → list ℕ → bool
| a []       := tt
| a (b :: l) := l.all (λ c, a + c ≠ b + b) && three_free a l

@[simp] lemma three_free_nil : three_free n [] := by exact rfl

lemma three_free.of_cons (hl : three_free a (b :: l)) : three_free a l := bool.band_elim_right hl

lemma three_free_iff_pairwise : three_free a l ↔ l.pairwise (λ b c, a + c ≠ b + b) :=
by induction l; simp [three_free, *, all_iff_forall]

lemma three_free.sublist (hl : three_free a l₂) (h : l₁ <+ l₂) : three_free a l₁ :=
by { rw three_free_iff_pairwise at hl ⊢, exact hl.sublist h }

lemma three_free_spec (hl : chain (>) a l) (h₁ : add_salem_spencer {n | n ∈ l}) :
  three_free a l ↔ add_salem_spencer {n | n ∈ a :: l} :=
begin
  rw [three_free_iff_pairwise, set_of_mem_cons, add_salem_spencer_insert],
  refine ⟨λ H, ⟨h₁, λ b c hb hc e, _, λ b c hb hc e, _⟩, λ H, _⟩,
  { cases H.forall_of_forall_of_flip _ _ hc hb e,
    { exact λ b hb, (add_lt_add_right (hl.rel hb) _).ne' },
    { exact (hl.pairwise transitive_gt).of_cons.imp_of_mem
        (λ b c hb hc h, (add_lt_add (hl.rel hc) h).ne') } },
  { exact absurd e (add_lt_add (hl.rel hb) (hl.rel hc)).ne },
  { exact pairwise.imp_mem.2 (pairwise_of_forall $ λ c b hc hb e,
      (H.2.1 hb hc e).not_gt $ hl.rel hb) }
end

/-- The Roth number algorithm invariant. -/
def roth_aux (a m d : ℕ) (l : list ℕ) : Prop :=
list.chain (>) m l → ∀ s : finset ℕ, (∀ x ∈ s, x < a + m) → s.filter (< m) = l.to_finset →
  add_salem_spencer (s : set ℕ) → s.card ≤ d + l.length

/-- The first side condition in the calculation of Roth numbers. The program branches to this
condition if `m ∈ s`. -/
def roth_aux₁ (a m d : ℕ) (l : list ℕ) : Prop :=
¬ three_free m l ∨ ∃ d', d = d' + 1 ∧ roth_aux a (m + 1) d' (m :: l)

/-- The second side condition in the calculation of Roth numbers. The program branches to this
condition if `m ∉ s`. -/
def roth_aux₂ (a m d : ℕ) (l : list ℕ) : Prop := roth_number_nat a ≤ d ∨ roth_aux a (m + 1) d l

lemma roth_aux_zero (m d : ℕ) (l : list ℕ) : roth_aux 0 m d l :=
begin
  intros h s hs₀ hs₁ hs₂,
  rw zero_add at hs₀,
  rw finset.filter_true_of_mem hs₀ at hs₁,
  rw [hs₁, card_to_finset, (h.pairwise transitive_gt).of_cons.nodup.dedup],
  exact le_add_self,
end

lemma roth_aux_succ (h₁ : roth_aux₂ a m d l) (h₂ : roth_aux₁ a m d l) : roth_aux (a + 1) m d l :=
begin
  intros hl s hs₀ hs₁ hs₂,
  have hls : ∀ ⦃x⦄, x ∈ l → x ∈ s := λ x,
    by { rw [←mem_to_finset, ←hs₁, finset.mem_filter], exact and.left },
  by_cases hm : m ∈ s,
  { obtain (h₂ | ⟨d, rfl, h₂⟩) := h₂,
    { rw [three_free_spec hl (hs₂.mono hls), set_of_mem_cons] at h₂,
      exact (h₂ $ hs₂.mono $ set.insert_subset.2 ⟨hm, hls⟩).elim },
    { rw [←finset.insert_eq_of_mem hm, add_right_comm],
      simp_rw add_right_comm _ 1 at hs₀,
      refine h₂ (hl.cons $ lt_succ_self _) (insert m s) _ _ _,
      refine λ x hx, (finset.mem_insert.1 hx).elim (λ h, h.le.trans_lt $
        lt_add_of_nonneg_of_lt a.zero_le m.lt_succ_self) (hs₀ _),
      { rw [finset.filter_insert, if_pos m.lt_succ_self, to_finset_cons, ←hs₁],
        ext b,
        simp_rw [finset.mem_insert, finset.mem_filter],
        exact or_congr_right
          (λ hb, and_congr_right' $ lt_succ_iff_lt_or_eq.trans $ or_iff_left hb) },
      { rwa finset.insert_eq_of_mem hm } } },
  { cases h₁,
    { have hl₃ := (hl.pairwise transitive_gt).of_cons.nodup,
      rw [←finset.filter_card_add_filter_neg_card_eq_card (< m), hs₁, add_comm,
        to_finset_card_of_nodup hl₃, add_le_add_iff_right],
      rw [←add_tsub_cancel_right a (1 + m), ←add_assoc, ←add_roth_number_Ico, add_comm] at h₁,
      refine ((hs₂.mono $ finset.filter_subset _ _).le_add_roth_number $ λ b hb, _).trans h₁,
      rw finset.mem_filter at hb,
      exact finset.mem_Ico.2 ⟨succ_le_iff.2 $ (not_lt.1 hb.2).lt_of_ne' $
        ne_of_mem_of_not_mem hb.1 hm, hs₀ _ hb.1⟩ },
    { simp_rw add_right_comm _ 1 at hs₀,
      refine h₁ _ _ hs₀ _ hs₂,
      { cases hl with _ _ b l hb hl',
        { exact chain.nil },
        { exact hl'.cons (gt_trans m.lt_succ_self hb) } },
      { ext b,
        rw [←hs₁, finset.mem_filter, finset.mem_filter, lt_succ_iff_lt_or_eq],
        exact and_congr_right (λ hb, or_iff_left $ ne_of_mem_of_not_mem hb hm) } } }
end

lemma roth_aux₂_left (h : roth_number_nat a ≤ d) : roth_aux₂ a m d l := or.inl h
lemma roth_aux₂_right (h : roth_aux a (m + 1) d l) : roth_aux₂ a m d l := or.inr h

lemma roth_aux₁_left (h : ¬ three_free m l) : roth_aux₁ a m d l := or.inl h
lemma roth_aux₁_right (h : roth_aux a (m + 1) d (m :: l)) : roth_aux₁ a m (d + 1) l :=
or.inr ⟨_, rfl, h⟩

lemma roth_aux_out (h : roth_aux n 0 d []) : roth_number_nat n ≤ d :=
begin
  rw roth_aux at h,
  simp only [add_zero, to_finset_nil, set.set_of_false, add_salem_spencer_empty,
    finset.filter_false, eq_self_iff_true, length, forall_true_left, chain.nil, not_lt_zero'] at h,
  obtain ⟨s, hs₀, hs₁, hs₂⟩ := add_roth_number_spec (finset.range n),
  convert h s _ hs₂,
  { exact hs₁.symm },
  { exact λ x hx, finset.mem_range.1 (hs₀ hx) }
end

meta def tactic.roth_auto_step : tactic unit :=
do t ← tactic.target,
   match t with
   | `(roth_aux 0 _ _ _) := `[refine roth_aux_zero _ _ _]
   | `(roth_aux _ _ _ _) := tactic.refine ``(roth_aux_succ _ _)
   | _ := tactic.fail "no"
   end

meta def tactic.interactive.roth_start : tactic unit :=
`[refine roth_aux_out _] >> tactic.roth_auto_step

meta def tactic.interactive.roth_leaf : tactic unit :=
do t ← tactic.target,
  match t with
  | `(roth_aux₂ _ _ _ _) := `[refine roth_aux₂_left _]
  | `(roth_aux₁ _ _ _ _) :=
      `[exact roth_aux₁_left dec_trivial] <|> tactic.trace "Try this: roth_node"
  | _ := tactic.fail "goal isn't a roth proof"
  end

meta def tactic.interactive.roth_node : tactic unit :=
do t ← tactic.target,
  match t with
  | `(roth_aux₂ _ _ _ _) := `[refine roth_aux₂_right _] >> tactic.roth_auto_step
  | `(roth_aux₁ _ _ _ _) := `[refine roth_aux₁_right _] >> tactic.roth_auto_step
  | _ := tactic.fail "goal isn't a roth proof"
  end

example : roth_number_nat 3 ≤ 2 → roth_number_nat 4 ≤ 3 → roth_number_nat 8 ≤ 4 →
  roth_number_nat 10 ≤ 5 :=
begin
  intros h₃ h₄ h₈,
  roth_start,
  { roth_node,
    { roth_leaf,
      sorry },
    roth_node,
    { roth_leaf,
      sorry },
    roth_node,
    { roth_node,
      { roth_node,
        { roth_leaf,
          sorry },
        roth_node,
        { roth_leaf,
          sorry },
        roth_node,
        { roth_node,
          { roth_leaf,
            sorry },
          roth_leaf },
        roth_leaf },
      roth_node,
      { roth_node,
        { roth_leaf,
          sorry },
        { roth_leaf } },
      roth_node,
      { roth_node,
        { roth_node,
          { roth_leaf,
            sorry },
          roth_leaf },
        roth_leaf },
      roth_leaf },
    roth_leaf },
  roth_node,
  { roth_leaf,
    sorry },
  roth_node,
  { roth_node,
    { roth_node,
      { roth_node,
        { roth_leaf,
          sorry },
        roth_node,
        { roth_leaf,
          sorry },
        roth_node,
        { roth_node,
          { roth_leaf,
            sorry },
          roth_node,
          { roth_node },
          roth_leaf },
        roth_leaf },
      roth_node,
      { roth_node,
        { roth_leaf,
          sorry },
        roth_node,
        { roth_node,
          { roth_leaf,
            sorry },
          roth_leaf },
        roth_leaf },
      roth_node,
      { roth_node,
        { roth_node,
          { roth_leaf,
            sorry },
          roth_leaf },
        roth_leaf },
      roth_leaf },
    roth_node,
    { roth_node,
      { roth_node,
        { roth_leaf,
          sorry },
        roth_leaf },
      roth_leaf },
    roth_node,
    { roth_node,
      { roth_node,
        { roth_node,
          { roth_leaf,
            sorry },
          roth_leaf },
        roth_leaf },
      roth_leaf },
    roth_leaf },
  roth_leaf,
end
