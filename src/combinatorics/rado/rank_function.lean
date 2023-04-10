/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import combinatorics.rado.auxiliary

/-!
# Rank functions

We define the type of rank functions on a type `α` and prove some properties.

See the docstring of `rank_fn` for the definition.
-/

section rk_fn_def

variables (α : Type*) [decidable_eq α]

/-- A *rank function* on a type `α` is a function `r` from `finset α` to natural numbers such that:
* `r ∅ = 0`
* `r s ≤ r ({a} ∪ s)`
* `r ({a} ∪ s) ≤ r s + 1`,
* `r ({a} ∪ s) = r s` and `r ({b} ∪ s) = r s` imply `r ({a, b} ∪ s) = r s`

(This definition is equivalent to the definition one can find on the
(Wikipedia page for matroids)[https://en.wikipedia.org/wiki/Matroid].
But note that we do not assume that the base type `α` is finite.)
-/
@[ext]
structure rank_fn :=
(to_fun : finset α → ℕ)
(empty' : to_fun ∅ = 0)
(le_insert' : ∀ a s, to_fun s ≤ to_fun (insert a s))
(insert_le' : ∀ a s, to_fun (insert a s) ≤ to_fun s + 1)
(dep' : ∀ {s a b}, to_fun (insert a s) = to_fun s → to_fun (insert b s) = to_fun s →
          to_fun (insert b (insert a s)) = to_fun s)

end rk_fn_def

namespace rank_fn

open finset

variables {α: Type*} [decidable_eq α]

/-- Set up coercion of rank functions to functions `finset α → ℕ`. -/
instance : has_coe_to_fun (rank_fn α) (λ _, finset α → ℕ) := {coe := rank_fn.to_fun}

lemma coe_fn_injective : function.injective (coe_fn : rank_fn α → finset α → ℕ) := rank_fn.ext

/-- The rank functions on `α` inherit a partial order from functions `finset α → ℕ`. -/
instance : partial_order (rank_fn α) :=
partial_order.lift (coe_fn : rank_fn α → (finset α → ℕ)) coe_fn_injective

@[simp]
lemma empty (r : rank_fn α) : r ∅ = 0 := r.empty'

lemma le_insert (r : rank_fn α) (a : α) (s : finset α) : r s ≤ r (insert a s) := r.le_insert' a s

lemma insert_le (r : rank_fn α) (a : α) (s : finset α) : r (insert a s) ≤ r s + 1 :=
r.insert_le' a s

lemma dep (r : rank_fn α) {s : finset α} {a b : α} (h₁ : r (insert a s) = r s)
  (h₂ : r (insert b s) = r s) : r (insert b (insert a s)) = r s :=
r.dep' h₁ h₂

/-- The rank of `s` enlarged by `a` is either equal to the rank of `s` or larger by `1`. -/
lemma insert_eq_or (r : rank_fn α) (a : α) (s : finset α) :
  r (insert a s) = r s ∨ r (insert a s) = r s + 1 :=
(r.insert_le a s).eq_or_lt.elim or.inr (λ h, or.inl $ nat.eq_of_le_of_lt_succ (r.le_insert _ _) h)

/-- A rank function is monotone with respect to subsets. -/
lemma mono_union (r : rank_fn α) (s t : finset α) : r s ≤ r (s ∪ t) :=
begin
  refine t.induction_on _ (λ a t h ih, _),
  { rw union_empty },
  { exact ih.trans ((union_insert a s t).symm ▸ r.le_insert a (s ∪ t)), }
end

/-- A rank function is monotone with respect to subsets. -/
lemma mono (r : rank_fn α) {s t : finset α} (h : s ⊆ t) : r s ≤ r t :=
begin
  convert r.mono_union s t,
  exact right_eq_union_iff_subset.mpr h,
end

/-- If adding `a` to `s` does not increase the rank, then adding `a` to `insert b s`
also does not increase the rank. -/
lemma stationary_insert (r : rank_fn α) {s : finset α} {a : α} (b : α) (h : r (insert a s) = r s) :
  r (insert a (insert b s)) = r (insert b s) :=
begin
  rw insert.comm,
  cases r.insert_eq_or b s with h' h',
  { exact h'.symm ▸ r.dep h h', },
  { refine le_antisymm ((r.insert_le b _).trans _)
             (r.mono $ insert_subset_insert _ $ subset_insert _ _),
    rw [h, h'], },
end

/-- If adding `a` to `s` does not increase the rank, then adding `a` to any larger set
also does not increase the rank. -/
lemma stationary_union (r : rank_fn α) (s t : finset α) {a : α}
  (ha : r (insert a s) = r s) : r (insert a (s ∪ t)) = r (s ∪ t) :=
begin
  refine t.induction_on _ (λ a t h ih, _),
  { rwa union_empty, },
  { rw union_insert,
    exact r.stationary_insert _ ih , }
end

/-- If adding `a` to `s` does not increase the rank, then adding `a` to any larger set
also does not increase the rank. -/
lemma stationary_subset (r : rank_fn α) {s t : finset α} (hst : s ⊆ t) {a : α}
  (h : r (insert a s) = r s) : r (insert a t) = r t :=
by convert r.stationary_union s t h; exact right_eq_union_iff_subset.mpr hst

/-- If enlarging `s` to `t` does not change the rank, then the same holds when
we enlarge `s ∪ u` to `t ∪ u`. -/
lemma stationary (r : rank_fn α) {s t : finset α} (u : finset α) (hst : s ⊆ t)
  (hr : r s = r t) : r (s ∪ u) = r (t ∪ u) :=
begin
  refine u.induction_on _ (λ a u h₁ h₂, _),
  { simpa only [union_empty], },
  { refine le_antisymm (r.mono $ union_subset_union hst subset.rfl) _,
    rw [union_insert, union_insert],
    cases eq_or_ne (r (insert a (s ∪ u))) (r (s ∪ u)) with h h,
    { rw [h, h₂],
      have H := (r.stationary_union _ t h).le,
      have hu : s ∪ u ∪ t = t ∪ u,
      { rw [union_assoc, union_comm u, ← union_assoc, union_eq_right_iff_subset.mpr hst], },
      rwa hu at H, },
    { rw [(r.insert_eq_or a (s ∪ u)).resolve_left h, h₂],
      exact r.insert_le _ _, } }
end

/- The submodularity property is not needed for the proof of Rado's Theorem;
   we include it for completeness. -/

/-- A rank function is "submodular". -/
lemma submodular' (r : rank_fn α) (s t u : finset α) :
  r s + r (s ∪ t ∪ u) ≤ r (s ∪ t) + r (s ∪ u) :=
begin
  refine t.induction_on _ (λ a t h ih, _),
  { rw union_empty, },
  { rw [union_insert, insert_union],
    cases r.insert_eq_or a (s ∪ t) with H H,
    { rw r.stationary_union _ u H,
      exact ih.trans (nat.add_le_add_right (r.le_insert _ _) _), },
    { rw H,
      refine (nat.add_le_add_left (r.insert_le _ _) _).trans _,
      rw [← add_assoc, nat.succ_add],
      exact nat.add_le_add_right ih _, } }
end

/-- A rank function is "submodular". -/
lemma submodular (r : rank_fn α) (s t : finset α) : r (s ∩ t) + r (s ∪ t) ≤ r s + r t :=
begin
  convert r.submodular' (s ∩ t) s t,
  repeat {rw [union_distrib_right, union_self, inter_union_self],},
  rw [inter_comm, union_distrib_right, union_self, inter_union_self],
end

/-- The rank of a union of two sets is bounded by the sum of their ranks. -/
lemma union (r : rank_fn α) (s t : finset α) : r (s ∪ t) ≤ r s + r t :=
le_add_self.trans (r.submodular s t)

/-- If the rank of `s` does not increase when we add any element of `t`, then
`s ∪ t` and `s` have the same rank. -/
lemma stationary' (r : rank_fn α) {s t : finset α} (h : ∀ a ∈ t, r (insert a s) = r s) :
  r (s ∪ t) = r s :=
begin
  revert h,
  refine t.induction_on _ (λ _ _ _ h', _),
  { simp only [implies_true_iff, union_empty, eq_self_iff_true], },
  { intro h,
    rw [← h' (λ a ha, h a $ mem_insert_of_mem ha), union_insert],
    exact r.stationary_union _ _ (h _ $ mem_insert_self _ _), }
end

variables (α)

/-- Cardinality of finsets is a rank function. -/
def card_rk : rank_fn α :=
{ to_fun := card,
  empty' := card_empty,
  le_insert' := λ a s, card_le_of_subset $ subset_insert _ _,
  insert_le' := card_insert_le,
  dep' := λ s a b ha hb, begin
    have h : insert b (insert a s) = s,
    { refine subset_antisymm (λ c hc, _) _,
      { rcases mem_insert.mp hc with rfl | hc₁,
        { exact (card_insert_eq_card_iff c s).mp hb, },
        { rcases mem_insert.mp hc₁ with rfl | hc₂,
          exacts [(card_insert_eq_card_iff c s).mp ha, hc₂], } },
      { exact subset_trans (subset_insert _ _) (subset_insert _ _), } },
    rw h,
  end }

variables {α}

instance : inhabited (rank_fn α) := { default := card_rk α }

@[simp]
lemma card_rk_eq_card (s : finset α) : card_rk α s = s.card := rfl

/-- The rank of a set `s` is bounded by its cardinality. -/
lemma le_card (r : rank_fn α) (s : finset α) : r s ≤ s.card :=
begin
  refine s.induction_on _ (λ a s h₁ h₂, _),
  { simp only [card_empty, rank_fn.empty], },
  { by_cases h : a ∈ s,
    { rwa insert_eq_of_mem h, },
    { exact ((r.insert_le a s).trans (add_le_add_right h₂ _)).trans_eq
              (card_insert_of_not_mem h).symm, } }
end

/-- Any rank function is bounded by the cardinality function. -/
lemma le_card_rk (r : rank_fn α) : r ≤ card_rk α := le_card r

/-- If the rank of `s` equals the cardinality of `s`, then the same is true for
all subsets of `s`. We state this using `s.card ≤ r s`; the reverse inequality holds always;
see `rank_fn.le_card`. -/
lemma card_le_subset (r : rank_fn α) {s t : finset α} (hs : s.card ≤ r s) (hts : t ⊆ s) :
  t.card ≤ r t :=
begin
  replace hs := le_antisymm (r.le_card _) hs,
  nth_rewrite 0 [← union_sdiff_of_subset hts] at hs, rw union_comm at hs,
  refine @nat.le_of_add_le_add_left (s \ t).card _ _ _,
  refine (((card_sdiff_add_card_eq_card hts).trans hs.symm).trans_le (r.union _ _)).trans _,
  exact ((nat.add_le_add_right (r.le_card _) _).trans $ nat.add_le_add_left rfl.le _),
end

end rank_fn
