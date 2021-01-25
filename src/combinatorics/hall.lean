/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import data.fintype.basic
import data.rel
import data.set.finite

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $$X_1,X_2,\dots,X_n$$ of some given set
$$S$$, Hall in [Hall1935] gave a necessary and sufficient condition
for there to be a list of distinct elements $$x_1,x_2,\dots,x_n$$ with
$$x_i∈ X_i$$ for each $$i$$: it is when the union of any $$k$$ of
these subsets has at least $$k$$ elements.

This file proves this for an indexed family `s : ι → finset α` of
finite sets, with `[fintype ι]`, along with some variants of the
statement.  The list of distinct representatives is given by an
injective function `f : ι → α` such that `∀ i, f i ∈ s i`.

## Main statements
* `all_card_le_bind_card_iff_exists_injective` is in terms of `s : ι → finset α`.
* `all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `rel.image r {a}` is a finite set for all `a : α`.
* `all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Todo

* The theorem is still true even if `ι` is not a finite type.  The infinite case
  follows from a compactness argument.
* The statement of the theorem in terms of bipartite graphs is in preparation.

## Tags

Hall's Marriage Theorem, indexed families
-/

open finset

universes u v

namespace hall_marriage_theorem

lemma inj_of_dite_disjoint_inj {α β : Type*} (s : set α) [decidable_pred s]
  (f : s → β) (f' : sᶜ → β)
  (hf : function.injective f) (hf' : function.injective f')
  (im_disj : ∀ {x x' : α} {hx : x ∈ s} {hx' : ¬ x' ∈ s}, f ⟨x, hx⟩ ≠ f' ⟨x', hx'⟩) :
  function.injective (λ x, if h : x ∈ s then f ⟨x, h⟩ else f' ⟨x, h⟩) :=
begin
  { rintros x₁ x₂ (h : dite _ _ _ = dite _ _ _),
    split_ifs at h,
    { injection (hf h), },
    { exact (im_disj h).elim, },
    { exact (im_disj h.symm).elim, },
    { injection (hf' h), }, },
end

variables {α : Type u} {β : Type v} [fintype α]
variables (r : α → finset β)

theorem hall_hard_inductive_zero (hn : fintype.card α = 0) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  rw fintype.card_eq_zero_iff at hn,
  refine ⟨λ a, (hn a).elim, by tauto⟩,
end

variables [decidable_eq β]

lemma hall_cond_of_erase {r : α → finset β} {a : α} (b : β)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card)
  (A' : finset {a' : α | a' ≠ a}) :
  A'.card ≤ (A'.bind (λ a', (r a').erase b)).card :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  specialize ha (A'.image coe),
  rw [nonempty.image_iff, finset.card_image_of_injective A' subtype.coe_injective] at ha,
  by_cases he : A'.nonempty,
  { have ha' : A'.card < (A'.bind (λ x, r x)).card,
    { specialize ha he (λ h, by { have h' := mem_univ a, rw ←h at h', simpa using h' }),
      convert ha using 2,
      ext x,
      simp only [mem_image, mem_bind, exists_prop, set_coe.exists,
                 exists_and_distrib_right, exists_eq_right, subtype.coe_mk], },
    rw bind_erase,
    by_cases hb : b ∈ A'.bind (λ x, r x),
    { rw card_erase_of_mem hb,
      exact nat.le_pred_of_lt ha' },
    { rw erase_eq_of_not_mem hb,
      exact nat.le_of_lt ha' }, },
  { rw [nonempty_iff_ne_empty, not_not] at he,
    subst A',
    simp },
end

/--
First case of the inductive step: assuming that
`∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card`
and that the statement of Hall's Marriage Theorem is true for all
`α'` of cardinality ≤ `n`, then it is true for `α` of cardinality `n + 1`.
-/
lemma hall_hard_inductive_step_A {r : α → finset β} {n : ℕ} (hn : fintype.card α = n + 1)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β),
        by exactI fintype.card α' ≤ n →
                  (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
                  ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  haveI : nonempty α := by { rw [←fintype.card_pos_iff, hn], exact nat.succ_pos _, },
  haveI : decidable_eq α := by { classical, apply_instance },
  /- Choose an arbitrary element `a : α` and `b : r a`. -/
  let a := classical.arbitrary α,
  have ra_ne : (r a).nonempty,
  { rw ←finset.card_pos,
    apply nat.lt_of_lt_of_le nat.one_pos,
    convert hr {a},
    rw finset.singleton_bind, },
  rcases classical.indefinite_description _ ra_ne with ⟨b, hb⟩,
  /- Restrict to everything except `a` and `b`. -/
  let α' := {a' : α | a' ≠ a},
  let r' : α' → finset β := λ a', (r a').erase b,
  have card_α'_le : fintype.card α' ≤ n,
  { rw [set.card_ne_eq, hn],
    exact le_refl _, },
  rcases ih r' card_α'_le (hall_cond_of_erase b ha) with ⟨f', hfinj, hfr⟩,
  /- Extend the resulting function. -/
  refine ⟨λ x, if h : x = a then b else f' ⟨x, h⟩, _, _⟩,
  { rintro x₁ x₂,
    have key : ∀ {x}, b ≠ f' x,
    { intros x h,
      specialize hfr x,
      rw ←h at hfr,
      simpa using hfr, },
    by_cases h₁ : x₁ = a; by_cases h₂ : x₂ = a; simp [h₁, h₂, hfinj, key, key.symm], },
  { intro x,
    split_ifs with hx,
    { rwa hx },
    { specialize hfr ⟨x, hx⟩,
      rw mem_erase at hfr,
      exact hfr.2, }, },
end

lemma hall_cond_of_restrict {α : Type u} {r : α → finset β} {A : finset α}
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (A' : finset (A : set α)) :
  A'.card ≤ (A'.bind (λ a', r a')).card :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  convert hr (A'.image coe) using 1,
  { rw card_image_of_injective _ subtype.coe_injective, },
  { apply congr_arg,
    ext y,
    simp, },
end

lemma hall_cond_of_compl {α : Type u} {r : α → finset β} {A : finset α}
  (huA : A.card = (A.bind r).card)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (B : finset (Aᶜ : set α)) :
  B.card ≤ (B.bind (λ a'', r a'' \ A.bind r)).card :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  have : B.card = (A ∪ B.image coe).card - A.card,
  { rw [card_disjoint_union, nat.add_sub_cancel_left,
        card_image_of_injective _ subtype.coe_injective],
    simp only [disjoint_left, not_exists, mem_image, exists_prop, set_coe.exists,
               exists_and_distrib_right, exists_eq_right, subtype.coe_mk],
    intros a ha hA h,
    exact (hA ha).elim },
  rw [this, huA],
  apply (nat.sub_le_sub_right (hr _) _).trans _,
  rw ← card_sdiff,
  { have : (A ∪ B.image subtype.val).bind r \ A.bind r ⊆ B.bind (λ a'', r a'' \ A.bind r),
    { intros t,
      simp only [mem_bind, mem_sdiff],
      simp only [not_exists, mem_image, and_imp, exists_prop, mem_union, not_and,
                 exists_and_distrib_right, exists_eq_right, subtype.exists, subtype.coe_mk,
                 exists_imp_distrib],
      rintro a (ha | ⟨a', ha', rfl⟩) rat hA,
      { exact (hA a ha rat).elim },
      { exact ⟨⟨a', ha', rat⟩, hA⟩, } },
    exact (card_le_of_subset this).trans le_rfl, },
  { apply bind_subset_bind_of_subset_left,
    apply subset_union_left }
end

/--
Second case of the inductive step: assuming that
`∃ (A : finset α), A ≠ univ → A.card = (A.bind r).card`
and that the statement of Hall's Marriage Theorem is true for all
`α'` of cardinality ≤ `n`, then it is true for `α` of cardinality `n + 1`.
-/
lemma hall_hard_inductive_step_B {r : α → finset β} {n : ℕ} (hn : fintype.card α = n + 1)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β),
        by exactI fintype.card α' ≤ n →
                  (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
                  ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x)
  (A : finset α)
  (hA : A.nonempty)
  (hnA : A ≠ univ)
  (huA : A.card = (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  /- Restrict to `A` -/
  let α' := (A : set α),
  let r' : α' → finset β := λ a', r a',
  rw nat.add_one at hn,
  have card_α'_le : fintype.card α' ≤ n,
  { apply nat.le_of_lt_succ,
    rw ←hn,
    convert (card_lt_iff_ne_univ _).mpr hnA,
    convert fintype.card_coe _ },
  rcases ih r' card_α'_le (hall_cond_of_restrict r A hr) with ⟨f', hf', hAf'⟩,
  /- Restrict to `Aᶜ` in the domain and `(A.bind r)ᶜ` in the codomain. -/
  let α'' := (A : set α)ᶜ,
  let r'' : α'' → finset β := λ a'', r a'' \ A.bind r,
  have card_α''_le : fintype.card α'' ≤ n,
  { apply nat.le_of_lt_succ,
    rw ←hn,
    convert (card_compl_lt_iff_nonempty _).mpr hA,
    convert fintype.card_coe _,
    rw coe_compl, },
  rcases ih r'' card_α''_le (hall_cond_of_compl huA hr) with ⟨f'', hf'', hAf''⟩,
  /- Put them together -/
  have f'_mem_bind : ∀ {x'} (hx' : x' ∈ A), f' ⟨x', hx'⟩ ∈ A.bind r,
  { intros,
    rw mem_bind,
    exact ⟨x', hx', hAf' _⟩, },
  have f''_not_mem_bind : ∀ {x''} (hx'' : ¬ x'' ∈ A), ¬ f'' ⟨x'', hx''⟩ ∈ A.bind r,
  { intros,
    have h := hAf'' ⟨x'', hx''⟩,
    rw mem_sdiff at h,
    exact h.2, },
  have im_disj : ∀ {x' x'' : α} {hx' : x' ∈ A} {hx'' : ¬x'' ∈ A}, f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩,
  { intros _ _ hx' hx'' h,
    apply f''_not_mem_bind hx'',
    rw ←h,
    apply f'_mem_bind, },
  refine ⟨λ x, if h : x ∈ A then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩,
  exact inj_of_dite_disjoint_inj A f' f'' hf' hf'' @im_disj,
  { intro x,
    split_ifs,
    { exact hAf' ⟨x, h⟩ },
    { exact sdiff_subset _ _ (hAf'' ⟨x, h⟩) } }
end

/--
If `α` has cardinality `n + 1` and the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
theorem hall_hard_inductive_step {r : α → finset β} {n : ℕ} (hn : fintype.card α = n + 1)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β),
        by exactI fintype.card α' ≤ n →
                  (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
                  ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  by_cases h : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card,
  { exact hall_hard_inductive_step_A hn hr @ih h, },
  { push_neg at h,
    rcases h with ⟨A, Ane, Anu, Ale⟩,
    have Aeq := nat.le_antisymm (hr _) Ale,
    exact hall_hard_inductive_step_B hn hr @ih A Ane Anu Aeq, },
end

/--
Here we combine the base case and the inductive step into
a full strong induction proof, thus completing the proof
of the second direction.
-/
theorem hall_hard_inductive (n : ℕ) (hn : fintype.card α = n)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  tactic.unfreeze_local_instances,
  revert α,
  refine nat.strong_induction_on n (λ n' ih, _),
  intros,
  rcases n' with (_|_),
  { exact hall_hard_inductive_zero r hn },
  { apply hall_hard_inductive_step hn hr,
    introsI α' _ r' hα',
    exact ih (fintype.card α') (nat.lt_succ_of_le hα') r' rfl, },
end

end hall_marriage_theorem

/--
This the version of Hall's Marriage Theorem in terms of indexed
families of finite sets `s : ι → finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `A.bind s` is the union of all the sets `s i` for `i ∈ A`.
-/
theorem all_card_le_bind_card_iff_exists_injective
  {ι α : Type*} [fintype ι] [decidable_eq α] (s : ι → finset α) :
  (∀ (A : finset ι), A.card ≤ (A.bind s).card)
  ↔ (∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ s x) :=
begin
  split,
  { exact hall_marriage_theorem.hall_hard_inductive s (fintype.card ι) rfl },
  { rintro ⟨f, hf₁, hf₂⟩ A,
    rw ←card_image_of_injective A hf₁,
    apply card_le_of_subset,
    intro b,
    rw [mem_image, mem_bind],
    rintros ⟨a, ha, rfl⟩,
    exact ⟨a, ha, hf₂ a⟩, },
end

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α β : Type*} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})]
  (A : finset α) : fintype (rel.image r A) :=
begin
  have h : rel.image r A = (A.bind (λ a, (rel.image r {a}).to_finset) : set β),
  { ext, simp [rel.image], },
  rw [h],
  apply finset_coe.fintype,
end

/--
This is a version of Hall's Marriage Theorem in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite).  There is
an injective function `α → β` respecting the relation iff for every
`k` terms of `α` there are at least `k` terms of `β` related to them.

If `[fintype β]`, then `[∀ (a : α), fintype (rel.image r {a})]` is automatically implied.
-/
theorem all_card_le_rel_image_card_iff_exists_injective
  {α β : Type*} [fintype α] [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})] :
  (∀ (A : finset α), A.card ≤ fintype.card (rel.image r A))
  ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  let r' := λ a, (rel.image r {a}).to_finset,
  have h : ∀ (A : finset α), fintype.card (rel.image r A) = (A.bind r').card,
  { intro A,
    rw ←set.to_finset_card,
    apply congr_arg,
    ext b,
    simp [rel.image], },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp [rel.image], },
  simp only [h, h'],
  apply finset.all_card_le_bind_card_iff_exists_injective,
end

/--
This is a version of Hall's Marriage Theorem in terms of a relation
between finite types.  It is like `hall_rel` but uses `finset.filter`
rather than `rel.image`.
-/
theorem all_card_le_filter_rel_iff_exists_injective
  {α β : Type*} [fintype α] [fintype β]
  (r : α → β → Prop) [∀ a, decidable_pred (r a)] :
  (∀ (A : finset α), A.card ≤ (univ.filter (λ (b : β), ∃ a ∈ A, r a b)).card)
  ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  haveI : decidable_eq β := by { classical, apply_instance },
  let r' := λ a, univ.filter (λ b, r a b),
  have h : ∀ (A : finset α), (univ.filter (λ (b : β), ∃ a ∈ A, r a b)) = (A.bind r'),
  { intro A,
    ext b,
    simp, },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp, },
  simp_rw [h, h'],
  apply all_card_le_bind_card_iff_exists_injective,
end
