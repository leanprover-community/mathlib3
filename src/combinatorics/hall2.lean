/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import data.fintype.basic
import data.rel

namespace finset


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

/-- A matching is an injective element of the product of an indexed family of sets. -/
lemma card_le_of_matching {α β : Type*} [decidable_eq β] (r : α → finset β)
  (f : α → β) (hf₁ : function.injective f) (hf₂ : ∀ x, f x ∈ r x) (A : finset α) :
  A.card ≤ (A.bind r).card :=
begin
  rw ←card_image_of_injective A hf₁,
  apply card_le_of_subset,
  intro b,
  rw [mem_image, mem_bind],
  rintros ⟨a, ha, rfl⟩,
  exact ⟨a, ha, hf₂ a⟩,
end

lemma bind_erase {α β : Type*} [decidable_eq β] (f : α → finset β) (s : finset α) (b : β) :
  s.bind (λ x, (f x).erase b) = (s.bind f).erase b :=
begin
  ext y,
  simp only [exists_prop, finset.mem_bind, ne.def, finset.mem_erase],
  tauto,
end

@[simp]
lemma nonempty.image_iff {α β: Type*} [decidable_eq β]
  (f : α → β) (s : finset α) :
  (s.image f).nonempty ↔ s.nonempty :=
begin
  split,
  { rintro ⟨y, hy⟩,
    rw finset.mem_image at hy,
    rcases hy with ⟨x, hx, rfl⟩,
    exact ⟨x, hx⟩, },
  { intro h,
    exact finset.nonempty.image h f, },
end

lemma card_eq_iff_eq_univ {α : Type*} [fintype α] (s : finset α) :
  s.card = fintype.card α ↔ s = finset.univ :=
begin
  split,
  { intro h,
    exact eq_univ_of_card _ h, },
  { rintro rfl,
    exact card_univ, },
end

lemma card_lt_of_ne_univ {α : Type*} [fintype α]
  (s : finset α) (hnu : s ≠ finset.univ) : s.card < fintype.card α :=
begin
  by_contra h,
  apply hnu,
  rw ←card_eq_iff_eq_univ,
  have h' : s.card ≤ fintype.card α := card_le_univ s,
  push_neg at h,
  exact nat.le_antisymm h' h,
end

lemma card_compl_lt_of_nonempty {α : Type*} [fintype α] [decidable_eq α]
  (s : finset α) (hne : s.nonempty) :
  sᶜ.card < fintype.card α :=
begin
  apply card_lt_of_ne_univ,
  cases hne with x hx,
  intro h,
  have h' := mem_univ x,
  rw ←h at h',
  simpa [hx] using h',
end

end finset

namespace fintype

lemma card_ne_eq {α : Type*} [fintype α] [decidable_eq α] (a : α) :
  fintype.card {x : α | x ≠ a} = fintype.card α - 1 :=
begin
  rw [←set.to_finset_card],
  convert_to (finset.univ.erase a).card = _,
  { congr,
    ext,
    rw [set.mem_to_finset, finset.mem_erase, set.mem_set_of_eq],
    simp only [finset.mem_univ, and_true], },
  { rw [finset.card_erase_of_mem (finset.mem_univ _), finset.card_univ],
    refl, },
end

end fintype

open finset


universes u v

namespace hall_marriage_theorem
variables {α : Type u} {β : Type v} [fintype α]
variables (r : α → finset β)

/-- Base case 0: the cardinality of `α` is ≤ `0` -/
theorem hall_hard_inductive_zero (hn : fintype.card α = 0) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  rw fintype.card_eq_zero_iff at hn,
  refine ⟨λ a, (hn a).elim, by tauto⟩,
end

variables [decidable_eq β]

/-- Base case 1: the cardinality of `α` is `1` -/
theorem hall_hard_inductive_one (hn : fintype.card α = 1)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  rcases fintype.card_eq_one_iff.mp hn with ⟨x, hx⟩,
  have hr' : 0 < (r x).card,
  { refine lt_of_lt_of_le nat.one_pos _,
    convert hr {x},
    simp, },
  rcases classical.indefinite_description _ (finset.card_pos.mp hr') with ⟨y, hy⟩,
  refine ⟨(λ _, y), _, (λ x', by rwa hx x')⟩,
  intros a a',
  simp [hx a, hx a'],
end

lemma hall_cond_of_erase (a : α) (b : β)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card) :
  ∀ (A : finset {a' : α | a' ≠ a}), A.card ≤ (A.bind (λ a', (r a').erase b)).card :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  intro A',
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


/-- First case of the inductive step: assuming that
`∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_A {n : ℕ} (hn : fintype.card α = n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β),
        by exactI fintype.card α' ≤ n →
                  (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
                  ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  haveI : nonempty α :=
  by { rw [←fintype.card_pos_iff, hn],
       exact nat.succ_pos _, },
  haveI : decidable_eq α := by { classical, apply_instance },
  /- Choose an arbitrary element `a : α` and `b : r a`. -/
  let a : α := classical.choice (by apply_instance),
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
  { rw [fintype.card_ne_eq, hn],
    exact le_refl _, },
  rcases ih r' card_α'_le (hall_cond_of_erase r a b ha) with ⟨f', hfinj, hfr⟩,
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

lemma hall_cond_of_restrict {α : Type u} (r : α → finset β) (A : finset α)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card) :
  ∀ (A' : finset (A : set α)), A'.card ≤ (A'.bind (λ a', r a')).card :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  intro A',
  convert hr (A'.image coe) using 1,
  { rw card_image_of_injective _ subtype.coe_injective, },
  { apply congr_arg,
    ext y,
    simp, },
end

lemma hall_cond_of_compl {α : Type u} (r : α → finset β) (A : finset α)
  (huA : A.card = (A.bind r).card)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card) :
  ∀ (B : finset ((A : set α)ᶜ : set α)), B.card ≤ (B.bind (λ a'', r a'' \ A.bind r)).card :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  intro B,
  have : B.card = (A ∪ B.image coe).card - A.card,
  { rw [card_disjoint_union, nat.add_sub_cancel_left,
        card_image_of_injective _ subtype.coe_injective],
    rw disjoint_left,
    simp only [not_exists, mem_image, exists_prop, set_coe.exists, exists_and_distrib_right,
               exists_eq_right, subtype.coe_mk],
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
      { exfalso,
        apply hA a ha rat },
      { exact ⟨⟨a', ha', rat⟩, hA⟩, } },
    exact (card_le_of_subset this).trans le_rfl, },
  { apply bind_subset_bind_of_subset_left,
    apply subset_union_left }
end

/-- Second case of the inductive step: assuming that
`∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_B {n : ℕ} (hn : fintype.card α = n.succ)
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
  have card_α'_le : fintype.card α' ≤ n,
  { apply nat.le_of_lt_succ,
    rw ←hn,
    convert card_lt_of_ne_univ _ hnA,
    convert fintype.card_coe _ },
  rcases ih r' card_α'_le (hall_cond_of_restrict r A hr) with ⟨f', hf', hAf'⟩,
  /- Restrict to `Aᶜ` in the domain and `(A.bind r)ᶜ` in the codomain. -/
  let α'' := (A : set α)ᶜ,
  let r'' : α'' → finset β := λ a'', r a'' \ A.bind r,
  have card_α''_le : fintype.card α'' ≤ n,
  { apply nat.le_of_lt_succ,
    rw ←hn,
    convert card_compl_lt_of_nonempty _ hA,
    convert fintype.card_coe _,
    rw coe_compl, },
  rcases ih r'' card_α''_le (hall_cond_of_compl r A huA hr) with ⟨f'', hf'', hAf''⟩,
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
  { rintros x₁ x₂ (h : dite _ _ _ = dite _ _ _),
    split_ifs at h,
    { injection (hf' h), },
    { exact (im_disj h).elim, },
    { exact (im_disj h.symm).elim, },
    { injection (hf'' h), }, },
  { intro x,
    split_ifs,
    { exact hAf' ⟨x, h⟩ },
    { exact sdiff_subset _ _ (hAf'' ⟨x, h⟩) } }
end

-- Note the generalisation over types here
/--
If `α` has cardinality `n + 1` and the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
theorem hall_hard_inductive_step (n : ℕ) (hn : fintype.card α = n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β),
        by exactI fintype.card α' ≤ n →
                  (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
                  ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  by_cases h : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card,
  { exact hall_hard_inductive_step_A r hn hr @ih h, },
  { push_neg at h,
    rcases h with ⟨A, Ane, Anu, Ale⟩,
    have Aeq := nat.le_antisymm (hr _) Ale,
    exact hall_hard_inductive_step_B r hn hr @ih A Ane Anu Aeq, },
end

/--
Here we combine the two base cases and the inductive step into
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
  rcases n' with (_|_|_),
  { exact hall_hard_inductive_zero r hn },
  { apply hall_hard_inductive_one r hn hr },
  { apply hall_hard_inductive_step r n'.succ hn hr,
    introsI α' _ r' hα',
    exact ih (fintype.card α') (nat.lt_succ_of_le hα') r' rfl, },
end

end hall_marriage_theorem

/--
We combine `hall_easy` and `hall_hard_inductive` into a proof
of Hall's Marriage Theorem.
-/
theorem hall {α β : Type*} [fintype α] [decidable_eq β] (r : α → finset β) :
  (∀ (A : finset α), A.card ≤ (A.bind r).card)
  ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x) :=
begin
  split,
  { exact hall_marriage_theorem.hall_hard_inductive r (fintype.card α) rfl },
  { rintro ⟨f, hf, hf2⟩,
    exact card_le_of_matching r f hf hf2 },
end


/-- If `[fintype β]`, then `[∀ (a : α), fintype (rel.image r {a})]` is automatically implied. -/
theorem hall_rel {α β : Type*} [fintype α] [decidable_eq β]
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
  apply hall,
end

/-- A version using `univ.filter` directly. -/
theorem hall_rel' {α β : Type*} [fintype α] [fintype β]
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
  apply hall,
end
