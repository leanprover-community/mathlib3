/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import data.fintype.basic
import data.rel

namespace finset

/-- Given a relation whose images are all finite, construct the `finset` version of `rel.image`. -/
def rel_image {α β : Type*} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})]
  (A : finset α) : finset β :=
A.bind (λ a, (rel.image r {a}).to_finset)

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α β : Type*} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})]
  (A : finset α) : fintype (rel.image r A) :=
begin
  have h : rel.image r A = (A.rel_image r : set β),
  { ext, simp [rel_image, rel.image], },
  rw [h],
  apply finset_coe.fintype,
end

lemma card_image_eq_card_rel_image {α β : Type*} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})] (A : finset α) :
  fintype.card (rel.image r A) = (rel_image r A).card :=
begin
  apply fintype.card_of_finset',
  simp [rel_image, rel.image],
end

/-- A matching is an injective element of the product of an indexed family of sets. -/
lemma card_le_of_matching {α β : Type*} [decidable_eq β] (ι : α → finset β)
  (f : α → β) (hf₁ : function.injective f) (hf₂ : ∀ x, f x ∈ ι x) (A : finset α) :
  A.card ≤ (A.bind ι).card :=
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
theorem hall_hard_inductive_zero (hn : fintype.card α ≤ 0) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  rw [nonpos_iff_eq_zero, fintype.card_eq_zero_iff] at hn,
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

/-- First case of the inductive step: assuming that
`∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_A [nonempty α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β),
        by exactI fintype.card α' ≤ n →
                  (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
                  ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  let a : α := classical.choice (by apply_instance),
  have ra_ne : (r a).nonempty,
  { rw ←finset.card_pos,
    apply nat.lt_of_lt_of_le nat.one_pos,
    convert hr {a},
    rw finset.singleton_bind, },
  rcases classical.indefinite_description _ ra_ne with ⟨b, hb⟩,
  let α' := {a' : α | a' ≠ a},
  let r' : α' → finset β := λ a', (r a').erase b,
  have card_α'_le : fintype.card α' ≤ n,
  { rw fintype.card_ne_eq,
    exact nat.sub_le_right_of_le_add hn },
  have hall_cond : ∀ (A : finset α'), A.card ≤ (A.bind r').card,
  { intro A',
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
      simp }, },
  rcases ih r' card_α'_le hall_cond with ⟨f', hfinj, hfr⟩,
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

/-- Second case of the inductive step: assuming that
`∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_B [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
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
  let α' := {a' : α // a' ∈ A},
  let r' : α' → finset β := λ a', r a' ∩ A.bind r,
  have card_α'_le : fintype.card α' ≤ n,
  { rw [fintype.card_of_subtype A (λ _, iff.rfl), ← nat.lt_succ_iff],
    have : A ⊂ univ := ⟨subset_univ _, λ t, hnA (le_antisymm (subset_univ _) t)⟩,
    apply lt_of_lt_of_le (card_lt_card this) hn },
  have hall_cond' : ∀ (A' : finset α'), A'.card ≤ (A'.bind r').card,
  { intro A',
    have h₁ := hr (A'.image subtype.val),
    have h₂ : (image subtype.val A').bind r ⊆ A'.bind r',
    { intro t,
      simp only [mem_image, and_imp, mem_bind, exists_prop, exists_and_distrib_right,
                 exists_eq_right, subtype.exists, subtype.coe_mk, exists_imp_distrib, mem_inter,
                 subtype.val_eq_coe],
      intros a hA hA' rat,
      exact ⟨⟨a, ⟨hA, hA'⟩, rat⟩, ⟨a, hA, rat⟩⟩, },
    rw card_image_of_injective _ subtype.val_injective at h₁,
    apply h₁.trans ((card_le_of_subset h₂).trans _),
    refl, },
  have h' := ih r' card_α'_le hall_cond',
  rcases h' with ⟨f', hf', hAf'⟩,
  let α'' := {a'' : α // a'' ∉ A},
  let r'' : α'' → finset β := λ a'', r a'' \ A.bind r,
  have h5 : fintype.card α'' ≤ n,
  { have : ¬univ ⊆ Aᶜ,
    { intro t,
      rcases hA with ⟨a, ha⟩,
      simpa [ha] using t (mem_univ a) },
    have : Aᶜ ⊂ univ := ⟨subset_univ _, this⟩,
    rw [fintype.card_of_subtype Aᶜ, ← nat.lt_succ_iff],
    { apply lt_of_lt_of_le (card_lt_card this) hn },
    { simp } },
  have h6 : (∀ (B : finset α''), B.card ≤ (B.bind r'').card),
  { intro B,
    have : (A ∪ B.image subtype.val).card - A.card = B.card,
    { rw [card_disjoint_union, nat.add_sub_cancel_left,
        card_image_of_injective _ (subtype.val_injective)],
      rw disjoint_left,
      simp only [not_exists, mem_image, exists_prop, exists_and_distrib_right, exists_eq_right,
        subtype.exists, subtype.coe_mk],
      intros a hA hA',
      apply (hA' hA).elim },
    rw ← this,
    rw huA,
    apply (nat.sub_le_sub_right (hr _) _).trans _,
    rw ← card_sdiff,
    { have :
        (A ∪ B.image subtype.val).bind r \ A.bind r ⊆ B.bind r'',
      { intros t,
        simp only [r'', mem_bind, mem_sdiff],
        simp only [not_exists, mem_image, and_imp, exists_prop, mem_union, not_and,
                   exists_and_distrib_right, exists_eq_right, subtype.exists, subtype.coe_mk,
                   exists_imp_distrib, subtype.val_eq_coe],
        rintro a (ha | hb) rat hA,
        { exfalso,
          apply hA a ha rat },
        { exact ⟨⟨a, hb, rat⟩, hA⟩, } },
      apply (card_le_of_subset this).trans _,
      refl, },
    { apply bind_subset_bind_of_subset_left,
      apply subset_union_left } },
  have h'' := ih r'' h5 h6,
  rcases h'' with ⟨f'', hf'', hAf''⟩,
  refine ⟨λ x, if h : x ∈ A then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩,
  { rintro x₁ x₂ (h : dite _ _ _ = dite _ _ _),
    split_ifs at h with h₁ h₂ h₂ h₁,
    { injection hf' h },
    { exfalso,
      specialize hAf' ⟨x₁, h₁⟩,
      specialize hAf'' ⟨x₂, h₂⟩,
      rw ←h at hAf'',
      rw mem_inter at hAf',
      rw mem_sdiff at hAf'',
      exact absurd hAf'.2 hAf''.2, },
    { exfalso,
      specialize hAf' ⟨x₂, h₂⟩,
      specialize hAf'' ⟨x₁, h₁⟩,
      rw h at hAf'',
      rw mem_inter at hAf',
      rw mem_sdiff at hAf'',
      exact absurd hAf'.2 hAf''.2, },
    { injection hf'' h } },
  { intro x,
    split_ifs,
    { exact inter_subset_left _ _ (hAf' ⟨x, h⟩) },
    { exact sdiff_subset _ _ (hAf'' ⟨x, h⟩) } }
end

-- Note the generalisation over types here
/--
If `α` has cardinality `n + 1` and the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
theorem hall_hard_inductive_step [nontrivial α] (n : ℕ) (hn : fintype.card α ≤ n.succ)
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
theorem hall_hard_inductive (n : ℕ) (hn : fintype.card α ≤ n)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  tactic.unfreeze_local_instances,
  induction n with k hk generalizing α,
  { apply hall_hard_inductive_zero r hn },
  { rw le_iff_lt_or_eq at hn,
    cases hn with hlt heq,
    { rw nat.lt_succ_iff at hlt,
      apply hk r hlt hr },
    cases k,
    { apply hall_hard_inductive_one r heq hr },
    { haveI : nontrivial α :=
      by { rw [←fintype.one_lt_card_iff_nontrivial, heq],
           exact nat.succ_lt_succ (nat.succ_pos _), },
      apply hall_hard_inductive_step r k.succ (by rw heq) hr @hk, }, },
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
  { exact hall_marriage_theorem.hall_hard_inductive r (fintype.card α) (le_refl _) },
  { rintro ⟨f, hf, hf2⟩,
    exact card_le_of_matching r f hf hf2 },
end


/-- If `[fintype β]`, then `[∀ (a : α), fintype (rel.image r {a})]` is automatically implied. -/
theorem hall' {α β : Type*} [fintype α] [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})] :
  (∀ (A : finset α), A.card ≤ fintype.card (rel.image r A))
  ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  let r' := λ a, (rel.image r {a}).to_finset,
  have h : ∀ A, rel_image r A = A.bind r',
  { intro A,
    ext b,
    simp [rel_image], },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp [rel.image], },
  simp only [h, h', card_image_eq_card_rel_image],
  apply hall,
end
