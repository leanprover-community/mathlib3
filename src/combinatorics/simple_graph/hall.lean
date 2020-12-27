import data.fintype.basic

open finset

universe u

variables {α β : Type u} [fintype α] [fintype β]
variables (r : α → β → Prop) [∀ a, decidable_pred (r a)]

def image_rel (A : finset α) : finset β := univ.filter (λ b, ∃ a ∈ A, r a b)

open_locale classical

theorem hall_easy (f : α → β) (hf₁ : function.injective f) (hf₂ : ∀ x, r x (f x)) (A : finset α) :
  A.card ≤ (image_rel r A).card :=
begin
  have h : (image f A) ⊆ (image_rel r A),
  { rw subset_iff,
    intros x h2,
    simp at h2,
    rcases h2 with ⟨a, ha, hfa⟩,
    unfold image_rel,
    simp,
    specialize hf₂ a,
    rw hfa at hf₂,
    refine ⟨a, ha, hf₂⟩ },
  have h2 := card_image_of_injective A hf₁,
  rw ← h2,
  apply card_le_of_subset h,
end

theorem hall_hard_inductive_zero (hn : fintype.card α ≤ 0)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  rw le_zero_iff_eq at hn,
  rw fintype.card_eq_zero_iff at hn,
  refine ⟨_, _⟩,
  intro a,
  specialize hn a,
  tauto,
  split,
  tauto,
  tauto,
end

theorem hall_hard_inductive_one (hn : fintype.card α = 1)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  rw fintype.card_eq_one_iff at hn,
  cases hn with x hx,
  specialize hr {x},
  rw [card_singleton, le_iff_lt_or_eq] at hr,
  cases hr with hlt heq,
  rw one_lt_card_iff at hlt,
  rcases hlt with ⟨b1, b2, hb1, hb2, hbne⟩,
  unfold image_rel at hb1,
  simp at hb1,
  use (λ a, b1),
  split,
  unfold function.injective,
  intros a1 a2 h,
  rw [hx a1, hx a2],
  intros x1,
  change r x1 b1,
  specialize hx x1,
  rw hx,
  exact hb1,

  symmetry' at heq,
  rw card_eq_one at heq,
  cases heq with a ha,
  use (λ x, a),
  split,
  unfold function.injective,
  intros a1 a2 ha,
  rw [hx a1, hx a2],
  intros x2,
  unfold image_rel at ha,
  rw eq_singleton_iff_unique_mem at ha,
  rcases ha with ⟨ha, ha2⟩,
  simp at ha,
  rw hx x2,
  exact ha,
end

lemma hall_hard_inductive_step_A [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card)
  (ih : ∀ {α' β' : Type u} [fintype α'] [fintype β'] (r' : α' → β' → Prop)
    [∀ a, decidable_pred (r' a)], by exactI fintype.card α' ≤ n →
    by exactI (∀ (A : finset α'), A.card ≤ (image_rel r' A).card) →
    ∃ (f : α' → β'), function.injective f ∧ ∀ x, r' x (f x)) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  rcases exists_pair_ne α with ⟨a, a', ne⟩,
  let α' := {a' : α // a' ≠ a},
  specialize ha {a} (singleton_nonempty a),
  simp at ha,
  rw eq_univ_iff_forall at ha,
  push_neg at ha,
  simp at ha,
  specialize ha a',
  symmetry' at ne,
  simp at ne,
  specialize ha ne,
  have hle := nat.lt_of_succ_le (le_of_lt ha),
  rw card_pos at hle,
  cases hle with b hb,
  let β' := {b' : β // b' ≠ b},
  let r' : α' → β' → Prop := λ a' b', r a' b',
  have h3 : fintype.card α' ≤ n,
  { sorry },
  have h4 : (∀ (A : finset α'), A.card ≤ (image_rel r' A).card),
  { sorry },
  specialize ih r' h3 h4,
  rcases ih with ⟨f', hfinj, hfr⟩,
  let f := λ x, if h : x = a then b else f' ⟨x, h⟩,
  use f,
  split,
  {
    sorry },
  { sorry },
end

lemma hall_hard_inductive_step_B [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (ha : ∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card)
  (ih : ∀ {α' β' : Type u} [fintype α'] [fintype β'] (r' : α' → β' → Prop)
    [∀ a, decidable_pred (r' a)], by exactI fintype.card α' ≤ n →
    by exactI (∀ (A : finset α'), A.card ≤ (image_rel r' A).card) →
    ∃ (f : α' → β'), function.injective f ∧ ∀ x, r' x (f x)) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) := sorry

-- Note the generalisation over types here
theorem hall_hard_inductive_step [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card)
  (ih : ∀ {α' β' : Type u} [fintype α'] [fintype β'] (r' : α' → β' → Prop)
    [∀ a, decidable_pred (r' a)], by exactI fintype.card α' ≤ n →
    by exactI (∀ (A : finset α'), A.card ≤ (image_rel r' A).card) →
    ∃ (f : α' → β'), function.injective f ∧ ∀ x, r' x (f x)) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  have h :  (∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card) ∨
        (∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card),
  classical,
  { rw or_iff_not_imp_left,
    intros ha,
    push_neg at ha,
    cases ha with x hx,
    use x,
    intros hb,
    specialize hr x,
    rcases hx with ⟨h4, h5, h6⟩,
    exact le_antisymm hr h6 },
  cases h with ha he,
  { apply hall_hard_inductive_step_A r hn ha,
    introsI α' β' h1 h2 h3 h4 h5 h6,
    apply ih,
    { exact h5 },
    { intro A,
      exact h6 A } },
  { apply hall_hard_inductive_step_B r hn he,
    introsI α' β' h1 h2 h3 h4 h5 h6,
    apply ih,
    { exact h5 },
    { intro A,
      apply h6 A } },
end

theorem hall_hard_inductive (n : ℕ) (hn : fintype.card α ≤ n)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  tactic.unfreeze_local_instances,
  induction n with k hk generalizing α β,
  apply hall_hard_inductive_zero r hn hr,
  rw le_iff_lt_or_eq at hn,
  cases hn with hlt heq,
  rw nat.lt_succ_iff at hlt,
  apply hk r hlt hr,
  cases k,
  apply hall_hard_inductive_one r heq hr,
  have h1lt := nat.succ_lt_succ (nat.zero_lt_succ k),
  rw ← heq at h1lt,
  rw fintype.one_lt_card_iff_nontrivial at h1lt,
  apply @hall_hard_inductive_step α β _ _ r _ h1lt (k.succ),
  rw le_iff_lt_or_eq,
  right,
  exact heq,
  exact hr,
  exact @hk,
end

theorem hall :
  (∀ (A : finset α), A.card ≤ (image_rel r A).card)
    ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  split,
  intros h,
  apply hall_hard_inductive r (fintype.card α) (le_refl (fintype.card α)) h,

  intros h,
  rcases h with ⟨f, hf, hf2⟩,
  exact hall_easy r f hf hf2,
end
