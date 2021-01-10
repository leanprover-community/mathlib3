import data.fintype.basic

open finset

universe u

variables {α β : Type u} [fintype α] [fintype β]
variables (r : α → β → Prop) [∀ a, decidable_pred (r a)]

def image_rel (A : finset α) : finset β := univ.filter (λ b, ∃ a ∈ A, r a b)

lemma image_rel_empty : image_rel r ∅ = ∅ := by simp [image_rel]

lemma image_rel_mono {A A' : finset α} (h : A ⊆ A') : image_rel r A ⊆ image_rel r A' :=
begin
  intro t,
  simp only [image_rel, true_and, and_imp, exists_prop, mem_filter, mem_univ, exists_imp_distrib],
  intros a ha rat,
  exact ⟨a, h ha, rat⟩,
end

open_locale classical

/-- Suppose there exists an injective function `f : α → β` where, for all `x` of type `α`,
 `r x (f x)`. Then for all finite sets `A` made up of elements of type `α`,
 `A.card ≤ (image_rel r A).card` -/
theorem hall_easy (f : α → β) (hf₁ : function.injective f) (hf₂ : ∀ x, r x (f x)) (A : finset α) :
  A.card ≤ (image_rel r A).card :=
begin
  suffices h : (image f A) ⊆ (image_rel r A),
  { rw ← card_image_of_injective A hf₁,
    apply card_le_of_subset h },
  rw subset_iff,
  intros x h2,
  simp only [mem_image, exists_prop] at h2,
  rcases h2 with ⟨a, ha, hfa⟩,
  specialize hf₂ a,
  rw hfa at hf₂,
  simp [image_rel],
  use ⟨a, ha, hf₂⟩,
end

/-- Base case 0: the cardinality of `α` is ≤ `0` -/
theorem hall_hard_inductive_zero (hn : fintype.card α ≤ 0)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  have h : α → false,
  { rwa [← fintype.card_eq_zero_iff, ← le_zero_iff_eq] },
  refine ⟨_, _⟩,
  { tautology },
  { tautology },
end

/-- Base case 1: the cardinality of `α` is `1` -/
theorem hall_hard_inductive_one (hn : fintype.card α = 1)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  rw fintype.card_eq_one_iff at hn,
  cases hn with x hx,
  suffices hh : ∃ b : β, r x b,
  { cases hh with b hb,
    use (λ a, b),
    split,
    { intros a1 a2 _,
      rw [hx a1, hx a2] },
    { intro a,
      rwa hx a } },
  specialize hr {x},
  rw [card_singleton, le_iff_lt_or_eq] at hr,
  cases hr with hlt heq,
  work_on_goal 0 {
    rw one_lt_card_iff at hlt,
    rcases hlt with ⟨b, _, hb, _, _⟩ },
  work_on_goal 1 {
    symmetry' at heq,
    rw card_eq_one at heq,
    cases heq with b hb',
    rw eq_singleton_iff_unique_mem at hb',
    cases hb' with hb _ },
  all_goals {
    use b,
    convert hb,
    simp [image_rel] },
end

/-- First case of the inductive step: assuming that
`∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
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
  have hle : (image_rel r {a}).nonempty,
  { rw [← card_pos, ← nat.succ_le_iff],
    apply le_of_lt (lt_of_le_of_lt _ (ha {a} (singleton_nonempty a) _)),
    { simp },
    { intro h,
      apply ne,
      rw [eq_comm, ← mem_singleton, h],
      simp } },
  cases hle with b hb,
  let β' := {b' : β // b' ≠ b},
  let r' : α' → β' → Prop := λ a' b', r a' b',
  have h3 : fintype.card α' ≤ n,
  { rw fintype.card_of_subtype (univ.erase a),
    { rwa [card_erase_of_mem (mem_univ _), card_univ, nat.pred_le_iff] },
    { simp } },
  have h4 : (∀ (A : finset α'), A.card ≤ (image_rel r' A).card),
  { intro A',
    rcases A'.eq_empty_or_nonempty with (rfl | Ane),
    { simp },
    have : A'.image subtype.val ≠ univ,
    { intro t,
      have : a ∉ A'.image subtype.val,
      { simp },
      apply this,
      rw t,
      simp },
    have ha' := ha (A'.image subtype.val) (Ane.image _) this,
    rw card_image_of_injective _ subtype.val_injective at ha',
    rw ← nat.lt_succ_iff,
    apply lt_of_lt_of_le ha',
    have : image_rel r (A'.image subtype.val) ⊆ insert b ((image_rel r' A').image subtype.val),
    { rw subset_insert_iff,
      intro b',
      simp only [image_rel, mem_filter, mem_erase, mem_image, mem_univ, true_and, exists_prop,
        subtype.exists, and_imp, exists_and_distrib_right, exists_eq_right, exists_imp_distrib],
      intros hb' a'' ha'' hA' ra''b,
      refine ⟨hb', _, _, hA', ra''b⟩ },
    apply (card_le_of_subset this).trans ((card_insert_le _ _).trans _),
    rw card_image_of_injective _ subtype.val_injective },
  rcases ih r' h3 h4 with ⟨f', hfinj, hfr⟩,
  refine ⟨λ x, if h : x = a then b else f' ⟨x, h⟩, _, _⟩,
  { rintro x₁ x₂ (t : dite _ _ _ = dite _ _ _),
    split_ifs at t with h₁ h₂ h₃ h₄,
    { subst h₁,
      subst h₂ },
    { subst h₁,
      apply ((f' ⟨x₂, h₂⟩).prop t.symm).elim },
    { subst h₃,
      apply ((f' ⟨x₁, h₁⟩).prop t).elim },
    { injection hfinj (subtype.coe_injective t) } },
  { intro x,
    split_ifs,
    { subst h,
      simpa [image_rel] using hb },
    { apply hfr ⟨x, h⟩ } }
end

/-- Second case of the inductive step: assuming that
`∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_B [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card)
  (ha : ∃ (A : finset α), A.nonempty ∧ A ≠ univ ∧ A.card = (image_rel r A).card)
  (ih : ∀ {α' β' : Type u} [fintype α'] [fintype β'] (r' : α' → β' → Prop)
    [∀ a, decidable_pred (r' a)], by exactI fintype.card α' ≤ n →
    by exactI (∀ (A : finset α'), A.card ≤ (image_rel r' A).card) →
    ∃ (f : α' → β'), function.injective f ∧ ∀ x, r' x (f x)) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  rcases ha with ⟨A, hA, hnA, huA⟩,
  let α' := {a' : α // a' ∈ A},
  let β' := {b' : β // b' ∈ image_rel r A},
  let r' : α' → β' → Prop := λ a' b', r a' b',
  have h3 : fintype.card α' ≤ n,
  { rw [fintype.card_of_subtype A (λ x, iff.rfl), ← nat.lt_succ_iff],
    have : A ⊂ univ := ⟨subset_univ _, λ t, hnA (le_antisymm (subset_univ _) t)⟩,
    apply lt_of_lt_of_le (card_lt_card this) hn },
  have h4 : (∀ (A' : finset α'), A'.card ≤ (image_rel r' A').card),
  { intro A',
    have h₁ := hr (A'.image subtype.val),
    have h₂ : image_rel r (image subtype.val A') ⊆ image subtype.val (image_rel r' A'),
    { intro t,
      simp only [image_rel, mem_filter, mem_image, exists_prop, mem_univ, true_and, subtype.exists,
        and_imp, exists_eq_right, exists_imp_distrib, exists_and_distrib_right],
      intros a hA hA' rat,
      refine ⟨_, _, _, hA', rat⟩,
      simp only [image_rel, mem_filter, mem_univ, true_and, exists_prop],
      refine ⟨_, hA, rat⟩ },
    rw card_image_of_injective _ subtype.val_injective at h₁,
    apply h₁.trans ((card_le_of_subset h₂).trans _),
    rw card_image_of_injective _ subtype.val_injective },
  have h' := ih r' h3 h4,
  rcases h' with ⟨f', hf', hAf'⟩,
  let α'' := {a'' : α // a'' ∉ A},
  let β'' := {b'' : β // b'' ∉ image_rel r A},
  let r'' : α'' → β'' → Prop := λ a'' b'', r a'' b'',
  have h5 : fintype.card α'' ≤ n,
  { have : ¬univ ⊆ Aᶜ,
    { intro t,
      rcases hA with ⟨a, ha⟩,
      simpa [ha] using t (mem_univ a) },
    have : Aᶜ ⊂ univ := ⟨subset_univ _, this⟩,
    rw [fintype.card_of_subtype Aᶜ, ← nat.lt_succ_iff],
    { apply lt_of_lt_of_le (card_lt_card this) hn },
    { simp } },
  have h6 : (∀ (B : finset α''), B.card ≤ (image_rel r'' B).card),
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
        image_rel r (A ∪ B.image subtype.val) \ image_rel r A ⊆ (image_rel r'' B).image subtype.val,
      { intros t,
        simp only [image_rel, mem_filter, mem_sdiff, mem_univ, true_and, exists_prop, not_exists,
          mem_image, mem_union, and_imp, not_and, exists_and_distrib_right, exists_eq_right,
          subtype.exists, subtype.coe_mk, exists_imp_distrib],
        rintro a (ha | ⟨ha, hB⟩) rat hA,
        { exfalso,
          apply hA a ha rat },
        { exact ⟨by simpa [image_rel] using hA, _, ha, hB, rat⟩ } },
      apply (card_le_of_subset this).trans _,
      rw card_image_of_injective _ subtype.val_injective },
    { apply image_rel_mono,
      apply subset_union_left } },
  have h'' := ih r'' h5 h6,
  rcases h'' with ⟨f'', hf'', hAf''⟩,
  refine ⟨λ x, if h : x ∈ A then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩,
  { rintro x₁ x₂ (h : dite _ _ _ = dite _ _ _),
    split_ifs at h with h₁ h₂ h₃ h₄,
    { injection hf' (subtype.coe_injective h) },
    { exfalso,
      apply (f'' ⟨x₂, h₂⟩).prop,
      rw ← h,
      apply (f' ⟨x₁, h₁⟩).prop },
    { exfalso,
      apply (f'' ⟨x₁, h₁⟩).prop,
      rw h,
      apply (f' ⟨x₂, h₃⟩).prop },
    { injection hf'' (subtype.coe_injective h) } },
  { intro x,
    split_ifs,
    { apply hAf' ⟨x, h⟩ },
    { apply hAf'' ⟨x, h⟩ } }
end

-- Note the generalisation over types here
/--
If `α` has cardinality `n + 1` and the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
theorem hall_hard_inductive_step [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card)
  (ih : ∀ {α' β' : Type u} [fintype α'] [fintype β'] (r' : α' → β' → Prop)
    [∀ a, decidable_pred (r' a)], by exactI fintype.card α' ≤ n →
    by exactI (∀ (A : finset α'), A.card ≤ (image_rel r' A).card) →
    ∃ (f : α' → β'), function.injective f ∧ ∀ x, r' x (f x)) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  have h :  (∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card) ∨
        (∃ (A : finset α), A.nonempty ∧ A ≠ univ ∧ A.card = (image_rel r A).card),
  classical,
  { rw or_iff_not_imp_left,
    intros ha,
    push_neg at ha,
    rcases ha with ⟨A, hA₁, hA₂, hA₃⟩,
    exact ⟨A, hA₁, hA₂, le_antisymm (hr _) hA₃⟩ },
  cases h with ha he,
  { apply hall_hard_inductive_step_A r hn ha,
    introsI α' β' h1 h2 h3 h4 h5 h6,
    apply ih,
    { exact h5 },
    { intro A,
      exact h6 A } },
  { apply hall_hard_inductive_step_B r hn hr he,
    introsI α' β' h1 h2 h3 h4 h5 h6,
    apply ih,
    { exact h5 },
    { intro A,
      apply h6 A } },
end

/--
Here we combine the two base cases and the inductive step into
a full strong induction proof, thus completing the proof
of the second direction.
-/
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

/--
We combine `hall_easy` and `hall_hard_inductive` into a proof
of Hall's Marriage Theorem.
-/
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
