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

end finset

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
  rw fintype.card_eq_one_iff at hn,
  cases hn with x hx,
  suffices hh : ∃ b : β, b ∈ r x,
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
    simp },
end

/-- First case of the inductive step: assuming that
`∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_A [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (ha : ∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β)
    , by exactI fintype.card α' ≤ n →
      (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
    ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  rcases exists_pair_ne α with ⟨a, a', ne⟩,
  let α' := {a' : α // a' ≠ a},
  have hle : (finset.bind {a} r).nonempty,
  { rw [← card_pos, ← nat.succ_le_iff],
    apply le_of_lt (lt_of_le_of_lt _ (ha {a} (singleton_nonempty a) _)),
    { simp },
    { intro h,
      apply ne,
      rw [eq_comm, ← mem_singleton, h],
      simp } },
  cases hle with b hb,
  let r' : α' → finset β := λ a', (r a').filter (λ b', b' ≠ b),
  have h3 : fintype.card α' ≤ n,
  { rw fintype.card_of_subtype (univ.erase a),
    { rwa [card_erase_of_mem (mem_univ _), card_univ, nat.pred_le_iff] },
    { simp } },
  have h4 : (∀ (A : finset α'), A.card ≤ (A.bind r').card),
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
    have : (A'.image subtype.val).bind r ⊆ insert b (A'.bind r'),
    { rw subset_insert_iff,
      intro b',
      simp only [mem_filter, mem_erase, mem_image, mem_univ, true_and, exists_prop,
        subtype.exists, and_imp, exists_and_distrib_right, exists_eq_right, exists_imp_distrib, mem_bind],
      intros hb' a'' ha'' hA' ra''b,
      use [a'', ha'', hA', ra''b], },
    apply (card_le_of_subset this).trans ((card_insert_le _ _).trans _),
    refl, },
  rcases ih r' h3 h4 with ⟨f', hfinj, hfr⟩,
  refine ⟨λ x, if h : x = a then b else f' ⟨x, h⟩, _, _⟩,
  { rintro x₁ x₂ (t : dite _ _ _ = dite _ _ _),
    split_ifs at t with h₁ h₂ h₃ h₄,
    { subst h₁,
      subst h₂ },
    { subst h₁, subst b,
      specialize hfr ⟨x₂, h₂⟩,
      rw [mem_filter] at hfr,
      exact (hfr.2 rfl).elim, },
    { subst h₃, subst b,
      specialize hfr ⟨x₁, h₁⟩,
      rw [mem_filter] at hfr,
      exact (hfr.2 rfl).elim, },
    { injection hfinj t, } },
  { intro x,
    split_ifs,
    { subst h,
      simpa using hb },
    { specialize hfr ⟨x, h⟩,
      rw mem_filter at hfr,
      exact hfr.1, } }
end

/-- Second case of the inductive step: assuming that
`∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_B [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
  (hr : ∀ (A : finset α), A.card ≤ (A.bind r).card)
  (ha : ∃ (A : finset α), A.nonempty ∧ A ≠ univ ∧ A.card = (A.bind r).card)
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β)
    , by exactI fintype.card α' ≤ n →
     (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
    ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  haveI : decidable_eq α := by { classical, apply_instance },
  rcases ha with ⟨A, hA, hnA, huA⟩,
  let α' := {a' : α // a' ∈ A},
  let r' : α' → finset β := λ a', r a' ∩ A.bind r,
  have h3 : fintype.card α' ≤ n,
  { rw [fintype.card_of_subtype A (λ x, iff.rfl), ← nat.lt_succ_iff],
    have : A ⊂ univ := ⟨subset_univ _, λ t, hnA (le_antisymm (subset_univ _) t)⟩,
    apply lt_of_lt_of_le (card_lt_card this) hn },
  have h4 : (∀ (A' : finset α'), A'.card ≤ (A'.bind r').card),
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
  have h' := ih r' h3 h4,
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
  (ih : ∀ {α' : Type u} [fintype α'] (r' : α' → finset β)
    , by exactI fintype.card α' ≤ n →
     (∀ (A : finset α'), A.card ≤ (A.bind r').card) →
    ∃ (f : α' → β), function.injective f ∧ ∀ x, f x ∈ r' x) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, f x ∈ r x :=
begin
  have h :  (∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (A.bind r).card) ∨
        (∃ (A : finset α), A.nonempty ∧ A ≠ univ ∧ A.card = (A.bind r).card),
  classical,
  { rw or_iff_not_imp_left,
    intros ha,
    push_neg at ha,
    rcases ha with ⟨A, hA₁, hA₂, hA₃⟩,
    exact ⟨A, hA₁, hA₂, le_antisymm (hr _) hA₃⟩ },
  cases h with ha he,
  { apply hall_hard_inductive_step_A r hn ha,
    intros,
    apply ih,
    { assumption },
    { assumption } },
  { apply hall_hard_inductive_step_B r hn hr he,
    intros,
    apply ih,
    { assumption },
    { assumption } },
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
    { have h1lt := nat.succ_lt_succ (nat.zero_lt_succ k),
      rw ← heq at h1lt,
      rw fintype.one_lt_card_iff_nontrivial at h1lt,
      apply hall_hard_inductive_step r k.succ,
      { rw le_iff_lt_or_eq,
        right,
        exact heq },
      { exact hr },
      { exact @hk } } },
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
