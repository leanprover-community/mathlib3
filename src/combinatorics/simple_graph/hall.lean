import data.fintype.basic

open finset

universe u

-- Let α and β be finite types
variables {α β : Type u} [fintype α] [fintype β]
-- Let r be some relation between elements of α and elements of β
variables (r : α → β → Prop) [∀ a, decidable_pred (r a)]

-- Suppose A is a finite set made up of elements of α, and define the image of r of A in β as image_rel r A.
def image_rel (A : finset α) : finset β := univ.filter (λ b, ∃ a ∈ A, r a b)

/-
 Our goal is to prove:
 theorem hall :
  (∀ (A : finset α), A.card ≤ (image_rel r A).card)
    ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x))
-/

-- Declaration needed for decidability
open_locale classical

/-- Suppose there exists an injective function `f : α → β` where, for all `x` of type `α`,
 `r x (f x)`. Then for all finite sets `A` made up of elements of type `α`,
 `A.card ≤ (image_rel r A).card` -/
theorem hall_easy (f : α → β) (hf₁ : function.injective f) (hf₂ : ∀ x, r x (f x)) (A : finset α) :
  A.card ≤ (image_rel r A).card :=
begin
  -- it's enough to show that the image of A under f is a subset of image_rel
  suffices h : (image f A) ⊆ (image_rel r A),
  {
    -- the cardinality of the image of an injective function is the cardinality of its preimage
    rw ← card_image_of_injective A hf₁,

    -- the cardinality of a subset is less than or equal to its superset
    apply card_le_of_subset h },

  -- use the fact that A is a subset of B if and only if x ∈ A implies x ∈ B
  rw subset_iff,

  -- let x be of type β and let h2 be the statement that x is in the image of f(A)
  intros x h2,

  -- convert h2 into an existential statement
  simp only [mem_image, exists_prop] at h2,

  -- break up h2 into its respective parts; i.e.
    -- a : α
    -- ha : a ∈ A
    -- hfa : f a = x
  rcases h2 with ⟨a, ha, hfa⟩,

  -- because a is of type α, by hf₂ we have that a is related to f(a) by r
  specialize hf₂ a,

  -- replace f a with x in hf₂
  rw hfa at hf₂,

  -- convert the goal into an existential statement
  simp [image_rel],

  -- close by supplying a as a witness and supplying ha and hf₂ as proofs that a works
  use ⟨a, ha, hf₂⟩,

end

/- we prove the opposite direction using strong induction on
   the cardinality of `α`. -/

/-- Base case 0: the cardinality of `α` is ≤ `0` -/
theorem hall_hard_inductive_zero (hn : fintype.card α ≤ 0)
  (hr : ∀ (A : finset α), A.card ≤ (image_rel r A).card) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  -- We know α is empty. `h` is the automation-friendly form of this fact
  have h : α → false,
  {
    -- two standard lemmas show that `h` is the same as `hn`
    rwa [← fintype.card_eq_zero_iff, ← le_zero_iff_eq],
  },
  -- split into two subgoals: give a function and then prove it has the desired properties
  refine ⟨_, _⟩,

  -- there is no nontrivial function out of α; `tauto` can deal with this for us
  { tautology },

  -- since our function is trivial, proving it has the properties is also trivial
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
  {
    cases hh with b hb,
    use (λ a, b),
    split,
    { intros a1 a2 _,
      rw [hx a1, hx a2] },
    { intro a,
      rwa hx a }
  },

  specialize hr {x},
  rw [card_singleton, le_iff_lt_or_eq] at hr,

  -- split into two cases. in each case we'll have something slightly different to do
  -- in order to get our witness `b` and prove `r x b`.
  cases hr with hlt heq,
  work_on_goal 0 {
    -- convert `hlt` into an existential statement
    rw one_lt_card_iff at hlt,

    -- pull out the witness `b` and proof `hb` from `hlt`
    rcases hlt with ⟨b, _, hb, _, _⟩ },

  work_on_goal 1 {
    -- flip the equality to make it easier to match the form of a `rw` lemma
    symmetry' at heq,

    -- convert statement to an existential
    rw card_eq_one at heq,

    -- pull out the witness `b` and not-the-right-proof `hb'` from `heq`
    cases heq with b hb',

    -- convert `hb'` to a conjunction, of which we care about only the left part
    rw eq_singleton_iff_unique_mem at hb',

    -- pull out the left part `hb`
    cases hb' with hb _ },

  all_goals {
    -- use the `b` witness for the goal
    use b,

    -- ask lean to unify our goal with the `hb` proof
    convert hb,

    -- now the simplifier can handle it, so long as we tell it to peek under the hood of
    -- the `image_rel` definition
    simp [image_rel] },

end

/-
We now split up the condition that `∀ (A : finset α), A.card ≤ (image_rel r A).card`
into the two cases
* `∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card`
* `∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card`
-/

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

/-- Second case of the inductive step: assuming that
`∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card`
and that the statement of Hall's Marriage Theorem
is true for all `α'` of cardinality ≤ `n`, then it is true for `α`.
-/
lemma hall_hard_inductive_step_B [nontrivial α] {n : ℕ} (hn : fintype.card α ≤ n.succ)
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
  { sorry },
  have h4 : (∀ (A_1 : finset α'), A_1.card ≤ (image_rel r' A_1).card),
  { sorry },
  have h' := ih r' h3 h4,

  rcases h' with ⟨f', hf', hAf'⟩,

  let α'' := {a'' : α // a'' ∉ A},
  let β'' := {b'' : β // b'' ∉ image_rel r A},
  let r'' : α'' → β'' → Prop := λ a'' b'', r a'' b'',
  have h5 : fintype.card α'' ≤ n,
  { sorry },
  have h6 : (∀ (A_1 : finset α''), A_1.card ≤ (image_rel r'' A_1).card),
  { sorry },
  have h'' := ih r'' h5 h6,

  rcases h'' with ⟨f'', hf'', hAf''⟩,

  let f : α → β := λ x, if h : x ∈ A then f' ⟨x, h⟩ else f'' ⟨x, h⟩,
  use f,
  sorry,
end

/-
Here we use the two cases and our induction hypothesis
to prove our inductive step.
-/

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
  -- this is the statement that allows us to break `∀ (A : finset α), A.card ≤ (image_rel r A).card)`
  -- into the aforementioned cases
  have h :  (∀ (A : finset α), A.nonempty → A ≠ univ → A.card < (image_rel r A).card) ∨
        (∃ (A : finset α), A.nonempty ∧ A ≠ univ ∧ A.card = (image_rel r A).card),
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
