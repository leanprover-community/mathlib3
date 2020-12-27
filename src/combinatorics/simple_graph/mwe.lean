import data.fintype.basic
import data.sym2
import data.fin

open finset

universes u v

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
  -- the image of f of A is a subset of image_rel
  have h : (image f A) ⊆ (image_rel r A),
  -- proof of h
  { -- use the fact that A is a subset of B if and only if x ∈ A implies x ∈ B
    rw subset_iff,
    -- let x be of type β and let h2 be the statement that x is in the image of f(A)
    intros x h2,
    -- simplify at h2 to get that there exists some a of type α such that a ∈ A and f(a) = x
    simp only [mem_image, exists_prop] at h2,
    -- break up h2 into its respective parts; i.e.
        -- a : α
        -- ha : a ∈ A
        -- hfa : f a = x
    rcases h2 with ⟨a, ha, hfa⟩,
    -- rewrite the definition of image_rel
    unfold image_rel,
    -- simplify
    simp,
    -- because a is of type α, by hf₂ we have that a is related to f(a) by r
    specialize hf₂ a,
    -- replace f a with x in hf₂
    rw hfa at hf₂,
    -- close the goal with a, ha, and hf₂
    refine ⟨a, ha, hf₂⟩ },
  -- the cardinality of the image of an injective function is the cardinality of its preimage
  rw ← card_image_of_injective A hf₁,
  -- the cardinality of a subset is less than or equal to its superset
  apply card_le_of_subset h,
end

/- we prove the opposite direction using strong induction on
   the cardinality of `α`. -/

/-- Base case 0: the cardinality of `α` is ≤ `0` -/
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

/-- Base case 1: the cardinality of `α` is `1` -/
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
  (ha : ∃ (A : finset α), A ≠ univ → A.card = (image_rel r A).card)
  (ih : ∀ {α' β' : Type u} [fintype α'] [fintype β'] (r' : α' → β' → Prop)
    [∀ a, decidable_pred (r' a)], by exactI fintype.card α' ≤ n →
    by exactI (∀ (A : finset α'), A.card ≤ (image_rel r' A).card) →
    ∃ (f : α' → β'), function.injective f ∧ ∀ x, r' x (f x)) :
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) := sorry

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


/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/-- A graph `G` is `β`-colorable if there is an assignment of elements of `β` to
vertices of `G` (allowing repetition) such that adjacent vertices have
distinct colors. -/
@[ext]
structure coloring (β : Type v) :=
(color : V → β)
(valid : ∀ ⦃v w : V⦄, G.adj v w → color v ≠ color w)

/-- A graph `G` is `β`-colorable if there is a `β`-coloring. -/
def colorable (β : Type v) : Prop := nonempty (G.coloring β)

/--
A `colorable G α` graph is an `α`-partite graph, so we define bipartite as `colorable G (fin 2)`.
-/
def is_bipartite (G : simple_graph V) : Prop := G.colorable (fin 2)

abbreviation bipartition (G : simple_graph V) := G.coloring (fin 2)

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure matching :=
(edges : set (sym2 V))
(sub_edges : edges ⊆ G.edge_set)
(disjoint : ∀ (x y ∈ edges) (v : V), v ∈ x → v ∈ y → x = y)

/--
`M.support` is the set of vertices of `G` that are
contained in some edge of the matching `M`
-/
def matching.support (M : G.matching) : set V :=
{v : V | ∃ x, x ∈ M.edges ∧ v ∈ x}

lemma matching.is_injective (M : G.matching) :

theorem hall_marriage_theorem
  (h2 : fintype.card (f.color_set 0) ≤ fintype.card (f.color_set 1)) :
  (∃ (M : G.matching), (f.color_set 0) ⊆ M.support) ↔
  (∀ (S ⊆ f.color_set 0),
    fintype.card S ≤ fintype.card (G.neighbor_set_image S)) :=
begin
  split,
  { rintros ⟨M, hM⟩ S hs,
    have Ssat := set.subset.trans hs hM,
    rw ←M.opposites_card_eq Ssat,
    have Sopp := M.opposites_card_eq Ssat,
    exact set.card_le_of_subset (M.opposite_set_subneighbor_set' S Ssat) },
  { intro hh,
    -- we have `to_partial`, that's what i need to do my strong induction proof
    -- either every subset of the left class has a neighbour set larger than it,
    -- or there's one where the neighbour set is the same
    have h : (∀ (S ⊆ f.color_set 0), fintype.card S < fintype.card (G.neighbor_set' S)) ∨
        (∃ (S ⊆ f.color_set 0), fintype.card S = fintype.card (G.neighbor_set' S)),
    { --simp_rw le_iff_eq_or_lt at hh,
      rw or_iff_not_imp_left,
      intro ha,
      push_neg at ha,
      cases ha with x hx,
      use x,
      specialize hh x,
      cases hx with h3 h4,
      specialize hh h3,
      have h7 := le_antisymm hh h4,
      split,
      exact h3,
      exact h7 },
      cases h with ha he,
      {

        sorry },
      -- jesus fuck
    -- ∀ x, x ≤ f x → (∀ x, x < f x) ∨ (∃ x, x = f x)
    --by_contra hv,

    -- induction on `|f.color_set 0|` using partial colorings
      --
      -- have `partial_coloring.restrict f.to_partial`
    -- base case: `|f.color_set 0| = 0`, i.e. `f.color_set 0 = ∅`
      -- this is trivial

    -- IH: `∀ (S ⊆ f.color_set 0), fintype.card S ≤ fintype.card (G.neighbor_set' S))`
    -- ` → ∃ (M : G.matching), (f.color_set 0) ⊆ M.support`
      -- what i mean by this is `f.color_set 0` when you push `f` through to an induced subgraph
    sorry },
end
