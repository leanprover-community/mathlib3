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
  have h : (image f A) ⊆ (image_rel r A),
  { rw subset_iff,
    intros x h2,
    simp only [mem_image, exists_prop] at h2,
    rcases h2 with ⟨a, ha, hfa⟩,
    unfold image_rel,
    simp only [true_and, exists_prop, mem_filter, mem_univ],
    specialize hf₂ a,
    rw hfa at hf₂,
    refine ⟨a, ha, hf₂⟩ },
  rw ← card_image_of_injective A hf₁,
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

variable [decidable_eq β]
lemma ite_injective (f₁ f₂ : α → β) (h₁ : function.injective f₁) (h₂ : function.injective f₂)
(h12 : disjoint (image f₁) (image f₂))(p : α → Prop) :
  function.injective (λ (a : α), if p a then f₁ a else f₂ a) :=
begin
  classical,
  intros a₁ a₂ h,
  dsimp at h,
  split_ifs at h,
  { apply h₁ h },
  { --rw disjoint_iff_ne at h12,
    sorry },
  { sorry },
  { apply h₂ h },
  --rw @disjoint_iff_ne β (image f₁) (image f₂) at h12,
  --apply h12,
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
  { sorry },
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
  ∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x) :=
begin
  cases ha with A ha,
  rcases eq_empty_or_nonempty A with (rfl | Ane),
  { have hb := @univ_nonempty_iff α _inst_1,
    --have hc := @nontrivial.to_nonempty α _inst_4,
    cases hb with hu hn,
    --specialize hn hc,
    rw card_empty at ha,
    have hemp := 0 = (image_rel r ∅).card,
    sorry },
  simp at ha,
  rcases exists_pair_ne α with ⟨a, a', ne⟩,

  let α' := {a' : α // a' ∈ A},
  let β' := {b' : β // b' ∈ (image_rel r A)},
  let r' : α' → β' → Prop := λ a' b', r a' b',
  have h3 : fintype.card α' ≤ n,
  { sorry },
  have h4 : (∀ (A : finset α'), A.card ≤ (image_rel r' A).card),
  { sorry },
  have ih' := ih r' h3 h4,
  rcases ih' with ⟨f', hf', hrf'⟩,

  let α'' := {a' : α // a' ∉ A},
  let β'' := {b' : β // b' ∉ (image_rel r A)},
  let r'' : α'' → β'' → Prop := λ a'' b'', r a'' b'',
  have h3' : fintype.card α'' ≤ n,
  { sorry },
  have h4' : (∀ (A : finset α''), A.card ≤ (image_rel r'' A).card),
  { sorry },
  have ih'' := ih r'' h3' h4',
  rcases ih'' with ⟨f'', hf'', hrf''⟩,

  refine ⟨λ a, if h₁ : a ∈ A then (f' ⟨a, h₁⟩).1 else (f'' ⟨a, h₁⟩).1, _, _⟩,
  --rw at hn,
  sorry,
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

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

/-- `G.neighbor_set_image S` is the union of neighbor_sets of `S ⊆ V` in `G`. -/
def neighbor_set_image (S : set V) : set V := ⋃v∈S, G.neighbor_set v

variables (v : V) [fintype (G.neighbor_set v)] (S : finset V) [fintype (G.neighbor_set_image S)]

/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

/-- `G.neighbor_set_image S` is the union of neighbor_sets of `S ⊆ V` in `G`. -/
def neighbor_finset_image : finset V := (G.neighbor_set_image S).to_finset

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.
-/
def edge_set : set (sym2 V) := sym2.from_rel G.sym

/-- A graph `G` is `C`-colorable if there is an assignment of elements of `C` to
vertices of `G` (allowing repetition) such that adjacent vertices have
distinct colors. -/
@[ext]
structure coloring (C : Type v) :=
(color : V → C)
(valid : ∀ ⦃v w : V⦄, G.adj v w → color v ≠ color w)

/-- A graph `G` is `C`-colorable if there is a `C`-coloring. -/
def colorable (C : Type v) : Prop := nonempty (G.coloring C)

namespace coloring
variables {G} {C : Type v} (f : G.coloring C)

/-- The set of vertices with the given color. -/
def color_set (c : C) : set V := f.color ⁻¹' {c}

variables (c : C) [fintype (f.color ⁻¹' {c})]

/-- The set of vertices with the given color. -/
def color_finset : finset V := (f.color ⁻¹' {c}).to_finset

def partition_adj (f : G.coloring C) (c1 c2 : C) :
  f.color_set c1 → f.color_set c2 → Prop := λ a b, G.adj a b

end coloring

/--
A `colorable G α` graph is an `α`-partite graph, so we define bipartite as `colorable G (fin 2)`.
-/
def is_bipartite : Prop := G.colorable (fin 2)

-- CR : keep this in?
abbreviation bipartition := G.coloring (fin 2)

variables [fintype V] [decidable_eq V] (b : G.bipartition)

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure matching :=
(edges : set (sym2 V))
(sub_edges : edges ⊆ G.edge_set)
(disjoint : ∀ (x y ∈ edges) (v : V), v ∈ x → v ∈ y → x = y)

namespace matching
variables {V} {G}


/--
`M.support` is the set of vertices of `G` that are
contained in some edge of the matching `M`
-/
def support (M : G.matching) : set V :=
{v : V | ∃ x, x ∈ M.edges ∧ v ∈ x}

--lemma matching.is_injective (M : G.matching) :


/-theorem hall :
  (∀ (A : finset α), A.card ≤ (image_rel r A).card)
    ↔ (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x))
  * `(A : finset α)` is `(S ⊆ b.color_set 0)`
  * `r : α → β → Prop` is `G.partite_adj`, but between the color classes somehow?
  * `image_rel r A` is `neighborhood`, but idk if that's even necessary
  * `(f : α → β), function.injective f ∧ ∀ x, r x (f x)` is `matching`
    - cast to function? cast injective function between bipartite color classes to matching?
  -/
theorem hall_marriage_theorem
  (h2 : fintype.card (b.color_set 0) ≤ fintype.card (b.color_set 1)) :
  (∀ (S ⊆ (b.color_finset 0)), card S ≤ card (G.neighbor_finset_image S))
   ↔ (∃ (M : G.matching), (b.color_set 0) ⊆ M.support) :=
begin
  have hall := hall (coloring.partition_adj b 0 1),
  cases hall with hall1 hall2,
  split,
  { intro h1,
    sorry },
  { intro h2,
    sorry },
end

end matching
end simple_graph
