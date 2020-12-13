import topology.separation
--import data.fintype.basic

open_locale classical

open set finset

variables {α : Type*} [topological_space α]

-- to data/finset/basic
/--
To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
/-
lemma finset.induction_on_union {X : Type*} (P : finset X → finset X → Prop)
  (symm : ∀ {a b}, P a b → P b a)
  (empty_right : ∀ {a}, P a ∅)
  (singletons : ∀ {a b}, P {a} {b})
  (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) :
  ∀ a b, P a b :=
begin
  intros a b,
  refine finset.induction_on b empty_right (λ x s xs hi, symm _),
  rw finset.insert_eq,
  apply union_of _ (symm hi),
  refine finset.induction_on a empty_right (λ a t ta hi, symm _),
  rw finset.insert_eq,
  exact union_of singletons (symm hi),
end
-/

variables {ff : Type*}

-- to topology/separation
/-
/--
`separate` is a predicate on pairs of `finset`s of a topological space.  It holds if the two
`finset`s are contained in disjoint open sets.
-/
def separate : finset α → finset α → Prop :=
  λ (s t : finset α), disjoint s t → ∃ U V : (set α), (is_open U) ∧ is_open V ∧
  (∀ a : α, a ∈ s → a ∈ U) ∧ (∀ a : α, a ∈ t → a ∈ V) ∧ disjoint U V

lemma separate_symm (s t : finset α) : separate s t → separate t s :=
begin
 intros h1 d,
 obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := h1 (disjoint.symm d),
 exact ⟨V, U, oV, oU, bV, aU, disjoint.symm UV⟩
end

lemma separate_empty_right : ∀ {a : finset α}, separate a ∅ :=
λ a d, ⟨_, _, is_open_univ, is_open_empty, λ a h, mem_univ a, λ a h, by cases h, disjoint_empty _⟩

lemma separate_union_of : ∀ {a b c : finset α}, separate a c → separate b c → separate (a ∪ b) c :=
begin
  intros a b c ac bc d,
  obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := ac (disjoint_of_subset_left (subset_union_left _ _) d),
  obtain ⟨W, X, oW, oX, aW, bX, WX⟩ := bc (disjoint_of_subset_left (subset_union_right _ _) d),
  refine ⟨U ∪ W, V ∩ X, is_open_union oU oW, is_open_inter oV oX,
    λ x xab, _, λ x xc, ⟨bV _ xc, bX _ xc⟩, _⟩,
  { cases finset.mem_union.mp xab with h h,
    { exact mem_union_left W (aU x h) },
    { exact mem_union_right U (aW x h) } },
  { apply set.disjoint_union_left.mpr,
    exact ⟨disjoint_of_subset_right (inter_subset_left _ _) UV,
      disjoint_of_subset_right (inter_subset_right _ _) WX⟩ },
end

lemma separate_of_singletons :
  (∀ a b, separate ({a} : finset α) {b}) → (∀ s t, separate (s : finset α) t) :=
λ sep, finset.induction_on_union separate separate_symm (λ _, separate_empty_right)
  sep (λ _ _ _, separate_union_of)
-/

lemma disjoint_finset_t2 [t2_space α] : ∀ (s t : finset α), separate s t :=
begin
  apply separate_of_singletons,
  intros a b d,
  simp only [forall_eq, finset.mem_singleton, set.disjoint_iff_inter_eq_empty],
  exact t2_separation
    (finset.not_mem_singleton.mp (finset.disjoint_singleton.mp (disjoint.comm.mp d))),
end
