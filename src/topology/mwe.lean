import topology.separation
--import data.fintype.basic

open_locale classical

open set finset

variables {α : Type*} [topological_space α]

lemma finset.my_induction {X : Type*} (P : finset X → finset X → Prop)
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

def dis : finset α → finset α → Prop :=
  λ (s t : finset α), disjoint s t → ∃ U V : (set α), (is_open U) ∧ is_open V ∧
  (∀ a : α, a ∈ s → a ∈ U) ∧ (∀ a : α, a ∈ t → a ∈ V) ∧ disjoint U V

lemma dis_symm (s t : finset α) : dis s t → dis t s :=
begin
 intros h1 d,
 obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := h1 (disjoint.symm d),
 exact ⟨V, U, oV, oU, bV, aU, disjoint.symm UV⟩
end

lemma dis_empty_right : ∀ {a : finset α}, dis a ∅ :=
λ a d, ⟨_, _, is_open_univ, is_open_empty, λ a h, mem_univ a, λ a h, by cases h, disjoint_empty _⟩

/-
lemma dis_singletons [t2_space α] : ∀ {a b : α}, dis ({a} : finset α) {b} :=
begin
  intros a b d,
  simp only [forall_eq, finset.mem_singleton, disjoint_iff_inter_eq_empty],
  exact t2_separation (finset.not_mem_singleton.mp (finset.disjoint_singleton.mp (disjoint.comm.mp d))),
end
-/

lemma dis_union_of : ∀ {a b c : finset α}, dis a c → dis b c → dis (a ∪ b) c :=
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

lemma disjoint_finset_t2 [t2_space α] : ∀ (s t : finset α), dis s t :=
begin
  refine finset.my_induction dis dis_symm (λ _, dis_empty_right) _ (λ _ _ _, dis_union_of),
  intros a b d,
  simp only [forall_eq, finset.mem_singleton, set.disjoint_iff_inter_eq_empty],
  exact t2_separation
    (finset.not_mem_singleton.mp (finset.disjoint_singleton.mp (disjoint.comm.mp d))),
end
