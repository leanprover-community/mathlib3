import data.fintype.basic
import topology.separation

open_locale classical

open set

/--
A couple of times, I found myself in the following situation:

I want to prove a lemma of the form ```∀ x y : Type*, R x y```
-/


lemma dind (P : ℕ → ℕ → Prop)
  (symm : ∀ a b, P a b ↔ P b a)
  (base : P 0 0)
  (indu : ∀ a b, P a b → P (a+1) b) :
  ∀ a b, P a b :=
begin
  intros a b,
  induction b with b hb,
  { induction a with a ha,
    { exact base },
    { exact indu a 0 ha } },
  { apply (symm a b.succ).mpr,
    apply indu,
    apply (symm a b).mp hb },
end



lemma finind {X : Type*} (P : finset X → finset X → Prop)
  (symm : ∀ a b, P a b ↔ P b a)
  (base : P ∅ ∅)
  (indu : ∀ a b : finset X, ∀ c : X, P a b → P (insert c a) b) :
  ∀ a b, P a b :=
begin
  intros a b,
  refine finset.induction_on b _ _,
  { refine finset.induction_on a _ _,
    { exact base },
    { intros x s xs hi,
      exact indu _ _ _ hi } },
  { intros x s xs hi,
    apply (symm a _).mpr,
    apply indu,
    apply (symm a _).mp hi },
end

def dis {α : Type*} [topological_space α] : finset α → finset α → Prop :=
  λ (s t : finset α), disjoint s t →
  ∃ U V : (set α), (is_open U) ∧ is_open V ∧ (∀ a : α, a ∈ s → a ∈ U) ∧ (∀ a : α, a ∈ t → a ∈ V)
  ∧ disjoint U V

lemma dis_symm {α : Type*} [topological_space α] (s t : finset α) : dis s t ↔ dis t s :=
begin
  split;
  { intros h1 d,
    unfold dis at h1,
    obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := h1 (disjoint.symm d),
    exact ⟨V, U, oV, oU, bV, aU, disjoint.symm UV⟩ }
end

lemma dis_empty {α : Type*} [topological_space α] : dis (∅ : finset α) ∅ :=
λ d, ⟨∅, ∅, is_open_empty, is_open_empty, λ a h, by cases h, λ a h, by cases h, empty_disjoint ∅⟩

lemma fin_ind {α : Type*} [topological_space α] [t2_space α] : ∀ (s t : finset α), dis s t :=
begin
--  revert s t,
  refine finind dis dis_symm dis_empty _,
  intros s t x ih d,
  obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := ih _,
--  revert s,
  obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := ih d,
end

#exit

lemma fin_ind {α : Type*} [topological_space α] [t2_space α] : ∀ (s t : finset α), disjoint s t →
  ∃ U V : (set α), (is_open U) ∧ is_open V ∧ (∀ a : α, a ∈ s → a ∈ U) ∧ (∀ a : α, a ∈ t → a ∈ V)
  ∧ disjoint U V :=
begin
--  revert s t,
  refine finind _ _ _,
end
