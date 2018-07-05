import tactic data.stream.basic data.set.basic data.finset data.multiset
       tactic.transport

open tactic

universe u
variable {α : Type}

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  dunfold has_subset.subset has_inter.inter at *,
--  trace_state,
  intro1, triv
end

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  delta has_subset.subset has_inter.inter at *,
--  trace_state,
  intro1, triv
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp at *,
--  trace_state,
  rw [←h, ←h']
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp at *,
  simp [h] at h',
  simp [*]
end

def my_id (x : α) := x

def my_id_def (x : α) : my_id x = x := rfl

example (x y z : ℕ) (h'' : true) (h : 0 + my_id y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp [my_id_def] at *, simp [h] at h', simp [*]
end

@[simp] theorem mem_set_of {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

-- TODO: write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl
theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
begin
  dsimp [subset_def, union_def] at *,
  intros x h,
  cases h; back_chaining_using_hs
end

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
begin
  dsimp [subset_def, inter_def] at *,
  intros x h,
  split; back_chaining_using_hs
end

/- extensionality -/

example : true :=
begin
  have : ∀ (s₀ s₁ : set ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target x ∈ s₀ ↔ x ∈ s₁,
    admit },
  have : ∀ (s₀ s₁ : finset ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target a ∈ s₀ ↔ a ∈ s₁,
    admit },
  have : ∀ (s₀ s₁ : multiset ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target multiset.count a s₀ = multiset.count a s₁,
    admit },
  have : ∀ (s₀ s₁ : list ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target list.nth s₀ n = list.nth s₁ n,
    admit },
  have : ∀ (s₀ s₁ : stream ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target stream.nth n s₀ = stream.nth n s₁,
    admit },
  have : ∀ n (s₀ s₁ : array n ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target array.read s₀ i = array.read s₁ i,
    admit },
  trivial
end

/- tauto -/

example (p : Prop) : p ∧ true ↔ p := by tauto

example (p : Prop) : p ∨ false → p := by tauto

/- transport -/
open tactic tactic.interactive

-- set_option profiler true

-- run_cmd do
--  mk_transportable_instance `group
-- run_cmd do
--  mk_transportable_instance `monoid
-- run_cmd do
--  mk_transportable_instance `ring
-- run_cmd do
--  mk_transportable_instance `field

-- run_cmd do
--  mk_to_fun `group
-- run_cmd do
--  mk_to_fun `monoid

-- set_option pp.notation false
set_option trace.app_builder true

-- run_cmd do
--  mk_to_fun `ring
run_cmd do
 mk_to_fun `field

-- run_cmd do
--  mk_to_fun `group >>= mk_on_equiv `group
-- run_cmd do
--  mk_to_fun `monoid >>= mk_on_equiv `monoid
-- run_cmd do
--  mk_to_fun `ring >>= mk_on_equiv `ring
-- run_cmd do
--  mk_to_fun `field >>= mk_on_equiv `field

-- attribute [derive transportable] group
-- attribute [derive transportable] monoid
-- attribute [derive transportable] ring
-- attribute [derive transportable] field
