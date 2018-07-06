import tactic data.stream.basic data.set.basic data.finset data.multiset
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

-- 260ms -- 82ms -- 214ms -- 38ms -- 30ms
example (p : Prop) : p ∧ true ↔ p := by tauto

-- 380ms -- 127ms -- 214ms -- 54ms -- 60ms
example (p : Prop) : p ∨ false ↔ p := by tauto
-- 1.66s -- 455ms -- 204ms -- 78ms -- 100ms
example (p q r : Prop) [decidable p] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
-- 1.67s -- 485ms -- 135ms -- 90ms -- 76ms
example (p q r : Prop) [decidable q] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
-- 1.63s -- 547ms -- 138ms -- 76ms -- 80ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ p) : q := by tauto
-- 1.55s -- 419ms -- 248ms -- 118ms -- 85ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : p) : ¬ q := by tauto
-- 1.62s -- 441ms -- 171ms -- 103ms -- 119ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by tauto
-- 2.41s -- 597ms -- 230ms -- 129ms -- 125ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ q) : p := by tauto
-- 5.38s -- 1.56s -- 1.18s -- 639ms -- 524ms
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ q) (h'' : ¬ p) : false := by tauto
-- 5.38s -- 1.61s -- 643ms -- 314ms -- 505ms
example (p q r : Prop) [decidable q] [decidable p] (h : p ↔ q) (h' : r ↔ q) (h'' : ¬ r) : ¬ p := by tauto
-- 3.7s -- 965ms -- 613ms -- 661ms -- 298ms
example (p q r : Prop) [decidable q] [decidable p] (h : p ↔ q) (h' : r ↔ q) : p ↔ r := by tauto
-- 7.27s -- 1.9s -- 1.32s -- 332ms -- 305ms
example (p q r : Prop) [decidable p] [decidable q] [decidable r] (h : ¬ p = q) (h' : r = q) : p ↔ ¬ r := by tauto
