import tactic.set
import tactic.ext
import tactic.tauto
import data.set.default
import data.finset.default

open set

namespace set_tests
universe v
variables {α β: Type*} {a:α} {s t u : set α} {f g : β → set α} 

lemma top_eq_univ : (⊤ : set α) = univ := by set_taut
lemma bot_eq_empty : (⊥ : set α) = ∅ :=  by set_taut
lemma sup_eq_union (s t : set α) : s ⊔ t = s ∪ t := by set_taut
lemma inf_eq_inter (s t : set α) : s ⊓ t = s ∩ t := by set_taut
lemma le_eq_subset (s t : set α) : s ≤ t = (s ⊆ t) := by set_taut





theorem set_of_set {s : set α} : set_of s = s := by set_taut

lemma sep_set_of {p q : α → Prop} : {a ∈ {a | p a } | q a} = {a | p a ∧ q a} := by set_taut

lemma set_of_and {p q : α → Prop} : {a | p a ∧ q a} = {a | p a} ∩ {a | q a} := by set_taut

lemma set_of_or {p q : α → Prop} : {a | p a ∨ q a} = {a | p a} ∪ {a | q a} := 
 by set_taut

theorem empty_def : (∅ : set α) = {x | false} :=  by set_taut

theorem set_of_false : {a : α | false} = ∅ := by set_taut

theorem set_of_true : {x : α | true} = univ := by set_taut

theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := by set_taut

theorem union_self (a : set α) : a ∪ a = a := by set_taut

theorem union_empty (a : set α) : a ∪ ∅ = a := by set_taut

theorem empty_union (a : set α) : ∅ ∪ a = a := by set_taut

theorem union_comm (a b : set α) : a ∪ b = b ∪ a := by set_taut

theorem union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) := by set_taut

theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) := by set_taut

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ := by set_taut

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by set_taut

--How???
theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by set_taut


lemma union_univ {s : set α} : s ∪ univ = univ := by set_taut

lemma univ_union {s : set α} : univ ∪ s = univ := by set_taut

theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := by set_taut

lemma inter_comm : s ∩ t = t ∩ s := by set_taut

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) := by set_taut

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by set_taut

theorem inter_univ (a : set α) : a ∩ univ = a := by set_taut

theorem univ_inter (a : set α) : univ ∩ a = a := by set_taut

theorem union_inter_cancel_left {s t : set α} : (s ∪ t) ∩ s = s := by set_taut

theorem union_inter_cancel_right {s t : set α} : (s ∪ t) ∩ t = t := by set_taut

/-! ### Distributivity laws -/

theorem inter_distrib_left (s t u : set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
by set_taut'

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
by set_taut'

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
by set_taut'

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
by set_taut'

theorem insert_def (x : α) (s : set α) : insert x s = { y | y = x ∨ y ∈ s } := 
by set_taut

theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by set_taut

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) := by set_taut

theorem insert_union (a:α) : insert a s ∪ t = insert a (s ∪ t) := by set_taut

theorem union_insert (a:α) : s ∪ insert a t = insert a (s ∪ t) := by set_taut

lemma insert_inter (x : α) (s t : set α) : insert x (s ∩ t) = insert x s ∩ insert x t := by set_taut

/-! ### Lemmas about singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ := by set_taut

lemma set_of_eq_eq_singleton {a : α} : {n | n = a} = {a} := by set_taut

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s := by set_taut

theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} := by set_taut

theorem pair_comm (a b : α) : ({a, b} : set α) = {b, a} := by set_taut

theorem set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} := by set_taut

theorem singleton_union : {a} ∪ s = insert a s := by set_taut

theorem union_singleton : s ∪ {a} = insert a s := by set_taut


theorem sep_mem_eq {s t : set α} : {x ∈ s | x ∈ t} = s ∩ t := by set_taut


theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} :
  x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) := by set_taut


theorem eq_sep_of_subset {s t : set α} (h : s ⊆ t) : s = {x ∈ t | x ∈ s} := by set_taut

lemma sep_univ {α} {p : α → Prop} : {a ∈ (univ : set α) | p a} = {a | p a} := by set_taut

--TODO: test the rest of the file data.set.basic.

/- Here are some more complex lemmas -/
lemma Inter_inter_eq_Inter_inter : (⋂ b, f b ∩ g b) = ⋂ b, (g b ∩ f b) :=
by set_taut'

lemma Inter_inter_eq_Inter_inter'' : (⋂ b, f b) ∩ (⋂ b, g b) = ⋂ b, (g b ∩ f b) :=
by set_taut'

lemma Union_inter_eq_Union_inter' : (⋃ b, f b ∩ g b) = ⋃ b, (g b ∩ f b) :=
by set_taut

lemma Inter_inter_eq_Inter_inter_of_nonempty {κ : Type*} [nonempty κ]
  (f : κ → set α) : (⋂ b, f b) ∩ s = ⋂ b, f b ∩ s  := by set_taut

/- It would be good to have a pattern like this, but it doesn't work
   well. Need to add intros or set.subset_def. -/
meta def solve_subsetsh : tactic unit :=
do lemmas ← simp_lemmas.mk_default,
do (tactic.simp_all lemmas []),
do tactic.tautology

lemma Inter_inter_subset_Inter_inter : (⋂ b, f b) ∩ s ⊆ ⋂ b, f b ∩ s  := begin
  rw set.subset_def, solve_subsetsh,
end 
 
lemma subset_trans (h_st : s ⊆ t) (h_tu : t ⊆ u)  : s ⊆ u := begin
  rw set.subset_def, 
  --intros x h1,
  tautology,
end 

lemma imp_trans' (P Q R : α → Prop) (h_PQ : ∀ a, P a → Q a) (h_QR : ∀ a, Q a → R a) (a' : α) (h_P : P a') : R a' := begin
  tautology,
end 

end set_tests

section finset_tests
variables {α β: Type*} [decidable_eq α] {s t u : finset α} {f : β → set α} 
lemma inter_comm' : s ∩ t = t ∩ s := by set_taut


lemma union_comm' : s ∪ t = t ∪ s := by set_taut

lemma inter_assoc' : (s ∩ t) ∩ u = s ∩ (t ∩ u) := by set_taut

lemma union_assoc' : (s ∪ t) ∪ u = s ∪ (t ∪ u) := by set_taut

lemma union_distrib : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by set_taut

lemma union_distrib_comm : (s ∪ t) ∩ u = (t ∩ u) ∪ (s ∩ u) := by set_taut

lemma Inter_union : (s ∪ t) ∩ u = (t ∩ u) ∪ (s ∩ u) := by set_taut

end finset_tests

