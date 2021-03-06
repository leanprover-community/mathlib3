/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import tactic.set
import tactic.ext
import tactic.tauto
import data.set.default
import data.finset.default

/-! The set equality lemmas from the file data.set.basic, reproven with set_taut or set_taut'.

  Did not include iff lemmas nor those that had additional
  conditions that didn't work. -/
open set

namespace set_tests
universe v
variables {α β: Type*} {a:α} {s t u : set α} {f g : β → set α}

lemma top_eq_univ : (⊤ : set α) = univ := by tactic.timetac "top_eq_univ" set_taut
lemma bot_eq_empty : (⊥ : set α) = ∅ :=  by tactic.timetac "bot_eq_empty" set_taut
lemma sup_eq_union (s t : set α) : s ⊔ t = s ∪ t := by tactic.timetac "sup_eq_union" set_taut
lemma inf_eq_inter (s t : set α) : s ⊓ t = s ∩ t := by tactic.timetac "inf_eq_inter" set_taut
lemma le_eq_subset (s t : set α) : s ≤ t = (s ⊆ t) := by tactic.timetac "le_eq_subset" set_taut

theorem set_of_set {s : set α} : set_of s = s := by tactic.timetac "set_of_set" set_taut

lemma sep_set_of {p q : α → Prop} : {a ∈ {a | p a } | q a} = {a | p a ∧ q a} := by tactic.timetac "sep_set_of" set_taut

lemma set_of_and {p q : α → Prop} : {a | p a ∧ q a} = {a | p a} ∩ {a | q a} := by tactic.timetac "set_of_and" set_taut

lemma set_of_or {p q : α → Prop} : {a | p a ∨ q a} = {a | p a} ∪ {a | q a} := by tactic.timetac "set_of_or" set_taut

theorem empty_def : (∅ : set α) = {x | false} :=  by tactic.timetac "empty_def" set_taut

theorem set_of_false : {a : α | false} = ∅ := by tactic.timetac "set_of_false" set_taut

theorem set_of_true : {x : α | true} = univ := by tactic.timetac "set_of_true" set_taut

theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := by tactic.timetac "union_def" set_taut

theorem union_self (a : set α) : a ∪ a = a := by tactic.timetac "union_self" set_taut

theorem union_empty (a : set α) : a ∪ ∅ = a := by tactic.timetac "union_empty" set_taut

theorem empty_union (a : set α) : ∅ ∪ a = a := by tactic.timetac "empty_union" set_taut

theorem union_comm (a b : set α) : a ∪ b = b ∪ a := by tactic.timetac "union_comm" set_taut

theorem union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
by tactic.timetac "union_assoc" set_taut

theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by tactic.timetac "union_left_comm" set_taut

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by tactic.timetac "union_right_comm" set_taut

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by tactic.timetac "union_eq_self_of_subset_left" set_taut

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by tactic.timetac "union_eq_self_of_subset_right" set_taut

lemma union_univ {s : set α} : s ∪ univ = univ :=
by tactic.timetac "union_univ" set_taut

lemma univ_union {s : set α} : univ ∪ s = univ :=
by tactic.timetac "univ_union" set_taut

theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} :=
by tactic.timetac "inter_def" set_taut

lemma inter_comm : s ∩ t = t ∩ s :=
by tactic.timetac "inter_comm" set_taut

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by tactic.timetac "inter_left_comm" set_taut

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by tactic.timetac "inter_right_comm" set_taut

theorem inter_univ (a : set α) : a ∩ univ = a :=
by tactic.timetac "inter_univ" set_taut

theorem univ_inter (a : set α) : univ ∩ a = a :=
by tactic.timetac "univ_inter" set_taut

theorem union_inter_cancel_left {s t : set α} : (s ∪ t) ∩ s = s :=
by tactic.timetac "union_inter_cancel_left" set_taut

theorem union_inter_cancel_right {s t : set α} : (s ∪ t) ∩ t = t :=
by tactic.timetac "union_inter_cancel_right" set_taut

/-! ### Distributivity laws -/

theorem inter_distrib_left (s t u : set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
by tactic.timetac "inter_distrib_left" set_taut'

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
by tactic.timetac "inter_distrib_right" set_taut'

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
by tactic.timetac "union_distrib_left" set_taut

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
by tactic.timetac "union_distrib_right" set_taut'


theorem insert_def (x : α) (s : set α) : insert x s = { y | y = x ∨ y ∈ s } :=
by tactic.timetac "insert_def" set_taut

theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by tactic.timetac "insert_eq_of_mem" set_taut

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
by tactic.timetac "insert_comm" set_taut

theorem insert_union (a:α) : insert a s ∪ t = insert a (s ∪ t) :=
by tactic.timetac "insert_union" set_taut

theorem union_insert (a:α) : s ∪ insert a t = insert a (s ∪ t) :=
by tactic.timetac "union_insert" set_taut

lemma insert_inter (x : α) (s t : set α) : insert x (s ∩ t) = insert x s ∩ insert x t :=
by tactic.timetac "insert_inter" set_taut

/-! ### Lemmas about singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ :=
by tactic.timetac "singleton_def" set_taut

lemma set_of_eq_eq_singleton {a : α} : {n | n = a} = {a} :=
by tactic.timetac "set_of_eq_eq_singleton" set_taut

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by tactic.timetac "insert_eq" set_taut

theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by tactic.timetac "pair_eq_singleton" set_taut

theorem pair_comm (a b : α) : ({a, b} : set α) = {b, a} :=
by tactic.timetac "pair_comm" set_taut

theorem set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
by tactic.timetac "set_compr_eq_eq_singleton" set_taut

theorem singleton_union : {a} ∪ s = insert a s :=
by tactic.timetac "singleton_union" set_taut

theorem union_singleton : s ∪ {a} = insert a s :=
by tactic.timetac "union_singleton" set_taut

theorem sep_mem_eq {s t : set α} : {x ∈ s | x ∈ t} = s ∩ t :=
by tactic.timetac "sep_mem_eq" set_taut

theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} :
  x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) :=
by tactic.timetac "mem_sep_eq" set_taut

theorem eq_sep_of_subset {s t : set α} (h : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
by tactic.timetac "eq_sep_of_subset" set_taut

lemma sep_univ {α} {p : α → Prop} : {a ∈ (univ : set α) | p a} = {a | p a} :=
by tactic.timetac "sep_univ" set_taut

lemma compl_set_of {α} (p : α → Prop) : {a | p a}ᶜ = { a | ¬ p a } :=
by tactic.timetac "compl_set_of" set_taut

theorem mem_compl_eq (s : set α) (x : α) : x ∈ sᶜ = (x ∉ s) :=
by tactic.timetac "mem_compl_eq" set_taut

theorem inter_compl_self (s : set α) : s ∩ sᶜ = ∅ :=
by tactic.timetac "inter_compl_self" set_taut

theorem compl_inter_self (s : set α) : sᶜ ∩ s = ∅ :=
by tactic.timetac "compl_inter_self" set_taut

theorem compl_empty : (∅ : set α)ᶜ = univ :=
by tactic.timetac "compl_empty" set_taut


theorem compl_union (s t : set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
by tactic.timetac "compl_union" set_taut'

theorem compl_inter (s t : set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
by tactic.timetac "compl_inter" set_taut'

theorem compl_univ : (univ : set α)ᶜ = ∅ := by tactic.timetac "compl_univ" set_taut'


lemma compl_singleton_eq (a : α) : ({a} : set α)ᶜ = {x | x ≠ a} := by tactic.timetac "compl_singleton_eq" set_taut

lemma compl_ne_eq_singleton (a : α) : ({x | x ≠ a} : set α)ᶜ = {a} :=
by tactic.timetac "compl_ne_eq_singleton" set_taut

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
by tactic.timetac "union_eq_compl_compl_inter_compl" set_taut

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
by tactic.timetac "inter_eq_compl_compl_union_compl" set_taut

theorem union_compl_self (s : set α) : s ∪ sᶜ = univ := by tactic.timetac "union_compl_self" set_taut

theorem compl_union_self (s : set α) : sᶜ ∪ s = univ := by tactic.timetac "compl_union_self" set_taut

theorem compl_comp_compl : compl ∘ compl = @id (set α) := by tactic.timetac "compl_comp_compl" set_taut

theorem diff_eq (s t : set α) : s \ t = s ∩ tᶜ := by tactic.timetac "diff_eq" set_taut

theorem diff_eq_compl_inter {s t : set α} : s \ t = tᶜ ∩ s := by tactic.timetac "diff_eq_compl_inter" set_taut

theorem union_diff_cancel' {s t u : set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ (u \ s) = u := by tactic.timetac "union_diff_cancel'" set_taut


theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
by tactic.timetac "union_diff_cancel" set_taut


theorem union_diff_left {s t : set α} : (s ∪ t) \ s = t \ s :=
by tactic.timetac "union_diff_left" set_taut

theorem union_diff_right {s t : set α} : (s ∪ t) \ t = s \ t :=
by tactic.timetac "union_diff_right" set_taut

theorem union_diff_distrib {s t u : set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
by tactic.timetac "union_diff_distrib" set_taut'

theorem inter_union_distrib_left {s t u : set α} : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by tactic.timetac "inter_union_distrib_left" set_taut'

theorem inter_union_distrib_right {s t u : set α} : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) := by tactic.timetac "inter_union_distrib_right" set_taut'

theorem union_inter_distrib_left {s t u : set α} : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=  by tactic.timetac "union_inter_distrib_left" set_taut'

theorem union_inter_distrib_right {s t u : set α} : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by tactic.timetac "union_inter_distrib_right" set_taut'

theorem inter_diff_assoc (a b c : set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
by tactic.timetac "inter_diff_assoc" set_taut

theorem inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
by tactic.timetac "inter_diff_self" set_taut

theorem inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s := by tactic.timetac "inter_union_diff" set_taut

theorem inter_union_compl (s t : set α) : (s ∩ t) ∪ (s ∩ tᶜ) = s := by tactic.timetac "inter_union_compl" set_taut



theorem compl_eq_univ_diff (s : set α) : sᶜ = univ \ s :=
by tactic.timetac "compl_eq_univ_diff" set_taut

lemma empty_diff (s : set α) : (∅ \ s : set α) = ∅ := by tactic.timetac "empty_diff" set_taut


theorem diff_empty {s : set α} : s \ ∅ = s := by tactic.timetac "diff_empty" set_taut

theorem diff_diff {u : set α} : s \ t \ u = s \ (t ∪ u) := by tactic.timetac "diff_diff" set_taut

-- the following statement contains parentheses to help the reader
lemma diff_diff_comm {s t u : set α} : (s \ t) \ u = (s \ u) \ t := by tactic.timetac "diff_diff_comm" set_taut

lemma diff_inter {s t u : set α} : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
by set_taut'

lemma diff_inter_diff {s t u : set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
by set_taut'

lemma diff_compl : s \ tᶜ = s ∩ t := by tactic.timetac "diff_compl" set_taut'

lemma diff_diff_right {s t u : set α} : s \ (t \ u) = (s \ t) ∪ (s ∩ u) :=
by set_taut'

theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
by by set_taut'

lemma insert_diff_self_of_not_mem {a : α} {s : set α} (h : a ∉ s) :
  insert a s \ {a} = s :=
by set_taut'


theorem union_diff_self {s t : set α} : s ∪ (t \ s) = s ∪ t :=
by set_taut'

theorem diff_union_self {s t : set α} : (s \ t) ∪ t = s ∪ t :=
by set_taut'

theorem diff_inter_self {a b : set α} : (b \ a) ∩ a = ∅ :=
by set_taut'

theorem diff_inter_self_eq_diff {s t : set α} : s \ (t ∩ s) = s \ t :=
by set_taut'

theorem diff_self_inter {s t : set α} : s \ (s ∩ t) = s \ t :=
by set_taut'

theorem diff_singleton_eq_self {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s := by tactic.timetac "diff_singleton_eq_self" set_taut'

theorem insert_diff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s := by set_taut'

lemma diff_self {s : set α} : s \ s = ∅ := by tactic.timetac "diff_self" set_taut'

lemma diff_diff_cancel_left {s t : set α} (h : s ⊆ t) : t \ (t \ s) = s :=
by set_taut'

end set_tests

namespace set_tests
variables {α β γ:Type*}
section preimage
variables {f : α → β} {g : β → γ}

theorem preimage_empty : f ⁻¹' ∅ = ∅ := by tactic.timetac "preimage_empty" set_taut


lemma preimage_congr {f g : α → β} {s : set β} (h : ∀ (x : α), f x = g x) : f ⁻¹' s = g ⁻¹' s := by tactic.timetac "preimage_congr" set_taut

theorem preimage_univ : f ⁻¹' univ = univ := by tactic.timetac "preimage_univ" set_taut

theorem subset_preimage_univ {s : set α} : s ⊆ f ⁻¹' univ := subset_univ _

theorem preimage_inter {s t : set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
by set_taut

theorem preimage_union {s t : set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
by set_taut

theorem preimage_compl {s : set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ := by tactic.timetac "preimage_compl" set_taut

theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := by set_taut

theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' {a | p a} = {a | p (f a)} := by tactic.timetac "preimage_set_of_eq" set_taut

theorem preimage_id {s : set α} : id ⁻¹' s = s := by tactic.timetac "preimage_id" set_taut

theorem preimage_id' {s : set α} : (λ x, x) ⁻¹' s = s := by tactic.timetac "preimage_id'" set_taut

theorem preimage_const_of_mem {b : β} {s : set β} (h : b ∈ s) :
  (λ (x : α), b) ⁻¹' s = univ := by set_taut

theorem preimage_const_of_not_mem {b : β} {s : set β} (h : b ∉ s) :
  (λ (x : α), b) ⁻¹' s = ∅ := by set_taut

theorem preimage_const (b : β) (s : set β) [decidable (b ∈ s)] :
  (λ (x : α), b) ⁻¹' s = if b ∈ s then univ else ∅ := begin
  cases decidable.em (b ∈ s) ; set_taut,
end

theorem preimage_comp {s : set γ} : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := by tactic.timetac "preimage_comp" set_taut

lemma preimage_preimage {g : β → γ} {f : α → β} {s : set γ} :
  f ⁻¹' (g ⁻¹' s) = (λ x, g (f x)) ⁻¹' s := by set_taut'

--Although this is set equality, set_taut' totally fails.
lemma preimage_coe_coe_diagonal {α : Type*} (s : set α) :
  (prod.map coe coe) ⁻¹' (diagonal α) = diagonal s := begin
  ext ⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩,
  simp [set.diagonal],
end

end preimage

end set_tests
-/
namespace set_tests
universe v
variables {α β: Type*} {a:α} {s t u : set α} {f g : β → set α}

--TODO: test the rest of the file data.set.basic.

/- Here are some more complex lemmas
   Inter_inter_eq_Inter_inter is what requires the additional lemma in
   set_taut. -/
lemma Inter_inter_eq_Inter_inter : (⋂ b, f b ∩ g b) = ⋂ b, (g b ∩ f b) :=
by set_taut'

lemma Inter_inter_eq_Inter_inter'' : (⋂ b, f b) ∩ (⋂ b, g b) = ⋂ b, (g b ∩ f b) :=
by set_taut'

lemma Union_inter_eq_Union_inter' : (⋃ b, f b ∩ g b) = ⋃ b, (g b ∩ f b) :=
by set_taut

lemma Inter_inter_eq_Inter_inter_of_nonempty {κ : Type*} [nonempty κ]
  (f : κ → set α) : (⋂ b, f b) ∩ s = ⋂ b, f b ∩ s  := by set_taut

end set_tests

section finset_tests
variables {α β: Type*} [decidable_eq α] {s t u : finset α} {f : β → set α}
lemma inter_comm' : s ∩ t = t ∩ s := by tactic.timetac "inter_comm'" set_taut


lemma union_comm' : s ∪ t = t ∪ s := by tactic.timetac "union_comm'" set_taut

lemma inter_assoc' : (s ∩ t) ∩ u = s ∩ (t ∩ u) := by tactic.timetac "inter_assoc'" set_taut

lemma union_assoc' : (s ∪ t) ∪ u = s ∪ (t ∪ u) := by tactic.timetac "union_assoc'" set_taut

lemma union_distrib : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by tactic.timetac "union_distrib" set_taut

lemma union_distrib_comm : (s ∪ t) ∩ u = (t ∩ u) ∪ (s ∩ u) := by tactic.timetac "union_distrib_comm" set_taut

lemma Inter_union : (s ∪ t) ∩ u = (t ∩ u) ∪ (s ∩ u) := by tactic.timetac "Inter_union" set_taut

end finset_tests

