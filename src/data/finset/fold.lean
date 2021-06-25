/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.finset.basic
import data.multiset.fold

/-!
# The fold operation for a commutative associative operation over a finset.
-/

namespace finset
open multiset

variables {α β γ : Type*}

/-! ### fold -/
section fold
variables (op : β → β → β) [hc : is_commutative β op] [ha : is_associative β op]
local notation a * b := op a b
include hc ha

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = `f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : finset α) : β := (s.1.map f).fold op b

variables {op} {f : α → β} {b : β} {s : finset α} {a : α}

@[simp] theorem fold_empty : (∅ : finset α).fold op b f = b := rfl

@[simp] theorem fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f :=
by { dunfold fold, rw [cons_val, map_cons, fold_cons_left], }

@[simp] theorem fold_insert [decidable_eq α] (h : a ∉ s) :
  (insert a s).fold op b f = f a * s.fold op b f :=
by unfold fold; rw [insert_val, ndinsert_of_not_mem h, map_cons, fold_cons_left]

@[simp] theorem fold_singleton : ({a} : finset α).fold op b f = f a * b := rfl

@[simp] theorem fold_map {g : γ ↪ α} {s : finset γ} :
  (s.map g).fold op b f = s.fold op b (f ∘ g) :=
by simp only [fold, map, multiset.map_map]

@[simp] theorem fold_image [decidable_eq α] {g : γ → α} {s : finset γ}
  (H : ∀ (x ∈ s) (y ∈ s), g x = g y → x = y) : (s.image g).fold op b f = s.fold op b (f ∘ g) :=
by simp only [fold, image_val_of_inj_on H, multiset.map_map]

@[congr] theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g :=
by rw [fold, fold, map_congr H]

theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
  s.fold op (b₁ * b₂) (λx, f x * g x) = s.fold op b₁ f * s.fold op b₂ g :=
by simp only [fold, fold_distrib]

theorem fold_hom {op' : γ → γ → γ} [is_commutative γ op'] [is_associative γ op']
  {m : β → γ} (hm : ∀x y, m (op x y) = op' (m x) (m y)) :
  s.fold op' (m b) (λx, m (f x)) = m (s.fold op b f) :=
by rw [fold, fold, ← fold_hom op hm, multiset.map_map]

theorem fold_union_inter [decidable_eq α] {s₁ s₂ : finset α} {b₁ b₂ : β} :
  (s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f = s₁.fold op b₂ f * s₂.fold op b₁ f :=
by unfold fold; rw [← fold_add op, ← map_add, union_val,
     inter_val, union_add_inter, map_add, hc.comm, fold_add]

@[simp] theorem fold_insert_idem [decidable_eq α] [hi : is_idempotent β op] :
  (insert a s).fold op b f = f a * s.fold op b f :=
begin
  by_cases (a ∈ s),
  { rw [← insert_erase h], simp [← ha.assoc, hi.idempotent] },
  { apply fold_insert h },
end

theorem fold_image_idem [decidable_eq α] {g : γ → α} {s : finset γ}
  [hi : is_idempotent β op] :
  (image g s).fold op b f = s.fold op b (f ∘ g) :=
begin
  induction s using finset.cons_induction with x xs hx ih,
  { rw [fold_empty, image_empty, fold_empty] },
  { haveI := classical.dec_eq γ,
    rw [fold_cons, cons_eq_insert, image_insert, fold_insert_idem, ih], }
end

lemma fold_op_rel_iff_and
  {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ (r x y ∧ r x z)) {c : β} :
  r c (s.fold op b f) ↔ (r c b ∧ ∀ x∈s, r c (f x)) :=
begin
  classical,
  apply finset.induction_on s, { simp },
  clear s, intros a s ha IH,
  rw [finset.fold_insert ha, hr, IH, ← and_assoc, and_comm (r c (f a)), and_assoc],
  apply and_congr iff.rfl,
  split,
  { rintro ⟨h₁, h₂⟩, intros b hb, rw finset.mem_insert at hb,
    rcases hb with rfl|hb; solve_by_elim },
  { intro h, split,
    { exact h a (finset.mem_insert_self _ _), },
    { intros b hb, apply h b, rw finset.mem_insert, right, exact hb } }
end

lemma fold_op_rel_iff_or
  {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ (r x y ∨ r x z)) {c : β} :
  r c (s.fold op b f) ↔ (r c b ∨ ∃ x∈s, r c (f x)) :=
begin
  classical,
  apply finset.induction_on s, { simp },
  clear s, intros a s ha IH,
  rw [finset.fold_insert ha, hr, IH, ← or_assoc, or_comm (r c (f a)), or_assoc],
  apply or_congr iff.rfl,
  split,
  { rintro (h₁|⟨x, hx, h₂⟩),
    { use a, simp [h₁] },
    { refine ⟨x, by simp [hx], h₂⟩ } },
  { rintro ⟨x, hx, h⟩,
    rw mem_insert at hx, cases hx,
    { left, rwa hx at h },
    { right, exact ⟨x, hx, h⟩ } }
end

omit hc ha

@[simp]
lemma fold_union_empty_singleton [decidable_eq α] (s : finset α) :
  finset.fold (∪) ∅ singleton s = s :=
begin
  apply finset.induction_on s,
  { simp only [fold_empty], },
  { intros a s has ih, rw [fold_insert has, ih, insert_eq], }
end

lemma fold_sup_bot_singleton [decidable_eq α] (s : finset α) :
  finset.fold (⊔) ⊥ singleton s = s :=
fold_union_empty_singleton s

section order
variables [linear_order β] (c : β)

lemma le_fold_min : c ≤ s.fold min b f ↔ (c ≤ b ∧ ∀ x∈s, c ≤ f x) :=
fold_op_rel_iff_and $ λ x y z, le_min_iff

lemma fold_min_le : s.fold min b f ≤ c ↔ (b ≤ c ∨ ∃ x∈s, f x ≤ c) :=
begin
  show _ ≥ _ ↔ _,
  apply fold_op_rel_iff_or,
  intros x y z,
  show _ ≤ _ ↔ _,
  exact min_le_iff
end

lemma lt_fold_min : c < s.fold min b f ↔ (c < b ∧ ∀ x∈s, c < f x) :=
fold_op_rel_iff_and $ λ x y z, lt_min_iff

lemma fold_min_lt : s.fold min b f < c ↔ (b < c ∨ ∃ x∈s, f x < c) :=
begin
  show _ > _ ↔ _,
  apply fold_op_rel_iff_or,
  intros x y z,
  show _ < _ ↔ _,
  exact min_lt_iff
end

lemma fold_max_le : s.fold max b f ≤ c ↔ (b ≤ c ∧ ∀ x∈s, f x ≤ c) :=
begin
  show _ ≥ _ ↔ _,
  apply fold_op_rel_iff_and,
  intros x y z,
  show _ ≤ _ ↔ _,
  exact max_le_iff
end

lemma le_fold_max : c ≤ s.fold max b f ↔ (c ≤ b ∨ ∃ x∈s, c ≤ f x) :=
fold_op_rel_iff_or $ λ x y z, le_max_iff

lemma fold_max_lt : s.fold max b f < c ↔ (b < c ∧ ∀ x∈s, f x < c) :=
begin
  show _ > _ ↔ _,
  apply fold_op_rel_iff_and,
  intros x y z,
  show _ < _ ↔ _,
  exact max_lt_iff
end

lemma lt_fold_max : c < s.fold max b f ↔ (c < b ∨ ∃ x∈s, c < f x) :=
fold_op_rel_iff_or $ λ x y z, lt_max_iff

end order

end fold

end finset
