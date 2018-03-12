/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro

Finite sets.
-/
import data.multiset order.boolean_algebra algebra.order_functions data.sigma.basic
open multiset subtype nat lattice

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

namespace finset

theorem eq_of_veq : ∀ {s t : finset α}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ h := by congr; assumption

@[simp] theorem val_inj {s t : finset α} : s.1 = t.1 ↔ s = t :=
⟨eq_of_veq, congr_arg _⟩

@[simp] theorem erase_dup_eq_self [decidable_eq α] (s : finset α) : erase_dup s.1 = s.1 :=
erase_dup_eq_self.2 s.2

end finset

namespace finset

instance has_decidable_eq [decidable_eq α] : decidable_eq (finset α)
| s₁ s₂ := decidable_of_iff _ val_inj

/- membership -/

instance : has_mem α (finset α) := ⟨λ a s, a ∈ s.1⟩

theorem mem_def {a : α} {s : finset α} : a ∈ s ↔ a ∈ s.1 := iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @finset.mk α s nd ↔ a ∈ s := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : finset α) : decidable (a ∈ s) :=
multiset.decidable_mem _ _

/- extensionality -/
theorem ext {s₁ s₂ : finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
val_inj.symm.trans $ nodup_ext s₁.2 s₂.2

/- subset -/

instance : has_subset (finset α) := ⟨λ s₁ s₂, ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂⟩

theorem subset_def {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ s₁.1 ⊆ s₂.1 := iff.rfl

@[simp] theorem subset.refl (s : finset α) : s ⊆ s := subset.refl _

theorem subset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := subset.trans

theorem mem_of_subset {s₁ s₂ : finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ := mem_of_subset

theorem subset.antisymm {s₁ s₂ : finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext.2 $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ (∀x, x ∈ s₁ → x ∈ s₂) := iff.rfl

@[simp] theorem val_le_iff {s₁ s₂ : finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ := le_iff_subset s₁.2

instance : has_ssubset (finset α) := ⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance : partial_order (finset α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _,
  le_antisymm := @subset.antisymm _ }

@[simp] theorem le_iff_subset {s₁ s₂ : finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ := iff.rfl
@[simp] theorem lt_iff_ssubset {s₁ s₂ : finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ := iff.rfl

@[simp] theorem val_lt_iff {s₁ s₂ : finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
and_congr val_le_iff $ not_congr val_le_iff

/- empty -/
protected def empty : finset α := ⟨0, nodup_zero⟩

instance : has_emptyc (finset α) := ⟨finset.empty⟩

instance : inhabited (finset α) := ⟨∅⟩

@[simp] theorem empty_val : (∅ : finset α).1 = 0 := rfl

@[simp] theorem not_mem_empty (a : α) : a ∉ (∅ : finset α) := id

@[simp] theorem ne_empty_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ≠ ∅
| e := not_mem_empty a $ e ▸ h

@[simp] theorem empty_subset (s : finset α) : ∅ ⊆ s := zero_subset _

theorem eq_empty_of_forall_not_mem {s : finset α} (H : ∀x, x ∉ s) : s = ∅ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

@[simp] theorem val_eq_zero {s : finset α} : s.1 = 0 ↔ s = ∅ := @val_inj _ s ∅

theorem subset_empty {s : finset α} : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

theorem exists_mem_of_ne_empty {s : finset α} (h : s ≠ ∅) : ∃ a : α, a ∈ s :=
exists_mem_of_ne_zero (mt val_eq_zero.1 h)

/-- `singleton a` is the set `{a}` containing `a` and nothing else. -/
def singleton (a : α) : finset α := ⟨_, nodup_singleton a⟩
local prefix `ι`:90 := singleton

@[simp] theorem singleton_val (a : α) : (ι a).1 = a :: 0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ι a ↔ b = a :=
by simp [singleton]

theorem not_mem_singleton {a b : α} : a ∉ ι b ↔ a ≠ b := by simp

theorem mem_singleton_self (a : α) : a ∈ ι a := by simp

theorem singleton_inj {a b : α} : ι a = ι b ↔ a = b :=
⟨λ h, mem_singleton.1 (h ▸ mem_singleton_self _), congr_arg _⟩

@[simp] theorem singleton_ne_empty (a : α) : ι a ≠ ∅ := ne_empty_of_mem (mem_singleton_self _)

/- insert -/
section decidable_eq
variables [decidable_eq α]

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : has_insert α (finset α) := ⟨λ a s, ⟨_, nodup_ndinsert a s.2⟩⟩

@[simp] theorem has_insert_eq_insert (a : α) (s : finset α) : has_insert.insert a s = insert a s := rfl

theorem insert_def (a : α) (s : finset α) : insert a s = ⟨_, nodup_ndinsert a s.2⟩ := rfl

@[simp] theorem insert_val (a : α) (s : finset α) : (insert a s).1 = ndinsert a s.1 := rfl

theorem insert_val' (a : α) (s : finset α) : (insert a s).1 = erase_dup (a :: s.1) :=
by simp [erase_dup_cons]

@[simp] theorem mem_insert {a b : α} {s : finset α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := mem_ndinsert

theorem mem_insert_self (a : α) (s : finset α) : a ∈ insert a s := by simp
theorem mem_insert_of_mem {a b : α} {s : finset α} (h : a ∈ s) : a ∈ insert b s := by simp *
theorem mem_of_mem_insert_of_ne {a b : α} {s : finset α} (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
(mem_insert.1 h).resolve_left

@[simp] theorem insert_eq_of_mem {a : α} {s : finset α} (h : a ∈ s) : insert a s = s :=
eq_of_veq $ ndinsert_of_mem h

@[simp] theorem insert.comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
ext.2 $ by simp [or.left_comm]

@[simp] theorem insert_idem (a : α) (s : finset α) : insert a (insert a s) = insert a s :=
ext.2 $ by simp

@[simp] theorem insert_ne_empty (a : α) (s : finset α) : insert a s ≠ ∅ :=
ne_empty_of_mem (mem_insert_self a s)

theorem insert_subset {a : α} {s t : finset α} : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp [subset_iff, or_imp_distrib, forall_and_distrib]

theorem subset_insert [h : decidable_eq α] (a : α) (s : finset α) : s ⊆ insert a s :=
λ b, mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
insert_subset.2 ⟨mem_insert_self _ _, subset.trans h (subset_insert _ _)⟩

lemma ssubset_iff {s t : finset α} : s ⊂ t ↔ (∃a, a ∉ s ∧ insert a s ⊆ t) :=
iff.intro
  (assume ⟨h₁, h₂⟩,
    have ∃a, a ∈ t ∧ a ∉ s, by simpa [finset.subset_iff, classical.not_forall] using h₂,
    let ⟨a, hat, has⟩ := this in ⟨a, has, insert_subset.mpr ⟨hat, h₁⟩⟩)
  (assume ⟨a, hat, has⟩,
    let ⟨h₁, h₂⟩ := insert_subset.mp has in
    ⟨h₂, assume h, hat $ h h₁⟩)

lemma ssubset_insert {s : finset α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
ssubset_iff.mpr ⟨a, h, subset.refl _⟩

@[recursor 6] protected theorem induction {p : finset α → Prop}
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
    cases nodup_cons.1 nd with m nd',
    rw [← (eq_of_veq _ : insert a (finset.mk s _) = ⟨a::s, nd⟩)],
    { exact h₂ (by exact m) (IH nd') },
    { rw [insert_val, ndinsert_of_not_mem m] }
  end) nd

@[elab_as_eliminator] protected theorem induction_on {p : finset α → Prop} (s : finset α)
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

@[simp] theorem singleton_eq_singleton (a : α) : _root_.singleton a = singleton a := rfl

@[simp] theorem insert_empty_eq_singleton (a : α) : {a} = singleton a := rfl

@[simp] theorem insert_singleton_self_eq (a : α) : ({a, a} : finset α) = ι a :=
by simp [singleton]

lemma insert_inj_of_not_mem {a : α} {s t : finset α} (has : a ∉ s) (hat : a ∉ t) 
    (hst : insert a s = insert a t) : s = t := 
ext.2 $ λ x, 
⟨λ h, mem_of_mem_insert_of_ne (hst ▸ (mem_insert_of_mem h) : x ∈ insert a t) (λ ha, has (ha ▸ h)), 
λ h, mem_of_mem_insert_of_ne (hst.symm ▸ (mem_insert_of_mem h) : x ∈ insert a s) (λ ha, hat (ha ▸ h))⟩

/- union -/

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : has_union (finset α) := ⟨λ s₁ s₂, ⟨_, nodup_ndunion s₁.1 s₂.2⟩⟩

theorem union_val_nd (s₁ s₂ : finset α) : (s₁ ∪ s₂).1 = ndunion s₁.1 s₂.1 := rfl

@[simp] theorem union_val (s₁ s₂ : finset α) : (s₁ ∪ s₂).1 = s₁.1 ∪ s₂.1 :=
ndunion_eq_union s₁.2

@[simp] theorem mem_union {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ := mem_ndunion

theorem mem_union_left {a : α} {s₁ : finset α} (s₂ : finset α) (h : a ∈ s₁) : a ∈ s₁ ∪ s₂ := by simp *

theorem mem_union_right {a : α} {s₂ : finset α} (s₁ : finset α) (h : a ∈ s₂) : a ∈ s₁ ∪ s₂ := by simp *

theorem not_mem_union {a : α} {s₁ s₂ : finset α} : a ∉ s₁ ∪ s₂ ↔ a ∉ s₁ ∧ a ∉ s₂ :=
by simp [not_or_distrib]

theorem union_subset {s₁ s₂ s₃ : finset α} (h₁ : s₁ ⊆ s₃) (h₂ : s₂ ⊆ s₃) : s₁ ∪ s₂ ⊆ s₃ :=
val_le_iff.1 (ndunion_le.2 ⟨h₁, val_le_iff.2 h₂⟩)

theorem subset_union_left {s₁ s₂ : finset α} : s₁ ⊆ s₁ ∪ s₂ := λ x, mem_union_left _

theorem subset_union_right {s₁ s₂ : finset α} : s₂ ⊆ s₁ ∪ s₂ := λ x, mem_union_right _

@[simp] theorem union_comm (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := by simp [ext, or_comm]

instance : is_commutative (finset α) (∪) := ⟨union_comm⟩

@[simp] theorem union_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
by simp [ext, or_comm, or.left_comm]

instance : is_associative (finset α) (∪) := ⟨union_assoc⟩

@[simp] theorem union_idempotent (s : finset α) : s ∪ s = s := ext.2 $ by simp

instance : is_idempotent (finset α) (∪) := ⟨union_idempotent⟩

theorem union_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
ext.2 $ by simp [or_comm, or.left_comm]

theorem union_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ := by simp

@[simp] theorem union_self (s : finset α) : s ∪ s = s := by simp

@[simp] theorem union_empty (s : finset α) : s ∪ ∅ = s := by simp [ext]

@[simp] theorem empty_union (s : finset α) : ∅ ∪ s = s := by simp [ext]

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ∪ s := by simp [ext, or_comm, or.left_comm]

@[simp] theorem insert_union (a : α) (s t : finset α) : insert a s ∪ t = insert a (s ∪ t) :=
by simp [ext, or_comm, or.left_comm]

@[simp] theorem union_insert (a : α) (s t : finset α) : s ∪ insert a t = insert a (s ∪ t) :=
by simp [ext, or.left_comm]

theorem insert_union_distrib (a : α) (s t : finset α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
by simp [ext]


/- inter -/

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : has_inter (finset α) := ⟨λ s₁ s₂, ⟨_, nodup_ndinter s₂.1 s₁.2⟩⟩

theorem inter_val_nd (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 := rfl

@[simp] theorem inter_val (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
ndinter_eq_inter s₁.2

@[simp] theorem mem_inter {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ := mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ := (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ := (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
and_imp.1 mem_inter.2

theorem inter_subset_left {s₁ s₂ : finset α} : s₁ ∩ s₂ ⊆ s₁ := λ a, mem_of_mem_inter_left

theorem inter_subset_right {s₁ s₂ : finset α} : s₁ ∩ s₂ ⊆ s₂ := λ a, mem_of_mem_inter_right

theorem subset_inter {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₁ ⊆ s₃ → s₁ ⊆ s₂ ∩ s₃ :=
by simp [subset_iff] {contextual:=tt}; finish

@[simp] theorem inter_comm (s₁ s₂ : finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ := ext.2 $ by simp [and_comm]

@[simp] theorem inter_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := ext.2 $ by simp [and_comm, and.left_comm]

@[simp] theorem inter_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) := ext.2 $ by simp [and.left_comm]

@[simp] theorem inter_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ := ext.2 $ by simp [and.left_comm]

@[simp] theorem inter_self (s : finset α) : s ∩ s = s := ext.2 $ by simp

@[simp] theorem inter_empty (s : finset α) : s ∩ ∅ = ∅ := ext.2 $ by simp

@[simp] theorem empty_inter (s : finset α) : ∅ ∩ s = ∅ := ext.2 $ by simp

@[simp] theorem insert_inter_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext.2 $ by simp; intro x; constructor; finish

@[simp] theorem inter_insert_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₁) :
  s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext.2 $ assume a', by by_cases h' : a' = a; simp [mem_inter, mem_insert, h, h', and_comm]

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₁) :
  s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : finset α} : a ∈ s → ι a ∩ s = ι a :=
show a ∈ s → insert a ∅ ∩ s = insert a ∅, by simp {contextual := tt}

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : finset α} : a ∉ s → ι a ∩ s = ∅ :=
show a ∉ s → insert a ∅ ∩ s = ∅, by simp {contextual := tt}

@[simp] theorem inter_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ∩ ι a = ι a :=
by rw [inter_comm, singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ∩ ι a = ∅ :=
by rw [inter_comm, singleton_inter_of_not_mem h]

/- lattice laws -/

instance : lattice (finset α) :=
{ le           := (⊆),
  le_refl      := subset.refl,
  le_trans     := assume a b c, subset.trans,
  le_antisymm  := assume a b, subset.antisymm,
  sup          := (∪),
  sup_le       := assume a b c, union_subset,
  le_sup_left  := assume a b, subset_union_left,
  le_sup_right := assume a b, subset_union_right,
  inf          := (∩),
  le_inf       := assume a b c, subset_inter,
  inf_le_left  := assume a b, inter_subset_left,
  inf_le_right := assume a b, inter_subset_right }

instance : semilattice_inf_bot (finset α) :=
{ bot := ∅, bot_le := empty_subset, ..finset.lattice.lattice }

instance : distrib_lattice (finset α) :=
{ le_sup_inf := assume a b c, show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c,
    by simp [subset_iff, and_imp, or_imp_distrib] {contextual:=tt},
  ..finset.lattice.lattice }

theorem inter_distrib_left (s t u : finset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext.2 $ by simp [mem_inter, mem_union]; intro; split; finish

theorem inter_distrib_right (s t u : finset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext.2 $ by simp [mem_inter, mem_union]; intro; split; finish

theorem union_distrib_left (s t u : finset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext.2 $ by simp [mem_inter, mem_union]; intro; split; finish

theorem union_distrib_right (s t u : finset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext.2 $ by simp [mem_inter, mem_union]; intro; split; finish

/- erase -/

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : finset α) (a : α) : finset α := ⟨_, nodup_erase_of_nodup a s.2⟩

@[simp] theorem erase_val (s : finset α) (a : α) : (erase s a).1 = s.1.erase a := rfl

@[simp] theorem mem_erase {a b : α} {s : finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
mem_erase_iff_of_nodup s.2

theorem not_mem_erase (a : α) (s : finset α) : a ∉ erase s a := by simp

@[simp] theorem erase_empty (a : α) : erase ∅ a = ∅ := rfl

theorem ne_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ≠ a := by simp {contextual:=tt}

theorem mem_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ∈ s := mem_of_mem_erase

theorem mem_erase_of_ne_of_mem {a b : α} {s : finset α} : a ≠ b → a ∈ s → a ∈ erase s b := by simp {contextual:=tt}

theorem erase_insert {a : α} {s : finset α} (h : a ∉ s) : erase (insert a s) a = s :=
ext.2 $ assume x, by simp; constructor; finish

theorem insert_erase {a : α} {s : finset α} (h : a ∈ s) : insert a (erase s a) = s :=
ext.2 $ assume x, by simp; constructor; finish

theorem erase_subset_erase (a : α) {s t : finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
val_le_iff.1 $ erase_le_erase _ $ val_le_iff.2 h

theorem erase_subset (a : α) (s : finset α) : erase s a ⊆ s := erase_subset _ _

lemma erase_ssubset {a : α} {s : finset α} (h : a ∈ s) : s.erase a ⊂ s :=
calc s.erase a ⊂ insert a (s.erase a) : ssubset_insert $ not_mem_erase _ _
  ... = _ : insert_erase h

theorem erase_eq_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq $ erase_of_not_mem h

theorem subset_insert_iff {a : α} {s t : finset α} : s ⊆ insert a t ↔ erase s a ⊆ t :=
by simp [subset_iff, or_iff_not_imp_left]; exact forall_congr (λ x, forall_swap)

theorem erase_insert_subset (a : α) (s : finset α) : erase (insert a s) a ⊆ s :=
subset_insert_iff.1 $ subset.refl _

theorem insert_erase_subset (a : α) (s : finset α) : s ⊆ insert a (erase s a) :=
subset_insert_iff.2 $ subset.refl _

/- sdiff -/

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : has_sdiff (finset α) := ⟨λs₁ s₂, ⟨s₁.1 - s₂.1, nodup_of_le (sub_le_self _ _) s₁.2⟩⟩

@[simp] theorem mem_sdiff {a : α} {s₁ s₂ : finset α} :
  a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂ := mem_sub_of_nodup s₁.2

@[simp] theorem sdiff_union_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : (s₂ \ s₁) ∪ s₁ = s₂ :=
ext.2 $ λ a, by simpa [or_and_distrib_left, dec_em] using or_iff_right_of_imp (@h a)

@[simp] theorem union_sdiff_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁ ∪ (s₂ \ s₁) = s₂ :=
(union_comm _ _).trans (sdiff_union_of_subset h)

@[simp] theorem inter_sdiff_self (s₁ s₂ : finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
ext.2 $ by simp {contextual := tt}

@[simp] theorem sdiff_inter_self (s₁ s₂ : finset α) : (s₂ \ s₁) ∩ s₁ = ∅ :=
by simp

theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : finset α} (h₁ : t₁ ⊆ t₂) (h₂ : s₂ ⊆ s₁) : t₁ \ s₁ ⊆ t₂ \ s₂ :=
by simpa [subset_iff] using λ a m₁ m₂, and.intro (h₁ m₁) (mt (@h₂ _) m₂)

end decidable_eq

/- attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the
  subtype `{x // x ∈ s}`. -/
def attach (s : finset α) : finset {x // x ∈ s} := ⟨attach s.1, nodup_attach.2 s.2⟩

@[simp] theorem attach_val (s : finset α) : s.attach.1 = s.1.attach := rfl

@[simp] theorem mem_attach (s : finset α) : ∀ x, x ∈ s.attach := mem_attach _

/- filter -/
section filter
variables {p q : α → Prop} [decidable_pred p] [decidable_pred q]

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (p : α → Prop) [decidable_pred p] (s : finset α) : finset α :=
⟨_, nodup_filter p s.2⟩

@[simp] theorem filter_val (s : finset α) : (filter p s).1 = s.1.filter p := rfl

@[simp] theorem mem_filter {s : finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := mem_filter

@[simp] theorem filter_subset (s : finset α) : s.filter p ⊆ s := filter_subset _

theorem filter_filter (s : finset α) :
  (s.filter p).filter q = s.filter (λa, p a ∧ q a) :=
ext.2 $ assume a, by simp [and_comm, and.left_comm]

@[simp] theorem filter_false {h} (s : finset α) : @filter α (λa, false) h s = ∅ :=
ext.2 $ assume a, by simp

variable [decidable_eq α]
theorem filter_union (s₁ s₂ : finset α) :
  (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
ext.2 $ by simp [or_and_distrib_right]

theorem filter_or (s : finset α) : s.filter (λ a, p a ∨ q a) = s.filter p ∪ s.filter q :=
ext.2 $ by simp [and_or_distrib_left]

theorem filter_and (s : finset α) : s.filter (λ a, p a ∧ q a) = s.filter p ∩ s.filter q :=
ext.2 $ by simp [and_comm, and.left_comm]

theorem filter_not (s : finset α) : s.filter (λ a, ¬ p a) = s \ s.filter p :=
ext.2 $ by simpa [and_comm] using λ a, and_congr_right $
  λ h : a ∈ s, (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : finset α) :
  s₁ \ s₂ = filter (∉ s₂) s₁ := ext.2 $ by simp

theorem filter_union_filter_neg_eq (s : finset α) : s.filter p ∪ s.filter (λa, ¬ p a) = s :=
by simp [filter_not]

theorem filter_inter_filter_neg_eq (s : finset α) : s.filter p ∩ s.filter (λa, ¬ p a) = ∅ :=
by simp [filter_not]

end filter

/- range -/
section range
variables {n m l : ℕ}

/-- `range n` is the set of integers less than `n`. -/
def range (n : ℕ) : finset ℕ := ⟨_, nodup_range n⟩

@[simp] theorem range_val (n : ℕ) : (range n).1 = multiset.range n := rfl

@[simp] theorem mem_range : m ∈ range n ↔ m < n := mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_succ : range (succ n) = insert n (range n) := eq_of_veq $ by simp

@[simp] theorem not_mem_range_self : n ∉ range n := not_mem_range_self

@[simp] theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m := range_subset

theorem exists_nat_subset_range (s : finset ℕ) : ∃n : ℕ, s ⊆ range n :=
finset.induction_on s ⟨0, by simp⟩ $ λ a s ha ⟨n, hn⟩,
⟨max (a + 1) n, insert_subset.2
  ⟨by simpa using le_max_left (a+1) n, subset.trans hn (by simp [le_max_right])⟩⟩

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : finset α) ∧ p x) ↔ false :=
by simp

theorem exists_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ (∃ x, x ∈ s ∧ p x) :=
by simp [or_and_distrib_right, exists_or_distrib]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : finset α) → p x) ↔ true :=
by simp

theorem forall_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ (∀ x, x ∈ s → p x) :=
by simp [or_imp_distrib, forall_and_distrib]

end finset

/- erase_dup on list and multiset -/

namespace multiset
variable [decidable_eq α]

/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def to_finset (s : multiset α) : finset α := ⟨_, nodup_erase_dup s⟩

@[simp] theorem to_finset_val (s : multiset α) : s.to_finset.1 = s.erase_dup := rfl

theorem to_finset_eq {s : multiset α} (n : nodup s) : finset.mk s n = s.to_finset :=
finset.val_inj.1 (erase_dup_eq_self.2 n).symm

@[simp] theorem mem_to_finset {a : α} {s : multiset α} : a ∈ s.to_finset ↔ a ∈ s :=
mem_erase_dup

end multiset

namespace list
variable [decidable_eq α]

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset (l : list α) : finset α := multiset.to_finset l

@[simp] theorem to_finset_val (l : list α) : l.to_finset.1 = (l.erase_dup : multiset α) := rfl

theorem to_finset_eq {l : list α} (n : nodup l) : @finset.mk α l n = l.to_finset :=
multiset.to_finset_eq n

@[simp] theorem mem_to_finset {a : α} {l : list α} : a ∈ l.to_finset ↔ a ∈ l :=
mem_erase_dup

end list

namespace finset

section image
variables [decidable_eq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : finset α) : finset β := (s.1.map f).to_finset

@[simp] theorem image_val (f : α → β) (s : finset α) : (image f s).1 = (s.1.map f).erase_dup := rfl

@[simp] theorem image_empty (f : α → β) : (∅ : finset α).image f = ∅ := rfl

variables {f : α → β} {s : finset α}

@[simp] theorem mem_image {b : β} : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by simp [mem_def]

@[simp] theorem mem_image_of_mem (f : α → β) {a} {s : finset α} (h : a ∈ s) : f a ∈ s.image f :=
mem_image.2 ⟨_, h, rfl⟩

theorem image_to_finset [decidable_eq α] {s : multiset α} : s.to_finset.image f = (s.map f).to_finset := ext.2 $ by simp

@[simp] theorem image_val_of_inj_on (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : (image f s).1 = s.1.map f :=
multiset.erase_dup_eq_self.2 (nodup_map_on H s.2)

theorem image_id [decidable_eq α] : s.image id = s := ext.2 $ by simp

theorem image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq $ by simp [erase_dup_map_erase_dup_eq]

theorem image_subset_image {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
by simp [subset_def, map_subset_map h]

theorem image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext.2 $ λ b, by simp [and_comm]; rw ← exists_and_distrib_left; exact
exists_congr (λ a, and.left_comm.trans $ and_congr_right $ λ e, by simp [e.symm])

theorem image_union [decidable_eq α] {f : α → β} (s₁ s₂ : finset α) : (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
ext.2 $ by simp [mem_image, or_and_distrib_right, exists_or_distrib]

theorem image_inter [decidable_eq α] (s₁ s₂ : finset α) (hf : ∀x y, f x = f y → x = y) : (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
ext.2 $ by simp [mem_image]; exact λ b,
⟨λ ⟨a, ⟨m₁, m₂⟩, e⟩, ⟨⟨a, m₁, e⟩, ⟨a, m₂, e⟩⟩,
 λ ⟨⟨a, m₁, e₁⟩, ⟨a', m₂, e₂⟩⟩, ⟨a, ⟨m₁, hf _ _ (e₂.trans e₁.symm) ▸ m₂⟩, e₁⟩⟩.

@[simp] theorem image_singleton [decidable_eq α] (f : α → β) (a : α) : (singleton a).image f = singleton (f a) :=
ext.2 $ by simp [mem_image, eq_comm]

@[simp] theorem image_insert [decidable_eq α] (f : α → β) (a : α) (s : finset α) :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp [insert_eq, image_union]

@[simp] theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_image_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma attach_image_val [decidable_eq α] {s : finset α} : s.attach.image subtype.val = s :=
eq_of_veq $ by simp [multiset.attach_map_val]

end image

/- card -/
section card

/-- `card s` is the cardinality (number of elements) of `s`. -/
def card (s : finset α) : nat := s.1.card

theorem card_def (s : finset α) : s.card = s.1.card := rfl

@[simp] theorem card_empty : card (∅ : finset α) = 0 := rfl

@[simp] theorem card_eq_zero {s : finset α} : card s = 0 ↔ s = ∅ :=
card_eq_zero.trans val_eq_zero

theorem card_pos {s : finset α} : 0 < card s ↔ s ≠ ∅ :=
pos_iff_ne_zero.trans $ not_congr card_eq_zero

@[simp] theorem card_insert_of_not_mem [decidable_eq α] {a : α} {s : finset α} (h : a ∉ s) : card (insert a s) = card s + 1 :=
by simpa [card] using congr_arg multiset.card (ndinsert_of_not_mem h)

theorem card_insert_le [decidable_eq α] (a : α) (s : finset α) : card (insert a s) ≤ card s + 1 :=
by by_cases a ∈ s; simp [h, nat.le_add_right]

theorem card_erase_of_mem [decidable_eq α] {a : α} {s : finset α} : a ∈ s → card (erase s a) = pred (card s) := card_erase_of_mem

theorem card_range (n : ℕ) : card (range n) = n := card_range n

theorem card_attach {s : finset α} : card (attach s) = card s := multiset.card_attach

theorem card_image_of_inj_on [decidable_eq β] {f : α → β} {s : finset α}
  (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : card (image f s) = card s :=
by simp [card, image_val_of_inj_on H]

theorem card_image_of_injective [decidable_eq β] {f : α → β} (s : finset α)
  (H : function.injective f) : card (image f s) = card s :=
card_image_of_inj_on $ λ x _ y _ h, H h

lemma card_eq_of_bijective [decidable_eq α] {s : finset α} {n : ℕ}
  (f : ∀i, i < n → α)
  (hf : ∀a∈s, ∃i, ∃h:i<n, f i h = a) (hf' : ∀i (h : i < n), f i h ∈ s)
  (f_inj : ∀i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) :
  card s = n :=
have ∀ (a : α), a ∈ s ↔ ∃i (hi : i ∈ range n), f i (mem_range.1 hi) = a,
  from assume a, ⟨assume ha, let ⟨i, hi, eq⟩ := hf a ha in ⟨i, mem_range.2 hi, eq⟩,
    assume ⟨i, hi, eq⟩, eq ▸ hf' i (mem_range.1 hi)⟩,
have s = ((range n).attach.image $ λi, f i.1 (mem_range.1 i.2)),
  by simpa [ext],
calc card s = card ((range n).attach.image $ λi, f i.1 (mem_range.1 i.2)) :
    by rw [this]
  ... = card ((range n).attach) :
    card_image_of_injective _ $ assume ⟨i, hi⟩ ⟨j, hj⟩ eq,
      subtype.eq $ f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq
  ... = card (range n) : card_attach
  ... = n : card_range n

lemma card_eq_succ [decidable_eq α] {s : finset α} {a : α} {n : ℕ} :
  s.card = n + 1 ↔ (∃a t, a ∉ t ∧ insert a t = s ∧ card t = n) :=
iff.intro
  (assume eq,
    have card s > 0, from eq.symm ▸ nat.zero_lt_succ _,
    let ⟨a, has⟩ := finset.exists_mem_of_ne_empty $ card_pos.mp this in
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by simp [eq, card_erase_of_mem has]⟩)
  (assume ⟨a, t, hat, s_eq, n_eq⟩, s_eq ▸ n_eq ▸ card_insert_of_not_mem hat)

theorem card_le_of_subset {s t : finset α} : s ⊆ t → card s ≤ card t :=
multiset.card_le_of_le ∘ val_le_iff.mpr

theorem eq_of_subset_of_card_le {s t : finset α} (h : s ⊆ t) (h₂ : card t ≤ card s) : s = t :=
eq_of_veq $ multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

lemma card_lt_card [decidable_eq α] {s t : finset α} (h : s ⊂ t) : s.card < t.card :=
card_lt_of_lt (val_lt_iff.2 h)

lemma card_le_card_of_inj_on [decidable_eq α] [decidable_eq β] {s : finset α} {t : finset β}
  (f : α → β) (hf : ∀a∈s, f a ∈ t) (f_inj : ∀a₁∈s, ∀a₂∈s, f a₁ = f a₂ → a₁ = a₂) :
  card s ≤ card t :=
calc card s = card (s.image f) : by rw [card_image_of_inj_on f_inj]
  ... ≤ card t : card_le_of_subset $
    assume x hx, match x, finset.mem_image.1 hx with _, ⟨a, ha, rfl⟩ := hf a ha end

lemma card_le_of_inj_on [decidable_eq α] {n} {s : finset α}
  (f : ℕ → α) (hf : ∀i<n, f i ∈ s) (f_inj : ∀i j, i<n → j<n → f i = f j → i = j) : n ≤ card s :=
calc n = card (range n) : (card_range n).symm
  ... ≤ card s : card_le_card_of_inj_on f
    (by simp; assumption)
    (by simp; exact assume a₁ h₁ a₂ h₂, f_inj a₁ a₂ h₁ h₂)

@[simp] lemma singleton_card (a : α) : card (finset.singleton a) = 1 := rfl

@[elab_as_eliminator] lemma strong_induction_on {p : finset α → Sort*} :
  ∀ (s : finset α), (∀s, (∀t ⊂ s, p t) → p s) → p s
| ⟨s, nd⟩ ih := multiset.strong_induction_on s
  (λ s IH nd, ih ⟨s, nd⟩ (λ ⟨t, nd'⟩ ss, IH t (val_lt_iff.2 ss) nd')) nd

@[elab_as_eliminator] lemma case_strong_induction_on [decidable_eq α] {p : finset α → Prop}
  (s : finset α) (h₀ : p ∅) (h₁ : ∀ a s, a ∉ s → (∀t ⊆ s, p t) → p (insert a s)) : p s :=
finset.strong_induction_on s $ λ s,
finset.induction_on s (λ _, h₀) $ λ a s n _ ih, h₁ a s n $
λ t ss, ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

end card

section bind
variables [decidable_eq β] {s : finset α} {t : α → finset β}

/-- `bind s t` is the union of `t x` over `x ∈ s` -/
protected def bind (s : finset α) (t : α → finset β) : finset β := (s.1.bind (λ a, (t a).1)).to_finset

@[simp] theorem bind_val (s : finset α) (t : α → finset β) :
  (s.bind t).1 = (s.1.bind (λ a, (t a).1)).erase_dup := rfl

@[simp] theorem bind_empty : finset.bind ∅ t = ∅ := rfl

@[simp] theorem mem_bind {b : β} : b ∈ s.bind t ↔ ∃a∈s, b ∈ t a :=
by simp [mem_def]

@[simp] theorem bind_insert [decidable_eq α] {a : α} : (insert a s).bind t = t a ∪ s.bind t :=
ext.2 $ by simp [or_and_distrib_right, exists_or_distrib]

theorem image_bind [decidable_eq γ] {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bind t = s.bind (λa, t (f a)) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp {contextual := tt})

theorem bind_image [decidable_eq γ] {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bind t).image f = s.bind (λa, (t a).image f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [image_union] {contextual := tt})

theorem bind_to_finset [decidable_eq α] (s : multiset α) (t : α → multiset β) :
  (s.bind t).to_finset = s.to_finset.bind (λa, (t a).to_finset) :=
ext.2 $ by simp

lemma bind_mono {t₁ t₂ : α → finset β} (h : ∀a∈s, t₁ a ⊆ t₂ a) : s.bind t₁ ⊆ s.bind t₂ :=
have ∀b a, a ∈ s → b ∈ t₁ a → (∃ (a : α), a ∈ s ∧ b ∈ t₂ a),
  from assume b a ha hb, ⟨a, ha, finset.mem_of_subset (h a ha) hb⟩,
by simpa [finset.subset_iff]

lemma bind_singleton {f : α → β} : s.bind (λa, {f a}) = s.image f :=
finset.ext.mpr $ by simp [eq_comm]

end bind

section prod
variables {s : finset α} {t : finset β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : finset α) (t : finset β) : finset (α × β) := ⟨_, nodup_product s.2 t.2⟩

@[simp] theorem product_val : (s.product t).1 = s.1.product t.1 := rfl

@[simp] theorem mem_product {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := mem_product

theorem product_eq_bind [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
 s.product t = s.bind (λa, t.image $ λb, (a, b)) :=
ext.2 $ by simp [and.left_comm]

@[simp] theorem card_product (s : finset α) (t : finset β) : card (s.product t) = card s * card t :=
multiset.card_product _ _

end prod

section sigma
variables {σ : α → Type*} {s : finset α} {t : Πa, finset (σ a)}

/-- `sigma s t` is the set of dependent pairs `⟨a, b⟩` such that `a ∈ s` and `b ∈ t a`. -/
protected def sigma (s : finset α) (t : Πa, finset (σ a)) : finset (Σa, σ a) :=
⟨_, nodup_sigma s.2 (λ a, (t a).2)⟩

@[simp] theorem mem_sigma {p : sigma σ} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1) := mem_sigma

theorem sigma_mono {s₁ s₂ : finset α} {t₁ t₂ : Πa, finset (σ a)} :
  s₁ ⊆ s₂ → (∀a, t₁ a ⊆ t₂ a) → s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
by simp [subset_iff, mem_sigma] {contextual := tt}

theorem sigma_eq_bind [decidable_eq α] [∀a, decidable_eq (σ a)] (s : finset α) (t : Πa, finset (σ a)) :
 s.sigma t = s.bind (λa, (t a).image $ λb, ⟨a, b⟩) :=
ext.2 $ by simp [and.left_comm]

end sigma

section pi
variables {δ : α → Type*} [decidable_eq α] [∀a, decidable_eq (δ a)]

def pi (s : finset α) (t : Πa, finset (δ a)) : finset (Πa∈s, δ a) :=
(s.1.pi (λa, (t a).1)).to_finset

lemma mem_pi {s : finset α} {t : Πa, finset (δ a)} {f : (Πa∈s, δ a)} :
  f ∈ s.pi t ↔ (∀a (h : a ∈ s), f a h ∈ t a) :=
by rcases s; rw [pi, multiset.mem_to_finset, multiset.mem_pi]; refl
end pi

section fold
variables (op : β → β → β) [hc : is_commutative β op] [ha : is_associative β op]
local notation a * b := op a b
include hc ha

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = `f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : finset α) : β := (s.1.map f).fold op b

variables {op} {f : α → β} {b : β} {s : finset α} {a : α}

@[simp] theorem fold_empty : (∅ : finset α).fold op b f = b := rfl

@[simp] theorem fold_insert [decidable_eq α] (h : a ∉ s) : (insert a s).fold op b f = f a * s.fold op b f :=
by simp [fold, ndinsert_of_not_mem h]

@[simp] theorem fold_singleton : (singleton a).fold op b f = f a * b :=
by simp [fold]

@[simp] theorem fold_image [decidable_eq α] [decidable_eq γ] {g : γ → α} {s : finset γ}
  (H : ∀ (x ∈ s) (y ∈ s), g x = g y → x = y) : (s.image g).fold op b f = s.fold op b (f ∘ g) :=
by simp [fold, image_val_of_inj_on H, map_map]

@[congr] theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g :=
by rw [fold, fold, map_congr H]

theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
  s.fold op (b₁ * b₂) (λx, f x * g x) = s.fold op b₁ f * s.fold op b₂ g :=
by simp [fold, fold_distrib]

theorem fold_hom {op' : γ → γ → γ} [is_commutative γ op'] [is_associative γ op']
  {m : β → γ} (hm : ∀x y, m (op x y) = op' (m x) (m y)) :
  s.fold op' (m b) (λx, m (f x)) = m (s.fold op b f) :=
by rw [fold, fold, ← fold_hom op hm, map_map]

theorem fold_union_inter [decidable_eq α] {s₁ s₂ : finset α} {b₁ b₂ : β} :
  (s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f = s₁.fold op b₂ f * s₂.fold op b₁ f :=
by unfold fold; rw [← fold_add op, ← map_add, union_val,
     inter_val, union_add_inter, map_add, hc.comm, fold_add]

@[simp] theorem fold_insert_idem [decidable_eq α] [hi : is_idempotent β op] :
  (insert a s).fold op b f = f a * s.fold op b f :=
by haveI := classical.prop_decidable;
   rw [fold, insert_val', ← fold_erase_dup_idem op, erase_dup_map_erase_dup_eq,
       fold_erase_dup_idem op]; simp [fold]

end fold

section sort
variables (r : α → α → Prop) [decidable_rel r]
  [tr : is_trans α r] [an : is_antisymm α r] [to : is_total α r]
include tr an to

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
def sort (s : finset α) : list α := sort r s.1

@[simp] theorem sort_sorted (s : finset α) : list.sorted r (sort r s) :=
sort_sorted _ _

@[simp] theorem sort_eq (s : finset α) : ↑(sort r s) = s.1 :=
sort_eq _ _

@[simp] theorem sort_nodup (s : finset α) : (sort r s).nodup :=
(by rw sort_eq; exact s.2 : @multiset.nodup α (sort r s))

@[simp] theorem sort_to_finset [decidable_eq α] (s : finset α) : (sort r s).to_finset = s :=
list.to_finset_eq (sort_nodup r s) ▸ eq_of_veq (sort_eq r s)

end sort

def disjoint (s t : finset α) : Prop := ∀ ⦃a⦄, a ∈ s → a ∈ t → false

theorem disjoint.symm {s t : finset α} (d : disjoint s t) : disjoint t s
| a i₂ i₁ := d i₁ i₂

@[simp] theorem disjoint_comm {s t : finset α} : disjoint s t ↔ disjoint t s :=
⟨disjoint.symm, disjoint.symm⟩

theorem disjoint_left {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := iff.rfl

theorem disjoint_right {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
disjoint_comm

theorem disjoint_iff_ne {s t : finset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {s t u : finset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t
| x m₁ := d (h m₁)

theorem disjoint_of_subset_right {s t u : finset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t
| x m m₁ := d m (h m₁)

@[simp] theorem empty_disjoint (l : finset α) : disjoint ∅ l
| a := (not_mem_empty a).elim

@[simp] theorem singleton_disjoint [decidable_eq α] {l : finset α} {a : α} : disjoint (singleton a) l ↔ a ∉ l :=
by simp [disjoint]; refl

@[simp] theorem disjoint_singleton [decidable_eq α] {l : finset α} {a : α} : disjoint l (singleton a) ↔ a ∉ l :=
by rw disjoint_comm; simp

@[simp] theorem disjoint_insert_left [decidable_eq α] {a : α} {s t : finset α} :
  disjoint (insert a s) t ↔ a ∉ t ∧ disjoint s t :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]; refl

@[simp] theorem disjoint_insert_right [decidable_eq α] {a : α} {s t : finset α} :
  disjoint s (insert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint_comm.trans $ by simp [disjoint_insert_left]

theorem inter_eq_empty_iff_disjoint [decidable_eq α] {s t : finset α} : s ∩ t = ∅ ↔ disjoint s t :=
by simp [ext, mem_inter]; refl

theorem inter_eq_zero_iff_disjoint [decidable_eq α] {s t : finset α} : s ∩ t = ∅ ↔ disjoint s t :=
by rw ← subset_empty; simp [subset_iff, disjoint]

@[simp] theorem disjoint_union_left [decidable_eq α] {s t u : finset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_union_right [decidable_eq α] {s t u : finset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_val {s t : finset α} : multiset.disjoint s.1 t.1 ↔ disjoint s t :=
by simp [disjoint, multiset.disjoint, mem_def]

@[simp] theorem card_disjoint_union [decidable_eq α] {s t : finset α} :
    disjoint s t → card (s ∪ t) = card s + card t :=
finset.induction_on s (by simp) $ begin simp {contextual := tt} end

end finset

namespace list
open finset
variable [decidable_eq α]
 
definition powerset : list α → finset (finset α)
| []       := {∅}
| (a :: l) := powerset l ∪ image (insert a) (powerset l)

private theorem image_insert_comm (x y : α) (s : finset (finset α)) :
  image (insert x) (image (insert y) s) = image (insert y) (image (insert x) s) := 
finset.ext.2 $ λ c,
have aux : ∀ x y : α, (∃ (a : finset α), (∃ (b : finset α), b ∈ s ∧ insert y b = a) ∧ insert x a = c) →
    ∃ (a : finset α), (∃ (b : finset α), b ∈ s ∧ insert x b = a) ∧ insert y a = c := λ x y ⟨a, ⟨b, h₁⟩, h₂⟩,
    ⟨insert x b, ⟨b, ⟨h₁.1, rfl⟩⟩, by rwa [insert.comm, h₁.2]⟩,
by simp [iff.intro (aux x y) (aux y x)]

theorem powerset_eq_powerset_of_perm {l₁ l₂ : list α} (p : l₁ ~ l₂) :
    powerset l₁ = powerset l₂ :=
list.perm_induction_on p
  rfl
  (by simp [powerset] {contextual := tt})
  (λ x y l₁ l₂ hp hs, 
  by simp [powerset, image_insert_comm, hs, image_union,  union_left_comm])
  $ λ l₁ l₂ l₃ h₁ h₂, eq.trans

end list

namespace multiset
open finset
variable [decidable_eq α]

definition powerset (s : multiset α) : finset (finset α) :=
quot.lift_on s
  (λ l, list.powerset l)
  (λ l₁ l₂ p, list.powerset_eq_powerset_of_perm p)

theorem powerset_cons {a : α} : ∀ {s : multiset α}, a ∉ s → powerset (a :: s) = 
    powerset s ∪ image (insert a) (powerset s) :=
λ s, quot.induction_on s $ λ l h, rfl

end multiset

namespace finset
variable [decidable_eq α]

def powerset (s : finset α) : finset (finset α) :=
multiset.powerset s.1

@[simp] theorem powerset_empty : powerset (∅ : finset α) = {∅} := rfl

theorem powerset_insert {a : α} : ∀ {s : finset α}, a ∉ s → powerset (insert a s) = 
    powerset s ∪ image (insert a) (powerset s) :=
λ s h, show multiset.powerset (multiset.ndinsert a (s.val)) = 
multiset.powerset s.val ∪ image (insert a) (multiset.powerset s.val), from 
(multiset.ndinsert_of_not_mem h).symm ▸ multiset.powerset_cons h

@[simp] lemma mem_powerset {s : finset α} : ∀ {x}, x ∈ powerset s ↔ x ⊆ s :=
finset.induction_on s (λ x, by split; simp [subset_empty] {contextual := tt}) 
$ λ a s has hi t, by rw [powerset_insert has, mem_union, mem_image];
exact ⟨λ h, or.cases_on h 
  (λ h, subset.trans (hi.1 h) (subset_insert _ _))
  (λ h, let ⟨u, hu, hau⟩ := h in
  hau ▸ insert_subset_insert _ (hi.1 hu)),
  λ h, have h :  erase t a ⊆ s := subset_insert_iff.1 h,
or.cases_on (decidable.em (a ∈ t))
  (λ h₁, or.inr ⟨erase t a, hi.2 h, insert_erase h₁⟩)
  (λ h₁, or.inl (hi.2 ((erase_eq_of_not_mem h₁) ▸ h)))⟩

theorem empty_mem_powerset (s : finset α) : ∅ ∈ powerset s :=
mem_powerset.2 (empty_subset s)

lemma card_powerset (s : finset α) : card (powerset s) = monoid.pow 2 (card s) := 
finset.induction_on s (by simp) $ λ a s has hi,
have h : finset.disjoint (powerset s) (image (insert a) (powerset s)) := λ t, begin
  rw [mem_image, mem_powerset],
  assume h h₁,
  rcases h₁ with ⟨u, hus, hau⟩,
  rw [← hau, insert_subset] at h,
  exact has h.1,
end,
have h_inj : ∀ t ∈ powerset s, ∀ u ∈ powerset s,
   insert a t = insert a u → t = u := λ t ht u hu h,
by rw mem_powerset at *;
  exact insert_inj_of_not_mem (λ ha, has (mem_of_subset ht ha)) (λ ha, has (mem_of_subset hu ha)) h,
by rw [card_insert_of_not_mem has, pow_add, powerset_insert has, 
    card_disjoint_union h, card_image_of_inj_on h_inj, hi, pow_one, mul_two]

end finset
