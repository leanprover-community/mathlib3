/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro

Finite sets.
-/
import logic.embedding order.boolean_algebra algebra.order_functions
  data.multiset data.sigma.basic data.set.lattice

open multiset subtype nat lattice

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

namespace finset

theorem eq_of_veq : ∀ {s t : finset α}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

@[simp] theorem val_inj {s t : finset α} : s.1 = t.1 ↔ s = t :=
⟨eq_of_veq, congr_arg _⟩

@[simp] theorem erase_dup_eq_self [decidable_eq α] (s : finset α) : erase_dup s.1 = s.1 :=
erase_dup_eq_self.2 s.2

instance has_decidable_eq [decidable_eq α] : decidable_eq (finset α)
| s₁ s₂ := decidable_of_iff _ val_inj

/- membership -/

instance : has_mem α (finset α) := ⟨λ a s, a ∈ s.1⟩

theorem mem_def {a : α} {s : finset α} : a ∈ s ↔ a ∈ s.1 := iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @finset.mk α s nd ↔ a ∈ s := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : finset α) : decidable (a ∈ s) :=
multiset.decidable_mem _ _

/- set coercion -/

/-- Convert a finset to a set in the natural way. -/
def to_set (s : finset α) : set α := {x | x ∈ s}

instance : has_lift (finset α) (set α) := ⟨to_set⟩

@[simp] lemma mem_coe {a : α} {s : finset α} : a ∈ (↑s : set α) ↔ a ∈ s := iff.rfl

@[simp] lemma set_of_mem {α} {s : finset α} : {a | a ∈ s} = ↑s := rfl

/- extensionality -/
theorem ext {s₁ s₂ : finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
val_inj.symm.trans $ nodup_ext s₁.2 s₂.2

@[extensionality]
theorem ext' {s₁ s₂ : finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
ext.2

@[simp] theorem coe_inj {s₁ s₂ : finset α} : (↑s₁ : set α) = ↑s₂ ↔ s₁ = s₂ :=
(set.ext_iff _ _).trans ext.symm

/- subset -/

instance : has_subset (finset α) := ⟨λ s₁ s₂, ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂⟩

theorem subset_def {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ s₁.1 ⊆ s₂.1 := iff.rfl

@[simp] theorem subset.refl (s : finset α) : s ⊆ s := subset.refl _

theorem subset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := subset.trans

theorem mem_of_subset {s₁ s₂ : finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ := mem_of_subset

theorem subset.antisymm {s₁ s₂ : finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext.2 $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ := iff.rfl

@[simp] theorem coe_subset {s₁ s₂ : finset α} :
  (↑s₁ : set α) ⊆ ↑s₂ ↔ s₁ ⊆ s₂ := iff.rfl

@[simp] theorem val_le_iff {s₁ s₂ : finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ := le_iff_subset s₁.2

instance : has_ssubset (finset α) := ⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance : partial_order (finset α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _,
  le_antisymm := @subset.antisymm _ }

theorem subset.antisymm_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
le_antisymm_iff

@[simp] theorem le_iff_subset {s₁ s₂ : finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ := iff.rfl
@[simp] theorem lt_iff_ssubset {s₁ s₂ : finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ := iff.rfl

@[simp] lemma coe_ssubset {s₁ s₂ : finset α} : (↑s₁ : set α) ⊂ ↑s₂ ↔ s₁ ⊂ s₂ :=
show (↑s₁ : set α) ⊂ ↑s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁,
  by simp only [set.ssubset_iff_subset_not_subset, finset.coe_subset]

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

lemma eq_empty_iff_forall_not_mem {s : finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
⟨by rintro rfl x; exact id, λ h, eq_empty_of_forall_not_mem h⟩

@[simp] theorem val_eq_zero {s : finset α} : s.1 = 0 ↔ s = ∅ := @val_inj _ s ∅

theorem subset_empty {s : finset α} : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

theorem exists_mem_of_ne_empty {s : finset α} (h : s ≠ ∅) : ∃ a : α, a ∈ s :=
exists_mem_of_ne_zero (mt val_eq_zero.1 h)

@[simp] lemma coe_empty : ↑(∅ : finset α) = (∅ : set α) := rfl

/-- `singleton a` is the set `{a}` containing `a` and nothing else. -/
def singleton (a : α) : finset α := ⟨_, nodup_singleton a⟩
local prefix `ι`:90 := singleton

@[simp] theorem singleton_val (a : α) : (ι a).1 = a :: 0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ι a ↔ b = a := mem_singleton

theorem not_mem_singleton {a b : α} : a ∉ ι b ↔ a ≠ b := not_iff_not_of_iff mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ι a := or.inl rfl

theorem singleton_inj {a b : α} : ι a = ι b ↔ a = b :=
⟨λ h, mem_singleton.1 (h ▸ mem_singleton_self _), congr_arg _⟩

@[simp] theorem singleton_ne_empty (a : α) : ι a ≠ ∅ := ne_empty_of_mem (mem_singleton_self _)

@[simp] lemma coe_singleton (a : α) : ↑(ι a) = ({a} : set α) := rfl

/- insert -/
section decidable_eq
variables [decidable_eq α]

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : has_insert α (finset α) := ⟨λ a s, ⟨_, nodup_ndinsert a s.2⟩⟩

@[simp] theorem has_insert_eq_insert (a : α) (s : finset α) : has_insert.insert a s = insert a s := rfl

theorem insert_def (a : α) (s : finset α) : insert a s = ⟨_, nodup_ndinsert a s.2⟩ := rfl

@[simp] theorem insert_val (a : α) (s : finset α) : (insert a s).1 = ndinsert a s.1 := rfl

theorem insert_val' (a : α) (s : finset α) : (insert a s).1 = erase_dup (a :: s.1) :=
by rw [erase_dup_cons, erase_dup_eq_self]; refl

theorem insert_val_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : (insert a s).1 = a :: s.1 :=
by rw [insert_val, ndinsert_of_not_mem h]

@[simp] theorem mem_insert {a b : α} {s : finset α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := mem_ndinsert

theorem mem_insert_self (a : α) (s : finset α) : a ∈ insert a s := mem_ndinsert_self a s.1
theorem mem_insert_of_mem {a b : α} {s : finset α} (h : a ∈ s) : a ∈ insert b s := mem_ndinsert_of_mem h
theorem mem_of_mem_insert_of_ne {a b : α} {s : finset α} (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
(mem_insert.1 h).resolve_left

@[simp] lemma coe_insert (a : α) (s : finset α) : ↑(insert a s) = (insert a ↑s : set α) :=
set.ext $ λ x, by simp only [mem_coe, mem_insert, set.mem_insert_iff]

@[simp] theorem insert_eq_of_mem {a : α} {s : finset α} (h : a ∈ s) : insert a s = s :=
eq_of_veq $ ndinsert_of_mem h

@[simp] theorem insert.comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
ext.2 $ λ x, by simp only [finset.mem_insert, or.left_comm]

@[simp] theorem insert_idem (a : α) (s : finset α) : insert a (insert a s) = insert a s :=
ext.2 $ λ x, by simp only [finset.mem_insert, or.assoc.symm, or_self]

@[simp] theorem insert_ne_empty (a : α) (s : finset α) : insert a s ≠ ∅ :=
ne_empty_of_mem (mem_insert_self a s)

theorem insert_subset {a : α} {s t : finset α} : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp only [subset_iff, mem_insert, forall_eq, or_imp_distrib, forall_and_distrib]

theorem subset_insert [h : decidable_eq α] (a : α) (s : finset α) : s ⊆ insert a s :=
λ b, mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
insert_subset.2 ⟨mem_insert_self _ _, subset.trans h (subset_insert _ _)⟩

lemma ssubset_iff {s t : finset α} : s ⊂ t ↔ (∃a, a ∉ s ∧ insert a s ⊆ t) :=
iff.intro
  (assume ⟨h₁, h₂⟩,
    have ∃a ∈ t, a ∉ s, by simpa only [finset.subset_iff, classical.not_forall] using h₂,
    let ⟨a, hat, has⟩ := this in ⟨a, has, insert_subset.mpr ⟨hat, h₁⟩⟩)
  (assume ⟨a, hat, has⟩,
    let ⟨h₁, h₂⟩ := insert_subset.mp has in
    ⟨h₂, assume h, hat $ h h₁⟩)

lemma ssubset_insert {s : finset α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
ssubset_iff.mpr ⟨a, h, subset.refl _⟩

@[recursor 6] protected theorem induction {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
    cases nodup_cons.1 nd with m nd',
    rw [← (eq_of_veq _ : insert a (finset.mk s _) = ⟨a::s, nd⟩)],
    { exact h₂ (by exact m) (IH nd') },
    { rw [insert_val, ndinsert_of_not_mem m] }
  end) nd

@[elab_as_eliminator] protected theorem induction_on {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (s : finset α) (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

@[simp] theorem singleton_eq_singleton (a : α) : _root_.singleton a = ι a := rfl

@[simp] theorem insert_empty_eq_singleton (a : α) : {a} = ι a := rfl

@[simp] theorem insert_singleton_self_eq (a : α) : ({a, a} : finset α) = ι a :=
insert_eq_of_mem $ mem_singleton_self _

/- union -/

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : has_union (finset α) := ⟨λ s₁ s₂, ⟨_, nodup_ndunion s₁.1 s₂.2⟩⟩

theorem union_val_nd (s₁ s₂ : finset α) : (s₁ ∪ s₂).1 = ndunion s₁.1 s₂.1 := rfl

@[simp] theorem union_val (s₁ s₂ : finset α) : (s₁ ∪ s₂).1 = s₁.1 ∪ s₂.1 :=
ndunion_eq_union s₁.2

@[simp] theorem mem_union {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ := mem_ndunion

theorem mem_union_left {a : α} {s₁ : finset α} (s₂ : finset α) (h : a ∈ s₁) : a ∈ s₁ ∪ s₂ := mem_union.2 $ or.inl h

theorem mem_union_right {a : α} {s₂ : finset α} (s₁ : finset α) (h : a ∈ s₂) : a ∈ s₁ ∪ s₂ := mem_union.2 $ or.inr h

theorem not_mem_union {a : α} {s₁ s₂ : finset α} : a ∉ s₁ ∪ s₂ ↔ a ∉ s₁ ∧ a ∉ s₂ :=
by rw [mem_union, not_or_distrib]

@[simp] lemma coe_union (s₁ s₂ : finset α) : ↑(s₁ ∪ s₂) = (↑s₁ ∪ ↑s₂ : set α) := set.ext $ λ x, mem_union

theorem union_subset {s₁ s₂ s₃ : finset α} (h₁ : s₁ ⊆ s₃) (h₂ : s₂ ⊆ s₃) : s₁ ∪ s₂ ⊆ s₃ :=
val_le_iff.1 (ndunion_le.2 ⟨h₁, val_le_iff.2 h₂⟩)

theorem subset_union_left (s₁ s₂ : finset α) : s₁ ⊆ s₁ ∪ s₂ := λ x, mem_union_left _

theorem subset_union_right (s₁ s₂ : finset α) : s₂ ⊆ s₁ ∪ s₂ := λ x, mem_union_right _

@[simp] theorem union_comm (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
ext.2 $ λ x, by simp only [mem_union, or_comm]

instance : is_commutative (finset α) (∪) := ⟨union_comm⟩

@[simp] theorem union_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
ext.2 $ λ x, by simp only [mem_union, or_assoc]

instance : is_associative (finset α) (∪) := ⟨union_assoc⟩

@[simp] theorem union_idempotent (s : finset α) : s ∪ s = s :=
ext.2 $ λ _, mem_union.trans $ or_self _

instance : is_idempotent (finset α) (∪) := ⟨union_idempotent⟩

theorem union_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
ext.2 $ λ _, by simp only [mem_union, or.left_comm]

theorem union_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
ext.2 $ λ x, by simp only [mem_union, or_assoc, or_comm (x ∈ s₂)]

@[simp] theorem union_self (s : finset α) : s ∪ s = s := union_idempotent s

@[simp] theorem union_empty (s : finset α) : s ∪ ∅ = s :=
ext.2 $ λ x, mem_union.trans $ or_false _

@[simp] theorem empty_union (s : finset α) : ∅ ∪ s = s :=
ext.2 $ λ x, mem_union.trans $ false_or _

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ∪ s := rfl

@[simp] theorem insert_union (a : α) (s t : finset α) : insert a s ∪ t = insert a (s ∪ t) :=
by simp only [insert_eq, union_assoc]

@[simp] theorem union_insert (a : α) (s t : finset α) : s ∪ insert a t = insert a (s ∪ t) :=
by simp only [insert_eq, union_left_comm]

theorem insert_union_distrib (a : α) (s t : finset α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
by simp only [insert_union, union_insert, insert_idem]


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

theorem inter_subset_left (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₁ := λ a, mem_of_mem_inter_left

theorem inter_subset_right (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₂ := λ a, mem_of_mem_inter_right

theorem subset_inter {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₁ ⊆ s₃ → s₁ ⊆ s₂ ∩ s₃ :=
by simp only [subset_iff, mem_inter] {contextual:=tt}; intros; split; trivial

@[simp] lemma coe_inter (s₁ s₂ : finset α) : ↑(s₁ ∩ s₂) = (↑s₁ ∩ ↑s₂ : set α) := set.ext $ λ _, mem_inter

@[simp] theorem inter_comm (s₁ s₂ : finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext.2 $ λ _, by simp only [mem_inter, and_comm]

@[simp] theorem inter_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext.2 $ λ _, by simp only [mem_inter, and_assoc]

@[simp] theorem inter_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
ext.2 $ λ _, by simp only [mem_inter, and.left_comm]

@[simp] theorem inter_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
ext.2 $ λ _, by simp only [mem_inter, and.right_comm]

@[simp] theorem inter_self (s : finset α) : s ∩ s = s :=
ext.2 $ λ _, mem_inter.trans $ and_self _

@[simp] theorem inter_empty (s : finset α) : s ∩ ∅ = ∅ :=
ext.2 $ λ _, mem_inter.trans $ and_false _

@[simp] theorem empty_inter (s : finset α) : ∅ ∩ s = ∅ :=
ext.2 $ λ _, mem_inter.trans $ false_and _

@[simp] theorem insert_inter_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext.2 $ λ x, have x = a ∨ x ∈ s₂ ↔ x ∈ s₂, from or_iff_right_of_imp $ by rintro rfl; exact h,
by simp only [mem_inter, mem_insert, or_and_distrib_left, this]

@[simp] theorem inter_insert_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₁) :
  s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext.2 $ λ x, have ¬ (x = a ∧ x ∈ s₂), by rintro ⟨rfl, H⟩; exact h H,
by simp only [mem_inter, mem_insert, or_and_distrib_right, this, false_or]

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₁) :
  s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : finset α} (H : a ∈ s) : ι a ∩ s = ι a :=
show insert a ∅ ∩ s = insert a ∅, by rw [insert_inter_of_mem H, empty_inter]

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : finset α} (H : a ∉ s) : ι a ∩ s = ∅ :=
eq_empty_of_forall_not_mem $ by simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[simp] theorem inter_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ∩ ι a = ι a :=
by rw [inter_comm, singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ∩ ι a = ∅ :=
by rw [inter_comm, singleton_inter_of_not_mem h]

/- lattice laws -/

instance : lattice (finset α) :=
{ sup          := (∪),
  sup_le       := assume a b c, union_subset,
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  inf          := (∩),
  le_inf       := assume a b c, subset_inter,
  inf_le_left  := inter_subset_left,
  inf_le_right := inter_subset_right,
  ..finset.partial_order }

@[simp] theorem sup_eq_union (s t : finset α) : s ⊔ t = s ∪ t := rfl
@[simp] theorem inf_eq_inter (s t : finset α) : s ⊓ t = s ∩ t := rfl

instance : semilattice_inf_bot (finset α) :=
{ bot := ∅, bot_le := empty_subset, ..finset.lattice.lattice }

instance : distrib_lattice (finset α) :=
{ le_sup_inf := assume a b c, show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c,
    by simp only [subset_iff, mem_inter, mem_union, and_imp, or_imp_distrib] {contextual:=tt};
    simp only [true_or, imp_true_iff, true_and, or_true],
  ..finset.lattice.lattice }

theorem inter_distrib_left (s t u : finset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := inf_sup_left

theorem inter_distrib_right (s t u : finset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := inf_sup_right

theorem union_distrib_left (s t u : finset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := sup_inf_left

theorem union_distrib_right (s t u : finset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) := sup_inf_right

/- erase -/

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : finset α) (a : α) : finset α := ⟨_, nodup_erase_of_nodup a s.2⟩

@[simp] theorem erase_val (s : finset α) (a : α) : (erase s a).1 = s.1.erase a := rfl

@[simp] theorem mem_erase {a b : α} {s : finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
mem_erase_iff_of_nodup s.2

theorem not_mem_erase (a : α) (s : finset α) : a ∉ erase s a := mem_erase_of_nodup s.2

@[simp] theorem erase_empty (a : α) : erase ∅ a = ∅ := rfl

theorem ne_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ≠ a :=
by simp only [mem_erase]; exact and.left

theorem mem_of_mem_erase {a b : α} {s : finset α} : b ∈ erase s a → b ∈ s := mem_of_mem_erase

theorem mem_erase_of_ne_of_mem {a b : α} {s : finset α} : a ≠ b → a ∈ s → a ∈ erase s b :=
by simp only [mem_erase]; exact and.intro

theorem erase_insert {a : α} {s : finset α} (h : a ∉ s) : erase (insert a s) a = s :=
ext.2 $ assume x, by simp only [mem_erase, mem_insert, and_or_distrib_left, not_and_self, false_or];
apply and_iff_right_of_imp; rintro H rfl; exact h H

theorem insert_erase {a : α} {s : finset α} (h : a ∈ s) : insert a (erase s a) = s :=
ext.2 $ assume x, by simp only [mem_insert, mem_erase, or_and_distrib_left, dec_em, true_and];
apply or_iff_right_of_imp; rintro rfl; exact h

theorem erase_subset_erase (a : α) {s t : finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
val_le_iff.1 $ erase_le_erase _ $ val_le_iff.2 h

theorem erase_subset (a : α) (s : finset α) : erase s a ⊆ s := erase_subset _ _

@[simp] lemma coe_erase (a : α) (s : finset α) : ↑(erase s a) = (↑s \ {a} : set α) :=
set.ext $ λ _, mem_erase.trans $ by rw [and_comm, set.mem_diff, set.mem_singleton_iff]; refl

lemma erase_ssubset {a : α} {s : finset α} (h : a ∈ s) : s.erase a ⊂ s :=
calc s.erase a ⊂ insert a (s.erase a) : ssubset_insert $ not_mem_erase _ _
  ... = _ : insert_erase h

theorem erase_eq_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq $ erase_of_not_mem h

theorem subset_insert_iff {a : α} {s t : finset α} : s ⊆ insert a t ↔ erase s a ⊆ t :=
by simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp];
exact forall_congr (λ x, forall_swap)

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
ext.2 $ λ a, by simpa only [mem_sdiff, mem_union, or_comm,
  or_and_distrib_left, dec_em, and_true] using or_iff_right_of_imp (@h a)

@[simp] theorem union_sdiff_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁ ∪ (s₂ \ s₁) = s₂ :=
(union_comm _ _).trans (sdiff_union_of_subset h)

@[simp] theorem inter_sdiff_self (s₁ s₂ : finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
eq_empty_of_forall_not_mem $
by simp only [mem_inter, mem_sdiff]; rintro x ⟨h, _, hn⟩; exact hn h

@[simp] theorem sdiff_inter_self (s₁ s₂ : finset α) : (s₂ \ s₁) ∩ s₁ = ∅ :=
(inter_comm _ _).trans (inter_sdiff_self _ _)

theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : finset α} (h₁ : t₁ ⊆ t₂) (h₂ : s₂ ⊆ s₁) : t₁ \ s₁ ⊆ t₂ \ s₂ :=
by simpa only [subset_iff, mem_sdiff, and_imp] using λ a m₁ m₂, and.intro (h₁ m₁) (mt (@h₂ _) m₂)

@[simp] lemma coe_sdiff (s₁ s₂ : finset α) : ↑(s₁ \ s₂) = (↑s₁ \ ↑s₂ : set α) :=
set.ext $ λ _, mem_sdiff

end decidable_eq

/- attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the
  subtype `{x // x ∈ s}`. -/
def attach (s : finset α) : finset {x // x ∈ s} := ⟨attach s.1, nodup_attach.2 s.2⟩

@[simp] theorem attach_val (s : finset α) : s.attach.1 = s.1.attach := rfl

@[simp] theorem mem_attach (s : finset α) : ∀ x, x ∈ s.attach := mem_attach _

@[simp] theorem attach_empty : attach (∅ : finset α) = ∅ := rfl

section decidable_pi_exists
variables {s : finset α}

instance decidable_dforall_finset {p : Πa∈s, Prop} [hp : ∀a (h : a ∈ s), decidable (p a h)] :
  decidable (∀a (h : a ∈ s), p a h) :=
multiset.decidable_dforall_multiset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidable_eq_pi_finset {β : α → Type*} [h : ∀a, decidable_eq (β a)] :
  decidable_eq (Πa∈s, β a) :=
multiset.decidable_eq_pi_multiset

instance decidable_dexists_finset {p : Πa∈s, Prop} [hp : ∀a (h : a ∈ s), decidable (p a h)] :
  decidable (∃a (h : a ∈ s), p a h) :=
multiset.decidable_dexists_multiset

end decidable_pi_exists

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
ext.2 $ assume a, by simp only [mem_filter, and_comm, and.left_comm]

@[simp] lemma filter_true {s : finset α} [h : decidable_pred (λ _, true)] :
  @finset.filter α (λ _, true) h s = s :=
by ext; simp

@[simp] theorem filter_false {h} (s : finset α) : @filter α (λa, false) h s = ∅ :=
ext.2 $ assume a, by simp only [mem_filter, and_false]; refl

lemma filter_congr {s : finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
eq_of_veq $ filter_congr H

variable [decidable_eq α]
theorem filter_union (s₁ s₂ : finset α) :
  (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
ext.2 $ λ _, by simp only [mem_filter, mem_union, or_and_distrib_right]

theorem filter_or (s : finset α) : s.filter (λ a, p a ∨ q a) = s.filter p ∪ s.filter q :=
ext.2 $ λ _, by simp only [mem_filter, mem_union, and_or_distrib_left]

theorem filter_and (s : finset α) : s.filter (λ a, p a ∧ q a) = s.filter p ∩ s.filter q :=
ext.2 $ λ _, by simp only [mem_filter, mem_inter, and_comm, and.left_comm, and_self]

theorem filter_not (s : finset α) : s.filter (λ a, ¬ p a) = s \ s.filter p :=
ext.2 $ by simpa only [mem_filter, mem_sdiff, and_comm, not_and] using λ a, and_congr_right $
  λ h : a ∈ s, (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : finset α) :
  s₁ \ s₂ = filter (∉ s₂) s₁ := ext.2 $ λ _, by simp only [mem_sdiff, mem_filter]

theorem filter_union_filter_neg_eq (s : finset α) : s.filter p ∪ s.filter (λa, ¬ p a) = s :=
by simp only [filter_not, union_sdiff_of_subset (filter_subset s)]

theorem filter_inter_filter_neg_eq (s : finset α) : s.filter p ∩ s.filter (λa, ¬ p a) = ∅ :=
by simp only [filter_not, inter_sdiff_self]

@[simp] lemma coe_filter (s : finset α) : ↑(s.filter p) = ({x ∈ ↑s | p x} : set α) :=
set.ext $ λ _, mem_filter

end filter

/- range -/
section range
variables {n m l : ℕ}

/-- `range n` is the set of integers less than `n`. -/
def range (n : ℕ) : finset ℕ := ⟨_, nodup_range n⟩

@[simp] theorem range_val (n : ℕ) : (range n).1 = multiset.range n := rfl

@[simp] theorem mem_range : m ∈ range n ↔ m < n := mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_succ : range (succ n) = insert n (range n) :=
eq_of_veq $ (range_succ n).trans $ (ndinsert_of_not_mem not_mem_range_self).symm

@[simp] theorem not_mem_range_self : n ∉ range n := not_mem_range_self

@[simp] theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m := range_subset

theorem exists_nat_subset_range (s : finset ℕ) : ∃n : ℕ, s ⊆ range n :=
finset.induction_on s ⟨0, empty_subset _⟩ $ λ a s ha ⟨n, hn⟩,
⟨max (a + 1) n, insert_subset.2
  ⟨by simpa only [mem_range] using le_max_left (a+1) n,
  subset.trans hn (by simpa only [range_subset] using le_max_right (a+1) n)⟩⟩

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : finset α) ∧ p x) ↔ false :=
by simp only [not_mem_empty, false_and, exists_false]

theorem exists_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ (∃ x, x ∈ s ∧ p x) :=
by simp only [mem_insert, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : finset α) → p x) ↔ true :=
iff_true_intro $ λ _, false.elim

theorem forall_mem_insert [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ (∀ x, x ∈ s → p x) :=
by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

end finset

namespace option

/-- Construct an empty or singleton finset from an `option` -/
def to_finset (o : option α) : finset α :=
match o with
| none   := ∅
| some a := finset.singleton a
end

@[simp] theorem to_finset_none : none.to_finset = (∅ : finset α) := rfl

@[simp] theorem to_finset_some {a : α} : (some a).to_finset = finset.singleton a := rfl

@[simp] theorem mem_to_finset {a : α} {o : option α} : a ∈ o.to_finset ↔ a ∈ o :=
by cases o; simp only [to_finset, finset.mem_singleton, option.mem_def, eq_comm]; refl

end option

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

@[simp] lemma to_finset_zero :
  to_finset (0 : multiset α) = ∅ :=
rfl

@[simp] lemma to_finset_cons (a : α) (s : multiset α) :
  to_finset (a :: s) = insert a (to_finset s) :=
finset.eq_of_veq erase_dup_cons

@[simp] lemma to_finset_add (s t : multiset α) :
  to_finset (s + t) = to_finset s ∪ to_finset t :=
finset.ext' $ by simp

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

@[simp] theorem to_finset_nil : to_finset (@nil α) = ∅ :=
rfl

@[simp] theorem to_finset_cons {a : α} {l : list α} : to_finset (a :: l) = insert a (to_finset l) :=
finset.eq_of_veq $ by by_cases h : a ∈ l; simp [finset.insert_val', multiset.erase_dup_cons, h]

end list

namespace finset

section map
open function

def map (f : α ↪ β) (s : finset α) : finset β :=
⟨s.1.map f, nodup_map f.2 s.2⟩

@[simp] theorem map_val (f : α ↪ β) (s : finset α) : (map f s).1 = s.1.map f := rfl

@[simp] theorem map_empty (f : α ↪ β) (s : finset α) : (∅ : finset α).map f = ∅ := rfl

variables {f : α ↪ β} {s : finset α}

@[simp] theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
mem_map.trans $ by simp only [exists_prop]; refl

theorem mem_map' (f : α ↪ β) {a} {s : finset α} : f a ∈ s.map f ↔ a ∈ s :=
mem_map_of_inj f.2

@[simp] theorem mem_map_of_mem (f : α ↪ β) {a} {s : finset α} : a ∈ s → f a ∈ s.map f :=
(mem_map' _).2

theorem map_to_finset [decidable_eq α] [decidable_eq β] {s : multiset α} :
  s.to_finset.map f = (s.map f).to_finset :=
ext.2 $ λ _, by simp only [mem_map, multiset.mem_map, exists_prop, multiset.mem_to_finset]

theorem map_refl : s.map (embedding.refl _) = s :=
ext.2 $ λ _, by simpa only [mem_map, exists_prop] using exists_eq_right

theorem map_map {g : β ↪ γ} : (s.map f).map g = s.map (f.trans g) :=
eq_of_veq $ by simp only [map_val, multiset.map_map]; refl

theorem map_subset_map {s₁ s₂ : finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
⟨λ h x xs, (mem_map' _).1 $ h $ (mem_map' f).2 xs,
 λ h, by simp [subset_def, map_subset_map h]⟩

theorem map_inj {s₁ s₂ : finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
by simp only [subset.antisymm_iff, map_subset_map]

def map_embedding (f : α ↪ β) : finset α ↪ finset β := ⟨map f, λ s₁ s₂, map_inj.1⟩

@[simp] theorem map_embedding_apply : map_embedding f s = map f s := rfl

theorem map_filter {p : β → Prop} [decidable_pred p] :
  (s.map f).filter p = (s.filter (p ∘ f)).map f :=
ext.2 $ λ b, by simp only [mem_filter, mem_map, exists_prop, and_assoc]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, h1, h2, rfl⟩,
by rintro ⟨x, h1, h2, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem map_union [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
ext.2 $ λ _, by simp only [mem_map, mem_union, exists_prop, or_and_distrib_right, exists_or_distrib]

theorem map_inter [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
ext.2 $ λ b, by simp only [mem_map, mem_inter, exists_prop]; exact
⟨by rintro ⟨a, ⟨m₁, m₂⟩, rfl⟩; exact ⟨⟨a, m₁, rfl⟩, ⟨a, m₂, rfl⟩⟩,
by rintro ⟨⟨a, m₁, e⟩, ⟨a', m₂, rfl⟩⟩; cases f.2 e; exact ⟨_, ⟨m₁, m₂⟩, rfl⟩⟩

@[simp] theorem map_singleton (f : α ↪ β) (a : α) : (singleton a).map f = singleton (f a) :=
ext.2 $ λ _, by simp only [mem_map, mem_singleton, exists_prop, exists_eq_left]; exact eq_comm

@[simp] theorem map_insert [decidable_eq α] [decidable_eq β]
  (f : α ↪ β) (a : α) (s : finset α) :
  (insert a s).map f = insert (f a) (s.map f) :=
by simp only [insert_eq, insert_empty_eq_singleton, map_union, map_singleton]

@[simp] theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_map_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma attach_map_val {s : finset α} : s.attach.map (embedding.subtype _) = s :=
eq_of_veq $ by rw [map_val, attach_val]; exact attach_map_val _

end map

section image
variables [decidable_eq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : finset α) : finset β := (s.1.map f).to_finset

@[simp] theorem image_val (f : α → β) (s : finset α) : (image f s).1 = (s.1.map f).erase_dup := rfl

@[simp] theorem image_empty (f : α → β) : (∅ : finset α).image f = ∅ := rfl

variables {f : α → β} {s : finset α}

@[simp] theorem mem_image {b : β} : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
by simp only [mem_def, image_val, mem_erase_dup, multiset.mem_map, exists_prop]

@[simp] theorem mem_image_of_mem (f : α → β) {a} {s : finset α} (h : a ∈ s) : f a ∈ s.image f :=
mem_image.2 ⟨_, h, rfl⟩

@[simp] lemma coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
set.ext $ λ _, mem_image.trans $ by simp only [exists_prop]; refl

theorem image_to_finset [decidable_eq α] {s : multiset α} : s.to_finset.image f = (s.map f).to_finset :=
ext.2 $ λ _, by simp only [mem_image, multiset.mem_to_finset, exists_prop, multiset.mem_map]

@[simp] theorem image_val_of_inj_on (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : (image f s).1 = s.1.map f :=
multiset.erase_dup_eq_self.2 (nodup_map_on H s.2)

theorem image_id [decidable_eq α] : s.image id = s :=
ext.2 $ λ _, by simp only [mem_image, exists_prop, id, exists_eq_right]

theorem image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq $ by simp only [image_val, erase_dup_map_erase_dup_eq, multiset.map_map]

theorem image_subset_image {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
by simp only [subset_def, image_val, subset_erase_dup', erase_dup_subset', multiset.map_subset_map h]

theorem image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext.2 $ λ b, by simp only [mem_filter, mem_image, exists_prop]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
 by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_union [decidable_eq α] {f : α → β} (s₁ s₂ : finset α) : (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
ext.2 $ λ _, by simp only [mem_image, mem_union, exists_prop, or_and_distrib_right, exists_or_distrib]

theorem image_inter [decidable_eq α] (s₁ s₂ : finset α) (hf : ∀x y, f x = f y → x = y) : (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
ext.2 $ by simp only [mem_image, exists_prop, mem_inter]; exact λ b,
⟨λ ⟨a, ⟨m₁, m₂⟩, e⟩, ⟨⟨a, m₁, e⟩, ⟨a, m₂, e⟩⟩,
 λ ⟨⟨a, m₁, e₁⟩, ⟨a', m₂, e₂⟩⟩, ⟨a, ⟨m₁, hf _ _ (e₂.trans e₁.symm) ▸ m₂⟩, e₁⟩⟩.

@[simp] theorem image_singleton [decidable_eq α] (f : α → β) (a : α) : (singleton a).image f = singleton (f a) :=
ext.2 $ λ x, by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm

@[simp] theorem image_insert [decidable_eq α] (f : α → β) (a : α) (s : finset α) :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp only [insert_eq, insert_empty_eq_singleton, image_singleton, image_union]

@[simp] theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_image_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma attach_image_val [decidable_eq α] {s : finset α} : s.attach.image subtype.val = s :=
eq_of_veq $ by rw [image_val, attach_val, multiset.attach_map_val, erase_dup_eq_self]

@[simp] lemma attach_insert [decidable_eq α] {a : α} {s : finset α} :
  attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : {x // x ∈ insert a s})
    ((attach s).image (λx, ⟨x.1, mem_insert_of_mem x.2⟩)) :=
ext.2 $ λ ⟨x, hx⟩, ⟨or.cases_on (mem_insert.1 hx)
  (assume h : x = a, λ _, mem_insert.2 $ or.inl $ subtype.eq h)
  (assume h : x ∈ s, λ _, mem_insert_of_mem $ mem_image.2 $ ⟨⟨x, h⟩, mem_attach _ _, subtype.eq rfl⟩),
λ _, finset.mem_attach _ _⟩

theorem map_eq_image (f : α ↪ β) (s : finset α) : s.map f = s.image f :=
eq_of_veq $ (multiset.erase_dup_eq_self.2 (s.map f).2).symm

lemma image_const [decidable_eq β] {s : finset α} (h : s ≠ ∅) (b : β) : s.image (λa, b) = singleton b :=
ext.2 $ assume b', by simp only [mem_image, exists_prop, exists_and_distrib_right,
  exists_mem_of_ne_empty h, true_and, mem_singleton, eq_comm]

protected def subtype {α} (p : α → Prop) [decidable_pred p] (s : finset α) : finset (subtype p) :=
(s.filter p).attach.map ⟨λ x, ⟨x.1, (finset.mem_filter.1 x.2).2⟩,
λ x y H, subtype.eq $ subtype.mk.inj H⟩

@[simp] lemma mem_subtype {p : α → Prop} [decidable_pred p] {s : finset α} :
  ∀{a : subtype p}, a ∈ s.subtype p ↔ a.val ∈ s
| ⟨a, ha⟩ := by simp [finset.subtype, ha]

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

@[simp] theorem card_insert_of_not_mem [decidable_eq α]
  {a : α} {s : finset α} (h : a ∉ s) : card (insert a s) = card s + 1 :=
by simpa only [card_cons, card, insert_val] using
congr_arg multiset.card (ndinsert_of_not_mem h)

theorem card_insert_le [decidable_eq α] (a : α) (s : finset α) : card (insert a s) ≤ card s + 1 :=
by by_cases a ∈ s; [{rw [insert_eq_of_mem h], apply nat.le_add_right},
rw [card_insert_of_not_mem h]]

@[simp] theorem card_singleton (a : α) : card (singleton a) = 1 := card_singleton _

theorem card_erase_of_mem [decidable_eq α] {a : α} {s : finset α} : a ∈ s → card (erase s a) = pred (card s) := card_erase_of_mem

@[simp] theorem card_range (n : ℕ) : card (range n) = n := card_range n

@[simp] theorem card_attach {s : finset α} : card (attach s) = card s := multiset.card_attach

theorem card_image_of_inj_on [decidable_eq β] {f : α → β} {s : finset α}
  (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : card (image f s) = card s :=
by simp only [card, image_val_of_inj_on H, card_map]

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
  by simpa only [ext, mem_image, exists_prop, subtype.exists, mem_attach, true_and],
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
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has, by simp only [eq, card_erase_of_mem has, pred_succ]⟩)
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
    (by simpa only [mem_range])
    (by simp only [mem_range]; exact assume a₁ h₁ a₂ h₂, f_inj a₁ a₂ h₁ h₂)

@[elab_as_eliminator] lemma strong_induction_on {p : finset α → Sort*} :
  ∀ (s : finset α), (∀s, (∀t ⊂ s, p t) → p s) → p s
| ⟨s, nd⟩ ih := multiset.strong_induction_on s
  (λ s IH nd, ih ⟨s, nd⟩ (λ ⟨t, nd'⟩ ss, IH t (val_lt_iff.2 ss) nd')) nd

@[elab_as_eliminator] lemma case_strong_induction_on [decidable_eq α] {p : finset α → Prop}
  (s : finset α) (h₀ : p ∅) (h₁ : ∀ a s, a ∉ s → (∀t ⊆ s, p t) → p (insert a s)) : p s :=
finset.strong_induction_on s $ λ s,
finset.induction_on s (λ _, h₀) $ λ a s n _ ih, h₁ a s n $
λ t ss, ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

lemma card_congr {s : finset α} {t : finset β} (f : Π a ∈ s, β)
  (h₁ : ∀ a ha, f a ha ∈ t) (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b)
  (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) : s.card = t.card :=
by haveI := classical.prop_decidable; exact
calc s.card = s.attach.card : card_attach.symm
... = (s.attach.image (λ (a : {a // a ∈ s}), f a.1 a.2)).card :
  eq.symm (card_image_of_injective _ (λ a b h, subtype.eq (h₂ _ _ _ _ h)))
... = t.card : congr_arg card (finset.ext.2 $ λ b,
    ⟨λ h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in ha₂ ▸ h₁ _ _,
      λ h, let ⟨a, ha₁, ha₂⟩ := h₃ b h in mem_image.2 ⟨⟨a, ha₁⟩, by simp [ha₂]⟩⟩)

lemma card_union_add_card_inter [decidable_eq α] (s t : finset α) :
  (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
finset.induction_on t (by simp) (λ a, by by_cases a ∈ s; simp * {contextual := tt})

lemma card_union_le [decidable_eq α] (s t : finset α) :
  (s ∪ t).card ≤ s.card + t.card :=
card_union_add_card_inter s t ▸ le_add_right _ _

lemma surj_on_of_inj_on_of_card_le {s : finset α} {t : finset β}
  (f : Π a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂)
  (hst : card t ≤ card s) :
  (∀ b ∈ t, ∃ a ha, b = f a ha) :=
by haveI := classical.dec_eq β; exact
λ b hb,
  have h : card (image (λ (a : {a // a ∈ s}), f (a.val) a.2) (attach s)) = card s,
    from @card_attach _ s ▸ card_image_of_injective _
      (λ ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h, subtype.eq $ hinj _ _ _ _ h),
  have h₁ : image (λ a : {a // a ∈ s}, f a.1 a.2) s.attach = t :=
  eq_of_subset_of_card_le (λ b h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in
    ha₂ ▸ hf _ _) (by simp [hst, h]),
begin
  rw ← h₁ at hb,
  rcases mem_image.1 hb with ⟨a, ha₁, ha₂⟩,
  exact ⟨a, a.2, ha₂.symm⟩,
end

end card

section bind
variables [decidable_eq β] {s : finset α} {t : α → finset β}

/-- `bind s t` is the union of `t x` over `x ∈ s` -/
protected def bind (s : finset α) (t : α → finset β) : finset β := (s.1.bind (λ a, (t a).1)).to_finset

@[simp] theorem bind_val (s : finset α) (t : α → finset β) :
  (s.bind t).1 = (s.1.bind (λ a, (t a).1)).erase_dup := rfl

@[simp] theorem bind_empty : finset.bind ∅ t = ∅ := rfl

@[simp] theorem mem_bind {b : β} : b ∈ s.bind t ↔ ∃a∈s, b ∈ t a :=
by simp only [mem_def, bind_val, mem_erase_dup, mem_bind, exists_prop]

@[simp] theorem bind_insert [decidable_eq α] {a : α} : (insert a s).bind t = t a ∪ s.bind t :=
ext.2 $ λ x, by simp only [mem_bind, exists_prop, mem_union, mem_insert,
  or_and_distrib_right, exists_or_distrib, exists_eq_left]
-- ext.2 $ λ x, by simp [or_and_distrib_right, exists_or_distrib]

@[simp] lemma singleton_bind [decidable_eq α] {a : α} : (singleton a).bind t = t a :=
show (insert a ∅ : finset α).bind t = t a, from bind_insert.trans $ union_empty _

theorem image_bind [decidable_eq γ] {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bind t = s.bind (λa, t (f a)) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [image_insert, bind_insert, ih])

theorem bind_image [decidable_eq γ] {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bind t).image f = s.bind (λa, (t a).image f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [bind_insert, image_union, ih])

theorem bind_to_finset [decidable_eq α] (s : multiset α) (t : α → multiset β) :
  (s.bind t).to_finset = s.to_finset.bind (λa, (t a).to_finset) :=
ext.2 $ λ x, by simp only [multiset.mem_to_finset, mem_bind, multiset.mem_bind, exists_prop]

lemma bind_mono {t₁ t₂ : α → finset β} (h : ∀a∈s, t₁ a ⊆ t₂ a) : s.bind t₁ ⊆ s.bind t₂ :=
have ∀b a, a ∈ s → b ∈ t₁ a → (∃ (a : α), a ∈ s ∧ b ∈ t₂ a),
  from assume b a ha hb, ⟨a, ha, finset.mem_of_subset (h a ha) hb⟩,
by simpa only [subset_iff, mem_bind, exists_imp_distrib, and_imp, exists_prop]

lemma bind_singleton {f : α → β} : s.bind (λa, {f a}) = s.image f :=
ext.2 $ λ x, by simp only [mem_bind, mem_image, insert_empty_eq_singleton, mem_singleton, eq_comm]

lemma image_bind_filter_eq [decidable_eq α] (s : finset β) (g : β → α) :
  (s.image g).bind (λa, s.filter $ (λc, g c = a)) = s :=
begin
  ext b,
  simp,
  split,
  { rintros ⟨a, ⟨b', _, _⟩, hb, _⟩, exact hb },
  { rintros hb, exact ⟨g b, ⟨b, hb, rfl⟩, hb, rfl⟩ }
end

end bind

section prod
variables {s : finset α} {t : finset β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : finset α) (t : finset β) : finset (α × β) := ⟨_, nodup_product s.2 t.2⟩

@[simp] theorem product_val : (s.product t).1 = s.1.product t.1 := rfl

@[simp] theorem mem_product {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := mem_product

theorem product_eq_bind [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
 s.product t = s.bind (λa, t.image $ λb, (a, b)) :=
ext.2 $ λ ⟨x, y⟩, by simp only [mem_product, mem_bind, mem_image, exists_prop, prod.mk.inj_iff,
  and.left_comm, exists_and_distrib_left, exists_eq_right, exists_eq_left]

@[simp] theorem card_product (s : finset α) (t : finset β) : card (s.product t) = card s * card t :=
multiset.card_product _ _

end prod

section sigma
variables {σ : α → Type*} {s : finset α} {t : Πa, finset (σ a)}

/-- `sigma s t` is the set of dependent pairs `⟨a, b⟩` such that `a ∈ s` and `b ∈ t a`. -/
protected def sigma (s : finset α) (t : Πa, finset (σ a)) : finset (Σa, σ a) :=
⟨_, nodup_sigma s.2 (λ a, (t a).2)⟩

@[simp] theorem mem_sigma {p : sigma σ} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1) := mem_sigma

theorem sigma_mono {s₁ s₂ : finset α} {t₁ t₂ : Πa, finset (σ a)}
  (H1 : s₁ ⊆ s₂) (H2 : ∀a, t₁ a ⊆ t₂ a) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
λ ⟨x, sx⟩ H, let ⟨H3, H4⟩ := mem_sigma.1 H in mem_sigma.2 ⟨H1 H3, H2 x H4⟩

theorem sigma_eq_bind [decidable_eq α] [∀a, decidable_eq (σ a)] (s : finset α) (t : Πa, finset (σ a)) :
 s.sigma t = s.bind (λa, (t a).image $ λb, ⟨a, b⟩) :=
ext.2 $ λ ⟨x, y⟩, by simp only [mem_sigma, mem_bind, mem_image, exists_prop,
  and.left_comm, exists_and_distrib_left, exists_eq_left, heq_iff_eq, exists_eq_right]

end sigma

section pi
variables {δ : α → Type*} [decidable_eq α]

def pi (s : finset α) (t : Πa, finset (δ a)) : finset (Πa∈s, δ a) :=
⟨s.1.pi (λ a, (t a).1), nodup_pi s.2 (λ a _, (t a).2)⟩

@[simp] lemma pi_val (s : finset α) (t : Πa, finset (δ a)) :
  (s.pi t).1 = s.1.pi (λ a, (t a).1) := rfl

@[simp] lemma mem_pi {s : finset α} {t : Πa, finset (δ a)} {f : Πa∈s, δ a} :
  f ∈ s.pi t ↔ (∀a (h : a ∈ s), f a h ∈ t a) :=
mem_pi _ _ _

def pi.empty (β : α → Sort*) [decidable_eq α] (a : α) (h : a ∈ (∅ : finset α)) : β a :=
multiset.pi.empty β a h

def pi.cons (s : finset α) (a : α) (b : δ a) (f : Πa, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) : δ a' :=
multiset.pi.cons s.1 a b f _ (multiset.mem_cons.2 $ mem_insert.symm.2 h)

@[simp] lemma pi.cons_same (s : finset α) (a : α) (b : δ a) (f : Πa, a ∈ s → δ a) (h : a ∈ insert a s) :
  pi.cons s a b f a h = b :=
multiset.pi.cons_same _

lemma pi.cons_ne {s : finset α} {a a' : α} {b : δ a} {f : Πa, a ∈ s → δ a} {h : a' ∈ insert a s} (ha : a ≠ a') :
  pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
multiset.pi.cons_ne _ _

lemma injective_pi_cons  {a : α} {b : δ a} {s : finset α} (hs : a ∉ s) :
  function.injective (pi.cons s a b) :=
assume e₁ e₂ eq,
@multiset.injective_pi_cons α _ δ a b s.1 hs _ _ $
  funext $ assume e, funext $ assume h,
  have pi.cons s a b e₁ e (by simpa only [mem_cons, mem_insert] using h) = pi.cons s a b e₂ e (by simpa only [mem_cons, mem_insert] using h),
    by rw [eq],
  this

@[simp] lemma pi_empty {t : Πa:α, finset (δ a)} :
  pi (∅ : finset α) t = singleton (pi.empty δ) := rfl

@[simp] lemma pi_insert [∀a, decidable_eq (δ a)]
  {s : finset α} {t : Πa:α, finset (δ a)} {a : α} (ha : a ∉ s) :
  pi (insert a s) t = (t a).bind (λb, (pi s t).image (pi.cons s a b)) :=
begin
  apply eq_of_veq,
  rw ← multiset.erase_dup_eq_self.2 (pi (insert a s) t).2,
  refine (λ s' (h : s' = a :: s.1), (_ : erase_dup (multiset.pi s' (λ a, (t a).1)) =
    erase_dup ((t a).1.bind $ λ b,
    erase_dup $ (multiset.pi s.1 (λ (a : α), (t a).val)).map $
      λ f a' h', multiset.pi.cons s.1 a b f a' (h ▸ h')))) _ (insert_val_of_not_mem ha),
  subst s', rw pi_cons,
  congr, funext b,
  rw multiset.erase_dup_eq_self.2,
  exact multiset.nodup_map (multiset.injective_pi_cons ha) (pi s t).2,
end

end pi

section powerset
def powerset (s : finset α) : finset (finset α) :=
⟨s.1.powerset.pmap finset.mk
  (λ t h, nodup_of_le (mem_powerset.1 h) s.2),
 nodup_pmap (λ a ha b hb, congr_arg finset.val)
   (nodup_powerset.2 s.2)⟩

@[simp] theorem mem_powerset {s t : finset α} : s ∈ powerset t ↔ s ⊆ t :=
by cases s; simp only [powerset, mem_mk, mem_pmap, mem_powerset, exists_prop, exists_eq_right]; rw ← val_le_iff

@[simp] theorem empty_mem_powerset (s : finset α) : ∅ ∈ powerset s :=
mem_powerset.2 (empty_subset _)

@[simp] theorem mem_powerset_self (s : finset α) : s ∈ powerset s :=
mem_powerset.2 (subset.refl _)

@[simp] theorem powerset_mono {s t : finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
⟨λ h, (mem_powerset.1 $ h $ mem_powerset_self _),
 λ st u h, mem_powerset.2 $ subset.trans (mem_powerset.1 h) st⟩

@[simp] theorem card_powerset (s : finset α) :
  card (powerset s) = 2 ^ card s :=
(card_pmap _ _ _).trans (card_powerset s.1)

end powerset

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
by unfold fold; rw [insert_val, ndinsert_of_not_mem h, map_cons, fold_cons_left]

@[simp] theorem fold_singleton : (singleton a).fold op b f = f a * b := rfl

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
by haveI := classical.prop_decidable;
   rw [fold, insert_val', ← fold_erase_dup_idem op, erase_dup_map_erase_dup_eq,
       fold_erase_dup_idem op]; simp only [map_cons, fold_cons_left, fold]

end fold

section sup
variables [semilattice_sup_bot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : finset β) (f : β → α) : α := s.fold (⊔) ⊥ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma sup_val : s.sup f = (s.1.map f).sup := rfl

@[simp] lemma sup_empty : (∅ : finset β).sup f = ⊥ :=
fold_empty

@[simp] lemma sup_insert [decidable_eq β] {b : β} : (insert b s : finset β).sup f = f b ⊔ s.sup f :=
fold_insert_idem

@[simp] lemma sup_singleton [decidable_eq β] {b : β} : ({b} : finset β).sup f = f b :=
calc _ = f b ⊔ (∅:finset β).sup f : sup_insert
  ... = f b : sup_bot_eq

lemma sup_union [decidable_eq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
finset.induction_on s₁ (by rw [empty_union, sup_empty, bot_sup_eq]) $ λ a s has ih,
by rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]

lemma sup_mono_fun {g : β → α} : (∀b∈s, f b ≤ g b) → s.sup f ≤ s.sup g :=
by letI := classical.dec_eq β; from
finset.induction_on s (λ _, le_refl _) (λ a s has ih H,
  by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq] at H;
     simp only [sup_insert]; exact sup_le_sup H.1 (ih H.2))

lemma le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
by letI := classical.dec_eq β; from
calc f b ≤ f b ⊔ s.sup f : le_sup_left
  ... = (insert b s).sup f : sup_insert.symm
  ... = s.sup f : by rw [insert_eq_of_mem hb]

lemma sup_le {a : α} : (∀b ∈ s, f b ≤ a) → s.sup f ≤ a :=
by letI := classical.dec_eq β; from
finset.induction_on s (λ _, bot_le) (λ n s hns ih H,
  by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq] at H;
     simp only [sup_insert]; exact sup_le H.1 (ih H.2))

lemma sup_le_iff {a : α} : s.sup f ≤ a ↔ (∀b ∈ s, f b ≤ a) :=
iff.intro (assume h b hb, le_trans (le_sup hb) h) sup_le

lemma sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
sup_le $ assume b hb, le_sup (h hb)

lemma sup_lt [is_total α (≤)] {a : α} : (⊥ < a) → (∀b ∈ s, f b < a) → s.sup f < a :=
have A : ∀ x y, x < a → y < a → x ⊔ y < a :=
begin
  assume x y hx hy,
  cases (is_total.total (≤) x y) with h,
  { simpa [sup_of_le_right h] using hy },
  { simpa [sup_of_le_left h] using hx }
end,
by letI := classical.dec_eq β; from
finset.induction_on s (by simp) (by simp [A] {contextual := tt})

lemma comp_sup_eq_sup_comp [is_total α (≤)] {γ : Type} [semilattice_sup_bot γ]
  (g : α → γ) (mono_g : monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
have A : ∀x y, g (x ⊔ y) = g x ⊔ g y :=
begin
  assume x y,
  cases (is_total.total (≤) x y) with h,
  { simp [sup_of_le_right h, sup_of_le_right (mono_g h)] },
  { simp [sup_of_le_left h, sup_of_le_left (mono_g h)] }
end,
by letI := classical.dec_eq β; from
finset.induction_on s (by simp [bot]) (by simp [A] {contextual := tt})

end sup

lemma sup_eq_supr [complete_lattice β] (s : finset α) (f : α → β) : s.sup f = (⨆a∈s, f a) :=
le_antisymm
  (finset.sup_le $ assume a ha, le_supr_of_le a $ le_supr _ ha)
  (supr_le $ assume a, supr_le $ assume ha, le_sup ha)

section inf
variables [semilattice_inf_top α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : finset β) (f : β → α) : α := s.fold (⊓) ⊤ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma inf_val : s.inf f = (s.1.map f).inf := rfl

@[simp] lemma inf_empty : (∅ : finset β).inf f = ⊤ :=
fold_empty

@[simp] lemma inf_insert [decidable_eq β] {b : β} : (insert b s : finset β).inf f = f b ⊓ s.inf f :=
fold_insert_idem

@[simp] lemma inf_singleton [decidable_eq β] {b : β} : ({b} : finset β).inf f = f b :=
calc _ = f b ⊓ (∅:finset β).inf f : inf_insert
  ... = f b : inf_top_eq

lemma inf_union [decidable_eq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
finset.induction_on s₁ (by rw [empty_union, inf_empty, top_inf_eq]) $ λ a s has ih,
by rw [insert_union, inf_insert, inf_insert, ih, inf_assoc]

lemma inf_mono_fun {g : β → α} : (∀b∈s, f b ≤ g b) → s.inf f ≤ s.inf g :=
by letI := classical.dec_eq β; from
finset.induction_on s (λ _, le_refl _) (λ a s has ih H,
  by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq] at H;
     simp only [inf_insert]; exact inf_le_inf H.1 (ih H.2))

lemma inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
by letI := classical.dec_eq β; from
calc f b ≥ f b ⊓ s.inf f : inf_le_left
  ... = (insert b s).inf f : inf_insert.symm
  ... = s.inf f : by rw [insert_eq_of_mem hb]

lemma le_inf {a : α} : (∀b ∈ s, a ≤ f b) → a ≤ s.inf f :=
by letI := classical.dec_eq β; from
finset.induction_on s (λ _, le_top) (λ n s hns ih H,
  by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq] at H;
     simp only [inf_insert]; exact le_inf H.1 (ih H.2))

lemma le_inf_iff {a : α} : a ≤ s.inf f ↔ (∀b ∈ s, a ≤ f b) :=
iff.intro (assume h b hb, le_trans h (inf_le hb)) le_inf

lemma inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
le_inf $ assume b hb, inf_le (h hb)

lemma lt_inf [is_total α (≤)] {a : α} : (a < ⊤) → (∀b ∈ s, a < f b) → a < s.inf f :=
have A : ∀ x y, a < x → a < y → a < x ⊓ y :=
begin
  assume x y hx hy,
  cases (is_total.total (≤) x y) with h,
  { simpa [inf_of_le_left h] using hy },
  { simpa [inf_of_le_right h] using hx }
end,
by letI := classical.dec_eq β; from
finset.induction_on s (by simp) (by simp [A] {contextual := tt})

lemma comp_inf_eq_inf_comp [is_total α (≤)] {γ : Type} [semilattice_inf_top γ]
  (g : α → γ) (mono_g : monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
have A : ∀x y, g (x ⊓ y) = g x ⊓ g y :=
begin
  assume x y,
  cases (is_total.total (≤) x y) with h,
  { simp [inf_of_le_left h, inf_of_le_left (mono_g h)] },
  { simp [inf_of_le_right h, inf_of_le_right (mono_g h)] }
end,
by letI := classical.dec_eq β; from
finset.induction_on s (by simp [top]) (by simp [A] {contextual := tt})

end inf

lemma inf_eq_infi [complete_lattice β] (s : finset α) (f : α → β) : s.inf f = (⨅a∈s, f a) :=
le_antisymm
  (le_infi $ assume a, le_infi $ assume ha, inf_le ha)
  (finset.le_inf $ assume a ha, infi_le_of_le a $ infi_le _ ha)

/- max and min of finite sets -/
section max_min
variables [decidable_linear_order α]

protected def max : finset α → option α :=
fold (option.lift_or_get max) none some

theorem max_eq_sup_with_bot (s : finset α) :
  s.max = @sup (with_bot α) α _ s some := rfl

@[simp] theorem max_empty : (∅ : finset α).max = none := rfl

@[simp] theorem max_insert {a : α} {s : finset α} :
  (insert a s).max = option.lift_or_get max (some a) s.max := fold_insert_idem

@[simp] theorem max_singleton {a : α} : finset.max {a} = some a := max_insert

@[simp] theorem max_singleton' {a : α} : finset.max (singleton a) = some a := max_singleton

theorem max_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.max :=
(@le_sup (with_bot α) _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem max_of_ne_empty {s : finset α} (h : s ≠ ∅) : ∃ a, a ∈ s.max :=
let ⟨a, ha⟩ := exists_mem_of_ne_empty h in max_of_mem ha

theorem max_eq_none {s : finset α} : s.max = none ↔ s = ∅ :=
⟨λ h, by_contradiction $
  λ hs, let ⟨a, ha⟩ := max_of_ne_empty hs in by rw [h] at ha; cases ha,
λ h, h.symm ▸ max_empty⟩

theorem mem_of_max {s : finset α} : ∀ {a : α}, a ∈ s.max → a ∈ s :=
finset.induction_on s (λ _ H, by cases H)
  (λ b s _ (ih : ∀ {a}, a ∈ s.max → a ∈ s) a (h : a ∈ (insert b s).max),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice max_choice (some b) s.max with q q;
      rw [max_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end)

theorem le_max_of_mem {s : finset α} {a b : α} (h₁ : a ∈ s) (h₂ : b ∈ s.max) : a ≤ b :=
by rcases @le_sup (with_bot α) _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

protected def min : finset α → option α :=
fold (option.lift_or_get min) none some

theorem min_eq_inf_with_top (s : finset α) :
  s.min = @inf (with_top α) α _ s some := rfl

@[simp] theorem min_empty : (∅ : finset α).min = none := rfl

@[simp] theorem min_insert {a : α} {s : finset α} :
  (insert a s).min = option.lift_or_get min (some a) s.min :=
fold_insert_idem

@[simp] theorem min_singleton {a : α} : finset.min {a} = some a := min_insert

theorem min_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.min :=
(@inf_le (with_top α) _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem min_of_ne_empty {s : finset α} (h : s ≠ ∅) : ∃ a, a ∈ s.min :=
let ⟨a, ha⟩ := exists_mem_of_ne_empty h in min_of_mem ha

theorem min_eq_none {s : finset α} : s.min = none ↔ s = ∅ :=
⟨λ h, by_contradiction $
  λ hs, let ⟨a, ha⟩ := min_of_ne_empty hs in by rw [h] at ha; cases ha,
λ h, h.symm ▸ min_empty⟩

theorem mem_of_min {s : finset α} : ∀ {a : α}, a ∈ s.min → a ∈ s :=
finset.induction_on s (λ _ H, by cases H) $
  λ b s _ (ih : ∀ {a}, a ∈ s.min → a ∈ s) a (h : a ∈ (insert b s).min),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice min_choice (some b) s.min with q q;
      rw [min_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end

theorem le_min_of_mem {s : finset α} {a b : α} (h₁ : b ∈ s) (h₂ : a ∈ s.min) : a ≤ b :=
by rcases @inf_le (with_top α) _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

end max_min

section sort
variables (r : α → α → Prop) [decidable_rel r]
  [is_trans α r] [is_antisymm α r] [is_total α r]

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

@[simp] theorem mem_sort {s : finset α} {a : α} : a ∈ sort r s ↔ a ∈ s :=
multiset.mem_sort _

end sort

section disjoint
variable [decidable_eq α]

theorem disjoint_left {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
by simp only [_root_.disjoint, inf_eq_inter, le_iff_subset, subset_iff, mem_inter, not_and, and_imp]; refl

theorem disjoint_val {s t : finset α} : disjoint s t ↔ s.1.disjoint t.1 :=
disjoint_left

theorem disjoint_iff_inter_eq_empty {s t : finset α} : disjoint s t ↔ s ∩ t = ∅ :=
disjoint_iff

theorem disjoint_right {s t : finset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
by rw [disjoint.comm, disjoint_left]

theorem disjoint_iff_ne {s t : finset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

theorem disjoint_of_subset_left {s t u : finset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
disjoint_left.2 (λ x m₁, (disjoint_left.1 d) (h m₁))

theorem disjoint_of_subset_right {s t u : finset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
disjoint_right.2 (λ x m₁, (disjoint_right.1 d) (h m₁))

@[simp] theorem disjoint_empty_left (s : finset α) : disjoint ∅ s := disjoint_bot_left

@[simp] theorem disjoint_empty_right (s : finset α) : disjoint s ∅ := disjoint_bot_right

@[simp] theorem singleton_disjoint {s : finset α} {a : α} : disjoint (singleton a) s ↔ a ∉ s :=
by simp only [disjoint_left, mem_singleton, forall_eq]

@[simp] theorem disjoint_singleton {s : finset α} {a : α} : disjoint s (singleton a) ↔ a ∉ s :=
disjoint.comm.trans singleton_disjoint

@[simp] theorem disjoint_insert_left {a : α} {s t : finset α} :
  disjoint (insert a s) t ↔ a ∉ t ∧ disjoint s t :=
by simp only [disjoint_left, mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

@[simp] theorem disjoint_insert_right {a : α} {s t : finset α} :
  disjoint s (insert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint.comm.trans $ by rw [disjoint_insert_left, disjoint.comm]

@[simp] theorem disjoint_union_left {s t u : finset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp only [disjoint_left, mem_union, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_union_right {s t u : finset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp only [disjoint_right, mem_union, or_imp_distrib, forall_and_distrib]

@[simp] theorem card_disjoint_union {s t : finset α} :
    disjoint s t → card (s ∪ t) = card s + card t :=
finset.induction_on s (λ _, by simp only [empty_union, card_empty, zero_add]) $ λ a s ha ih H,
have h1 : a ∉ s ∪ t, from λ h, or.elim (mem_union.1 h) ha (disjoint_insert_left.1 H).1,
by rw [insert_union, card_insert_of_not_mem h1, card_insert_of_not_mem ha, ih (disjoint_insert_left.1 H).2, add_right_comm]

end disjoint

theorem sort_sorted_lt [decidable_linear_order α] (s : finset α) :
  list.sorted (<) (sort (≤) s) :=
(sort_sorted _ _).imp₂ (@lt_of_le_of_ne _ _) (sort_nodup _ _)

instance [has_repr α] : has_repr (finset α) := ⟨λ s, repr s.1⟩

def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : finset (fin n) :=
⟨s.1.pmap (λ a ha, ⟨a, ha⟩) h, multiset.nodup_pmap (λ _ _ _ _, fin.mk.inj) s.2⟩

@[simp] lemma mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ m ∈ s, m < n) {a : fin n} :
  a ∈ s.attach_fin h ↔ a.1 ∈ s :=
⟨λ h, let ⟨b, hb₁, hb₂⟩ := multiset.mem_pmap.1 h in hb₂ ▸ hb₁,
λ h, multiset.mem_pmap.2 ⟨a.1, h, fin.eta _ _⟩⟩

@[simp] lemma card_attach_fin {n : ℕ} (s : finset ℕ) (h : ∀ m ∈ s, m < n) :
  (s.attach_fin h).card = s.card := multiset.card_pmap _ _ _

section choose
variables (p : α → Prop) [decidable_pred p] (l : finset α)

def choose_x (hp : (∃! a, a ∈ l ∧ p a)) : { a // a ∈ l ∧ p a } :=
multiset.choose_x p l.val hp

def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

theorem lt_wf {α} [decidable_eq α] : well_founded (@has_lt.lt (finset α) _) :=
have H : subrelation (@has_lt.lt (finset α) _)
    (inv_image (<) card),
  from λ x y hxy, card_lt_card hxy,
subrelation.wf H $ inv_image.wf _ $ nat.lt_wf

section decidable_linear_order

variables {α} [decidable_linear_order α]

def min' (S : finset α) (H : S ≠ ∅) : α :=
@option.get _ S.min $
  let ⟨k, hk⟩ := exists_mem_of_ne_empty H in
  let ⟨b, hb⟩ := min_of_mem hk in by simp at hb; simp [hb]

def max' (S : finset α) (H : S ≠ ∅) : α :=
@option.get _ S.max $
  let ⟨k, hk⟩ := exists_mem_of_ne_empty H in
  let ⟨b, hb⟩ := max_of_mem hk in by simp at hb; simp [hb]

variables (S : finset α) (H : S ≠ ∅)

theorem min'_mem : S.min' H ∈ S := mem_of_min $ by simp [min']

theorem min'_le (x) (H2 : x ∈ S) : S.min' H ≤ x := le_min_of_mem H2 $ option.get_mem _

theorem le_min' (x) (H2 : ∀ y ∈ S, x ≤ y) : x ≤ S.min' H := H2 _ $ min'_mem _ _

theorem max'_mem : S.max' H ∈ S := mem_of_max $ by simp [max']

theorem le_max' (x) (H2 : x ∈ S) : x ≤ S.max' H := le_max_of_mem H2 $ option.get_mem _

theorem max'_le (x) (H2 : ∀ y ∈ S, y ≤ x) : S.max' H ≤ x := H2 _ $ max'_mem _ _

theorem min'_lt_max' {i j} (H1 : i ∈ S) (H2 : j ∈ S) (H3 : i ≠ j) : S.min' H < S.max' H :=
begin
  rcases lt_trichotomy i j with H4 | H4 | H4,
  { have H5 := min'_le S H i H1,
    have H6 := le_max' S H j H2,
    apply lt_of_le_of_lt H5,
    apply lt_of_lt_of_le H4 H6 },
  { cc },
  { have H5 := min'_le S H j H2,
    have H6 := le_max' S H i H1,
    apply lt_of_le_of_lt H5,
    apply lt_of_lt_of_le H4 H6 }
end

end decidable_linear_order

end finset

namespace list
variable [decidable_eq α]

theorem to_finset_card_of_nodup {l : list α} (h : l.nodup) : l.to_finset.card = l.length :=
congr_arg card $ (@multiset.erase_dup_eq_self α _ l).2 h

end list
