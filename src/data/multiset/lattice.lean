/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.multiset.finset_ops
import data.multiset.fold

/-!
# Lattice operations on multisets
-/

namespace multiset
variables {α : Type*}

/-! ### sup -/
section sup
-- can be defined with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variables [semilattice_sup α] [order_bot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup (s : multiset α) : α := s.fold (⊔) ⊥

@[simp] lemma sup_zero : (0 : multiset α).sup = ⊥ :=
fold_zero _ _

@[simp] lemma sup_cons (a : α) (s : multiset α) :
  (a ::ₘ s).sup = a ⊔ s.sup :=
fold_cons_left _ _ _ _

@[simp] lemma sup_singleton {a : α} : ({a} : multiset α).sup = a :=
sup_bot_eq

@[simp] lemma sup_add (s₁ s₂ : multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

lemma sup_le {s : multiset α} {a : α} : s.sup ≤ a ↔ (∀b ∈ s, b ≤ a) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib] {contextual := tt})

lemma le_sup {s : multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
sup_le.1 le_rfl _ h

lemma sup_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
sup_le.2 $ assume b hb, le_sup (h hb)

variables [decidable_eq α]

@[simp] lemma sup_dedup (s : multiset α) : (dedup s).sup = s.sup :=
fold_dedup_idem _ _ _

@[simp] lemma sup_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup :=
by rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp

@[simp] lemma sup_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup :=
by rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp

@[simp] lemma sup_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).sup = a ⊔ s.sup :=
by rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_cons]; simp

lemma nodup_sup_iff {α : Type*} [decidable_eq α] {m : multiset (multiset α) } :
  m.sup.nodup ↔ ∀ (a : multiset α), a ∈ m → a.nodup :=
begin
  apply m.induction_on,
  { simp },
  { intros a s h,
    simp [h] }
end

end sup

/-! ### inf -/
section inf
-- can be defined with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variables [semilattice_inf α] [order_top α]

/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf (s : multiset α) : α := s.fold (⊓) ⊤

@[simp] lemma inf_zero : (0 : multiset α).inf = ⊤ :=
fold_zero _ _

@[simp] lemma inf_cons (a : α) (s : multiset α) :
  (a ::ₘ s).inf = a ⊓ s.inf :=
fold_cons_left _ _ _ _

@[simp] lemma inf_singleton {a : α} : ({a} : multiset α).inf = a :=
inf_top_eq

@[simp] lemma inf_add (s₁ s₂ : multiset α) : (s₁ + s₂).inf = s₁.inf ⊓ s₂.inf :=
eq.trans (by simp [inf]) (fold_add _ _ _ _ _)

lemma le_inf {s : multiset α} {a : α} : a ≤ s.inf ↔ (∀b ∈ s, a ≤ b) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib] {contextual := tt})

lemma inf_le {s : multiset α} {a : α} (h : a ∈ s) : s.inf ≤ a :=
le_inf.1 le_rfl _ h

lemma inf_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₂.inf ≤ s₁.inf :=
le_inf.2 $ assume b hb, inf_le (h hb)

variables [decidable_eq α]

@[simp] lemma inf_dedup (s : multiset α) : (dedup s).inf = s.inf :=
fold_dedup_idem _ _ _

@[simp] lemma inf_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).inf = s₁.inf ⊓ s₂.inf :=
by rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add]; simp

@[simp] lemma inf_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).inf = s₁.inf ⊓ s₂.inf :=
by rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add]; simp

@[simp] lemma inf_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).inf = a ⊓ s.inf :=
by rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_cons]; simp

end inf

end multiset
