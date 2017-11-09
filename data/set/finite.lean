/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Finite sets -- assuming a classical logic.
-/
import data.set.lattice data.set.prod data.nat.basic logic.function
noncomputable theory
open classical set lattice function
local attribute [instance] decidable_inhabited prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {ι : Sort w}


namespace set

/-
local attribute [instance] classical.decidable_inhabited classical.prop_decidable
-/

inductive finite : set α → Prop
| empty : finite ∅
| insert : ∀a s, a ∉ s → finite s → finite (insert a s)

def infinite (s : set α) : Prop := ¬ finite s

attribute [simp] finite.empty

@[simp] theorem finite_insert {a : α} {s : set α} (h : finite s) : finite (insert a s) :=
classical.by_cases
  (assume : a ∈ s, by simp [*])
  (assume : a ∉ s, finite.insert a s this h)

@[simp] theorem finite_singleton {a : α} : finite ({a} : set α) :=
finite_insert finite.empty

theorem finite_union {s t : set α} (hs : finite s) (ht : finite t) : finite (s ∪ t) :=
finite.drec_on ht (by simp [hs]) $ assume a t _ _, by simp; exact finite_insert

theorem finite_subset {s : set α} (hs : finite s) : ∀{t}, t ⊆ s → finite t :=
begin
  induction hs with a t' ha ht' ih,
  { intros t ht, simp [(subset_empty_iff t).mp ht, finite.empty] },
  { intros t ht,
    have tm : finite (t \ {a}) :=
      (ih $ show t \ {a} ⊆ t',
        from assume x ⟨hxt, hna⟩, or.resolve_left (ht hxt) (by simp at hna; assumption)),
    cases (classical.em $ a ∈ t) with ha hna,
    { exact have finite (insert a (t \ {a})), from finite_insert tm,
      show finite t,
        by simp [ha] at this; assumption },
    { simp [sdiff_singleton_eq_same, hna] at tm, exact tm } }
end

theorem finite_image {s : set α} {f : α → β} (h : finite s) : finite (f '' s) :=
begin
  induction h with a s' hns' hs' hi,
  simp [image_empty, finite.empty],
  simp [image_insert_eq, finite_insert, hi]
end

theorem finite_of_finite_image {s : set α} {f : α → β}
  (hf : injective f) (hs : finite (f '' s)) : finite s :=
if hα : nonempty α
then
  let ⟨a⟩ := hα in
  have h : inhabited α := ⟨a⟩,
  have finite (@inv_fun _ _ h f '' (f '' s)), from finite_image hs,
  by rwa [←image_comp, inv_fun_comp hf, image_id] at this
else
  have s = ∅, from eq_empty_of_forall_not_mem $ assume a, (hα ⟨a⟩).elim,
  by simp [this]

theorem finite_sUnion {s : set (set α)} (h : finite s) : (∀t∈s, finite t) → finite (⋃₀ s) :=
begin
  induction h with a s' hns' hs' hi,
  { simp [finite.empty] },
  { intro h,
    simp,
    apply finite_union,
    { apply h, simp },
    { exact (hi $ assume t ht, h _ $ mem_insert_of_mem _ ht) } }
end

lemma finite_le_nat : ∀{n:ℕ}, finite {i | i ≤ n}
| 0 := by simp [nat.le_zero_iff, set_compr_eq_eq_singleton]
| (n + 1) :=
  have insert (n + 1) {i | i ≤ n} = {i | i ≤ n + 1},
    from set.ext $ by simp [nat.le_add_one_iff],
  this ▸ finite_insert finite_le_nat

lemma finite_prod {s : set α} {t : set β} (hs : finite s) (ht : finite t) :
  finite (set.prod s t) :=
begin
  induction hs,
  case finite.empty { simp },
  case finite.insert a s has hs ih {
    rw [set.insert_prod],
    exact finite_union (finite_image ht) ih
  }
end

end set
