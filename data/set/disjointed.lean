/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Disjointed sets
-/
import data.set.lattice data.nat.basic
open set classical lattice
local attribute [instance] prop_decidable

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}
  {s t u : set α}

def pairwise {α : Type*} (p : α → α → Prop) := ∀i j, i ≠ j → p i j

namespace set

def disjointed (f : ℕ → set α) (n : ℕ) : set α := f n ∩ (⋂i<n, - f i)

lemma disjoint_disjointed {f : ℕ → set α} : pairwise (disjoint on disjointed f) :=
assume i j h,
have ∀i j, i < j → disjointed f i ∩ disjointed f j = ∅,
  from assume i j hij, eq_empty_iff_forall_not_mem.2 $ assume x h,
  have x ∈ f i, from h.left.left,
  have x ∈ (⋂i<j, - f i), from h.right.right,
  have x ∉ f i, begin simp at this; exact this _ hij end,
  absurd ‹x ∈ f i› this,
show disjointed f i ∩ disjointed f j = ∅,
  from (ne_iff_lt_or_gt.mp h).elim (this i j) begin rw [inter_comm], exact this j i end

lemma disjointed_Union {f : ℕ → set α} : (⋃n, disjointed f n) = (⋃n, f n) :=
subset.antisymm (Union_subset_Union $ assume i, inter_subset_left _ _) $
  assume x h,
  have ∃n, x ∈ f n, from (mem_Union_eq _ _).mp h,
  have hn : ∀ (i : ℕ), i < nat.find this → x ∉ f i,
    from assume i, nat.find_min this,
  (mem_Union_eq _ _).mpr ⟨nat.find this, nat.find_spec this, by simp; assumption⟩

lemma disjointed_induct {f : ℕ → set α} {n : ℕ} {p : set α → Prop}
  (h₁ : p (f n)) (h₂ : ∀t i, p t → p (t - f i)) :
  p (disjointed f n) :=
have ∀n t, p t → p (t ∩ (⋂i<n, - f i)),
begin
  intro n, induction n,
  case nat.zero {
    have h : (⋂ (i : ℕ) (H : i < 0), -f i) = univ,
      { apply eq_univ_of_forall,
        simp [mem_Inter, nat.not_lt_zero] },
    simp [h, inter_univ] },
  case nat.succ n ih {
    intro t,
    have h : (⨅i (H : i < n.succ), -f i) = (⨅i (H : i < n), -f i) ⊓ - f n,
      by simp [nat.lt_succ_iff_lt_or_eq, infi_or, infi_inf_eq, inf_comm],
    change (⋂ (i : ℕ) (H : i < n.succ), -f i) = (⋂ (i : ℕ) (H : i < n), -f i) ∩ - f n at h,
    rw [h, ←inter_assoc],
    exact assume ht, h₂ _ _ (ih _ ht) }
end,
this _ _ h₁

lemma disjointed_of_mono {f : ℕ → set α} {n : ℕ} (hf : monotone f) :
  disjointed f (n + 1) = f (n + 1) \ f n :=
have (⋂i (h : i < n + 1), -f i) = - f n,
  from le_antisymm
    (infi_le_of_le n $ infi_le_of_le (nat.lt_succ_self _) $ subset.refl _)
    (le_infi $ assume i, le_infi $ assume hi, neg_le_neg $ hf $ nat.le_of_succ_le_succ hi),
by simp [disjointed, this, sdiff_eq]

end set
