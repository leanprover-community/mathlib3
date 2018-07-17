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

/-- A relation `p` holds pairwise if `p i j` for all `i ≠ j`. -/
def pairwise {α : Type*} (p : α → α → Prop) := ∀i j, i ≠ j → p i j

namespace set

/-- If `f : ℕ → set α` is a sequence of sets, then `disjointed f` is
  the sequence formed with each set subtracted from the later ones
  in the sequence, to form a disjoint sequence. -/
def disjointed (f : ℕ → set α) (n : ℕ) : set α := f n ∩ (⋂i<n, - f i)

lemma disjoint_disjointed {f : ℕ → set α} : pairwise (disjoint on disjointed f) :=
λ i j h, begin
  wlog h' : i ≤ j; [skip, {revert a, exact (this h.symm).symm}],
  rintro a ⟨⟨h₁, _⟩, h₂, h₃⟩, simp at h₃,
  exact h₃ _ (lt_of_le_of_ne h' h) h₁
end

lemma disjointed_Union {f : ℕ → set α} : (⋃n, disjointed f n) = (⋃n, f n) :=
subset.antisymm (Union_subset_Union $ assume i, inter_subset_left _ _) $
  assume x h,
  have ∃n, x ∈ f n, from mem_Union.mp h,
  have hn : ∀ (i : ℕ), i < nat.find this → x ∉ f i,
    from assume i, nat.find_min this,
  mem_Union.mpr ⟨nat.find this, nat.find_spec this, by simp; assumption⟩

lemma disjointed_induct {f : ℕ → set α} {n : ℕ} {p : set α → Prop}
  (h₁ : p (f n)) (h₂ : ∀t i, p t → p (t \ f i)) :
  p (disjointed f n) :=
have ∀n t, p t → p (t ∩ (⋂i<n, - f i)),
begin
  intro n, induction n,
  case nat.zero {
    have h : (⋂ (i : ℕ) (H : i < 0), -f i) = univ,
      { apply eq_univ_of_forall,
        simp [mem_Inter, nat.not_lt_zero] },
    simp [h, inter_univ] },
  case nat.succ : n ih {
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
by simp [disjointed, this, diff_eq]

end set
