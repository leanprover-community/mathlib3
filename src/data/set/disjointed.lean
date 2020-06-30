/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Disjointed sets
-/
import data.set.lattice
import tactic.wlog
open set classical
open_locale classical

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}
  {s t u : set α}

/-- A relation `p` holds pairwise if `p i j` for all `i ≠ j`. -/
def pairwise {α : Type*} (p : α → α → Prop) := ∀i j, i ≠ j → p i j

theorem set.pairwise_on_univ {r : α → α → Prop} :
  (univ : set α).pairwise_on r ↔ pairwise r :=
by simp only [pairwise_on, pairwise, mem_univ, forall_const]

theorem set.pairwise_on.on_injective {s : set α} {r : α → α → Prop} (hs : pairwise_on s r)
  {f : β → α} (hf : function.injective f) (hfs : ∀ x, f x ∈ s) :
  pairwise (r on f) :=
λ i j hij, hs _ (hfs i) _ (hfs j) (hf.ne hij)

theorem pairwise_on_bool {r} (hr : symmetric r) {a b : α} :
  pairwise (r on (λ c, cond c a b)) ↔ r a b :=
by simp [pairwise, bool.forall_bool, function.on_fun];
   exact and_iff_right_of_imp (@hr _ _)

theorem pairwise_disjoint_on_bool [semilattice_inf_bot α] {a b : α} :
  pairwise (disjoint on (λ c, cond c a b)) ↔ disjoint a b :=
pairwise_on_bool $ λ _ _, disjoint.symm

theorem pairwise.pairwise_on {p : α → α → Prop} (h : pairwise p) (s : set α) : s.pairwise_on p :=
λ x hx y hy, h x y

theorem pairwise_disjoint_fiber (f : α → β) : pairwise (disjoint on (λ y : β, f ⁻¹' {y})) :=
set.pairwise_on_univ.1 $ pairwise_on_disjoint_fiber f univ

namespace set

/-- If `f : ℕ → set α` is a sequence of sets, then `disjointed f` is
  the sequence formed with each set subtracted from the later ones
  in the sequence, to form a disjoint sequence. -/
def disjointed (f : ℕ → set α) (n : ℕ) : set α := f n ∩ (⋂i<n, (f i)ᶜ)

lemma disjoint_disjointed {f : ℕ → set α} : pairwise (disjoint on disjointed f) :=
λ i j h, begin
  wlog h' : i ≤ j; [skip, {revert a, exact (this h.symm).symm}],
  rintro a ⟨⟨h₁, _⟩, h₂, h₃⟩, simp at h₃,
  exact h₃ _ (lt_of_le_of_ne h' h) h₁
end

lemma disjoint_disjointed' {f : ℕ → set α} :
  ∀ i j, i ≠ j → (disjointed f i) ∩ (disjointed f j) = ∅ :=
λ i j hij, disjoint_iff.1 $ disjoint_disjointed i j hij

lemma disjointed_subset {f : ℕ → set α} {n : ℕ} : disjointed f n ⊆ f n := inter_subset_left _ _

lemma Union_lt_succ {f : ℕ → set α} {n} : (⋃i < nat.succ n, f i) = f n ∪ (⋃i < n, f i) :=
ext $ λ a, by simp [nat.lt_succ_iff_lt_or_eq, or_and_distrib_right, exists_or_distrib, or_comm]

lemma Inter_lt_succ {f : ℕ → set α} {n} : (⋂i < nat.succ n, f i) = f n ∩ (⋂i < n, f i) :=
ext $ λ a, by simp [nat.lt_succ_iff_lt_or_eq, or_imp_distrib, forall_and_distrib, and_comm]

lemma Union_disjointed {f : ℕ → set α} : (⋃n, disjointed f n) = (⋃n, f n) :=
subset.antisymm (Union_subset_Union $ assume i, inter_subset_left _ _) $
  assume x h,
  have ∃n, x ∈ f n, from mem_Union.mp h,
  have hn : ∀ (i : ℕ), i < nat.find this → x ∉ f i,
    from assume i, nat.find_min this,
  mem_Union.mpr ⟨nat.find this, nat.find_spec this, by simp; assumption⟩

lemma disjointed_induct {f : ℕ → set α} {n : ℕ} {p : set α → Prop}
  (h₁ : p (f n)) (h₂ : ∀t i, p t → p (t \ f i)) :
  p (disjointed f n) :=
begin
  rw disjointed,
  generalize_hyp : f n = t at h₁ ⊢,
  induction n,
  case nat.zero { simp [nat.not_lt_zero, h₁] },
  case nat.succ : n ih {
    rw [Inter_lt_succ, inter_comm ((f n)ᶜ), ← inter_assoc],
    exact h₂ _ n ih }
end

lemma disjointed_of_mono {f : ℕ → set α} {n : ℕ} (hf : monotone f) :
  disjointed f (n + 1) = f (n + 1) \ f n :=
have (⋂i (h : i < n + 1), (f i)ᶜ) = (f n)ᶜ,
  from le_antisymm
    (infi_le_of_le n $ infi_le_of_le (nat.lt_succ_self _) $ subset.refl _)
    (le_infi $ assume i, le_infi $ assume hi, compl_le_compl $ hf $ nat.le_of_succ_le_succ hi),
by simp [disjointed, this, diff_eq]

lemma Union_disjointed_of_mono {f : ℕ → set α} (hf : monotone f) :
  ∀ n : ℕ, (⋃i<n.succ, disjointed f i) = f n
| 0 := by rw [Union_lt_succ]; simp [disjointed, nat.not_lt_zero]
| (n+1) := by rw [Union_lt_succ,
  disjointed_of_mono hf, Union_disjointed_of_mono n,
  diff_union_self, union_eq_self_of_subset_right (hf (nat.le_succ _))]

end set
