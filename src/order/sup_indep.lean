/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pairwise
import data.set.finite

/-!
# Finite supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

In distributive lattices, this is equivalent to being pairwise disjoint.

## Implementation notes

We avoid the "obvious" definition `∀ i ∈ s, disjoint (f i) ((s.erase i).sup f)` because `erase`
would require decidable equality on `ι`.

## TODO

`complete_lattice.independent` and `complete_lattice.set_independent` should live in this file.
-/

variables {α β ι ι' : Type*}

namespace finset
section lattice
variables [lattice α] [order_bot α]

/-- Supremum independence of finite sets. We avoid the "obvious" definition using `s.erase i`
because `erase` would require decidable equality on `ι`. -/
def sup_indep (s : finset ι) (f : ι → α) : Prop :=
∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → disjoint (f i) (t.sup f)

variables {s t : finset ι} {f : ι → α} {i : ι}

instance [decidable_eq ι] [decidable_eq α] : decidable (sup_indep s f) :=
begin
  apply @finset.decidable_forall_of_decidable_subsets _ _ _ _,
  intros t ht,
  apply @finset.decidable_dforall_finset _ _ _ _,
  exact λ i hi, @implies.decidable _ _ _ (decidable_of_iff' (_ = ⊥) disjoint_iff),
end

lemma sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) : s.sup_indep f :=
λ u hu i hi, ht (hu.trans h) (h hi)

lemma sup_indep_empty (f : ι → α) : (∅ : finset ι).sup_indep f := λ _ _ a ha, ha.elim

lemma sup_indep_singleton (i : ι) (f : ι → α) : ({i} : finset ι).sup_indep f :=
λ s hs j hji hj, begin
  rw [eq_empty_of_ssubset_singleton ⟨hs, λ h, hj (h hji)⟩, sup_empty],
  exact disjoint_bot_right,
end

lemma sup_indep.pairwise_disjoint (hs : s.sup_indep f) : (s : set ι).pairwise_disjoint f :=
λ a ha b hb hab, sup_singleton.subst $ hs (singleton_subset_iff.2 hb) ha $ not_mem_singleton.2 hab

/-- The RHS looks like the definition of `complete_lattice.independent`. -/
lemma sup_indep_iff_disjoint_erase [decidable_eq ι] :
  s.sup_indep f ↔ ∀ i ∈ s, disjoint (f i) ((s.erase i).sup f) :=
⟨λ hs i hi, hs (erase_subset _ _) hi (not_mem_erase _ _), λ hs t ht i hi hit,
  (hs i hi).mono_right (sup_mono $ λ j hj, mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

@[simp] lemma sup_indep_pair [decidable_eq ι] {i j : ι} (hij : i ≠ j) :
  ({i, j} : finset ι).sup_indep f ↔ disjoint (f i) (f j) :=
⟨λ h, h.pairwise_disjoint (by simp) (by simp) hij, λ h, begin
  rw sup_indep_iff_disjoint_erase,
  intros k hk,
  rw [finset.mem_insert, finset.mem_singleton] at hk,
  obtain rfl | rfl := hk,
  { convert h using 1,
    rw [finset.erase_insert, finset.sup_singleton],
    simpa using hij },
  { convert h.symm using 1,
    have : ({i, k} : finset ι).erase k = {i},
    { ext,
      rw [mem_erase, mem_insert, mem_singleton, mem_singleton, and_or_distrib_left,
        ne.def, not_and_self, or_false, and_iff_right_of_imp],
      rintro rfl,
      exact hij },
    rw [this, finset.sup_singleton] }
end⟩

lemma sup_indep_univ_bool (f : bool → α) :
  (finset.univ : finset bool).sup_indep f ↔ disjoint (f ff) (f tt) :=
begin
  have : tt ≠ ff := by simp only [ne.def, not_false_iff],
  exact (sup_indep_pair this).trans disjoint.comm,
end

@[simp] lemma sup_indep_univ_fin_two (f : fin 2 → α) :
  (finset.univ : finset (fin 2)).sup_indep f ↔ disjoint (f 0) (f 1) :=
begin
  have : (0 : fin 2) ≠ 1 := by simp,
  exact sup_indep_pair this,
end

lemma sup_indep.attach (hs : s.sup_indep f) : s.attach.sup_indep (f ∘ subtype.val) :=
begin
  intros t ht i _ hi,
  classical,
  rw ←finset.sup_image,
  refine hs (image_subset_iff.2 $ λ (j : {x // x ∈ s}) _, j.2) i.2 (λ hi', hi _),
  rw mem_image at hi',
  obtain ⟨j, hj, hji⟩ := hi',
  rwa subtype.ext hji at hj,
end

end lattice

section distrib_lattice
variables [distrib_lattice α] [order_bot α] {s : finset ι} {f : ι → α}

lemma sup_indep_iff_pairwise_disjoint : s.sup_indep f ↔ (s : set ι).pairwise_disjoint f :=
⟨sup_indep.pairwise_disjoint, λ hs t ht i hi hit,
  disjoint_sup_right.2 $ λ j hj, hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias sup_indep_iff_pairwise_disjoint ↔ finset.sup_indep.pairwise_disjoint
  set.pairwise_disjoint.sup_indep

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sup [decidable_eq ι] {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
begin
  simp_rw sup_indep_iff_pairwise_disjoint at ⊢ hs hg,
  rw [sup_eq_bUnion, coe_bUnion],
  exact hs.bUnion_finset hg,
end

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.bUnion [decidable_eq ι] {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.bUnion g).sup_indep f :=
by { rw ←sup_eq_bUnion, exact hs.sup hg }

end distrib_lattice
end finset

lemma complete_lattice.independent_iff_sup_indep [complete_lattice α] {s : finset ι} {f : ι → α} :
  complete_lattice.independent (f ∘ (coe : s → ι)) ↔ s.sup_indep f :=
begin
  classical,
  rw finset.sup_indep_iff_disjoint_erase,
  refine subtype.forall.trans (forall₂_congr $ λ a b, _),
  rw finset.sup_eq_supr,
  congr' 2,
  refine supr_subtype.trans _,
  congr' 1 with x,
  simp [supr_and, @supr_comm _ (x ∈ s)],
end

alias complete_lattice.independent_iff_sup_indep ↔ complete_lattice.independent.sup_indep
  finset.sup_indep.independent

/-- A variant of `complete_lattice.independent_iff_sup_indep` for `fintype`s. -/
lemma complete_lattice.independent_iff_sup_indep_univ [complete_lattice α] [fintype ι] {f : ι → α} :
  complete_lattice.independent f ↔ finset.univ.sup_indep f :=
begin
  classical,
  simp [finset.sup_indep_iff_disjoint_erase, complete_lattice.independent, finset.sup_eq_supr],
end

alias complete_lattice.independent_iff_sup_indep_univ ↔ complete_lattice.independent.sup_indep_univ
  finset.sup_indep.independent_of_univ
