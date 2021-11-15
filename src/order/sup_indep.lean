/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import data.set.pairwise

/-!
# Finite supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

In distributive lattices, this is equivalent to being pairwise disjoint.

## TODO

As we don't have `lattice_bot`, we're forced to pick between `bounded_lattice` (which assumes `top`
unnecessarily) and `distrib_lattice_bot` (which assumes distributivity unnecessarily). For now we
pick `distrib_lattice_bot` for it to apply to `finset α`, although this use is redundant with
`set.pairwise_disjoint`.

`complete_lattice.independent` and `complete_lattice.set_independent` should live in this file.

There are ways to state `finset.sup_indep` without resorting to `decidable_eq ι`. Should we switch
to such a definition?
-/

variables {α β ι ι' : Type*}

namespace finset
variables [distrib_lattice_bot α]

/-- Supremum independence of finite sets. -/
def sup_indep (s : finset ι) (f : ι → α) : Prop :=
∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → disjoint (f i) (t.sup f)

variables {s t : finset ι} {f : ι → α}

lemma sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) : s.sup_indep f :=
λ u hu i hi, ht (hu.trans h) (h hi)

lemma sup_indep_empty (f : ι → α) : (∅ : finset ι).sup_indep f := λ _ _ a ha, ha.elim

lemma sup_indep_singleton (i : ι) (f : ι → α) : ({i} : finset ι).sup_indep f :=
λ s hs j hji hj, begin
  suffices h : s = ∅,
  { rw [h, sup_empty],
    exact disjoint_bot_right },
  refine eq_empty_iff_forall_not_mem.2 (λ k hk, ne_of_mem_of_not_mem hk hj _),
  rw [mem_singleton.1 hji, mem_singleton.1 (hs hk)],
end

-- Once `finset.sup_indep` will have been generalized to non distributive lattices, can we state
-- this lemma for nondistributive atomic lattices? This setting makes the `←` implication much
-- harder.
lemma sup_indep_iff_pairwise_disjoint : s.sup_indep f ↔ (s : set ι).pairwise_disjoint f :=
⟨λ hs a ha b hb hab,
sup_singleton.subst $ hs (singleton_subset_iff.2 hb) ha $ not_mem_singleton.2 hab,
  λ hs t ht i hi hit,
    disjoint_sup_right.2 $ λ j hj, hs _ hi _ (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias sup_indep_iff_pairwise_disjoint ↔ finset.sup_indep.pairwise_disjoint
  set.pairwise_disjoint.sup_indep

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

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sup [decidable_eq ι] {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
begin
  rintro t ht i hi hit,
  rw disjoint_sup_right,
  refine λ j hj, _,
  have hij : i ≠ j := (ne_of_mem_of_not_mem hj hit).symm,
  replace hj := ht hj,
  rw mem_sup at hi hj,
  obtain ⟨i', hi', hi⟩ := hi,
  obtain ⟨j', hj', hj⟩ := hj,
  obtain hij' | hij' := eq_or_ne i' j',
  { exact (hg j' hj').pairwise_disjoint _ (hij'.subst hi) _ hj hij },
  { exact (hs.pairwise_disjoint _ hi' _ hj' hij').mono (le_sup hi) (le_sup hj) }
end

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.bUnion [decidable_eq ι] {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.bUnion g).sup_indep f :=
by { rw ←sup_eq_bUnion, exact hs.sup hg }

/-- The RHS looks like the definition of `complete_lattice.independent`. -/
lemma sup_indep_iff_disjoint_erase [decidable_eq ι] :
  s.sup_indep f ↔ ∀ i ∈ s, disjoint (f i) ((s.erase i).sup f) :=
⟨λ hs i hi, hs (erase_subset _ _) hi (not_mem_erase _ _), λ hs t ht i hi hit,
  (hs i hi).mono_right (sup_mono $ λ j hj, mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

end finset

-- TODO: Relax `complete_distrib_lattice` to `complete_lattice` once `finset.sup_indep` is general
-- enough
lemma complete_lattice.independent_iff_sup_indep [complete_distrib_lattice α] {s : finset ι}
  {f : ι → α} :
  complete_lattice.independent (f ∘ (coe : s → ι)) ↔ s.sup_indep f :=
begin
  classical,
  rw finset.sup_indep_iff_disjoint_erase,
  refine subtype.forall.trans (forall_congr $ λ a, forall_congr $ λ b, _),
  rw finset.sup_eq_supr,
  congr' 2,
  refine supr_subtype.trans _,
  congr' 1 with x,
  simp [supr_and, @supr_comm _ (x ∈ s)],
end

alias complete_lattice.independent_iff_sup_indep ↔ complete_lattice.independent.sup_indep
  finset.sup_indep.independent
