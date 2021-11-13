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
-/

variables {α β ι ι' : Type*}

namespace finset
variables [distrib_lattice_bot α] [decidable_eq ι] [decidable_eq ι']

/-- Supremum independence of finite sets. -/
def sup_indep (s : finset ι) (f : ι → α) : Prop := ∀ ⦃a⦄, a ∈ s → disjoint (f a) ((s.erase a).sup f)

variables {s t : finset ι} {f : ι → α}

lemma sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) : s.sup_indep f :=
λ a ha, (ht $ h ha).mono_right $ sup_mono $ erase_subset_erase _ h

lemma sup_indep_empty (f : ι → α) : (∅ : finset ι).sup_indep f := λ a ha, ha.elim

lemma sup_indep_singleton (i : ι) (f : ι → α) : ({i} : finset ι).sup_indep f :=
λ j hj, by { rw [mem_singleton.1 hj, erase_singleton, sup_empty], exact disjoint_bot_right }

lemma sup_indep.attach (hs : s.sup_indep f) : s.attach.sup_indep (f ∘ subtype.val) :=
λ i _,
  by { rw [←finset.sup_image, image_erase subtype.val_injective, attach_image_val], exact hs i.2 }

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sup {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
begin
  rintro i hi,
  rw disjoint_sup_right,
  refine λ j hj, _,
  rw mem_sup at hi,
  obtain ⟨i', hi', hi⟩ := hi,
  rw [mem_erase, mem_sup] at hj,
  obtain ⟨hij, j', hj', hj⟩ := hj,
  obtain hij' | hij' := eq_or_ne j' i',
  { exact disjoint_sup_right.1 (hg i' hi' hi) _ (mem_erase.2 ⟨hij, hij'.subst hj⟩) },
  { exact (hs hi').mono (le_sup hi) ((le_sup hj).trans $ le_sup $ mem_erase.2 ⟨hij', hj'⟩) }
end

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.bUnion {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.bUnion g).sup_indep f :=
by { rw ←sup_eq_bUnion, exact hs.sup hg }

lemma sup_indep.pairwise_disjoint  (hs : s.sup_indep f) : (s : set ι).pairwise_disjoint f :=
λ a ha b hb hab, (hs ha).mono_right $ le_sup $ mem_erase.2 ⟨hab.symm, hb⟩

-- Once `finset.sup_indep` will have been generalized to non distributive lattices, can we state
-- this lemma for nondistributive atomic lattices? This setting makes the `←` implication much
-- harder.
lemma sup_indep_iff_pairwise_disjoint : s.sup_indep f ↔ (s : set ι).pairwise_disjoint f :=
begin
  refine ⟨λ hs a ha b hb hab, (hs ha).mono_right $ le_sup $ mem_erase.2 ⟨hab.symm, hb⟩,
    λ hs a ha, _⟩,
  rw disjoint_sup_right,
  exact λ b hb, hs a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm,
end

alias sup_indep_iff_pairwise_disjoint ↔ finset.sup_indep.pairwise_disjoint
  set.pairwise_disjoint.sup_indep

end finset

-- TODO: Relax `complete_distrib_lattice` to `complete_lattice` once `finset.sup_indep` is general
-- enough
lemma complete_lattice.independent_iff_sup_indep [complete_distrib_lattice α] [decidable_eq ι]
  {s : finset ι} {f : ι → α} :
  complete_lattice.independent (f ∘ (coe : s → ι)) ↔ s.sup_indep f :=
begin
  refine subtype.forall.trans (forall_congr $ λ a, forall_congr $ λ b, _),
  rw finset.sup_eq_supr,
  congr' 2,
  refine supr_subtype.trans _,
  congr' 1 with x,
  simp [supr_and, @supr_comm _ (x ∈ s)],
end

alias complete_lattice.independent_iff_sup_indep ↔ complete_lattice.independent.sup_indep
  finset.sup_indep.independent
