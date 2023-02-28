/-
Copyright (c) 2021 Aaron Anderson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Kevin Buzzard, Yaël Dillies, Eric Wieser
-/
import data.finset.pairwise
import data.finset.powerset
import data.fintype.basic

/-!
# Supremum independence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

## Main definitions

* `finset.sup_indep s f`: a family of elements `f` are supremum independent on the finite set `s`.
* `complete_lattice.set_independent s`: a set of elements are supremum independent.
* `complete_lattice.independent f`: a family of elements are supremum independent.

## Main statements

* In a distributive lattice, supremum independence is equivalent to pairwise disjointness:
  * `finset.sup_indep_iff_pairwise_disjoint`
  * `complete_lattice.set_independent_iff_pairwise_disjoint`
  * `complete_lattice.independent_iff_pairwise_disjoint`
* Otherwise, supremum independence is stronger than pairwise disjointness:
  * `finset.sup_indep.pairwise_disjoint`
  * `complete_lattice.set_independent.pairwise_disjoint`
  * `complete_lattice.independent.pairwise_disjoint`

## Implementation notes

For the finite version, we avoid the "obvious" definition
`∀ i ∈ s, disjoint (f i) ((s.erase i).sup f)` because `erase` would require decidable equality on
`ι`.
-/

variables {α β ι ι' : Type*}

/-! ### On lattices with a bottom element, via `finset.sup` -/

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
  finset.disjoint_sup_right.2 $ λ j hj, hs hi (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias sup_indep_iff_pairwise_disjoint ↔ sup_indep.pairwise_disjoint
  _root_.set.pairwise_disjoint.sup_indep

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


/-! ### On complete lattices via `has_Sup.Sup` -/

namespace complete_lattice
variables [complete_lattice α]

open set function

/-- An independent set of elements in a complete lattice is one in which every element is disjoint
  from the `Sup` of the rest. -/
def set_independent (s : set α) : Prop := ∀ ⦃a⦄, a ∈ s → disjoint a (Sup (s \ {a}))

variables {s : set α} (hs : set_independent s)

@[simp]
lemma set_independent_empty : set_independent (∅ : set α) :=
λ x hx, (set.not_mem_empty x hx).elim

theorem set_independent.mono {t : set α} (hst : t ⊆ s) :
  set_independent t :=
λ a ha, (hs (hst ha)).mono_right (Sup_le_Sup (diff_subset_diff_left hst))

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
lemma set_independent.pairwise_disjoint : s.pairwise_disjoint id :=
λ x hx y hy h, disjoint_Sup_right (hs hx) ((mem_diff y).mpr ⟨hy, h.symm⟩)

lemma set_independent_pair {a b : α} (hab : a ≠ b) :
  set_independent ({a, b} : set α) ↔ disjoint a b :=
begin
  split,
  { intro h,
    exact h.pairwise_disjoint (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hab, },
  { rintros h c ((rfl : c = a) | (rfl : c = b)),
    { convert h using 1,
      simp [hab, Sup_singleton] },
    { convert h.symm using 1,
      simp [hab, Sup_singleton] }, },
end

include hs

/-- If the elements of a set are independent, then any element is disjoint from the `Sup` of some
subset of the rest. -/
lemma set_independent.disjoint_Sup {x : α} {y : set α} (hx : x ∈ s) (hy : y ⊆ s) (hxy : x ∉ y) :
  disjoint x (Sup y) :=
begin
  have := (hs.mono $ insert_subset.mpr ⟨hx, hy⟩) (mem_insert x _),
  rw [insert_diff_of_mem _ (mem_singleton _), diff_singleton_eq_self hxy] at this,
  exact this,
end

omit hs

/-- An independent indexed family of elements in a complete lattice is one in which every element
  is disjoint from the `supr` of the rest.

  Example: an indexed family of non-zero elements in a
  vector space is linearly independent iff the indexed family of subspaces they generate is
  independent in this sense.

  Example: an indexed family of submodules of a module is independent in this sense if
  and only the natural map from the direct sum of the submodules to the module is injective. -/
def independent {ι : Sort*} {α : Type*} [complete_lattice α] (t : ι → α) : Prop :=
∀ i : ι, disjoint (t i) (⨆ (j ≠ i), t j)

lemma set_independent_iff {α : Type*} [complete_lattice α] (s : set α) :
  set_independent s ↔ independent (coe : s → α) :=
begin
  simp_rw [independent, set_independent, set_coe.forall, Sup_eq_supr],
  refine forall₂_congr (λ a ha, _),
  congr' 2,
  convert supr_subtype.symm,
  simp [supr_and],
end

variables {t : ι → α} (ht : independent t)

theorem independent_def : independent t ↔ ∀ i : ι, disjoint (t i) (⨆ (j ≠ i), t j) :=
iff.rfl

theorem independent_def' :
  independent t ↔ ∀ i, disjoint (t i) (Sup (t '' {j | j ≠ i})) :=
by {simp_rw Sup_image, refl}

theorem independent_def'' :
  independent t ↔ ∀ i, disjoint (t i) (Sup {a | ∃ j ≠ i, t j = a}) :=
by {rw independent_def', tidy}

@[simp]
lemma independent_empty (t : empty → α) : independent t.

@[simp]
lemma independent_pempty (t : pempty → α) : independent t.

/-- If the elements of a set are independent, then any pair within that set is disjoint. -/
lemma independent.pairwise_disjoint : pairwise (disjoint on t) :=
λ x y h, disjoint_Sup_right (ht x) ⟨y, supr_pos h.symm⟩

lemma independent.mono
  {s t : ι → α} (hs : independent s) (hst : t ≤ s) :
  independent t :=
λ i, (hs i).mono (hst i) $ supr₂_mono $ λ j _, hst j

/-- Composing an independent indexed family with an injective function on the index results in
another indepedendent indexed family. -/
lemma independent.comp {ι ι' : Sort*}
  {t : ι → α} {f : ι' → ι} (ht : independent t) (hf : injective f) :
  independent (t ∘ f) :=
λ i, (ht (f i)).mono_right $ begin
  refine (supr_mono $ λ i, _).trans (supr_comp_le _ f),
  exact supr_const_mono hf.ne,
end

lemma independent.comp' {ι ι' : Sort*}
  {t : ι → α} {f : ι' → ι} (ht : independent $ t ∘ f) (hf : surjective f) :
  independent t :=
begin
  intros i,
  obtain ⟨i', rfl⟩ := hf i,
  rw ← hf.supr_comp,
  exact (ht i').mono_right (bsupr_mono $ λ j' hij, mt (congr_arg f) hij),
end

lemma independent.set_independent_range (ht : independent t) :
  set_independent $ range t :=
begin
  rw set_independent_iff,
  rw ← coe_comp_range_factorization t at ht,
  exact ht.comp' surjective_onto_range,
end

lemma independent.injective (ht : independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : injective t :=
begin
  intros i j h,
  by_contra' contra,
  apply h_ne_bot j,
  suffices : t j ≤ ⨆ k (hk : k ≠ i), t k,
  { replace ht := (ht i).mono_right this,
    rwa [h, disjoint_self] at ht, },
  replace contra : j ≠ i, { exact ne.symm contra, },
  exact le_supr₂ j contra,
end

lemma independent_pair {i j : ι} (hij : i ≠ j) (huniv : ∀ k, k = i ∨ k = j):
  independent t ↔ disjoint (t i) (t j) :=
begin
  split,
  { exact λ h, h.pairwise_disjoint hij },
  { rintros h k,
    obtain rfl | rfl := huniv k,
    { refine h.mono_right (supr_le $ λ i, supr_le $ λ hi, eq.le _),
      rw (huniv i).resolve_left hi },
    { refine h.symm.mono_right (supr_le $ λ j, supr_le $ λ hj, eq.le _),
      rw (huniv j).resolve_right hj } },
end

/-- Composing an indepedent indexed family with an order isomorphism on the elements results in
another indepedendent indexed family. -/
lemma independent.map_order_iso {ι : Sort*} {α β : Type*}
  [complete_lattice α] [complete_lattice β] (f : α ≃o β) {a : ι → α} (ha : independent a) :
  independent (f ∘ a) :=
λ i, ((ha i).map_order_iso f).mono_right (f.monotone.le_map_supr₂ _)

@[simp] lemma independent_map_order_iso_iff {ι : Sort*} {α β : Type*}
  [complete_lattice α] [complete_lattice β] (f : α ≃o β) {a : ι → α} :
  independent (f ∘ a) ↔ independent a :=
⟨ λ h, have hf : f.symm ∘ f ∘ a = a := congr_arg (∘ a) f.left_inv.comp_eq_id,
      hf ▸ h.map_order_iso f.symm,
  λ h, h.map_order_iso f⟩

/-- If the elements of a set are independent, then any element is disjoint from the `supr` of some
subset of the rest. -/
lemma independent.disjoint_bsupr {ι : Type*} {α : Type*} [complete_lattice α]
  {t : ι → α} (ht : independent t) {x : ι} {y : set ι} (hx : x ∉ y) :
  disjoint (t x) (⨆ i ∈ y, t i) :=
disjoint.mono_right (bsupr_mono $ λ i hi, (ne_of_mem_of_not_mem hi hx : _)) (ht x)

end complete_lattice

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

section frame

namespace complete_lattice
variables [order.frame α]

lemma set_independent_iff_pairwise_disjoint {s : set α} :
  set_independent s ↔ s.pairwise_disjoint id :=
⟨set_independent.pairwise_disjoint, λ hs i hi, disjoint_Sup_iff.2 $ λ j hj,
  hs hi hj.1 $ ne.symm hj.2⟩

alias set_independent_iff_pairwise_disjoint ↔ _ _root_.set.pairwise_disjoint.set_independent

lemma independent_iff_pairwise_disjoint {f : ι → α} : independent f ↔ pairwise (disjoint on f) :=
⟨independent.pairwise_disjoint, λ hs i, disjoint_supr_iff.2 $ λ j, disjoint_supr_iff.2 $ λ hij,
  hs hij.symm⟩

end complete_lattice

end frame
