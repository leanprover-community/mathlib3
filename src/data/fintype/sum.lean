/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import data.finset.sum
import logic.embedding.set

/-!
## Instances

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide the `fintype` instance for the sum of two fintypes.
-/

universes u v

variables {α β : Type*}

open finset

instance (α : Type u) (β : Type v) [fintype α] [fintype β] : fintype (α ⊕ β) :=
{ elems := univ.disj_sum univ,
  complete := by rintro (_ | _); simp }

@[simp] lemma finset.univ_disj_sum_univ {α β : Type*} [fintype α] [fintype β] :
  univ.disj_sum univ = (univ : finset (α ⊕ β)) :=
rfl

@[simp] theorem fintype.card_sum [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
card_disj_sum _ _

/-- If the subtype of all-but-one elements is a `fintype` then the type itself is a `fintype`. -/
def fintype_of_fintype_ne (a : α) (h : fintype {b // b ≠ a}) : fintype α :=
fintype.of_bijective (sum.elim (coe : {b // b = a} → α) (coe : {b // b ≠ a} → α)) $
  by { classical, exact (equiv.sum_compl (= a)).bijective }

lemma image_subtype_ne_univ_eq_image_erase [fintype α] [decidable_eq β] (k : β) (b : α → β) :
  image (λ i : {a // b a ≠ k}, b ↑i) univ = (image b univ).erase k :=
begin
  apply subset_antisymm,
  { rw image_subset_iff,
    intros i _,
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _)) },
  { intros i hi,
    rw mem_image,
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩,
    subst ha,
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩ }
end

lemma image_subtype_univ_ssubset_image_univ [fintype α] [decidable_eq β] (k : β) (b : α → β)
  (hk : k ∈ image b univ) (p : β → Prop) [decidable_pred p] (hp : ¬ p k) :
  image (λ i : {a // p (b a)}, b ↑i) univ ⊂ image b univ :=
begin
  split,
  { intros x hx,
    rcases mem_image.1 hx with ⟨y, _, hy⟩,
    exact hy ▸ mem_image_of_mem b (mem_univ y) },
  { intros h,
    rw mem_image at hk,
    rcases hk with ⟨k', _, hk'⟩, subst hk',
    have := h (mem_image_of_mem b (mem_univ k')),
    rw mem_image at this,
    rcases this with ⟨j, hj, hj'⟩,
    exact hp (hj' ▸ j.2) }
end

/-- Any injection from a finset `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
lemma finset.exists_equiv_extend_of_card_eq [fintype α] [decidable_eq β] {t : finset β}
  (hαt : fintype.card α = t.card) {s : finset α} {f : α → β} (hfst : s.image f ⊆ t)
  (hfs : set.inj_on f s) :
  ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i :=
begin
  classical,
  induction s using finset.induction with a s has H generalizing f,
  { obtain ⟨e⟩ : nonempty (α ≃ ↥t) := by rwa [← fintype.card_eq, fintype.card_coe],
    use e,
    simp },
  have hfst' : finset.image f s ⊆ t := (finset.image_mono _ (s.subset_insert a)).trans hfst,
  have hfs' : set.inj_on f s := hfs.mono (s.subset_insert a),
  obtain ⟨g', hg'⟩ := H hfst' hfs',
  have hfat : f a ∈ t := hfst (mem_image_of_mem _ (s.mem_insert_self a)),
  use g'.trans (equiv.swap (⟨f a, hfat⟩ : t) (g' a)),
  simp_rw mem_insert,
  rintro i (rfl | hi),
  { simp },
  rw [equiv.trans_apply, equiv.swap_apply_of_ne_of_ne, hg' _ hi],
  { exact ne_of_apply_ne subtype.val (ne_of_eq_of_ne (hg' _ hi) $
    hfs.ne (subset_insert _ _ hi) (mem_insert_self _ _) $ ne_of_mem_of_not_mem hi has) },
  { exact g'.injective.ne (ne_of_mem_of_not_mem hi has) },
end

/-- Any injection from a set `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
lemma set.maps_to.exists_equiv_extend_of_card_eq [fintype α] {t : finset β}
  (hαt : fintype.card α = t.card) {s : set α} {f : α → β} (hfst : s.maps_to f t)
  (hfs : set.inj_on f s) :
  ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i :=
begin
  classical,
  let s' : finset α := s.to_finset,
  have hfst' : s'.image f ⊆ t := by simpa [← finset.coe_subset] using hfst,
  have hfs' : set.inj_on f s' := by simpa using hfs,
  obtain ⟨g, hg⟩ := finset.exists_equiv_extend_of_card_eq hαt hfst' hfs',
  refine ⟨g, λ i hi, _⟩,
  apply hg,
  simpa using hi,
end

lemma fintype.card_subtype_or (p q : α → Prop)
  [fintype {x // p x}] [fintype {x // q x}] [fintype {x // p x ∨ q x}] :
  fintype.card {x // p x ∨ q x} ≤ fintype.card {x // p x} + fintype.card {x // q x} :=
begin
  classical,
  convert fintype.card_le_of_embedding (subtype_or_left_embedding p q),
  rw fintype.card_sum
end

lemma fintype.card_subtype_or_disjoint (p q : α → Prop) (h : disjoint p q)
  [fintype {x // p x}] [fintype {x // q x}] [fintype {x // p x ∨ q x}] :
  fintype.card {x // p x ∨ q x} = fintype.card {x // p x} + fintype.card {x // q x} :=
begin
  classical,
  convert fintype.card_congr (subtype_or_equiv p q h),
  simp
end

section
open_locale classical

@[simp] lemma infinite_sum : infinite (α ⊕ β) ↔ infinite α ∨ infinite β :=
begin
  refine ⟨λ H, _, λ H, H.elim (@sum.infinite_of_left α β) (@sum.infinite_of_right α β)⟩,
  contrapose! H, haveI := fintype_of_not_infinite H.1, haveI := fintype_of_not_infinite H.2,
  exact infinite.false
end

end
