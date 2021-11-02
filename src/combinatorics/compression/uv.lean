/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.finset.basic

/-!
# UV compressions

This file defines UV compression. Broadly speaking, a compression in combinatorics is an operation
that preserves a certain measure and reduces another one. UV compressing a finset along
`U V : finset α` means removing from it everything that's in `V` and adding everything that's in
`U`, ``. We define this operationmo
UV compressions are immensely useful to prove the Kruskal-Katona theorem.
The idea is that compressing a set family might decrease the size of its
shadow, and so iterated compressions should hopefully minimise the shadow.

## TODO

Define the shadow of a family of finsets and prove that compressing reduces the shadow. Those
results already exist on the branch `combinatorics`.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/

open finset

variable {α : Type*}

-- The namespace here is useful to distinguish between other compressions.
namespace UV
section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_rel (@disjoint α _)]
  [decidable_rel ((≤) : α → α → Prop)]

/-- To UV-compress `A`, if it doesn't touch `U` and does contain `V`, we remove `V` and
put `U` in. We'll only really use this when `|U| = |V|` and `U ∩ V = ∅`. -/
def compress (u v a : α) : α := if disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a

/-- Compressing a set is idempotent. -/
lemma compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a :=
begin
  simp only [compress],
  split_ifs with h h',
  { suffices : u = ⊥,
    { rw [this, sup_bot_eq, sup_bot_eq, sdiff_idem] },
    rw ← disjoint_self,
    have : u \ v = u := (h.1.mono_right h.2).sdiff_eq_left,
    nth_rewrite 1 ←this,
    exact h'.1.mono_right (sdiff_le_self_sdiff le_sup_right) },

end

end generalized_boolean_algebra

variables [decidable_eq α]

variables {n : ℕ}

variables {𝒜 : finset (finset α)} {U V A : finset α}

/-- Compression doesn't change the size of a set. -/
lemma compress_size (U V : finset α) (A : finset α) (h₁ : U.card = V.card) :
  (compress U V A).card = A.card :=
begin
  rw compress, split_ifs,
    rw [card_sdiff (subset.trans h.2 (subset_union_left _ _)),
        card_disjoint_union h.1.symm, h₁, nat.add_sub_cancel],
  refl
end

/-- Part of the compressed family, where we keep sets whose compression is already present. -/
@[reducible]
def compress_remains (U V : finset α) (𝒜 : finset (finset α)) :=
𝒜.filter (λ A, compress U V A ∈ 𝒜)

/-- Part of the compressed family, where we move the sets whose compression is not there. -/
@[reducible]
def compress_motion (U V : finset α) (𝒜 : finset (finset α)) :=
(𝒜.filter (λ A, compress U V A ∉ 𝒜)).image (λ A, compress U V A)

/-- To UV-compress a set family, we keep all the sets whose compression is present, and move all the
sets whose compression is not there (and take this union). -/
def compress_family (U V : finset α) (𝒜 : finset (finset α)) :=
  compress_motion U V 𝒜 ∪ compress_remains U V 𝒜
local notation `CC` := compress_family

lemma mem_compress_remains (U V A : finset α) :
  A ∈ compress_remains U V 𝒜 ↔ A ∈ 𝒜 ∧ compress U V A ∈ 𝒜 :=
by rw mem_filter

lemma mem_compress_motion (U V A : finset α) :
  A ∈ compress_motion U V 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A) :=
begin
  simp [compress_motion],
  split; rintro ⟨p, q, r⟩,
    exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
  exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩,
end

/-- `A` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compress (U V : finset α) {A : finset α} :
  A ∈ CC U V 𝒜 ↔
  (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A)) ∨ (A ∈ 𝒜 ∧ compress U V A ∈ 𝒜) :=
by rw [compress_family, mem_union, mem_compress_remains, mem_compress_motion]

lemma compress_self (U A : finset α) : compress U U A = A :=
begin
  rw compress,
  split_ifs,
  { rw [←sup_eq_union, h.1.symm.sup_sdiff_cancel_right] },
  refl,
end

lemma compress_motion_self (U : finset α) : compress_motion U U 𝒜 = ∅ :=
begin
  refine eq_empty_of_forall_not_mem (λ s hs, _),
  rw mem_compress_motion at hs,
  obtain ⟨t, ht, rfl⟩ := hs.2,
  rw compress_self at hs,
  exact hs.1 ht,
end

lemma compress_remains_self (U : finset α) : compress_remains U U 𝒜 = 𝒜 :=
by { ext s, rw [mem_compress_remains, compress_self, and_self] }

/-- `is_compressed U V 𝒜` expresses that `𝒜` is UV-compressed. -/
@[reducible]
def is_compressed (U V : finset α) (𝒜 : finset (finset α)) := CC U V 𝒜 = 𝒜

/-- The empty family is compressed. -/
lemma is_compressed_self (𝒜 : finset (finset α)) : is_compressed U U 𝒜 :=
by rw [is_compressed, compress_family, compress_motion_self, compress_remains_self, empty_union]

/-- Compressing a family is idempotent. -/
lemma compress_family_idempotent (U V : finset α) (𝒜 : finset (finset α)) :
  CC U V (CC U V 𝒜) = CC U V 𝒜 :=
begin
  have : ∀ A ∈ CC U V 𝒜, compress U V A ∈ CC U V 𝒜,
    intros A HA, rw mem_compress at HA ⊢, simp [compress_idem],
    rcases HA with ⟨_, B, _, rfl⟩ | ⟨_, _⟩,
      left, refine ⟨_, B, ‹_›, _⟩; rwa compress_idem,
    right, assumption,
  have : filter (λ A, compress U V A ∉ CC U V 𝒜) (CC U V 𝒜) = ∅,
    rw ← filter_false (CC U V 𝒜), apply filter_congr, simpa,
  rw [compress_family, compress_motion, this, image_empty, union_comm,
      compress_remains, ← this],
  exact filter_union_filter_neg_eq _ (compress_family U V 𝒜),
end

lemma compress_disjoint (U V : finset α) :
  disjoint (compress_motion U V 𝒜) (compress_remains U V 𝒜) :=
begin
  rw disjoint_left, intros A HA HB,
  rw mem_compress_remains at HB,
  rw mem_compress_motion at HA,
  exact HA.1 HB.1
end

/-- Compression is kinda injective. -/
lemma inj_ish {U V : finset α} {A B : finset α}
  (hA : disjoint U A ∧ V ⊆ A) (hB : disjoint U B ∧ V ⊆ B)
  (Z : (A ∪ U) \ V = (B ∪ U) \ V) : A = B :=
begin
  ext x, split,
  all_goals {
    intro p, by_cases h₁: (x ∈ V), { exact hB.2 h₁ <|> exact hA.2 h₁ },
    have := mem_sdiff.2 ⟨mem_union_left U ‹_›, h₁⟩,
    rw Z at this <|> rw ← Z at this,
    rw [mem_sdiff, mem_union] at this,
    suffices: x ∉ U, tauto,
    apply disjoint_right.1 ‹disjoint _ _ ∧ _›.1 p }
end

/-- Compressing a set family doesn't change its size. -/
lemma compressed_size (U V : finset α) :
  (CC U V 𝒜).card = 𝒜.card :=
begin
  rw [compress_family, card_disjoint_union (compress_disjoint _ _),
      card_image_of_inj_on],
    rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
    rw [disjoint_iff_inter_eq_empty, inter_comm],
    apply filter_inter_filter_neg_eq,
  intros A HA B HB Z,
  rw [mem_coe, mem_filter] at HA HB,
  dsimp at Z,
  rw compress at HA Z,
  split_ifs at HA Z,
    rw compress at HB Z,
    split_ifs at HB Z,
      exact inj_ish h h_1 Z,
    tauto,
  tauto
end

/--
If A is in the compressed family but V is a subset of A, A must have been
in the original family.
-/
lemma compress_held {U V A : finset α}
  (h₁ : A ∈ CC U V 𝒜) (h₂ : V ⊆ A) (h₃ : U.card = V.card) :
  A ∈ 𝒜 :=
begin
  rw mem_compress at h₁, rcases h₁ with ⟨_, B, H, HB⟩ | _,
    rw compress at HB, split_ifs at HB,
      have : V = ∅,
        apply eq_empty_of_forall_not_mem,
        intros x xV, replace h₂ := h₂ xV,
        rw [← HB, mem_sdiff] at h₂, exact h₂.2 xV,
      have : U = ∅,
        rwa [← finset.card_eq_zero, h₃, finset.card_eq_zero],
      rw [‹U = ∅›, ‹V = ∅›, union_empty, sdiff_empty] at HB, rwa ← HB,
    rwa ← HB,
  tauto
end

/--
If A is not in the original family but is in the compressed family, then
A has been compressed, and its original was in the original family.
-/
lemma compress_moved {U V A : finset α}
  (h₁ : A ∈ CC U V 𝒜) (h₂ : A ∉ 𝒜) :
  U ⊆ A ∧ disjoint V A ∧ (A ∪ V) \ U ∈ 𝒜 :=
begin
  rw mem_compress at h₁,
  rcases h₁ with ⟨_, B, H, HB⟩ | _,
  { rw compress at HB,
    split_ifs at HB,
    { rw ← HB at *, refine ⟨_, disjoint_sdiff, _⟩,
        have : disjoint U V := disjoint_of_subset_right h.2 h.1,
        rw union_sdiff_distrib, rw this.sdiff_eq_left,
        apply subset_union_right _ _,
      rwa [sdiff_union_of_subset, union_sdiff_self, h.1.sdiff_eq_right],
      apply trans h.2 (subset_union_left _ _) },
    { rw HB at *, tauto } },
  tauto
end

/--
If A is in the compressed family and does move under compression, then the
compressed version was in the original family.
-/
lemma uncompressed_was_already_there
  {U V A : finset α} (h₁ : A ∈ CC U V 𝒜) (h₂ : V ⊆ A) (h₃ : disjoint U A) :
  (A ∪ U) \ V ∈ 𝒜 :=
begin
  rw mem_compress at h₁, have : disjoint U A ∧ V ⊆ A := ⟨h₃, h₂⟩,
  rcases h₁ with ⟨_, B, B_in_A, cB_eq_A⟩ | ⟨_, cA_in_A⟩,
  { by_cases a: (A ∪ U) \ V = A,
      have : U \ V = U, apply disjoint.sdiff_eq_left,
        apply (disjoint_of_subset_right h₂ h₃),
      have : U = ∅,
        rw ← disjoint_self_iff_empty,
        suffices: disjoint U (U \ V), rw ‹U \ V = U› at this, assumption,
        apply disjoint_of_subset_right (subset_union_right (A \ V) _),
        rwa [← union_sdiff_distrib, a],
      have : V = ∅,
        rw ← disjoint_self_iff_empty, apply disjoint_of_subset_right h₂,
        rw ← a, apply disjoint_sdiff,
      simpa [a, cB_eq_A.symm, compress, ‹U = ∅›, ‹V = ∅›],
    have : compress U V A = (A ∪ U) \ V, rw compress, split_ifs, refl,
    exfalso, apply a, rw [← this, ← cB_eq_A, compress_idem] },
  { rw compress at cA_in_A, split_ifs at cA_in_A, assumption }
end

lemma sdiff_sdiff {A B C : finset α} (h : C ⊆ A) : A \ (B \ C) = A \ B ∪ C :=
by rw [sdiff_sdiff_right', sup_eq_union, inf_eq_inter, (inter_eq_right_iff_subset _ _).2 h]

lemma sdiff_erase {A : finset α} {x : α} (hx : x ∈ A) : A \ A.erase x = {x} :=
by rw [← sdiff_singleton_eq_erase, sdiff_sdiff (singleton_subset_iff.2 hx), finset.sdiff_self,
  empty_union]

end UV
