/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.finset.card

/-!
# UV-compressions

This file defines UV-compression. It is an operation on a set family that reduces its shadow.

UV-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

UV-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `uv.compress`: `compress u v a` is `a` compressed along `u` and `v`.
* `uv.compression`: `compression u v s` is the compression of the set family `s` along `u` and `v`.
  It is the compressions of the elements of `s` whose compression is not already in `s` along with
  the element whose compression is already in `s`. This way of splitting into what moves and what
  does not ensures the compression doesn't squash the set family, which is proved by
  `uv.card_compress`.

## Notation

`𝓒` (typed with `\MCC`) is notation for `uv.compression` in locale `finset_family`.

## Notes

Even though our emphasis is on `finset α`, we define UV-compressions more generally in a generalized
boolean algebra, so that one can use it for `set α`.

## TODO

Prove that compressing reduces the size of shadow. This result and some more already exist on the
branch `combinatorics`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/

open finset

variable {α : Type*}

/-- UV-compression is injective on the elements it moves. See `uv.compress`. -/
lemma sup_sdiff_inj_on [generalized_boolean_algebra α] (u v : α) :
  {x | disjoint u x ∧ v ≤ x}.inj_on (λ x, (x ⊔ u) \ v) :=
begin
  rintro a ha b hb hab,
  have h : (a ⊔ u) \ v \ u ⊔ v = (b ⊔ u) \ v \ u ⊔ v,
  { dsimp at hab,
    rw hab },
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h,
end

-- The namespace is here to distinguish from other compressions.
namespace uv

/-! ### UV-compression in generalized boolean algebras -/

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_rel (@disjoint α _ _)]
  [decidable_rel ((≤) : α → α → Prop)] {s : finset α} {u v a b : α}

/-- To UV-compress `a`, if it doesn't touch `U` and does contain `V`, we remove `V` and
put `U` in. We'll only really use this when `|U| = |V|` and `U ∩ V = ∅`. -/
def compress (u v a : α) : α := if disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a

/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
def compression (u v : α) (s : finset α) :=
s.filter (λ a, compress u v a ∈ s) ∪ (s.image $ compress u v).filter (λ a, a ∉ s)

localized "notation `𝓒 ` := uv.compression" in finset_family

/-- `is_compressed u v s` expresses that `s` is UV-compressed. -/
def is_compressed (u v : α) (s : finset α) := 𝓒 u v s = s

lemma compress_of_disjoint_of_le (hua : disjoint u a) (hva : v ≤ a) :
  compress u v a = (a ⊔ u) \ v :=
if_pos ⟨hua, hva⟩

/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compression :
  a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a :=
by simp_rw [compression, mem_union, mem_filter, mem_image, and_comm (a ∉ s)]

@[simp] lemma compress_self (u a : α) : compress u u a = a :=
begin
  unfold compress,
  split_ifs,
  { exact h.1.symm.sup_sdiff_cancel_right },
  { refl }
end

@[simp] lemma compression_self (u : α) (s : finset α) : 𝓒 u u s = s :=
begin
  unfold compression,
  convert union_empty s,
  { ext a,
    rw [mem_filter, compress_self, and_self] },
  { refine eq_empty_of_forall_not_mem (λ a ha, _),
    simp_rw [mem_filter, mem_image, compress_self] at ha,
    obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := ha,
    exact hb' hb }
end

/-- Any family is compressed along two identical elements. -/
lemma is_compressed_self (u : α) (s : finset α) : is_compressed u u s := compression_self u s

lemma compress_disjoint (u v : α) :
  disjoint (s.filter (λ a, compress u v a ∈ s)) ((s.image $ compress u v).filter (λ a, a ∉ s)) :=
disjoint_left.2 $ λ a ha₁ ha₂, (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1

/-- Compressing an element is idempotent. -/
@[simp] lemma compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a :=
begin
  unfold compress,
  split_ifs with h h',
  { rw [le_sdiff_iff.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem] },
  { refl },
  { refl }
end

lemma compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s :=
begin
  rw mem_compression,
  by_cases compress u v a ∈ s,
  { rw compress_idem,
    exact or.inl ⟨h, h⟩ },
  { exact or.inr ⟨h, a, ha, rfl⟩ }
end

-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
lemma compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) : compress u v a ∈ 𝓒 u v s :=
begin
  rw mem_compression at ⊢ ha,
  simp only [compress_idem, exists_prop],
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha,
  { exact or.inl ⟨ha, ha⟩ },
  { exact or.inr ⟨by rwa compress_idem, b, hb, (compress_idem _ _ _).symm⟩ }
end

/-- Compressing a family is idempotent. -/
@[simp] lemma compression_idem (u v : α) (s : finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s :=
begin
  have h : filter (λ a, compress u v a ∉ 𝓒 u v s) (𝓒 u v s) = ∅ :=
    filter_false_of_mem (λ a ha h, h $ compress_mem_compression_of_mem_compression ha),
  rw [compression, image_filter, h, image_empty, ←h],
  exact filter_union_filter_neg_eq _ (compression u v s),
end

/-- Compressing a family doesn't change its size. -/
lemma card_compression (u v : α) (s : finset α) : (𝓒 u v s).card = s.card :=
begin
  rw [compression, card_disjoint_union (compress_disjoint _ _), image_filter, card_image_of_inj_on,
    ←card_disjoint_union, filter_union_filter_neg_eq],
  { rw disjoint_iff_inter_eq_empty,
    exact filter_inter_filter_neg_eq _ _ },
  intros a ha b hb hab,
  dsimp at hab,
  rw [mem_coe, mem_filter, function.comp_app] at ha hb,
  rw compress at ha hab,
  split_ifs at ha hab with has,
  { rw compress at hb hab,
    split_ifs at hb hab with hbs,
    { exact sup_sdiff_inj_on u v has hbs hab },
    { exact (hb.2 hb.1).elim } },
  { exact (ha.2 ha.1).elim }
end

/-- If `a` is in the family compression and can be compressed, then its compression is in the
original family. -/
lemma sup_sdiff_mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hua : disjoint u a) :
  (a ⊔ u) \ v ∈ s :=
begin
  rw [mem_compression, compress_of_disjoint_of_le hua hva] at ha,
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha,
  { exact ha },
  have hu : u = ⊥,
  { suffices : disjoint u (u \ v),
    { rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this },
    refine hua.mono_right _,
    rw [←compress_idem, compress_of_disjoint_of_le hua hva],
    exact sdiff_le_sdiff_right le_sup_right },
  have hv : v = ⊥,
  { rw ←disjoint_self,
    apply disjoint.mono_right hva,
    rw [←compress_idem, compress_of_disjoint_of_le hua hva],
    exact disjoint_sdiff_self_right },
  rwa [hu, hv, compress_self, sup_bot_eq, sdiff_bot],
end

/-- If `a` is in the `u, v`-compression but `v ≤ a`, then `a` must have been in the original
family. -/
lemma mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hvu : v = ⊥ → u = ⊥) : a ∈ s :=
begin
  rw mem_compression at ha,
  obtain ha | ⟨_, b, hb, h⟩ := ha,
  { exact ha.1 },
  unfold compress at h,
  split_ifs at h,
  { rw [←h, le_sdiff_iff] at hva,
    rw [hvu hva, hva, sup_bot_eq, sdiff_bot] at h,
    rwa ←h },
  { rwa ←h }
end

end generalized_boolean_algebra

/-! ### UV-compression on finsets -/

open_locale finset_family

variables [decidable_eq α] {𝒜 : finset (finset α)} {U V A : finset α}

/-- Compressing a finset doesn't change its size. -/
lemma card_compress (hUV : U.card = V.card) (A : finset α) : (compress U V A).card = A.card :=
begin
  unfold compress,
  split_ifs,
  { rw [card_sdiff (h.2.trans le_sup_left), sup_eq_union, card_disjoint_union h.1.symm, hUV,
    add_tsub_cancel_right] },
  { refl }
end

end uv
