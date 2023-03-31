/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.set_family.shadow

/-!
# UV-compressions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  `uv.card_compression`.
* `uv.card_shadow_compression_le`: Compressing reduces the size of the shadow. This is a key fact in
  the proof of Kruskal-Katona.

## Notation

`𝓒` (typed with `\MCC`) is notation for `uv.compression` in locale `finset_family`.

## Notes

Even though our emphasis is on `finset α`, we define UV-compressions more generally in a generalized
boolean algebra, so that one can use it for `set α`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/

section generalized_boolean_algebra
variables {α : Type*} [generalized_boolean_algebra α] {x y z : α}

lemma disjoint.le_sdiff_of_sup_le_left (hxz : disjoint x z) (h : z ⊔ x ≤ y) : x ≤ y \ z :=
hxz.symm.sup_sdiff_cancel_left.ge.trans (sdiff_le_sdiff_right h)

lemma inf_sdiff_left_comm : x \ z ⊓ y = (x ⊓ y) \ z :=
by rw [@inf_comm _ _ x, inf_comm, inf_sdiff_assoc]

end generalized_boolean_algebra

namespace finset
variables {α : Type*} [decidable_eq α] {s t u : finset α} {a : α}

lemma erase_eq (s : finset α) (a : α) : s.erase a = s \ {a} := (sdiff_singleton_eq_erase _ _).symm

lemma sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
sdiff_sup_sdiff_cancel hts hut

lemma sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a :=
by simp_rw [←sdiff_singleton_eq_erase, sdiff_union_sdiff_cancel hts (singleton_subset_iff.2 ha)]

lemma insert_union_comm (s t : finset α) : insert a s ∪ t = s ∪ insert a t :=
by rw [insert_union, union_insert]

lemma erase_union_distrib (s t : finset α) : (s ∪ t).erase a = s.erase a ∪ t.erase a :=
by simp_rw [erase_eq, union_sdiff_distrib]

lemma _root_.disjoint.finset_union_sdiff_cancel_left (h : disjoint s t) : (s ∪ t) \ s = t :=
h.sup_sdiff_cancel_left

lemma _root_.disjoint.finset_union_sdiff_cancel_right (h : disjoint s t) : (s ∪ t) \ t = s :=
h.sup_sdiff_cancel_right

lemma _root_.disjoint.finset_subset_sdiff_of_union_subset_left (hsu : disjoint s u)
  (h : u ∪ s ⊆ t) : s ⊆ t \ u :=
hsu.le_sdiff_of_sup_le_left h

lemma sdiff_sdiff_eq_sdiff_union {a b c : finset α} (h : c ⊆ a) : a \ (b \ c) = a \ b ∪ c :=
sdiff_sdiff_eq_sdiff_sup h

lemma sdiff_erase' {s t : finset α} {a : α} (h : a ∈ s) : s \ t.erase a = insert a (s \ t) :=
by rw [←sdiff_singleton_eq_erase, sdiff_sdiff_eq_sdiff_union (singleton_subset_iff.2 h), insert_eq,
  union_comm]

end finset

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

/-- UV-compressing `a` means removing `v` from it and adding `u` if `a` and `u` are disjoint and
`v ≤ a` (in some sense, it replaces the `u` part of `a` by the `v` part). Else, UV-compressing `a`
doesn't do anything. This is most useful when `u` and `v` are disjoint finsets of same size. -/
def compress (u v a : α) : α := if disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a

/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
def compression (u v : α) (s : finset α) :=
s.filter (λ a, compress u v a ∈ s) ∪ (s.image $ compress u v).filter (λ a, a ∉ s)

localized "notation (name := uv.compression) `𝓒 ` := uv.compression" in finset_family

/-- `is_compressed u v s` expresses that `s` is UV-compressed. -/
def is_compressed (u v : α) (s : finset α) := 𝓒 u v s = s

lemma compress_of_disjoint_of_le (hua : disjoint u a) (hva : v ≤ a) :
  compress u v a = (a ⊔ u) \ v :=
if_pos ⟨hua, hva⟩

lemma compress_of_disjoint_of_le' (hva : disjoint v a) (hua : u ≤ a) :
  compress u v ((a ⊔ v) \ u) = a :=
by rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
  ((hva.mono_right hua).le_sdiff_of_sup_le_left $ sup_le_sup_right hua _),
  sdiff_sup_cancel (le_sup_of_le_left hua), hva.symm.sup_sdiff_cancel_right]

/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compression :
  a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a :=
by simp_rw [compression, mem_union, mem_filter, mem_image, and_comm (a ∉ s)]

protected lemma is_compressed.eq (h : is_compressed u v s) : 𝓒 u v s = s := h

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

@[simp] lemma compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a :=
begin
  refine (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans _,
  rw [sup_sdiff_self_right, sup_sdiff, disjoint_sdiff_self_right.sdiff_eq_left, sup_eq_right],
  exact sdiff_sdiff_le,
end

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
@[simp] lemma card_compression (u v : α) (s : finset α) : (𝓒 u v s).card = s.card :=
begin
  rw [compression, card_disjoint_union (compress_disjoint _ _), image_filter, card_image_of_inj_on,
    ←card_disjoint_union, filter_union_filter_neg_eq],
  { rw disjoint_iff_inter_eq_empty,
    exact filter_inter_filter_neg_eq _ _ _ },
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

lemma le_of_mem_compression (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : u ≤ a :=
begin
  rw mem_compression at h,
  obtain _ | ⟨-, b, hb, hba⟩ := h,
  { cases ha h.1 },
  unfold compress at hba,
  split_ifs at hba,
  { rw ←hba,
    exact (h.1.mono_right h.2).le_sdiff_of_sup_le_left (sup_le_sup_right h.2 _) },
  { cases ne_of_mem_of_not_mem hb ha hba }
end

lemma disjoint_of_mem_compression (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : disjoint v a :=
begin
  rw mem_compression at h,
  obtain _ | ⟨-, b, hb, hba⟩ := h,
  { cases ha h.1 },
  unfold compress at hba,
  split_ifs at hba,
  { rw ←hba,
    exact disjoint_sdiff_self_right },
  { cases ne_of_mem_of_not_mem hb ha hba }
end

lemma sup_sdiff_mem_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) :
  (a ⊔ v) \ u ∈ s :=
begin
  rw mem_compression at h,
  obtain _ | ⟨-, b, hb, hba⟩ := h,
  { cases ha h.1 },
  unfold compress at hba,
  split_ifs at hba,
  { rwa [←hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left] },
  { cases ne_of_mem_of_not_mem hb ha hba }
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
    rwa [←h, hvu hva, hva, sup_bot_eq, sdiff_bot] },
  { rwa ←h }
end

end generalized_boolean_algebra

/-! ### UV-compression on finsets -/

open_locale finset_family

variables [decidable_eq α] {𝒜 : finset (finset α)} {u v a : finset α}

/-- Compressing a finset doesn't change its size. -/
lemma card_compress (hUV : u.card = v.card) (A : finset α) : (compress u v A).card = A.card :=
begin
  unfold compress,
  split_ifs,
  { rw [card_sdiff (h.2.trans le_sup_left), sup_eq_union, card_disjoint_union h.1.symm, hUV,
      add_tsub_cancel_right] },
  { refl }
end

/-- UV-compression will reduce the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about compression for
Kruskal-Katona -/
lemma shadow_compression_subset_compression_shadow (u v : finset α)
  (huv : ∀ x ∈ u, ∃ y ∈ v, is_compressed (u.erase x) (v.erase y) 𝒜) :
  ∂ (𝓒 u v 𝒜) ⊆ 𝓒 u v (∂ 𝒜) :=
begin
  set 𝒜' := 𝓒 u v 𝒜,
  suffices h : ∀ s, s ∈ ∂ 𝒜' → s ∉ ∂ 𝒜 → u ⊆ s ∧ disjoint v s ∧ (s ∪ v) \ u ∈ ∂ 𝒜 ∧ u ∉ ∂ 𝒜',
  { rintro s hs',
    rw mem_compression,
    by_cases hs : s ∈ 𝒜.shadow,
    { refine or.inl ⟨hs, _⟩,
      rw compress,
      split_ifs with h,
      { sorry },
      { exact hs } },
    { obtain ⟨hus, hvs, h, _⟩ := h _ hs' hs,
      exact or.inr ⟨hs, _, h, compress_of_disjoint_of_le' hvs hus⟩ } },
  sorry,
end

/-- UV-compression will reduce the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about compression for
Kruskal-Katona -/
lemma card_shadow_compression_le' (u v : finset α)
  (huv : ∀ x ∈ u, ∃ y ∈ v, is_compressed (u.erase x) (v.erase y) 𝒜) :
  (∂ (𝓒 u v 𝒜)).card ≤ (∂ 𝒜).card :=
(card_le_of_subset $ shadow_compression_subset_compression_shadow _ _ huv).trans
  (card_compression _ _ _).le

/-- UV-compression will reduce the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about compression for
Kruskal-Katona -/
lemma card_shadow_compression_le (u v : finset α)
  (huv : ∀ x ∈ u, ∃ y ∈ v, is_compressed (u.erase x) (v.erase y) 𝒜) :
  (∂ (𝓒 u v 𝒜)).card ≤ (∂ 𝒜).card :=
begin
  set 𝒜' := 𝓒 u v 𝒜,
  suffices : (∂ 𝒜' \ ∂ 𝒜 ∪ ∂ 𝒜' ∩ ∂ 𝒜).card ≤ (∂ 𝒜 \ ∂ 𝒜' ∪ ∂ 𝒜 ∩ ∂ 𝒜').card,
  { rwa [sdiff_union_inter, sdiff_union_inter] at this },
  suffices : (∂ 𝒜' \ ∂ 𝒜).card ≤ (∂ 𝒜 \ ∂ 𝒜').card,
  { rw [card_disjoint_union (disjoint_sdiff_inter _ _),
      card_disjoint_union (disjoint_sdiff_inter _ _), inter_comm],
    exact add_le_add_right ‹_› _ },
  -- We will define an injection `∂ 𝒜' \ ∂ 𝒜 → ∂ 𝒜 \ ∂ 𝒜'`.
  -- First, let's prove a few facts about things in the domain:
  suffices h : ∀ s ∈ ∂ 𝒜' \ ∂ 𝒜, u ⊆ s ∧ disjoint v s ∧ (s ∪ v) \ u ∈ ∂ 𝒜 \ ∂ 𝒜',
  { refine card_le_card_of_inj_on (λ s, (s ∪ v) \ u) (λ s hs, (h s hs).2.2) (λ s₁ hs₁ s₂ hs₂, _),
    exact sup_sdiff_inj_on _ _ ⟨(h s₁ hs₁).2.1, (h s₁ hs₁).1⟩ ⟨(h s₂ hs₂).2.1, (h s₂ hs₂).1⟩ },
  intros s hs,
  obtain ⟨hs𝒜', hs𝒜⟩ : s ∈ ∂ 𝒜' ∧ s ∉ ∂ 𝒜 := mem_sdiff.1 hs,
  -- This is gonna be useful a couple of times so let's name it.
  have m : ∀ y ∉ s, insert y s ∉ 𝒜 := λ y h a, hs𝒜 (mem_shadow_iff_insert_mem.2 ⟨y, h, a⟩),
  obtain ⟨x, _, _⟩ := mem_shadow_iff_insert_mem.1 hs𝒜',
  have hus : u ⊆ insert x s := le_of_mem_compression ‹insert x s ∈ 𝒜'› (m _ ‹x ∉ s›),
  have hvs : disjoint v (insert x s) := disjoint_of_mem_compression ‹_› (m _ ‹x ∉ s›),
  have : (insert x s ∪ v) \ u ∈ 𝒜 := sup_sdiff_mem_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›),
  have hsv : disjoint s v := hvs.symm.mono_left (subset_insert _ _),
  have hvu : disjoint v u := disjoint_of_subset_right hus hvs,
  have hxv : x ∉ v := disjoint_right.1 hvs (mem_insert_self _ _),
  have : v \ u = v := sdiff_eq_self_of_disjoint ‹disjoint v u›,
  -- The first key part is that `x ∉ u`
  have : x ∉ u,
  { intro a,
    obtain ⟨y, hyv, hxy⟩ := huv x ‹x ∈ u›,
    -- If `x ∈ u`, we can get `y ∈ v` so that `𝒜` is `(u.erase x, v.erase y)`-compressed
    apply m y (disjoint_right.1 hsv hyv),
    -- and we will use this `y` to contradict `m`, so we would like to show `insert y s ∈ 𝒜`.
    -- We do this by showing the below
    have : ((insert x s ∪ v) \ u ∪ erase u x) \ erase v y ∈ 𝒜,
    { refine sup_sdiff_mem_of_mem_compression (by rwa hxy.eq) _
        (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff),
      rw [union_sdiff_distrib, ‹v \ u = v›],
      exact (erase_subset _ _).trans (subset_union_right _ _) },
    -- and then arguing that it's the same
    convert this,
    rw [sdiff_union_erase_cancel (hus.trans $ subset_union_left _ _) ‹x ∈ u›, erase_union_distrib,
      erase_insert ‹x ∉ s›, erase_eq_of_not_mem ‹x ∉ v›, sdiff_erase' (mem_union_right _ hyv),
      hsv.finset_union_sdiff_cancel_right] },
  -- Now that this is done, it's immediate that `u ⊆ s`
  have hus : u ⊆ s,
  { rwa [←erase_eq_of_not_mem ‹x ∉ u›, ←subset_insert_iff] },
  -- and we already had that `v` and `s` are disjoint
  refine ⟨hus, hsv.symm, _⟩,
  -- so it only remains to get `(s ∪ v) \ u ∈ ∂ 𝒜 \ ∂ 𝒜'`
  simp_rw [mem_sdiff, mem_shadow_iff_insert_mem],
  refine ⟨⟨x, _, _⟩, _⟩,
  -- `(s ∪ v) \ u ∈ ∂ 𝒜` is pretty direct:
  { exact not_mem_sdiff_of_not_mem_left (not_mem_union.2 ⟨‹x ∉ s›, ‹x ∉ v›⟩) },
  { rwa [←insert_sdiff_of_not_mem _ ‹x ∉ u›, ←insert_union] },
  -- For (s ∪ v) \ u ∉ ∂ 𝒜', we split up based on w ∈ u
  rintro ⟨w, hwB, hw𝒜'⟩,
  have : v ⊆ insert w ((s ∪ v) \ u) := (hvu.finset_subset_sdiff_of_union_subset_left $
    union_subset_union hus subset.rfl).trans (subset_insert _ _),
  by_cases hwu : w ∈ u,
    -- If `w ∈ u`, we find `z ∈ v`, and contradict `m` again
  { obtain ⟨z, hz, hxy⟩ := huv w ‹w ∈ u›,
    apply m z (disjoint_right.1 hsv hz),
    have : insert w ((s ∪ v) \ u) ∈ 𝒜,
    { refine mem_of_mem_compression hw𝒜' ‹_› _,
      rintro rfl,
      refine eq_empty_of_forall_not_mem (λ a ha, _),
      obtain ⟨b, hb, -⟩ := huv a ha,
      exact hb },
    have : (insert w ((s ∪ v) \ u) ∪ erase u w) \ erase v z ∈ 𝒜,
    { refine sup_sdiff_mem_of_mem_compression (by rwa hxy.eq) ((erase_subset _ _).trans ‹_›) _,
      rw ←sdiff_erase' (mem_union_left _ $ hus hwu),
      exact disjoint_sdiff },
    convert this,
    rw [insert_union_comm, insert_erase ‹w ∈ u›, sdiff_union_of_subset
      (hus.trans $ subset_union_left _ _), sdiff_erase' (mem_union_right _ ‹z ∈ v›),
      hsv.finset_union_sdiff_cancel_right] },
  -- If `w ∉ u`, we contradict `m` again
  rw [mem_sdiff, ←not_imp, not_not] at hwB,
  apply m w (hwu ∘ hwB ∘ mem_union_left _),
  have : (insert w ((s ∪ v) \ u) ∪ u) \ v ∈ 𝒜 := sup_sdiff_mem_of_mem_compression
    ‹insert w ((s ∪ v) \ u) ∈ 𝒜'› ‹_› (disjoint_insert_right.2 ⟨‹_›, disjoint_sdiff⟩),
  convert this,
  rw [insert_union, sdiff_union_of_subset (hus.trans $ subset_union_left _ _),
    insert_sdiff_of_not_mem _ (hwu ∘ hwB ∘ mem_union_right _), hsv.finset_union_sdiff_cancel_right],
end

end uv
