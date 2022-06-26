/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.set_family.shadow
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

local attribute [instance] decidable_eq_of_decidable_le

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

/-- If `A` is not in the original family but is in the compressed family, then `A` has been
compressed, and its original was in the original family. -/
lemma compress_moved (h₁ : A ∈ 𝓒 U V 𝒜) (h₂ : A ∉ 𝒜) :
  U ⊆ A ∧ disjoint V A ∧ (A ∪ V) \ U ∈ 𝒜 :=
begin
  rw mem_compression at h₁,
  obtain _ | ⟨_, B, H, HB⟩ := h₁,
  { tauto },
  { unfold compress at HB,
    split_ifs at HB,
    { rw ← HB at *,
      refine ⟨_, disjoint_sdiff, _⟩,
        have : disjoint U V := disjoint_of_subset_right h.2 h.1,
        rw sup_sdiff,
        rw sdiff_eq_self_of_disjoint this,
        apply subset_union_right _ _,
      rwa [sdiff_union_of_subset, sup_sdiff_right_self,
            sdiff_eq_self_of_disjoint h.1.symm],
      apply trans h.2 (subset_union_left _ _) },
    { rw HB at *, tauto } }
end

lemma sdiff_sdiff {A B C : finset α} (h : C ⊆ A) : A \ (B \ C) = A \ B ∪ C :=
begin
  ext1 i,
  simp only [mem_union, not_and, mem_sdiff],
  push_neg,
  refine ⟨_, _⟩,
  rintro ⟨iA, iBC⟩,
  by_cases (i ∈ C),
  right, exact h,
  left,
  refine ⟨iA, mt iBC h⟩,
  rintro (⟨iA, niB⟩ | iC),
  refine ⟨iA, λ iB, (niB iB).elim⟩,
  refine ⟨h iC, λ _, iC⟩,
end

/-- Here's the key fact about compression for Kruskal-Katona. If, for all `x ∈ U` there is
`y ∈ V` such that `𝒜` is `(U-x,V-y)`-compressed, then UV-compression will reduce the size of the
shadow of `𝒜`. -/
theorem card_shadow_compression_le {U V : finset α}
  (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜) (hvu : V = ∅ → U = ∅) :
  (∂ (𝓒 U V 𝒜)).card ≤ (∂𝒜).card :=
begin
  set 𝒜' := 𝓒 U V 𝒜,
  suffices : (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
  { suffices z : (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜').card,
    { rwa [sdiff_union_inter, sdiff_union_inter] at z },
    rw [card_disjoint_union, card_disjoint_union, inter_comm],
    apply add_le_add_right ‹_›,
    any_goals { apply disjoint_sdiff_inter } },

  -- We'll define an injection ∂𝒜' \ ∂𝒜 → ∂𝒜 \ ∂𝒜'. First, let's prove
  -- a few facts about things in the domain:
  suffices q₁ : ∀ B ∈ ∂𝒜' \ ∂𝒜, U ⊆ B ∧ disjoint V B ∧ (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜',
  { apply card_le_card_of_inj_on (λ B, (B ∪ V) \ U) (λ B HB, (q₁ B HB).2.2),
    intros B₁ HB₁ B₂ HB₂ k,
    exact sup_sdiff_inj_on _ _ ⟨(q₁ B₁ HB₁).2.1, (q₁ B₁ HB₁).1⟩ ⟨(q₁ B₂ HB₂).2.1, (q₁ B₂ HB₂).1⟩ k },
  intros B HB,
  obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
  -- This is gonna be useful a couple of times so let's name it.
  have m: ∀ y ∉ B, insert y B ∉ 𝒜 := λ y H a, k' (mem_shadow_iff_insert_mem.2 ⟨y, H, a⟩),
  rcases mem_shadow_iff_insert_mem.1 k with ⟨x, _, _⟩,
  have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
  have : disjoint V B := (disjoint_insert_right.1 q.2.1).2,
  have dVU : disjoint V U := disjoint_of_subset_right q.1 q.2.1,
  have : V \ U = V := sdiff_eq_self_of_disjoint ‹disjoint V U›,
  -- The first key part is that x ∉ U
  have : x ∉ U,
  { intro a,
    rcases h₁ x ‹x ∈ U› with ⟨y, Hy, xy_comp⟩,
    -- If `x ∈ U`, we can get `y ∈ V` so that `𝒜` is `(U-x,V-y)`-compressed
    apply m y (disjoint_left.1 ‹disjoint V B› Hy),
    -- and we'll use this `y` to contradict `m`.
    rw is_compressed at xy_comp,
    have : (insert x B ∪ V) \ U ∈ 𝓒 (erase U x) (erase V y) 𝒜,
      rw xy_comp, exact q.2.2,
    -- So we'd like to show insert y B ∈ 𝒜.
    -- We do this by showing the below
    have : ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y ∈ 𝒜,
      apply sup_sdiff_mem_of_mem_compression this _,
        apply disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff,
      rw [union_sdiff_distrib, ‹V \ U = V›],
      apply subset.trans (erase_subset _ _) (subset_union_right _ _),
    -- and then arguing that it's the same
    suffices : ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y = insert y B,
      rwa ← this,
    have : x ∉ B ∪ V := not_mem_union.2 ⟨‹x ∉ B›, disjoint_right.1 ‹disjoint V U› a⟩,
    have : erase U x ⊆ insert x B ∪ V := trans (erase_subset x _)
                                          (trans q.1 (subset_union_left _ V)),
    -- which is just a pain.
    rw [← sdiff_sdiff ‹U.erase x ⊆ insert x B ∪ V›, finset.sdiff_erase ‹x ∈ U›,
        sdiff_singleton_eq_erase, insert_union, erase_insert ‹x ∉ B ∪ V›, union_sdiff_distrib,
        sdiff_erase ‹y ∈ V›, sdiff_eq_self_of_disjoint, union_comm, insert_eq],
    rw [disjoint.comm],
    apply disjoint_of_subset_left (erase_subset _ _) ‹disjoint V B› },
  -- Now that that's done, it's immediate that U ⊆ B
  have : U ⊆ B, rw [← erase_eq_of_not_mem ‹x ∉ U›, ← subset_insert_iff], exact q.1,
  -- and we already had that V and B are disjoint
  refine ⟨‹_›, ‹_›, _⟩,
  -- so it only remains to get (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜'
  rw mem_sdiff,
  have : x ∉ V := disjoint_right.1 q.2.1 (mem_insert_self _ _),
  split,
    -- (B ∪ V) \ U ∈ ∂𝒜 is pretty direct:
  { rw mem_shadow_iff_insert_mem,
    refine ⟨x, _, _⟩,
    { simp [mem_sdiff, mem_union], tauto! },
    convert q.2.2,
    rw [insert_eq, insert_eq, union_assoc, union_sdiff_distrib _ (B ∪ V),
        sdiff_eq_self_of_disjoint (disjoint_singleton_left.2 ‹x ∉ U›)] },
  -- For (B ∪ V) \ U ∉ ∂𝒜', we split up based on w ∈ U
  rw mem_shadow_iff_insert_mem,
  rintro ⟨w, hwB, hw𝒜'⟩,
  by_cases (w ∈ U),
    -- If w ∈ U, we find z ∈ V, and contradict m again
  { rcases h₁ w ‹w ∈ U› with ⟨z, Hz, xy_comp⟩,
    apply m z (disjoint_left.1 ‹disjoint V B› Hz),
    have : insert w ((B ∪ V) \ U) ∈ 𝒜,
    { refine mem_of_mem_compression hw𝒜' (subset.trans _ (subset_insert _ _)) hvu,
      rw union_sdiff_distrib, rw ‹V \ U = V›, apply subset_union_right },
    have : (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z ∈ 𝒜,
    { refine sup_sdiff_mem_of_mem_compression _ _ _,
          rw is_compressed at xy_comp, rwa xy_comp,
        apply subset.trans (erase_subset _ _),
        apply subset.trans _ (subset_insert _ _),
        rw [union_sdiff_distrib, ‹V \ U = V›], apply subset_union_right,
      rw disjoint_insert_right, split, apply not_mem_erase,
      apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_sdiff },
    have : (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = insert z B,
    { rw [insert_union, ← union_insert, insert_erase h,
        sdiff_union_of_subset (subset.trans ‹U ⊆ B› (subset_union_left _ _)),
        union_sdiff_distrib, sdiff_eq_self_of_disjoint
        (disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm),
        ← sdiff_singleton_eq_erase, sdiff_sdiff_self_left,
        inter_singleton_of_mem Hz, union_comm],
      refl },
    rwa ← this },
  -- If w ∉ U, we contradict m again
  rw [mem_sdiff, ← not_imp, not_not] at hwB,
  have : w ∉ V := h ∘ hwB ∘ mem_union_right _,
  have : w ∉ B := h ∘ hwB ∘ mem_union_left _,
  apply m w this,

  have : (insert w ((B ∪ V) \ U) ∪ U) \ V ∈ 𝒜,
    refine sup_sdiff_mem_of_mem_compression ‹insert w ((B ∪ V) \ U) ∈ 𝒜'›
            (trans _ (subset_insert _ _)) _,
      rw [union_sdiff_distrib, ‹V \ U = V›], apply subset_union_right,
      rw disjoint_insert_right, exact ⟨‹_›, disjoint_sdiff⟩,
  convert this, rw [insert_union, sdiff_union_of_subset (trans ‹U ⊆ B› (subset_union_left _ _)),
                    ← insert_union, union_sdiff_self], symmetry,
  rw [_root_.sdiff_eq_self_iff_disjoint],
  exact disjoint_insert_right.2 ⟨‹w ∉ V›, ‹disjoint V B›⟩,
end

end uv
