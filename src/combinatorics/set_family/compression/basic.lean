/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.card

/-!
# General theory of set family compressions

This file defines a generic compression. The idea of a compression is to turn a finite set into
another finite set of same cardinality such that:
* This operation is idempotent.
* The compression has the same cardinality as the original set.
* The compression is smaller than the original set according to a measure of interest (eg. number of
  shattered sets for down-compression, or size of the shadow for UV-compression).

Here we consider compressions that move elements along an idempotent function (ie. "compress" them).
To preserve cardinality, we mustn't move element whose image is already there.

# Main declarations

* `finset.compression`:  Generic compression.
* `finset.compression_idem`: Compression is idempotent.
* `finset.card_compression`: Compression preserves cardinality.
-/

namespace finset
variables {α : Type*} [decidable_eq α] {f : α → α} {s : finset α} {a : α}

/-- To compress a family along a function `f`, we apply `f` each of its elements, except that we
don't want to reduce the cardinality, so we keep all elements whose image is already present. This
is meant to be used for idempotent `f`. -/
def compression (f : α → α) (s : finset α) : finset α :=
(s.filter $ λ a, f a ∈ s).disj_union ((s.image f).filter $ λ a, a ∉ s) $
  λ a h₁ h₂, (mem_filter.1 h₂).2 (mem_filter.1 h₁).1

@[simp] lemma compression_id : compression (id : α → α) = id := funext $ by simp [compression]

@[simp] lemma mem_compression :
  a ∈ s.compression f ↔ a ∈ s ∧ f a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, f b = a :=
by simp_rw [compression, mem_disj_union, mem_filter, mem_image, and_comm (a ∉ s)]

lemma apply_mem_compression (hf : ∀ a, f (f a) = f a) (ha : a ∈ s) : f a ∈ s.compression f :=
by simpa only [mem_compression, hf, and_self, and_iff_left (⟨a, ha, rfl⟩ : ∃ b ∈ s, f b = f a)]
  using em (f a ∈ s)

-- This is a special case of `apply_mem_compression` once we have `compression_idem`.
lemma apply_mem_compression_of_mem_compression (hf : ∀ a, f (f a) = f a) :
  a ∈ s.compression f → f a ∈ s.compression f :=
begin
  simp_rw [mem_compression, hf],
  refine or.imp (λ h, ⟨h.2, h.2⟩) _,
  rintro ⟨ha, b, hb, rfl⟩,
  simp_rw hf,
  exact ⟨ha, b, hb, rfl⟩,
end

lemma compression_idem (hf : ∀ a, f (f a) = f a) :
  (s.compression f).compression f = s.compression f :=
begin
  ext,
  refine mem_compression.trans ⟨_, λ h, or.inl ⟨h, apply_mem_compression_of_mem_compression hf h⟩⟩,
  rintro (h | ⟨ha, b, hb, rfl⟩),
  { exact h.1 },
  { cases ha (apply_mem_compression_of_mem_compression hf hb) }
end

lemma card_compression (hf : {a | f a ≠ a}.inj_on f) : (s.compression f).card = s.card :=
begin
  rw [compression, card_disj_union, image_filter, card_image_of_inj_on (hf.mono $ λ a ha, _),
    ←card_disjoint_union, filter_union_filter_neg_eq],
  { exact disjoint_filter_filter_neg _ _ },
  rw [mem_coe, mem_filter] at ha,
  exact (ne_of_mem_of_not_mem ha.1 ha.2).symm,
end

end finset
