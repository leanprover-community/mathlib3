/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import data.finset.prod

/-!
# fintype instance for the product of two fintypes.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}

open finset function

namespace set
variables {s t : set α}

lemma to_finset_prod (s : set α) (t : set β) [fintype s] [fintype t] [fintype (s ×ˢ t)] :
  (s ×ˢ t).to_finset = s.to_finset ×ˢ t.to_finset :=
by { ext, simp }

lemma to_finset_off_diag {s : set α} [decidable_eq α] [fintype s] [fintype s.off_diag] :
  s.off_diag.to_finset = s.to_finset.off_diag :=
finset.ext $ by simp

end set

instance (α β : Type*) [fintype α] [fintype β] : fintype (α × β) :=
⟨univ ×ˢ univ, λ ⟨a, b⟩, by simp⟩

@[simp] lemma finset.univ_product_univ {α β : Type*} [fintype α] [fintype β] :
  (univ : finset α) ×ˢ (univ : finset β) = univ :=
rfl

@[simp] theorem fintype.card_prod (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α × β) = fintype.card α * fintype.card β :=
card_product _ _

section
open_locale classical

@[simp] lemma infinite_prod :
  infinite (α × β) ↔ infinite α ∧ nonempty β ∨ nonempty α ∧ infinite β :=
begin
  refine ⟨λ H, _, λ H, H.elim (and_imp.2 $ @prod.infinite_of_left α β)
    (and_imp.2 $ @prod.infinite_of_right α β)⟩,
  rw and.comm, contrapose! H, introI H',
  rcases infinite.nonempty (α × β) with ⟨a, b⟩,
  haveI := fintype_of_not_infinite (H.1 ⟨b⟩), haveI := fintype_of_not_infinite (H.2 ⟨a⟩),
  exact H'.false
end

instance pi.infinite_of_left {ι : Sort*} {π : ι → Sort*} [∀ i, nontrivial $ π i]
  [infinite ι] : infinite (Π i : ι, π i) :=
begin
  choose m n hm using λ i, exists_pair_ne (π i),
  refine infinite.of_injective (λ i, m.update i (n i)) (λ x y h, not_not.1 $ λ hne, _),
  simp_rw [update_eq_iff, update_noteq hne] at h,
  exact (hm x h.1.symm).elim,
end

/-- If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` is infinite. -/
lemma pi.infinite_of_exists_right {ι : Type*} {π : ι → Type*} (i : ι)
  [infinite $ π i] [∀ i, nonempty $ π i] :
  infinite (Π i : ι, π i) :=
let ⟨m⟩ := @pi.nonempty ι π _ in infinite.of_injective _ (update_injective m i)

/-- See `pi.infinite_of_exists_right` for the case that only one `π i` is infinite. -/
instance pi.infinite_of_right {ι : Sort*} {π : ι → Sort*} [∀ i, infinite $ π i] [nonempty ι] :
  infinite (Π i : ι, π i) :=
pi.infinite_of_exists_right (classical.arbitrary ι)

/-- Non-dependent version of `pi.infinite_of_left`. -/
instance function.infinite_of_left {ι π : Sort*} [nontrivial π]
  [infinite ι] : infinite (ι → π) :=
pi.infinite_of_left

/-- Non-dependent version of `pi.infinite_of_exists_right` and `pi.infinite_of_right`. -/
instance function.infinite_of_right {ι π : Sort*} [infinite π] [nonempty ι] :
  infinite (ι → π) :=
pi.infinite_of_right

end
