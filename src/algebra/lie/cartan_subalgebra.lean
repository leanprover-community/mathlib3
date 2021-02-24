/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `lie_subalgebra.normalizer`
  * `lie_subalgebra.le_normalizer_of_ideal`
  * `lie_subalgebra.is_cartan_subalgebra`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/

universes u v w w₁ w₂

variables {R : Type u} {L : Type v}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] (H : lie_subalgebra R L)

namespace lie_subalgebra

/-- The normalizer of a Lie subalgebra `H` is the set of elements of the Lie algebra whose bracket
with any element of `H` lies in `H`. It is the Lie algebra equivalent of the group-theoretic
normalizer (see `subgroup.normalizer`) and is an idealizer in the sense of abstract algebra. -/
def normalizer : lie_subalgebra R L :=
{ carrier   := { x : L | ∀ (y : L), (y ∈ H) → ⁅x, y⁆ ∈ H },
  zero_mem' := λ y hy, by { rw zero_lie y, exact H.zero_mem, },
  add_mem'  := λ z₁ z₂ h₁ h₂ y hy, by { rw add_lie, exact H.add_mem (h₁ y hy) (h₂ y hy), },
  smul_mem' := λ t y hy z hz, by { rw smul_lie, exact H.smul_mem t (hy z hz), },
  lie_mem'  := λ z₁ z₂ h₁ h₂ y hy, by
    { rw lie_lie, exact H.sub_mem (h₁ _ (h₂ y hy)) (h₂ _ (h₁ y hy)), }, }

lemma mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ (y : L), (y ∈ H) → ⁅x, y⁆ ∈ H := iff.rfl

lemma le_normalizer : H ≤ H.normalizer :=
begin
  rw le_def, intros x hx,
  simp only [submodule.mem_coe, mem_coe_submodule, coe_coe, mem_normalizer_iff] at ⊢ hx,
  intros y, exact H.lie_mem hx,
end

/-- A Lie subalgebra is an ideal of its normalizer. -/
lemma ideal_in_normalizer : ∀ (x y : L), x ∈ H.normalizer → y ∈ H → ⁅x,y⁆ ∈ H :=
begin
  simp only [mem_normalizer_iff],
  intros x y h, exact h y,
end

/-- The normalizer of a Lie subalgebra `H` is the maximal Lie subalgebra in which `H` is a Lie
ideal. -/
lemma le_normalizer_of_ideal {N : lie_subalgebra R L}
  (h : ∀ (x y : L), x ∈ N → y ∈ H → ⁅x,y⁆ ∈ H) : N ≤ H.normalizer :=
begin
  intros x hx,
  rw mem_normalizer_iff,
  exact λ y, h x y hx,
end

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class is_cartan_subalgebra :=
(nilpotent : lie_algebra.is_nilpotent R H)
(self_normalizing : H.normalizer = H)

end lie_subalgebra

@[simp] lemma lie_ideal.normalizer_eq_top {R : Type u} {L : Type v}
  [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) :
  (I : lie_subalgebra R L).normalizer = ⊤ :=
begin
  ext x, simp only [lie_subalgebra.mem_normalizer_iff, lie_subalgebra.mem_top, iff_true],
  intros y hy, exact I.lie_mem hy,
end

open lie_ideal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance lie_algebra.top_is_cartan_subalgebra_of_nilpotent [lie_algebra.is_nilpotent R L] :
  lie_subalgebra.is_cartan_subalgebra ⊤ :=
{ nilpotent        :=
    by { rwa lie_algebra.nilpotent_iff_equiv_nilpotent lie_subalgebra.top_equiv_self, },
  self_normalizing :=
    by { rw [← top_coe_lie_subalgebra, normalizer_eq_top, top_coe_lie_subalgebra], }, }
