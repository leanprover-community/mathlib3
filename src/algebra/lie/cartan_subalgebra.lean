/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent
import algebra.lie.centralizer

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `lie_subalgebra.is_cartan_subalgebra`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/

universes u v w w₁ w₂

variables {R : Type u} {L : Type v}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] (H : lie_subalgebra R L)

namespace lie_subalgebra

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class is_cartan_subalgebra : Prop :=
(nilpotent        : lie_algebra.is_nilpotent R H)
(self_normalizing : H.normalizer = H)

instance [is_cartan_subalgebra H] : lie_algebra.is_nilpotent R H := is_cartan_subalgebra.nilpotent

@[simp] lemma centralizer_eq_self_of_is_cartan_subalgebra
  (H : lie_subalgebra R L) [H.is_cartan_subalgebra] :
  H.to_lie_submodule.centralizer = H.to_lie_submodule :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, lie_subalgebra.coe_centralizer_eq_normalizer,
  lie_subalgebra.is_cartan_subalgebra.self_normalizing, lie_subalgebra.coe_to_lie_submodule]

end lie_subalgebra

@[simp] lemma lie_ideal.normalizer_eq_top {R : Type u} {L : Type v}
  [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) :
  (I : lie_subalgebra R L).normalizer = ⊤ :=
begin
  ext x,
  simpa only [lie_subalgebra.mem_normalizer_iff, lie_subalgebra.mem_top, iff_true]
    using λ y hy, I.lie_mem hy
end

open lie_ideal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance lie_algebra.top_is_cartan_subalgebra_of_nilpotent [lie_algebra.is_nilpotent R L] :
  lie_subalgebra.is_cartan_subalgebra (⊤ : lie_subalgebra R L) :=
{ nilpotent        := infer_instance,
  self_normalizing :=
    by { rw [← top_coe_lie_subalgebra, normalizer_eq_top, top_coe_lie_subalgebra], }, }
