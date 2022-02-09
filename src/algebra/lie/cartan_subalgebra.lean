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

lemma mem_normalizer_iff' (x : L) : x ∈ H.normalizer ↔ ∀ (y : L), (y ∈ H) → ⁅y, x⁆ ∈ H :=
forall_congr (λ y, forall_congr (λ hy, by rw [← lie_skew, H.neg_mem_iff]))

lemma le_normalizer : H ≤ H.normalizer :=
λ x hx, show ∀ (y : L), y ∈ H → ⁅x,y⁆ ∈ H, from λ y, H.lie_mem hx

variables {H}

/-- A Lie subalgebra is an ideal of its normalizer. -/
lemma ideal_in_normalizer : ∀ {x y : L}, x ∈ H.normalizer → y ∈ H → ⁅x,y⁆ ∈ H :=
λ x y h, h y

/-- A Lie subalgebra `H` is an ideal of any Lie subalgebra `K` containing `H` and contained in the
normalizer of `H`. -/
lemma exists_nested_lie_ideal_of_le_normalizer
  {K : lie_subalgebra R L} (h₁ : H ≤ K) (h₂ : K ≤ H.normalizer) :
  ∃ (I : lie_ideal R K), (I : lie_subalgebra R K) = of_le h₁ :=
begin
  rw exists_nested_lie_ideal_coe_eq_iff,
  exact λ x y hx hy, ideal_in_normalizer (h₂ hx) hy,
end

/-- The normalizer of a Lie subalgebra `H` is the maximal Lie subalgebra in which `H` is a Lie
ideal. -/
lemma le_normalizer_of_ideal {N : lie_subalgebra R L}
  (h : ∀ (x y : L), x ∈ N → y ∈ H → ⁅x,y⁆ ∈ H) : N ≤ H.normalizer :=
λ x hx y, h x y hx

lemma normalizer_eq_self_iff :
  H.normalizer = H ↔ (lie_module.max_triv_submodule R H $ L ⧸ H.to_lie_submodule) = ⊥ :=
begin
  rw lie_submodule.eq_bot_iff,
  refine ⟨λ h, _, λ h, le_antisymm (λ x hx, _) H.le_normalizer⟩,
  { rintros ⟨x⟩ hx,
    suffices : x ∈ H, by simpa,
    rw [← h, H.mem_normalizer_iff'],
    intros y hy,
    replace hx : ⁅_, lie_submodule.quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩,
    rwa [← lie_module_hom.map_lie, lie_submodule.quotient.mk_eq_zero] at hx, },
  { let y := lie_submodule.quotient.mk' H.to_lie_submodule x,
    have hy : y ∈ lie_module.max_triv_submodule R H (L ⧸ H.to_lie_submodule),
    { rintros ⟨z, hz⟩,
      rw [← lie_module_hom.map_lie, lie_submodule.quotient.mk_eq_zero, coe_bracket_of_module,
        submodule.coe_mk, mem_to_lie_submodule],
      exact (H.mem_normalizer_iff' x).mp hx z hz, },
    simpa using h y hy, },
end

variables (H)

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class is_cartan_subalgebra : Prop :=
(nilpotent        : lie_algebra.is_nilpotent R H)
(self_normalizing : H.normalizer = H)

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
