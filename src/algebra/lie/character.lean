/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.abelian
import algebra.lie.solvable
import linear_algebra.dual

/-!
# Characters of Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A character of a Lie algebra `L` over a commutative ring `R` is a morphism of Lie algebras `L → R`,
where `R` is regarded as a Lie algebra over itself via the ring commutator. For an Abelian Lie
algebra (e.g., a Cartan subalgebra of a semisimple Lie algebra) a character is just a linear form.

## Main definitions

  * `lie_algebra.lie_character`
  * `lie_algebra.lie_character_equiv_linear_dual`

## Tags

lie algebra, lie character
-/

universes u v w w₁

namespace lie_algebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

/-- A character of a Lie algebra is a morphism to the scalars. -/
abbreviation lie_character := L →ₗ⁅R⁆ R

variables {R L}

@[simp] lemma lie_character_apply_lie (χ : lie_character R L) (x y : L) : χ ⁅x, y⁆ = 0 :=
by rw [lie_hom.map_lie, lie_ring.of_associative_ring_bracket, mul_comm, sub_self]

lemma lie_character_apply_of_mem_derived
  (χ : lie_character R L) {x : L} (h : x ∈ derived_series R L 1) : χ x = 0 :=
begin
  rw [derived_series_def, derived_series_of_ideal_succ, derived_series_of_ideal_zero,
    ← lie_submodule.mem_coe_submodule, lie_submodule.lie_ideal_oper_eq_linear_span] at h,
  apply submodule.span_induction h,
  { rintros y ⟨⟨z, hz⟩, ⟨⟨w, hw⟩, rfl⟩⟩, apply lie_character_apply_lie, },
  { exact χ.map_zero, },
  { intros y z hy hz, rw [lie_hom.map_add, hy, hz, add_zero], },
  { intros t y hy, rw [lie_hom.map_smul, hy, smul_zero], },
end

/-- For an Abelian Lie algebra, characters are just linear forms. -/
@[simps] def lie_character_equiv_linear_dual [is_lie_abelian L] :
  lie_character R L ≃ module.dual R L :=
{ to_fun    := λ χ, (χ : L →ₗ[R] R),
  inv_fun   := λ ψ,
  { map_lie' := λ x y, by
    rw [lie_module.is_trivial.trivial, lie_ring.of_associative_ring_bracket, mul_comm, sub_self,
      linear_map.to_fun_eq_coe, linear_map.map_zero],
    .. ψ, },
  left_inv  := λ χ, by { ext, refl, },
  right_inv := λ ψ, by { ext, refl, }, }

end lie_algebra
