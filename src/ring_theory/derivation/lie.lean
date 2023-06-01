/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import algebra.lie.of_associative
import ring_theory.derivation.basic

/-!
# Results

- `derivation.lie_algebra`: The `R`-derivations from `A` to `A` form an lie algebra over `R`.

-/

namespace derivation

variables {R : Type*} [comm_ring R]
variables {A : Type*} [comm_ring A] [algebra R A]
variables (D : derivation R A A) {D1 D2 : derivation R A A} (a : A)

section lie_structures

/-! # Lie structures -/

/-- The commutator of derivations is again a derivation. -/
instance : has_bracket (derivation R A A) (derivation R A A) :=
⟨λ D1 D2, mk' (⁅(D1 : module.End R A), (D2 : module.End R A)⁆) $ λ a b,
  by { simp only [ring.lie_def, map_add, algebra.id.smul_eq_mul, linear_map.mul_apply, leibniz,
    coe_fn_coe, linear_map.sub_apply], ring, }⟩

@[simp] lemma commutator_coe_linear_map :
  ↑⁅D1, D2⁆ = ⁅(D1 : module.End R A), (D2 : module.End R A)⁆ := rfl

lemma commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) := rfl

instance : lie_ring (derivation R A A) :=
{ add_lie     := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_add], ring, },
  lie_add     := λ d e f, by { ext a, simp only [commutator_apply, add_apply, map_add], ring, },
  lie_self    := λ d, by { ext a, simp only [commutator_apply, add_apply, map_add], ring_nf, },
  leibniz_lie := λ d e f,
    by { ext a, simp only [commutator_apply, add_apply, sub_apply, map_sub], ring, } }

instance : lie_algebra R (derivation R A A) :=
{ lie_smul := λ r d e, by { ext a, simp only [commutator_apply, map_smul, smul_sub, smul_apply]},
  ..derivation.module }

end lie_structures

end derivation
