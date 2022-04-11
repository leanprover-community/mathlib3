/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import analysis.complex.basic
import data.complex.cardinality
import data.polynomial.cardinal
import ring_theory.algebraic

/-!
### Cardinality of algebraic numbers

In this file, we prove the following result: the cardinality of algebraic numbers under an R-algebra
is at most `# polynomial R * ω`. From this, we deduce that real and complex algebraic numbers have
cardinality `ω`.

Although this can be used to prove transcendental numbers exist, a more direct proof is given by
`liouville.is_transcendental`.
-/

universes u v

open cardinal polynomial
open_locale cardinal

section

variables (R : Type u) (A : Type v) [comm_ring R] [is_domain R] [comm_ring A] [is_domain A]
  [algebra R A] [no_zero_smul_divisors R A]

theorem algebraic_cardinal_mk_lift_le_mul : cardinal.lift.{u v} (#{x : A | is_algebraic R x}) ≤
  cardinal.lift.{v u} (#(polynomial R)) * ω :=
begin
  let g : {x : A | is_algebraic R x} → polynomial R := λ x, classical.some x.2,
  apply cardinal.mk_le_mk_mul_of_mk_preimage_le g (λ f, _),
  suffices : fintype (g ⁻¹' {f}),
  { exact @mk_le_omega _ (@fintype.encodable _ this) },
  by_cases hf : f = 0,
  { rw hf,
    convert set.fintype_empty,
    exact set.eq_empty_iff_forall_not_mem.mpr (λ x, (classical.some_spec x.2).1) },
  let h : g ⁻¹' {f} → f.root_set A := λ x, ⟨x.1.1, (mem_root_set_iff hf x.1.1).mpr begin
    have key' : g x = f := x.2,
    simp_rw ← key',
    exact (classical.some_spec x.1.2).2
  end⟩,
  exact fintype.of_injective h (λ _ _, subtype.ext ∘ subtype.ext ∘ subtype.ext_iff.mp),
end

theorem algebraic_cardinal_mk_le_max : #{x : A | is_algebraic R x} ≤ max (#R) ω :=
(algebraic_cardinal_mk_le_mul R A).trans $ (mul_le_mul_right' cardinal_mk_le_max _).trans $
  by simp [le_total]

end

theorem omega_le_algebraic_cardinal_mk_of_char_zero (R A : Type*) [comm_ring R] [is_domain R]
  [ring A] [algebra R A] [char_zero A] : ω ≤ #{x : A | is_algebraic R x} :=
@mk_le_of_injective (ulift ℕ) {x : A | is_algebraic R x} (λ n, ⟨_, is_algebraic_nat n.down⟩)
  (λ m n hmn, by simpa using hmn)

@[simp] theorem real.algebraic_cardinal_mk : #{x : ℝ | is_algebraic ℚ x} = ω :=
((algebraic_cardinal_mk_le_mul ℚ ℝ).trans (by simp)).antisymm
  (omega_le_algebraic_cardinal_mk_of_char_zero ℚ ℝ)

@[simp] theorem complex.algebraic_cardinal_mk : #{x : ℂ | is_algebraic ℚ x} = ω :=
((algebraic_cardinal_mk_le_mul ℚ ℂ).trans (by simp)).antisymm
  (omega_le_algebraic_cardinal_mk_of_char_zero ℚ ℂ)
