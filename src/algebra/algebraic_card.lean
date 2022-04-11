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

open cardinal polynomial topological_space
open_locale cardinal

lemma algebraic_cardinal_mk_le_mul
  {R A : Type*} [comm_ring R] [is_domain R] [comm_ring A] [is_domain A] [algebra R A]
  [no_zero_smul_divisors R A] : #{x : A | is_algebraic R x} ≤ #(polynomial R) * ω :=
begin
  let S := {x : A | is_algebraic R x},
  let g : S → polynomial R := λ x, classical.some x.2,
  refine cardinal.mk_le_mk_mul_of_mk_preimage_le ω g (λ f, _),
  suffices : fintype (g ⁻¹' {f}),
  { exact @mk_le_omega _ (@fintype.encodable _ this) },
  by_cases hf : f = 0,
  { rw hf,
    have key : g ⁻¹' {0} = ∅,
    { exact set.eq_empty_iff_forall_not_mem.mpr (λ x, (classical.some_spec x.2).1), },
    rw key,
    exact set.fintype_empty },
  let h : g ⁻¹' {f} → f.root_set A := λ x, ⟨x.1.1, begin
    refine (mem_root_set_iff hf x.1.1).mpr _,
    have key' : g x  = f := x.2,
    simp_rw ← key',
    exact (classical.some_spec x.1.2).2,
  end⟩,
  exact fintype.of_injective h (λ _ _, subtype.ext ∘ subtype.ext ∘ subtype.ext_iff.mp),
end

theorem algebraic_cardinal_mk_le_mul' (R) {A} [comm_ring R] [is_domain R] [comm_ring A]
  [is_domain A] [algebra R A] [no_zero_smul_divisors R A] [topological_space A] [t1_space A]
  {s : set (set A)} (hs : is_topological_basis s) : #{x : A | is_algebraic R x} ≤ max (#R) ω * #s :=
(algebraic_cardinal_mk_le_mul R hs).trans (mul_le_mul_right' polynomial.cardinal_mk_le_max _)

theorem omega_le_algebraic_cardinal_mk_of_char_zero (R A : Type*) [comm_ring R] [is_domain R]
  [ring A] [algebra R A] [char_zero A] : ω ≤ #{x : A | is_algebraic R x} :=
@mk_le_of_injective (ulift ℕ) {x : A | is_algebraic R x} (λ n, ⟨_, is_algebraic_nat n.down⟩)
  (λ m n hmn, by simpa using hmn)

@[simp] theorem real.algebraic_cardinal_mk : #{x : ℝ | is_algebraic ℚ x} = ω :=
((algebraic_cardinal_mk_le_mul ℚ ℝ).trans (by simp)).antisymm
  (omega_le_algebraic_card_of_char_zero ℚ ℝ)

@[simp] theorem complex.algebraic_cardinal_mk : #{x : ℂ | is_algebraic ℚ x} = ω :=
((algebraic_cardinal_mk_le_mul ℚ ℂ).trans (by simp)).antisymm
  (omega_le_algebraic_card_of_char_zero ℚ ℂ)
