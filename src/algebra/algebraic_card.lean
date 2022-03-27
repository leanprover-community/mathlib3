/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import analysis.complex.basic
import data.complex.cardinality
import data.polynomial.cardinal
import ring_theory.algebraic
import topology.bases

/-!
### Cardinality of algebraic numbers

In this file, we prove the following result: the cardinality of algebraic numbers under an R-algebra
that's also a T1 topological space with basis s is at most `# polynomial R * # s`. From this, we
deduce that real and complex algebraic numbers have cardinality `ω`.

Although this can be used to prove transcendental numbers exist, a more direct proof is given by
`liouville.is_transcendental`.
-/

open cardinal polynomial topological_space
open_locale cardinal

theorem algebraic_card (R) {A} [comm_ring R] [is_domain R] [comm_ring A] [is_domain A] [algebra R A]
  [no_zero_smul_divisors R A] [topological_space A] [t1_space A] {s : set (set A)}
  (hs : is_topological_basis s) : #{x : A | is_algebraic R x} ≤ #(polynomial R) * #s :=
begin
  classical,
  apply @mk_le_of_surjective (polynomial R × s) {x : A | is_algebraic R x} (λ ⟨p, t, ht⟩,
    if hr : p ≠ 0 ∧ ∃ x : A, x ∈ t ∩ p.root_set A
    then ⟨classical.some hr.2, p, hr.1, (mem_root_set_iff hr.1 _).1 (classical.some_spec hr.2).2⟩
    else ⟨0, is_algebraic_zero⟩),
  rintro ⟨x, p, hp, he⟩,
  suffices : ∃ t ∈ s, t ∩ p.root_set A = {x},
  { rcases this with ⟨t, hts, ht⟩,
    have hx := set.mem_singleton x,
    have H : ¬p = 0 ∧ ∃ x, x ∈ t ∩ p.root_set A := ⟨hp, x, by rwa ←ht at hx⟩,
    use [p, t, hts],
    simp_rw dif_pos H,
    simpa [ht, set.mem_singleton_iff] using classical.some_spec H.2 },
  { have H : is_open (p.root_set A \ {x})ᶜ := begin
      rw is_open_compl_iff,
      refine set.finite.is_closed (set.finite.inter_of_left _ _),
      exact p.root_set_finite A
    end,
    rw [compl_sdiff, hs.is_open_iff] at H,
    rcases H x (set.mem_union_right _ (set.mem_singleton x)) with ⟨t, ht, hts, hxt⟩,
    use [t, ht],
    rw set.eq_singleton_iff_unique_mem,
    use [hts, (mem_root_set_iff hp _).2 he],
    rintros y ⟨hyt, hy⟩,
    cases hxt hyt with hy' hy',
    { exact (hy' hy).elim },
    { exact hy' } }
end

theorem algebraic_card' (R) {A} [comm_ring R] [is_domain R] [comm_ring A] [is_domain A]
  [algebra R A] [no_zero_smul_divisors R A] [topological_space A] [t1_space A] {s : set (set A)}
  (hs : is_topological_basis s) : #{x : A | is_algebraic R x} ≤ max (#R) ω * #s :=
(algebraic_card R hs).trans (mul_le_mul_right' polynomial.cardinal_mk_le_max _)

theorem algebraic_card_of_second_countable (R A : Type*) [comm_ring R] [is_domain R] [comm_ring A]
  [is_domain A] [algebra R A] [no_zero_smul_divisors R A] [topological_space A] [t1_space A]
  [second_countable_topology A] : #{x : A | is_algebraic R x} ≤ max (#R) ω :=
begin
  rcases exists_countable_basis A with ⟨s, hs', _, hs⟩,
  apply ((algebraic_card' R hs).trans ((mul_le_mul_left' ((mk_set_le_omega s).2 hs') _))).trans,
  rw mul_omega_eq (le_max_right _ _)
end

theorem omega_le_algebraic_card_of_char_zero (R A : Type*) [comm_ring R] [is_domain R] [ring A]
  [algebra R A] [char_zero A] : ω ≤ #{x : A | is_algebraic R x} :=
@mk_le_of_injective (ulift ℕ) {x : A | is_algebraic R x} (λ n, ⟨_, is_algebraic_nat n.down⟩)
  (λ m n hmn, by simpa using hmn)

namespace real

theorem is_algebraic_rat : ∀ n : ℚ, is_algebraic ℚ (n : ℝ) :=
is_algebraic_algebra_map

theorem is_algebraic_nat (n : ℕ) : is_algebraic ℚ (n : ℝ) :=
by { rw ←rat.cast_coe_nat n, exact is_algebraic_rat n }

@[simp] theorem algebraic_card : #{x : ℝ | is_algebraic ℚ x} = ω :=
((algebraic_card_of_second_countable ℚ ℝ).trans (by rw [mk_rat, max_self])).antisymm
  (omega_le_algebraic_card_of_char_zero ℚ ℝ)

end real

namespace complex

theorem is_algebraic_rat (n : ℚ) : is_algebraic ℚ (n : ℂ) :=
by { rw ←complex.of_real_rat_cast, exact is_algebraic_algebra_map n }

theorem is_algebraic_nat (n : ℕ) : is_algebraic ℚ (n : ℂ) :=
by { rw ←rat.cast_coe_nat n, exact is_algebraic_rat n }

@[simp] theorem algebraic_card : #{x : ℂ | is_algebraic ℚ x} = ω :=
((algebraic_card_of_second_countable ℚ ℂ).trans (by rw [mk_rat, max_self])).antisymm
  (omega_le_algebraic_card_of_char_zero ℚ ℂ)

end complex
