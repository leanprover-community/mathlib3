/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import analysis.complex.basic
import data.real.cardinality
import data.polynomial.cardinal
import ring_theory.algebraic
import topology.bases

/-!
### Cardinality of algebraic numbers

In this file, we prove the following result: the cardinality of algebraic numbers under an R-algebra
that's also a T1 topological space with basis s is at most `# polynomial R * # s`. From this, we
deduce that real and complex algebraic numbers have cardinality `ω`, and in particular that a
trascendental number exists.
-/

open cardinal polynomial topological_space
open_locale cardinal

theorem algebraic_card (R) {A} [comm_ring R] [is_domain R] [ring A] [algebra R A]
  [topological_space A] [t1_space A] {s : set (set A)} (hs : is_topological_basis s) :
  #{x : A | is_algebraic R x} ≤ #(polynomial R) * #s :=
begin
  classical,
  apply @mk_le_of_surjective (polynomial R × s) {x : A | is_algebraic R x} (λ ⟨p, t, ht⟩,
    if hr : p ≠ 0 ∧ ∃ x : A, x ∈ t ∩ {x | aeval x p = 0}
    then ⟨classical.some hr.2, p, hr.1, (classical.some_spec hr.2).2⟩
    else ⟨0, is_algebraic_zero⟩),
  rintro ⟨x, p, hp, he⟩,
  suffices : ∃ t ∈ s, t ∩ {x : A | aeval x p = 0} = {x},
  { rcases this with ⟨t, hts, ht⟩,
    have hx := set.mem_singleton x,
    have H : ¬p = 0 ∧ ∃ x, x ∈ t ∩ {y | aeval y p = 0} := ⟨hp, x, by rwa ←ht at hx⟩,
    use [p, t, hts],
    simp_rw dif_pos H,
    simpa [ht, set.mem_singleton_iff] using classical.some_spec H.2 },
  { have H : is_open ({y : A | aeval y p = 0} \ {x})ᶜ := begin
      rw is_open_compl_iff,
      refine set.finite.is_closed (set.finite.inter_of_left _ _),
      sorry -- THIS SHOULD BE A THEOREM!
    end,
    rw [compl_sdiff, hs.is_open_iff] at H,
    rcases H x (set.mem_union_right _ (set.mem_singleton x)) with ⟨t, ht, hts, hxt⟩,
    use [t, ht],
    rw set.eq_singleton_iff_unique_mem,
    use [hts, he],
    rintros y ⟨hyt, hy⟩,
    cases hxt hyt with hy' hy',
    { exact (hy' hy).elim },
    { exact hy' } }
end

theorem algebraic_card' (R) {A} [comm_ring R] [is_domain R] [ring A] [algebra R A]
  [topological_space A] [t1_space A] {s : set (set A)} (hs : is_topological_basis s) :
  #{x : A | is_algebraic R x} ≤ max (#R) ω * #s :=
(algebraic_card R hs).trans (mul_le_mul_right' polynomial.cardinal_mk_le_max _)

theorem algebraic_card_of_second_countable (R A : Type*) [comm_ring R] [is_domain R] [ring A]
  [algebra R A] [topological_space A] [t1_space A] [second_countable_topology A] :
  #{x : A | is_algebraic R x} ≤ max (#R) ω :=
begin
  rcases exists_countable_basis A with ⟨s, hs', _, hs⟩,
  apply ((algebraic_card' R hs).trans ((mul_le_mul_left' ((mk_set_le_omega s).2 hs') _))).trans,
  rw mul_omega_eq (le_max_right _ _)
end

namespace real

theorem rat_is_algebraic : ∀ n : ℚ, is_algebraic ℚ (n : ℝ) :=
is_algebraic_algebra_map

theorem nat_is_algebraic (n : ℕ) : is_algebraic ℚ (n : ℝ) :=
by { rw ←rat.cast_coe_nat n, exact rat_is_algebraic n }

theorem algebraic_card : #{x : ℝ | is_algebraic ℚ x} = ω :=
begin
  apply le_antisymm,
  { apply (algebraic_card_of_second_countable ℚ ℝ).trans,
    rw [mk_rat, max_self] },
  { let g : ulift ℕ → {x : ℝ | is_algebraic ℚ x} := λ n, ⟨_, nat_is_algebraic n.down⟩,
    apply @mk_le_of_injective _ _ g (λ m n hmn, _),
    have := nat.cast_inj.1 (subtype.mk.inj hmn),
    apply_fun @ulift.up ℕ at this,
    rwa [ulift.up_down, ulift.up_down] at this }
end

/-- There exists a transcendental number. -/
theorem exists_transcendental : ∃ x : ℝ, transcendental ℚ x := begin
  show ∃ x : ℝ, ¬ is_algebraic ℚ x,
  by_contra' H : ∀ x : ℝ, x ∈ {x : ℝ | is_algebraic ℚ x},
  have := algebraic_card,
  rw [set.eq_univ_of_forall H, mk_univ, mk_real] at this,
  exact omega_lt_continuum.ne' this
end

end real

namespace complex

theorem rat_is_algebraic (n : ℚ) : is_algebraic ℚ (n : ℂ) :=
by { rw ←complex.of_real_rat_cast, exact is_algebraic_algebra_map n }

theorem nat_is_algebraic (n : ℕ) : is_algebraic ℚ (n : ℂ) :=
by { rw ←rat.cast_coe_nat n, exact rat_is_algebraic n }

theorem algebraic_card : #{x : ℂ | is_algebraic ℚ x} = ω :=
begin
  apply le_antisymm,
  { apply (algebraic_card_of_second_countable ℚ ℂ).trans,
    rw [mk_rat, max_self] },
  { let g : ulift ℕ → {x : ℂ | is_algebraic ℚ x} := λ n, ⟨_, nat_is_algebraic n.down⟩,
    apply @mk_le_of_injective _ _ g (λ m n hmn, _),
    have := nat.cast_inj.1 (subtype.mk.inj hmn),
    apply_fun @ulift.up ℕ at this,
    rwa [ulift.up_down, ulift.up_down] at this }
end

/-- There exists a transcendental number. -/
theorem exists_transcendental : ∃ x : ℂ, transcendental ℚ x := begin
  show ∃ x : ℂ, ¬ is_algebraic ℚ x,
  by_contra' H : ∀ x : ℂ, x ∈ {x : ℂ | is_algebraic ℚ x},
  have := algebraic_card,
  have mk_complex : #ℂ = 𝔠 := sorry, -- THIS SHOULD BE A THEOREM!
  rw [set.eq_univ_of_forall H, mk_univ, mk_complex] at this,
  exact omega_lt_continuum.ne' this
end

end complex
