/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.real.cardinality
import data.polynomial.cardinal
import data.rat.denumerable
import ring_theory.algebraic
import set_theory.cardinal_ordinal

/-!
### Cardinality of algebraic numbers

In this file, we prove that the set of the real algebraic numbers over `ℚ` has cardinality `ω`. We
do this by constructing a surjection from `polynomial ℚ × ℚ × ℚ` into this set. We deduce the
existence of a trascendental number.
-/

open cardinal polynomial
open_locale cardinal

theorem rat_is_algebraic : ∀ n : ℚ, is_algebraic ℚ (n : ℝ) :=
is_algebraic_algebra_map

theorem nat_is_algebraic (n : ℕ) : is_algebraic ℚ (n : ℝ) :=
by { rw ←rat.cast_coe_nat n, exact rat_is_algebraic n }

theorem algebraic_card : #{x : ℝ | is_algebraic ℚ x} = ω :=
begin
  apply le_antisymm,
  { classical,
    let f : polynomial ℚ × ℚ × ℚ → {x : ℝ | is_algebraic ℚ x} := λ ⟨p, q, r⟩,
      if hr : p ≠ 0 ∧ ∃ x : ℝ, x ∈ set.Ioo (q : ℝ) r ∧ aeval x p = 0
      then ⟨classical.some hr.2, p, hr.1, (classical.some_spec hr.2).2⟩
      else ⟨0, zero_is_algebraic ℚ⟩,
    suffices : function.surjective f,
    { apply (mk_le_of_surjective this).trans,
      simp [mk_rat],
      rw ←max_eq_right (@mk_le_omega ℚ _),
      exact cardinal_mk_le_max },
    intro x,
    rcases x.2 with ⟨p, hp, he⟩,
    -- A finite set of reals is disconnected.
    suffices : ∃ s t : ℝ, s < x.1 ∧ x.1 < t ∧ ∀ y, y ∈ set.Ioo s t ∧ aeval y p = 0 → y = x.1,
    { rcases this with ⟨s, t, hs, ht, Hy⟩,
      -- `exists_rat_near` is close to this.
      suffices H : ∀ s t : ℝ, s < t → ∃ q : ℚ, ↑q ∈ set.Ioo s t,
      { cases H s x hs with q hq,
        cases H x t ht with r hr,
        use [p, q, r],
        change dite _ _ _ = _,
        have Hss := set.Ioo_subset_Ioo hq.1.le hr.2.le,
        have : p ≠ 0 ∧ ∃ x : ℝ, x ∈ set.Ioo (q : ℝ) ↑r ∧ aeval x p = 0 :=
          ⟨hp, x.val, ⟨hq.2, hr.1⟩, he⟩,
        have hc := classical.some_spec this.2,
        rw dif_pos this,
        exact subtype.val_inj.1 (Hy _ ⟨Hss hc.1, hc.2⟩) },
      sorry },
    sorry },
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
