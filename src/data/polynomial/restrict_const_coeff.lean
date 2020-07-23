/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import data.mv_polynomial
import ring_theory.ideals
import ring_theory.ideal_operations
import ring_theory.jacobson_ideal

/-!
# Restrict Constant Coefficients

-/

noncomputable theory

open polynomial

universes u v

namespace ideal
variables {R : Type u} [comm_ring R] {I : ideal R}
variables {S : Type v} [comm_ring S]

lemma coeff_zero_mem_of_mem_span_C [comm_ring R] {f : polynomial R} {I : ideal R} :
  f ∈ span (C '' (I : set R)) → coeff f 0 ∈ I :=
begin
  intro h,
  apply submodule.span_induction h,
  { intros g hg,
    rw set.mem_image at hg,
    rcases hg with ⟨x, ⟨hx, hxg⟩⟩,
    rwa [← hxg, coeff_C_zero] },
  { exact I.zero_mem },
  { intros g g' hg hg',
    simp,
    exact I.add_mem hg hg' },
  { intros x g hg,
    simp,
    exact I.smul_mem _ hg }
end

section restrict_const_coeff

/-- `restrict_const_coeff I` is the ideal of polynomials with constant coefficient in I -/
def restrict_const_coeff (I : ideal R) : ideal (polynomial R) := span (insert X (C '' (I : set R)))

lemma mem_restrict_const_coeff_iff_coeff_zero_mem {f : polynomial R} :
  f ∈ restrict_const_coeff I ↔ coeff f 0 ∈ I :=
begin
  split,
  { intro h,
    rcases mem_span_insert.1 h with ⟨f', g, hg, hf⟩,
    simp [hf, coeff_zero_mem_of_mem_span_C hg] },
  { cases polynomial_exists_downshift f with g hg,
    exact λ h, mem_span_insert.2 ⟨g, C (f.coeff 0), mem_map_of_mem h, hg⟩ }
end

lemma restrict_const_coeff.is_prime [H : is_prime I] : is_prime (restrict_const_coeff I) :=
begin
  split,
  { refine λ h, H.left _,
    rw eq_top_iff,
    intros x _,
    have : C x ∈ restrict_const_coeff I := h.symm ▸ submodule.mem_top,
    rwa [mem_restrict_const_coeff_iff_coeff_zero_mem, coeff_C] at this },
  { intros f g hfg,
    rw mem_restrict_const_coeff_iff_coeff_zero_mem at hfg,
    simp at hfg,
    cases H.right hfg,
    { left,
      rwa mem_restrict_const_coeff_iff_coeff_zero_mem },
    { right,
      rwa mem_restrict_const_coeff_iff_coeff_zero_mem } }
end

end restrict_const_coeff

end ideal
