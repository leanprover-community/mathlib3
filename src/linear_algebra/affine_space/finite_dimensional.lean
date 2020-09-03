/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import linear_algebra.affine_space.independent
import linear_algebra.finite_dimensional

noncomputable theory
open_locale big_operators
open_locale classical

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

-/

section affine_space'

variables (k : Type*) {V : Type*} {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space V P]
variables {ι : Type*}
include V

open finite_dimensional

/-- The `vector_span` of a finite set is finite-dimensional. -/
lemma finite_dimensional_vector_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (vector_span k s) :=
span_of_finite k $ vsub_set_finite_of_finite h

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
lemma finite_dimensional_direction_affine_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (affine_span k s).direction :=
(direction_affine_span k s).symm ▸ finite_dimensional_vector_span_of_finite k h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (affine_span k (set.range p)).direction :=
finite_dimensional_direction_affine_span_of_finite k (set.finite_range _)

/-- The direction of the affine span of a subset of a family indexed
by a `fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_image_of_fintype [fintype ι] (p : ι → P)
  (s : set ι) : finite_dimensional k (affine_span k (p '' s)).direction :=
finite_dimensional_direction_affine_span_of_finite k ((set.finite.of_fintype _).image _)

variables {k}

/-- The `vector_span` of a finite affinely independent family has
dimension one less than its cardinality. -/
lemma findim_vector_span_of_affine_independent [fintype ι] {p : ι → P}
  (hi : affine_independent k p) {n : ℕ} (hc : fintype.card ι = n + 1) :
  findim k (vector_span k (set.range p)) = n :=
begin
  have hi' := affine_independent_set_of_affine_independent hi,
  have hc' : fintype.card (set.range p) = n + 1,
  by rwa set.card_range_of_injective (injective_of_affine_independent hi),
  have hn : (set.range p).nonempty,
  { refine set.range_nonempty_iff_nonempty.2 (fintype.card_pos_iff.1 _),
    simp [hc] },
  rcases hn with ⟨p₁, hp₁⟩,
  rw affine_independent_set_iff_linear_independent_vsub k hp₁ at hi',
  have hfr : (set.range p \ {p₁}).finite := (set.finite_range _).subset (set.diff_subset _ _),
  haveI := hfr.fintype,
  have hf : set.finite ((λ (p : P), p -ᵥ p₁) '' (set.range p \ {p₁})) := hfr.image _,
  haveI := hf.fintype,
  have hc : hf.to_finset.card = n,
  { rw [hf.card_to_finset,
        set.card_image_of_injective (set.range p \ {p₁}) (vsub_left_injective _)],
    have hd : insert p₁ (set.range p \ {p₁}) = set.range p,
    { rw [set.insert_diff_singleton, set.insert_eq_of_mem hp₁] },
    have hc'' : fintype.card ↥(insert p₁ (set.range p \ {p₁})) = n + 1,
    { convert hc' },
    rw set.card_insert (set.range p \ {p₁}) (λ h, ((set.mem_diff p₁).2 h).2 rfl) at hc'',
    simpa using hc'' },
  rw [vector_span_eq_span_vsub_set_right_ne k hp₁, findim_span_set_eq_card _ hi', ←hc],
  congr
end

/-- The `vector_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = findim k V + 1) :
  vector_span k (set.range p) = ⊤ :=
eq_top_of_findim_eq $ findim_vector_span_of_affine_independent hi hc

/-- The `affine_span` of a finite affinely independent family whose
cardinality is one more than that of the finite-dimensional space is
`⊤`. -/
lemma affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one [finite_dimensional k V]
  [fintype ι] {p : ι → P} (hi : affine_independent k p) (hc : fintype.card ι = findim k V + 1) :
  affine_span k (set.range p) = ⊤ :=
begin
  have hn : (set.range p).nonempty,
  { refine set.range_nonempty_iff_nonempty.2 (fintype.card_pos_iff.1 _),
    simp [hc] },
  rw [←affine_subspace.direction_eq_top_iff_of_nonempty ((affine_span_nonempty k _).2 hn),
      direction_affine_span],
  exact vector_span_eq_top_of_affine_independent_of_card_eq_findim_add_one hi hc
end

end affine_space'
