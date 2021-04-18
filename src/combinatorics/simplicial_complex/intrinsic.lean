import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import algebra.module.linear_map
import analysis.convex.topology

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}

namespace affine

def intrinsic_frontier (A : set E) :
  set E :=
coe '' (frontier {x : affine_span ℝ A | ↑x ∈ A})

def intrinsic_interior (A : set E) :
  set E :=
coe '' (interior {x : affine_span ℝ A | ↑x ∈ A})

lemma intrinsic_frontier_eq_closure_diff_intrinsic_interior :
  intrinsic_frontier A = closure A \ intrinsic_interior A :=
begin
  sorry
end

lemma closure_eq_intrinsic_interior_union_intrinsic_frontier :
  closure A = intrinsic_interior A ⋃ intrinsic_frontier A :=
begin
  sorry
end

lemma interior_subset_intrinsic_interior :
  interior A ⊆ intrinsic_interior A :=
begin
  rintro x hx,
  use ⟨x, subset_affine_span ℝ A (interior_subset hx)⟩,
  simp,
  sorry
end

lemma intrinsic_frontier_subset_frontier :
  intrinsic_frontier A ⊆ frontier A :=
begin
  have aux_lemma : ∀ B : set E, coe '' closure {x : affine_span ℝ A | ↑x ∈ B} ⊆ closure B,
  {
    rintro B _ ⟨x, hx, rfl⟩,
    rw mem_closure_iff_seq_limit at ⊢ hx,
    obtain ⟨f, hfB, hflim⟩ := hx,
    refine ⟨λ y, f y, hfB, _⟩,
    sorry
    --use filter.tendsto_coe,
  },
  rintro x hx,
  unfold intrinsic_frontier at hx,
  rw frontier_eq_closure_inter_closure at ⊢ hx,
  obtain ⟨x', hx', rfl⟩ := hx,
  exact ⟨aux_lemma _ ⟨x', hx'.1, rfl⟩, aux_lemma Aᶜ ⟨x', hx'.2, rfl⟩⟩,
end

end affine
