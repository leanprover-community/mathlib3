/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.convex_independence
import combinatorics.simplicial_complex.glued

/-!
# Polytopes
-/

open geometry geometry.simplicial_complex set

variables {𝕜 E : Type*}

namespace geometry
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  {S : simplicial_complex 𝕜 E} {n : ℕ} {X Y : finset E} {C : set E} {x : E} {A : set (finset E)}

variables (𝕜 E)

/-- A polytope is a set for which there exists a pure simplicial complex which has the same
underlying space. -/
@[ext] structure polytope :=
(space : set E)
(realisable : ∃ {S : simplicial_complex 𝕜 E} {n : ℕ}, S.pure n ∧ space = S.space)

variables {𝕜 E} {p : polytope 𝕜 E}

/-- A constructor for polytopes from an underlying simplicial complex. -/
def simplicial_complex.to_polytope (hS : S.pure n) : polytope 𝕜 E := ⟨S.space, S, n, hS, rfl⟩

noncomputable def polytope.to_simplicial_complex (p : polytope 𝕜 E) : simplicial_complex 𝕜 E :=
classical.some p.realisable

lemma pure_polytope_realisation : p.to_simplicial_complex.pure n :=
sorry -- (classical.some_spec p.realisable).1

lemma polytope_space_eq_realisation_space :
  p.space = p.to_simplicial_complex.space :=
sorry -- (classical.some_spec p.realisable).2

def polytope.vertices (p : polytope 𝕜 E) :
  set E :=
⋂ (S : simplicial_complex 𝕜 E) (H : p.space = S.space), S.vertices

lemma vertices_subset_space :
  p.vertices ⊆ p.space :=
begin
  rintro x hx,
  have hx' : x ∈ p.to_simplicial_complex.vertices,
  { --apply bInter_subset_of_mem (polytope_space_eq_realisation_space :
     -- p.to_simplicial_complex ∈ set_of (λ q : simplicial_complex 𝕜 E, p.space = q.space)),
     sorry
  },
  rw polytope_space_eq_realisation_space,
  exact simplicial_complex.mem_space_iff.2 ⟨{x}, hx', by simp⟩,
end

def polytope.edges (p : polytope 𝕜 E) :
  set (finset E) :=
⋂ (S : simplicial_complex 𝕜 E) (H : p.space = S.space), {X | X ∈ S.faces ∧ X.card = 2}

--def polytope.faces {n : ℕ} (P : polytope 𝕜 E) : set (finset E) :=
--  P.realisation.boundary.faces

noncomputable def polytope.triangulation (p : polytope 𝕜 E) : simplicial_complex 𝕜 E :=
begin
  classical,
  exact
  if p.space.nonempty ∧ convex 𝕜 p.space then begin
    have hpnonempty : p.space.nonempty := sorry,
    let x := classical.some hpnonempty,
    have hx := classical.some_spec hpnonempty,
    sorry
  end else p.to_simplicial_complex,
end

/-- Every convex polytope can be realised by a simplicial complex with the same vertices-/
lemma polytope.triangulable_of_convex (hp : convex 𝕜 p.space) :
  p.triangulation.vertices = p.vertices :=
begin
  cases p.space.eq_empty_or_nonempty with hpempty hpnonempty,
  { /-rw empty_space_of_empty_simplicial_complex,
    use hpempty,
    rintro X (hX : {X} ∈ {∅}),
    simp at hX,
    exfalso,
    exact hX,-/
    sorry
  },
  obtain ⟨x, hx⟩ := hpnonempty,
  --consider the boundary of some realisation of P and remove it x,
  --have := P.realisation.boundary.erasure {x},
  --then add it back by taking the pyramid of this monster with x
  sorry
end

/-lemma convex_polytope_iff_intersection_of_half_spaces {space : set E} {n : ℕ} :
  ∃ {S : simplicial_complex 𝕜 E}, S.pure ∧ space = S.space ↔ ∃ half spaces and stuff-/
variables (𝕜 E)

@[ext] structure polytopial_complex :=
(faces : set (finset E))
(indep : ∀ {X}, X ∈ faces → convex_independent 𝕜 (λ p, p : (X : set E) → E))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → (Y : set E) = (X : set E) ∩ affine_span 𝕜 (Y : set E)
  → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull 𝕜 ↑X ∩ convex_hull 𝕜 ↑Y ⊆ convex_hull 𝕜 (X ∩ Y : set E))

variables {𝕜 E} {P : polytopial_complex 𝕜 E}

def polytopial_complex.polytopes (P : polytopial_complex 𝕜 E) : set (polytope 𝕜 E) := sorry

def polytopial_complex.space (P : polytopial_complex 𝕜 E) : set E :=
⋃ (p ∈ P.polytopes), (p : polytope 𝕜 E).space

lemma mem_space_iff : x ∈ P.space ↔ ∃ p : polytope 𝕜 E, p ∈ P.polytopes ∧ x ∈ p.space :=
by simp [polytopial_complex.space]

def simplicial_complex.to_polytopial_complex (S : simplicial_complex 𝕜 E) :
  polytopial_complex 𝕜 E :=
{ faces := S.faces,
  indep := λ X hX, (S.indep hX).convex_independent,
  down_closed := λ X Y hX hYX hY, S.down_closed hX hYX sorry,
  disjoint := S.inter_subset_convex_hull }

noncomputable def polytope.to_polytopial_complex (p : polytope 𝕜 E) : polytopial_complex 𝕜 E :=
p.to_simplicial_complex.to_polytopial_complex

def polytopial_complex.to_simplicial_complex (P : polytopial_complex 𝕜 E) :
  simplicial_complex 𝕜 E :=
{ faces := ⋃ (p ∈ P.polytopes), (p : polytope 𝕜 E).to_simplicial_complex.faces,
  indep := λ X hX, begin
    obtain ⟨p, hp, hX⟩ := mem_Union₂.1 hX,
    exact p.to_simplicial_complex.indep hX,
  end,
  down_closed := λ X Y hX hYX hY, begin
    rw mem_Union₂ at ⊢ hX,
    obtain ⟨p, hp, hX⟩ := hX,
    exact ⟨p, hp, p.to_simplicial_complex.down_closed hX hYX hY⟩,
  end,
  inter_subset_convex_hull := λ X Y hX hY, begin
    obtain ⟨p, hp, hX⟩ := mem_Union₂.1 hX,
    obtain ⟨q, hq, hY⟩ := mem_Union₂.1 hY,
    sorry --this is wrong because faces of adjacent polytopes aren't required to glue nicely
    -- causes problem as soon as their shared faces aren't simplices
  end,
  not_empty_mem := sorry }

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [decidable_eq E] [add_comm_group E] [module 𝕜 E] {C : set E}

def polytopial_complex.coplanarless (P : polytopial_complex 𝕜 E) : Prop :=
∀ X Y ∈ P.faces, adjacent X Y → (X : set E) ⊆ affine_span 𝕜 (Y : set E) →
  X.card = finite_dimensional.finrank 𝕜 E + 1

lemma polytopial_space_iff_simplicial_space [finite_dimensional 𝕜 E] :
  (∃ (S : simplicial_complex 𝕜 E), S.space = C) ↔
  ∃ (P : polytopial_complex 𝕜 E), P.space = C :=
begin
  split,
  { rintro ⟨S, hS⟩,
    sorry
  },
  sorry
end

end linear_ordered_field
end geometry
