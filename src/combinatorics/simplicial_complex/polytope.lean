/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.convex_independence
import combinatorics.simplicial_complex.glued

open set affine
namespace poly
variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {x : E} {X Y : finset E} {C : set E} {A : set (finset E)}

/--
A polytope of dimension `n` in `R^m` is a subset for which there exists a simplicial complex which
is pure of dimension `n` and has the same underlying space.
-/
@[ext] structure polytope (E : Type*) [normed_group E] [normed_space ℝ E] :=
(space : set E)
(realisable : ∃ {S : simplicial_complex E}, S.pure ∧ space = S.space)

variables {p : polytope E}

/--
A constructor for polytopes from an underlying simplicial complex
-/
def simplicial_complex.to_polytope (hS : S.pure) :
  polytope E :=
{ space := S.space,
  realisable := ⟨S, hS, rfl⟩}

noncomputable def polytope.to_simplicial_complex (p : polytope E) :
  simplicial_complex E := classical.some p.realisable

lemma pure_polytope_realisation :
  p.to_simplicial_complex.pure :=
(classical.some_spec p.realisable).1

lemma polytope_space_eq_realisation_space :
  p.space = p.to_simplicial_complex.space :=
(classical.some_spec p.realisable).2

def polytope.vertices (p : polytope E) :
  set E :=
⋂ (S : simplicial_complex E) (H : p.space = S.space), S.vertices

lemma vertices_subset_space :
  p.vertices ⊆ p.space :=
begin
  rintro x hx,
  have hx' : x ∈ p.to_simplicial_complex.vertices,
  {
    --apply bInter_subset_of_mem (polytope_space_eq_realisation_space :
     -- p.to_simplicial_complex ∈ set_of (λ q : simplicial_complex E, p.space = q.space)),
     sorry
  },
  rw polytope_space_eq_realisation_space,
  exact mem_space_iff.2 ⟨{x}, hx', by simp⟩,
end

def polytope.edges (p : polytope E) :
  set (finset E) :=
⋂ (S : simplicial_complex E) (H : p.space = S.space), {X | X ∈ S.faces ∧ X.card = 2}

--def polytope.faces {n : ℕ} (P : polytope E) : set (finset E) :=
--  P.realisation.boundary.faces

noncomputable def polytope.triangulation (p : polytope E) :
  simplicial_complex E :=
begin
  classical,
  exact
  if p.space.nonempty ∧ convex p.space then begin
    have hpnonempty : p.space.nonempty := sorry,
    let x := classical.some hpnonempty,
    have hx := classical.some_spec hpnonempty,
    sorry
  end else p.to_simplicial_complex,
end

/- Every convex polytope can be realised by a simplicial complex with the same vertices-/
lemma polytope.triangulable_of_convex (hp : convex p.space) :
  p.triangulation.vertices = p.vertices :=
begin
  cases p.space.eq_empty_or_nonempty with hpempty hpnonempty,
  {
    /-rw empty_space_of_empty_simplicial_complex,
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
  ∃ {S : simplicial_complex E}, S.pure ∧ space = S.space ↔ ∃ half spaces and stuff-/

@[ext] structure polytopial_complex (E : Type*) [normed_group E] [normed_space ℝ E] :=
(faces : set (finset E))
(indep : ∀ {X}, X ∈ faces → convex_independent (λ p, p : (X : set E) → E))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → (Y : set E) = (X : set E) ∩ affine_span ℝ (Y : set E)
  → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E))

variables {P : polytopial_complex E}

def polytopial_complex.polytopes (P : polytopial_complex E) :
  set (polytope E) :=
  sorry

def polytopial_complex.space (P : polytopial_complex E) :
  set E :=
⋃ (p ∈ P.polytopes), (p : polytope E).space

lemma mem_space_iff :
  x ∈ P.space ↔ ∃ (p : polytope E), p ∈ P.polytopes ∧ x ∈ p.space :=
begin
  unfold polytopial_complex.space,
  simp,
end

def simplicial_complex.to_polytopial_complex (S : simplicial_complex E) :
  polytopial_complex E :=
{ faces := S.faces,
  indep := λ X hX, (S.indep hX).convex_independent,
  down_closed := λ X Y hX hYX hY, S.down_closed hX hYX,
  disjoint := S.disjoint }

noncomputable def polytope.to_polytopial_complex (p : polytope E) :
  polytopial_complex E :=
simplicial_complex.to_polytopial_complex p.to_simplicial_complex
--@Bhavik I can't use dot notation here because of namespace problems. Do you have a fix?

def polytopial_complex.coplanarless (P : polytopial_complex E) :
  Prop :=
∀ X Y ∈ P.faces, adjacent X Y → (X : set E) ⊆ affine_span ℝ (Y : set E) →
  X.card = finite_dimensional.finrank ℝ E + 1

def polytopial_complex.to_simplicial_complex (P : polytopial_complex E) :
  simplicial_complex E :=
{ faces := ⋃ (p ∈ P.polytopes), (p : polytope E).to_simplicial_complex.faces,
  indep := begin
    rintro X hX,
    rw mem_bUnion_iff at hX,
    obtain ⟨p, hp, hX⟩ := hX,
    exact p.to_simplicial_complex.indep hX,
  end,
  down_closed := begin
    rintro X Y hX hYX,
    rw mem_bUnion_iff at ⊢ hX,
    obtain ⟨p, hp, hX⟩ := hX,
    exact ⟨p, hp, p.to_simplicial_complex.down_closed hX hYX⟩,
  end,
  disjoint := begin
    rintro X Y hX hY,
    rw mem_bUnion_iff at hX hY,
    obtain ⟨p, hp, hX⟩ := hX,
    obtain ⟨q, hq, hY⟩ := hY,
    sorry --this is wrong because faces of adjacent polytopes aren't required to glue nicely
    -- causes problem as soon as their shared faces aren't simplices
  end }

lemma polytopial_space_iff_simplicial_space [finite_dimensional ℝ E] :
  (∃ (S : simplicial_complex E), S.space = C) ↔
  ∃ (P : polytopial_complex E), P.space = C :=
begin
  split,
  {
    rintro ⟨S, hS⟩,
    sorry
  },
  sorry
end

end poly
