import combinatorics.simplicial_complex.pure

namespace affine
open set
variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {X Y : finset E} {A : set (finset E)}

/--
A polytope of dimension `n` in `R^m` is a subset for which there exists a simplicial complex which
is pure of dimension `n` and has the same underlying space.
-/
@[ext] structure polytope (E : Type*) [normed_group E] [normed_space ℝ E] (n : ℕ) :=
(space : set E)
(realisable : ∃ {S : simplicial_complex E}, S.pure_of n ∧ space = S.space)

variables {P : polytope E n}
/--
A constructor for polytopes from an underlying simplicial complex
-/
def simplicial_complex.to_polytope (hS : S.pure_of n) :
  polytope E n :=
{ space := S.space,
  realisable := ⟨S, hS, rfl⟩}

def polytope.vertices (P : polytope E n) :
  set E :=
⋂ (S : simplicial_complex E) (H : P.space = S.space), {x | {x} ∈ S.faces}

def polytope.edges (P : polytope E n) :
  set (finset E) :=
⋂ (S : simplicial_complex E) (H : P.space = S.space), {X | X ∈ S.faces ∧ X.card = 2}

noncomputable def polytope.realisation (P : polytope E n) :
  simplicial_complex E := classical.some P.realisable

lemma pure_polytope_realisation :
  P.realisation.pure_of n :=
(classical.some_spec P.realisable).1

--def polytope.faces {n : ℕ} (P : polytope E n) : set (finset E) :=
--  P.realisation.boundary.faces

/- Every convex polytope can be realised by a simplicial complex with the same vertices-/
lemma polytope.triangulable_of_convex (hP : convex P.space) :
  ∃ (S : simplicial_complex E), P.space = S.space ∧ ∀ x, {x} ∈ S.faces → x ∈ P.vertices :=
begin
  cases P.space.eq_empty_or_nonempty with hPempty hPnonempty,
  {
    use empty_simplicial_complex E,
    rw empty_space_of_empty_simplicial_complex,
    use hPempty,
    rintro X (hX : {X} ∈ {∅}),
    simp at hX,
    exfalso,
    exact hX,
  },
  obtain ⟨x, hx⟩ := hPnonempty,
  --consider the boundary of some realisation of P and remove it x,
  --have := P.realisation.boundary.erasure {x},
  --then add it back by taking the pyramid of this monster with x
  sorry
end

noncomputable def polytope.triangulation_of_convex (hP : convex P.space) :
  simplicial_complex E := classical.some (polytope.triangulable_of_convex hP)

/-lemma convex_polytope_iff_intersection_of_half_spaces {space : set E} {n : ℕ} :
  ∃ {S : simplicial_complex E}, S.pure ∧ space = S.space ↔ ∃ half spaces and stuff-/

end affine
