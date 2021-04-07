import tactic
import data.fincard
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import analysis.specific_limits
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme_point
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.simplex
import combinatorics.simplicial_complex.boundary
import combinatorics.simplicial_complex.pure
import combinatorics.simplicial_complex.subdivision
import combinatorics.simplicial_complex.skeleton

namespace affine

open_locale classical affine big_operators
open set
variables {m n : ℕ} {S : simplicial_complex m}
local notation `E` := fin m → ℝ

lemma boundary_space_eq_space_frontier_of_full_dimensional  {S : simplicial_complex m}
  (hS : S.pure_of (m + 1)) :
  S.boundary.space = frontier S.space :=
begin
  ext x,
  split,
  {
    sorry,
  },
  {
    sorry
  }
end




/- combi_interior X is the topological interior iff X is of dimension m -/
lemma interiors_agree_of_full_dimensional {S : simplicial_complex m}
  {X} (hX : X ∈ S.faces) (hXdim : X.card = m + 1) :
  combi_interior X = interior (convex_hull X) :=
begin
  --rw ← closure_combi_interior_eq_convex_hull,
  unfold combi_interior,
  sorry
end

/--
A simplicial complex is locally finite iff each point belongs to finitely many faces.
-/
lemma locally_finite_iff_mem_finitely_many_faces {S : simplicial_complex m} :
  S.locally_finite ↔ ∀ (x : fin m → ℝ), finite {X | X ∈ S.faces ∧ x ∈ convex_hull (X : set E)} :=
begin
  split,
  { unfold simplicial_complex.locally_finite,
    contrapose!,
    rintro ⟨x, hx⟩,
    by_cases hxspace : x ∈ S.space,
    { obtain ⟨X, ⟨hX, hXhull, hXbound⟩, hXunique⟩ := combi_interiors_partition hxspace,
      simp at hXunique,
      use [X, hX],
      split,
      { apply finset.nonempty_of_ne_empty,
        rintro rfl,
        simpa using hXhull },
      rintro hXlocallyfinite,
      apply hx,
      suffices h : {X : finset (fin m → ℝ) | X ∈ S.faces ∧ x ∈ convex_hull ↑X} ⊆
        {Y : finset (fin m → ℝ) | Y ∈ S.faces ∧ X ⊆ Y},
      { exact finite.subset hXlocallyfinite h },
      rintro Y ⟨hY, hYhull⟩,
      use hY,
      have hXYhull := S.disjoint hX hY ⟨hXhull, hYhull⟩,
      norm_cast at hXYhull,
      by_contra hXY,
      apply hXbound,
      have hYX : X ∩ Y ⊂ X,
      { use finset.inter_subset_left X Y,
        rintro hXXY,
        exact hXY (finset.subset_inter_iff.1 hXXY).2 },
      exact mem_combi_frontier_iff.2 ⟨X ∩ Y, hYX, hXYhull⟩ },
    { exfalso,
      apply hx,
      suffices h : {X : finset (fin m → ℝ) | X ∈ S.faces ∧ x ∈ convex_hull ↑X} = ∅,
      { rw h,
        exact finite_empty },
      apply eq_empty_of_subset_empty,
      rintro X ⟨hX, h⟩,
      exact hxspace (mem_bUnion hX h) }},
  { rintro hS X hX h,
    obtain ⟨x, hx⟩ := h,
    suffices h : {Y : finset (fin m → ℝ) | Y ∈ S.faces ∧ X ⊆ Y} ⊆
      {Y : finset (fin m → ℝ) | Y ∈ S.faces ∧ x ∈ convex_hull ↑Y},
    { exact (hS x).subset h },
    rintro Y ⟨hY, hXY⟩,
    exact ⟨hY, subset_convex_hull Y (hXY hx)⟩ }
end


lemma boundary_face_iff_subset_space_frontier_of_full_dimensional {S : simplicial_complex m}
  (hS : S.pure_of (m + 1)) {X : finset E} :
  X ∈ S.boundary.faces ↔ X ∈ S.faces ∧ ↑X ⊆ frontier S.space :=
begin
  split,
  { rintro ⟨Y, hY, hXY, Z, hZ, hYZ, hZunique⟩,
    use S.down_closed hY hXY,
    sorry
  },
  {
    rintro ⟨hX, hXspace⟩,
    sorry
  }
end

lemma closed_space_of_locally_finite {S : simplicial_complex m} (hS : S.locally_finite) :
  is_closed S.space :=
begin
  sorry
end

lemma space_frontier_eq {S : simplicial_complex m} :
  frontier S.space = (⋃ (X ∈ S.facets) (H : (X : finset E).card ≤ m), convex_hull ↑X)
  ∪ (⋃ (X ∈ S.boundary.faces), combi_interior X) :=
begin
  sorry
end

lemma boundary_space_eq_of_full_dimensional {S : simplicial_complex m}
  (hS : S.full_dimensional) {X : finset E} :
  frontier S.space = S.boundary.space :=
begin
  rw space_frontier_eq,
  rw combi_interiors_cover,
  ext x,
  split,
  {
    sorry
  },
  sorry
end

lemma boundary_mono {S₁ S₂ : simplicial_complex m} (hS : S₁ ≤ S₂) :
  S₁.boundary ≤ S₂.boundary :=
begin
  /-cases S₂.faces.eq_empty_or_nonempty with hS₂empty hS₂nonempty,
  {
    rw hS₂empty,
  },
  rw subdivision_iff_partition at ⊢ hS,-/
  have hspace : S₁.boundary.space = S₂.boundary.space,
  {
    sorry
  },
  /-rw subdivision_iff_partition,
  split,
  {
    sorry
  },
  use le_of_eq hspace,
  rintro X₂ ⟨Y₂, Z₂, hY₂, hZ₂, hX₂Y₂, hY₂Z₂, hZ₂max⟩,
  obtain ⟨hempty, hspace, hpartition⟩ := subdivision_iff_partition.1 hS,
  obtain ⟨F, hF, hX₂F⟩ := hpartition (S₂.down_closed hY₂ hX₂Y₂),
  use F, rw and.comm, use hX₂F,
  rintro X₁ hX₁,-/

  use hspace,
  rintro X₁ ⟨Y₁, hY₁, hX₁Y₁, Z₁, hZ₁, hY₁Z₁, hZ₁max⟩,
  cases X₁.eq_empty_or_nonempty with hX₁empty hX₁nonempty,
  {
    sorry},
  obtain ⟨X₂, hX₂, hX₁X₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2
    (S₁.down_closed hY₁ hX₁Y₁),
  obtain ⟨Y₂, hY₂, hY₁Y₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2 hY₁,
  obtain ⟨Z₂, hZ₂, hZ₁Z₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2 hZ₁,
  refine ⟨X₂, _, convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior _ _ hX₁X₂⟩,
  refine ⟨Y₂, hY₂, _, Z₂, hZ₂, ⟨_, _⟩⟩,
  {
    apply subset_of_combi_interior_inter_convex_hull_nonempty hX₂ hY₂,
    obtain ⟨x, hxX₁⟩ := nonempty_combi_interior_of_nonempty (S₁.indep (S₁.down_closed hY₁ hX₁Y₁))
      hX₁nonempty,
    use [x, hX₁X₂ hxX₁],
    apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hY₁)
      (S₂.indep hY₂) hY₁Y₂,
    exact convex_hull_mono hX₁Y₁ hxX₁.1,
  },
  {
    obtain ⟨x, hxX₁⟩ := hX₁nonempty,
    obtain ⟨y, hyY₁⟩ := nonempty_combi_interior_of_nonempty (S₁.indep hY₁) ⟨x, hX₁Y₁ hxX₁⟩,
    split,
    {
      apply subset_of_combi_interior_inter_convex_hull_nonempty hY₂ hZ₂,
      use [y, hY₁Y₂ hyY₁],
      apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hZ₁)
        (S₂.indep hZ₂) hZ₁Z₂,
      exact convex_hull_mono hY₁Z₁.1 hyY₁.1,
    },
    {
      rintro hZ₂Y₂,
      by_cases hY₂Z₂ : Y₂ ⊆ Z₂,
      {
        apply hY₁Z₁.2,
        have := finset.subset.antisymm hY₂Z₂ hZ₂Y₂,
        subst this,
        sorry
      },
      {
        apply (hY₁Y₂ hyY₁).2,
        rw mem_combi_frontier_iff,
        use [Z₂, ⟨hZ₂Y₂, hY₂Z₂⟩],
        apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior (S₁.indep hZ₁)
          (S₂.indep hZ₂) hZ₁Z₂,
        exact convex_hull_mono hY₁Z₁.1 hyY₁.1,
      }
    },
  },
  {
    sorry
  },
  { exact S₁.indep (S₁.down_closed hY₁ hX₁Y₁) },
  { exact S₂.indep hX₂ }
end

/--
A m-simplex not on the boundary of a full dimensional complex belongs to exactly two cells.
-/
lemma two_surfaces_of_non_boundary_subcell_of_full_dimensional {S : simplicial_complex m}
  {X : finset E} (hS : S.full_dimensional) (hX : X ∉ S.boundary.faces) (hXcard : X.card = m) :
  nat.card {Y | Y ∈ S.faces ∧ X ⊂ Y} = 2 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at X)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ X → b ∉ X → X ∪ {a} ∈ S.faces → X ∪ {b} ∈ S.faces →
  --   ∃ w : E → ℝ, w a < 0 ∧ ∑ y in X ∪ {a}, w y = 1 ∧ (X ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

/-A simplicial complex is connected iff its space is-/
def simplicial_complex.connected (S : simplicial_complex m) : Prop := connected_space S.space

/-A simplicial complex is connected iff its 1-skeleton is-/
lemma connected_iff_one_skeleton_connected {S : simplicial_complex m} :
  S.connected ↔ (S.skeleton 1).connected :=
begin
  split,
  { rintro h,
    unfold simplicial_complex.connected,
    sorry
  },
  {
    sorry
  }
end

lemma locally_compact_realisation_iff_locally_finite (S : simplicial_complex m) :
  S.locally_finite ↔ locally_compact_space S.space :=
  begin
    rw locally_finite_iff_mem_finitely_many_faces,
    split,
    {
      rintro hS,
      apply locally_compact_of_compact_nhds,
      rintro ⟨x, hx⟩,
      specialize hS x,
      sorry
    },
    {
      rintro hS x,
      --obtain ⟨a, b⟩ := hS x,
      sorry
    }
  end

/-The pyramid of a vertex v with respect to a simplicial complex S is the surcomplex consisting of
all faces of S along with all faces of S with v added -/
def pyramid {S : simplicial_complex m}
  (hS : ∀ X ∈ S.faces, finset.card X ≤ m) {v : fin m → ℝ} (hv : v ∉ convex_hull S.space) :
  simplicial_complex m :=
 {faces := {X' | ∃ X ∈ S.faces, X' ⊆ X ∪ {v}},
   --an alternative is S.faces ∪ S.faces.image (insert v)
   --a problem is that S.faces = ∅ should output (S.pyramid hS v hv).faces = {v} but this def doesn't
   --as said in the definition of empty_simplicial_complex, a solution is to define faces = {∅}
   --instead of faces = ∅.
  indep := begin
    rintro X' ⟨X, hX, hX'X⟩,
    sorry
  end,
  down_closed := λ X' Y ⟨X, hX, hX'X⟩ hYX', ⟨X, hX, subset.trans hYX' hX'X⟩,
  disjoint := begin
    rintro X' Y' ⟨X, hX, hX'X⟩ ⟨Y, hY, hY'Y⟩,
    sorry
  end}

lemma subcomplex_pyramid {S : simplicial_complex m} {v : fin m → ℝ}
  (hS : ∀ X ∈ S.faces, finset.card X ≤ m) (hv : v ∉ convex_hull S.space) :
  S.faces ⊆ (pyramid hS hv).faces := λ X hX, ⟨X, hX, finset.subset_union_left X {v}⟩

--S₁ ≤ S₂ → S₁.space = S₂.space so maybe we can get rid of hv₂?
lemma pyramid_mono {S₁ S₂ : simplicial_complex m} {v : fin m → ℝ}
  (hS₁ : ∀ X ∈ S₁.faces, finset.card X ≤ m) (hS₂ : ∀ X ∈ S₂.faces, finset.card X ≤ m)
  (hv₁ : v ∉ convex_hull S₁.space) (hv₂ : v ∉ convex_hull S₂.space) :
  S₁ ≤ S₂ → pyramid hS₁ hv₁ ≤ pyramid hS₂ hv₂ :=
begin
  rintro h,
  split,
  {
    sorry
  },
  {
    rintro X ⟨Y, hY, hXYv⟩,
    obtain ⟨Z, hZ, hYZhull⟩ := h.2 hY,
    use Z ∪ {v},
    split,
    {
      exact ⟨Z, hZ, subset.refl _⟩,
    },
    have hXYvhull : convex_hull ↑X ⊆ convex_hull ↑(Y ∪ {v}) := convex_hull_mono hXYv,
    have hYvZvhull : convex_hull ↑(Y ∪ {v}) ⊆ convex_hull ↑(Z ∪ {v}),
    {
      sorry
    },
    exact subset.trans hXYvhull hYvZvhull,
  }
end

/--
A polytope of dimension `n` in `R^m` is a subset for which there exists a simplicial complex which
is pure of dimension `n` and has the same underlying space.
-/
@[ext] structure polytope (m n : ℕ) :=
(space : set (fin m → ℝ))
(realisable : ∃ {S : simplicial_complex m}, S.pure_of n ∧ space = S.space)

def polytope.vertices (P : polytope m n) : set (fin m → ℝ) :=
  ⋂ (S : simplicial_complex m) (H : P.space = S.space), {x | {x} ∈ S.faces}

def polytope.edges (P : polytope m n) : set (finset (fin m → ℝ)) :=
  ⋂ (S : simplicial_complex m) (H : P.space = S.space), {X | X ∈ S.faces ∧ X.card = 2}

noncomputable def polytope.realisation (P : polytope m n) :
  simplicial_complex m := classical.some P.realisable

lemma pure_polytope_realisation (P : polytope m n) : P.realisation.pure_of n :=
  (classical.some_spec P.realisable).1

--def polytope.faces {n : ℕ} (P : polytope m n) : set (finset (fin m → ℝ)) :=
--  P.realisation.boundary.faces

/- Every convex polytope can be realised by a simplicial complex with the same vertices-/
lemma polytope.triangulable_of_convex {P : polytope m n} : convex P.space
  → ∃ (S : simplicial_complex m), P.space = S.space ∧ ∀ x, {x} ∈ S.faces → x ∈ P.vertices :=
begin
  rintro hPconvex,
  cases P.space.eq_empty_or_nonempty with hPempty hPnonempty,
  {
    use empty_simplicial_complex m,
    rw empty_space_of_empty_simplicial_complex m,
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

noncomputable def polytope.triangulation_of_convex {P : polytope m n} (hP : convex P.space) :
  simplicial_complex m := classical.some (polytope.triangulable_of_convex hP)

/-lemma convex_polytope_iff_intersection_of_half_spaces {space : set E} {n : ℕ} :
  ∃ {S : simplicial_complex m}, S.pure ∧ space = S.space ↔ ∃ half spaces and stuff-/

--def simplicial_complex.nonsingular (S : simplicial_complex m) {X : finset (fin m → ℝ)} : Prop :=
--  homeomorph (S.link {X}).space (metric.ball (0 : E) 1)

/-def simplicial_complex.mesh_size (S : simplicial_complex m) : ℝ := sorry --max diameter of simplices

def barycentrisation : list (fin m → ℝ) → fin m → ℝ :=
  λ L,

def simplicial_complex.barycentric_subdivision (S : simplicial_complex m) : simplicial_complex m :=
{ faces := {X | ∃ {L : list (fin m → ℝ)}, list.to_finset L ∈ S.faces ∧ X = },
  indep := _,
  down_closed := _,
  disjoint := _ }-/

end affine
