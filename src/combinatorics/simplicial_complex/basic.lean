import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme_point
import combinatorics.simplicial_complex.simplex
-- import data.nat.parity

open_locale classical affine big_operators
open set
variables (m : ℕ) {n : ℕ}
local notation `E` := fin m → ℝ

namespace affine

/--
A simplicial complex in `R^m`.
TODO: generalise to normed affine spaces `E`, so this is `simplicial_complex E`.
-/
@[ext] structure simplicial_complex :=
(faces : set (finset E))
(indep : ∀ {X}, X ∈ faces → affine_independent ℝ (λ p, p : (X : set E) → E))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E))

variables {m} {S : simplicial_complex m}

/--
A constructor for simplicial complexes by specifying a surcomplex whose set of faces is
downward closed.
-/
@[simp] def simplicial_complex.of_surcomplex {S : simplicial_complex m}
  (faces : set (finset E)) (subset_surcomplex : faces ⊆ S.faces)
  (down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces) :
  simplicial_complex m :=
{ faces := faces,
  indep := λ X hX, S.indep (subset_surcomplex hX),
  down_closed := λ X Y hX hYX, down_closed hX hYX,
  disjoint := λ X Y hX hY, S.disjoint (subset_surcomplex hX) (subset_surcomplex hY) }

/--
A constructor for simplicial complexes by specifying a set of faces to close downward.
-/
@[simp] def simplicial_complex.of_set_closure {A : set (finset E)}
  (indep : ∀ {X}, X ∈ A → affine_independent ℝ (λ p, p : (X : set E) → E))
  (disjoint : ∀ {X Y}, X ∈ A → Y ∈ A →
    convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E)) :
  simplicial_complex m :=
{ faces := {X | ∃ Y, Y ∈ A ∧ X ⊆ Y},
  indep := λ X ⟨Y, hY, hXY⟩, affine_independent_of_subset_affine_independent (indep hY) hXY,
  down_closed := λ X Y ⟨Z, hZ, hXZ⟩ hYX, ⟨Z, hZ, subset.trans hYX hXZ⟩,
  disjoint :=
  begin
    rintro W X ⟨Y, hY, hWY⟩ ⟨Z, hZ, hXZ⟩ x ⟨hxW, hxX⟩,
    have hxYZ : x ∈ convex_hull (Y ∩ Z : set E) :=
      disjoint hY hZ ⟨convex_hull_mono hWY hxW, convex_hull_mono hXZ hxX⟩,
    have hxWZ : x ∈ convex_hull (W ∩ Z : set E),
    { have := disjoint_convex_hull_of_subsets (indep hY) hWY (finset.inter_subset_left Y Z),
      norm_cast at this hxYZ,
      exact_mod_cast convex_hull_mono
        (finset.inter_subset_inter_left (finset.inter_subset_right Y Z)) (this ⟨hxW, hxYZ⟩), },
    have hxYX : x ∈ convex_hull (Y ∩ X : set E),
    { have := disjoint_convex_hull_of_subsets (indep hZ) (finset.inter_subset_right Y Z) hXZ,
      norm_cast at this hxYZ,
      exact_mod_cast convex_hull_mono
        (finset.inter_subset_inter_right (finset.inter_subset_left Y Z)) (this ⟨hxYZ, hxX⟩), },
    norm_cast at hxWZ hxYX,
    have hxWX := disjoint_convex_hull_of_subsets (indep hY)
      (subset.trans (finset.inter_subset_inter_right hWY) (finset.inter_subset_left Y Z))
      (finset.inter_subset_left Y X) ⟨hxWZ, hxYX⟩,
    norm_cast at hxWX,
    exact_mod_cast convex_hull_mono (subset.trans
      (finset.inter_subset_inter_right (finset.inter_subset_left W Z))
      (finset.inter_subset_inter_left (finset.inter_subset_right Y X))) hxWX,
  end}

/--
A constructor for simplicial complexes by specifying a face to close downward.
-/
@[simp] def simplicial_complex.of_simplex {X : finset E}
  (indep : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  simplicial_complex m :=
simplicial_complex.of_set_closure m
  begin rintro Y (hY : Y = X), rw hY, exact indep end
  begin rintro Y Z (hY : Y = X) (hZ : Z = X), rw [hY, hZ, inter_self _, inter_self _],
    exact subset.refl _ end

lemma mem_simplex_complex_iff {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  Y ∈ (simplicial_complex.of_simplex m hX).faces ↔ Y ⊆ X :=
begin
  split,
  { rintro ⟨Z, (hZ : Z = X), hYX⟩,
    rw ← hZ,
    exact hYX },
  { rintro hYX,
    exact ⟨X, rfl, hYX⟩ }
end

/--
The empty simplicial complex is made up of only the empty simplex
-/
def empty_simplicial_complex (m : ℕ) : simplicial_complex m :=
{ faces := {∅},
  indep :=
  begin
    rintro X (rfl : _ = _),
    apply affine_independent_of_subsingleton ℝ _,
    simp,
  end,
  down_closed := λ X Y hX, hX.symm ▸ finset.subset_empty.1,
  disjoint :=
  begin
    rintro X _ (rfl : X = ∅) (rfl : Y = ∅),
    simp,
  end, }

lemma empty_mem_faces_of_nonempty {S : simplicial_complex m} : (S.faces).nonempty → ∅ ∈ S.faces :=
  λ ⟨X, hX⟩, S.down_closed hX (empty_subset X)

/--
The underlying space of a simplicial complex.
-/
def simplicial_complex.space (S : simplicial_complex m) : set E :=
  ⋃ X ∈ S.faces, convex_hull (X : set E)

lemma mem_space_iff {S : simplicial_complex m} {x : E} :
  x ∈ S.space ↔ ∃ X ∈ S.faces, x ∈ convex_hull (X : set E) :=
begin
  unfold simplicial_complex.space,
  rw mem_bUnion_iff,
end

lemma empty_space_of_empty_simplicial_complex (m : ℕ) : (empty_simplicial_complex m).space = ∅ :=
begin
  unfold empty_simplicial_complex simplicial_complex.space,
  simp,
end

lemma convex_hull_face_subset_space {X} (hX : X ∈ S.faces) :
  convex_hull ↑X ⊆ S.space :=
λ x hx, mem_bUnion hX hx

lemma face_subset_space {X} (hX : X ∈ S.faces) :
  (X : set E) ⊆ S.space :=
set.subset.trans (subset_convex_hull _) (convex_hull_face_subset_space hX)

def simplicial_complex.points (S : simplicial_complex m) : set E :=
⋃ k ∈ S.faces, (k : set E)

lemma points_subset_space :
  S.points ⊆ S.space :=
bUnion_subset_bUnion_right (λ x hx, subset_convex_hull x)

/-def simplicial_complex.dimension (S : simplicial_complex m) {X : finset (fin m → ℝ)} : ℕ :=
  Sup {X.card - 1 | X ∈ S.faces}-/

/-The dimension of a simplicial complex is the maximal dimension of its faces-/
/-def simplicial_complex.dimension (S : simplicial_complex m) : ℕ :=
 Sup {finset.card (X : set E) | X ∈ S.faces}-/

-- Dumb bug in mathlib, see
--https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/R.5Em.20is.20finite.20dimensional.20over.20R/near/231748016
instance {m : ℕ} : finite_dimensional ℝ (fin m → ℝ) := sorry

--Refinement of `size_bound`
lemma simplex_dimension_le_space_dimension {S : simplicial_complex m} {X : finset E}
  (hX : X ∈ S.faces) :
finset.card X ≤ m + 1 :=
begin
  convert size_bound (S.indep hX),
  simp,
end

def simplicial_complex.facets (S : simplicial_complex m) : set (finset (fin m → ℝ)) :=
{X | X ∈ S.faces ∧ (∀ {Y}, Y ∈ S.faces → X ⊆ Y → X = Y)}

lemma facets_subset {S : simplicial_complex m} : S.facets ⊆ S.faces := λ X hX, hX.1

lemma not_facet_iff_subface {S : simplicial_complex m} {X : finset (fin m → ℝ)} :
  X ∈ S.faces → (X ∉ S.facets ↔ ∃ {Y}, Y ∈ S.faces ∧ X ⊂ Y) :=
begin
  rintro hX,
  split,
  { rintro (hX' : ¬(X ∈ S.faces ∧ (∀ {Y}, Y ∈ S.faces → X ⊆ Y → X = Y))),
    push_neg at hX',
    obtain ⟨Y, hY⟩ := hX' hX,
    exact ⟨Y, hY.1, ⟨hY.2.1, (λ hYX, hY.2.2 (finset.subset.antisymm hY.2.1 hYX))⟩⟩, },
  { rintro ⟨Y, hY⟩ ⟨hX, hX'⟩,
    have := hX' hY.1 hY.2.1,
    rw this at hY,
    exact hY.2.2 (subset.refl Y), }
end

lemma subfacet {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  ∃ {Y}, Y ∈ S.facets ∧ X ⊆ Y :=
begin
  apply finset.strong_downward_induction_on' (λ Y hY, simplex_dimension_le_space_dimension hY) hX,
  rintro Y hY h,
  by_cases hYfacet : Y ∈ S.facets,
  { exact ⟨Y, hYfacet, finset.subset.refl _⟩, },
  { obtain ⟨Z, hZ₁, hZ₂⟩ := (not_facet_iff_subface hY).mp hYfacet,
    obtain ⟨W, hW⟩ := h hZ₁ hZ₂,
    exact ⟨W, hW.1, finset.subset.trans hZ₂.1 hW.2⟩, }
end

lemma facets_empty {S : simplicial_complex m} (hS : S.faces = ∅) : S.facets = ∅ :=
begin
  rw [←subset_empty_iff, ←hS],
  exact facets_subset,
end

lemma facets_empty_iff_faces_empty {S : simplicial_complex m} :
  S.facets = ∅ ↔ S.faces = ∅ :=
begin
  classical,
  split,
  { intro h,
    by_contra h',
    rw [←ne.def, set.ne_empty_iff_nonempty] at h',
    rcases h' with ⟨X, hX⟩,
    rcases subfacet hX with ⟨Y, hY, hZ⟩,
    rw h at hY,
    apply hY },
  { exact facets_empty }
end

lemma facets_singleton {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hS : S.faces = {X}) :
  S.facets = {X} :=
begin
  ext X,
  unfold simplicial_complex.facets,
  rw hS,
  simp,
  exact λ hX _, hX,
end

lemma facets_singleton_empty {S : simplicial_complex m} (hS : S.faces = {∅}) : S.facets = {∅} :=
  facets_singleton hS

/--
The cells of a simplicial complex are its simplices whose dimension matches the one of the space
-/
def simplicial_complex.cells (S : simplicial_complex m) : set (finset (fin m → ℝ)) :=
{X | X ∈ S.faces ∧ X.card = m + 1}

lemma cells_subset_facets {S : simplicial_complex m} : S.cells ⊆ S.facets :=
begin
  rintro X ⟨hX, hXcard⟩,
  by_contra,
  obtain ⟨Y, hY, hXY⟩ := (not_facet_iff_subface hX).mp h,
  have := finset.card_lt_card hXY,
  have := simplex_dimension_le_space_dimension hY,
  linarith,
end

/--
The closure of a set of faces is the set of their subfaces
-/
def simplicial_complex.closure (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m := {
  faces := {X | X ∈ S.faces ∧ ∃ {X'}, X' ∈ A ∧ X ⊆ X'},
  indep := λ X ⟨hX, _⟩, S.indep hX,
  down_closed := λ X Y ⟨hX, X', hX', hXX'⟩ hYX,
    ⟨S.down_closed hX hYX, X', hX', subset.trans hYX hXX'⟩,
  disjoint := λ X Y ⟨hX, _⟩ ⟨hY, _⟩, S.disjoint hX hY }
/-Previous def
def simplicial_complex.closure (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m := simplicial_complex.of_surcomplex
  {X | X ∈ S.faces ∧ ∃ {X'}, X' ∈ A ∧ X ⊆ X'}
  (λ X ⟨hX, _⟩, hX)
  (λ X Y ⟨hX, X', hX', hXX'⟩ hYX, ⟨S.down_closed hX hYX, X', hX', subset.trans hYX hXX'⟩)-/

--Homonymy problem
lemma closure_empty {S : simplicial_complex m} (hS : S.faces.nonempty) : (S.closure ∅).faces = ∅ :=
begin
  unfold simplicial_complex.closure,
  simp,
end

lemma closure_singleton_empty {S : simplicial_complex m} (hS : S.faces.nonempty) :
  (S.closure {∅}).faces = {∅} :=
begin
  ext X,
  split,
  {
    rintro ⟨hX, X', (hX' : X' = ∅), hXX'⟩,
    rw hX' at hXX',
    exact finset.subset_empty.1 hXX',
  },
  {
    rintro (hX : X = ∅),
    rw hX,
    obtain ⟨Y, hY⟩ := hS,
    exact ⟨S.down_closed hY (empty_subset Y), ∅, mem_singleton ∅, subset.refl ∅⟩,
  }
end

--Homonymy problem
lemma closure_singleton {S : simplicial_complex m} {x : fin m → ℝ} (hx : {x} ∈ S.faces) :
  (S.closure {{x}}).faces = {∅, {x}} :=
begin
  ext Y,
  split,
  { rintro ⟨hY, Z, (hZ : Z = {x}), hYZ⟩,
    rw hZ at hYZ,
    simp only [mem_singleton_iff, mem_insert_iff],
    rwa ← finset.subset_singleton_iff },
  { have hxS : {x} ∈ (S.closure {{x}}).faces := ⟨hx, {x}, rfl, finset.subset.refl {x}⟩,
    simp only [mem_singleton_iff, mem_insert_iff],
    rintro (rfl | rfl),
    { exact empty_mem_faces_of_nonempty (nonempty_of_mem hxS) },
    { assumption } }
end

lemma mem_closure_singleton_iff {S : simplicial_complex m} {X Y : finset (fin m → ℝ)} :
  Y ∈ (S.closure {X}).faces ↔ Y ∈ S.faces ∧ Y ⊆ X :=
begin
  split,
  {
    rintro ⟨hY, Z, (hZ : Z = X), hYZ⟩,
    rw hZ at hYZ,
    exact ⟨hY, hYZ⟩,
  },
  {
    rintro ⟨hY, hYX⟩,
    exact ⟨hY, X, rfl, hYX⟩,
  }
end

lemma closure_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.closure A).faces ⊆ S.faces := λ X ⟨hX, _⟩, hX

--Homonymy problem
lemma faces_subset_closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.faces ∩ A ⊆ (S.closure A).faces := λ X hX, ⟨hX.1, X, hX.2, subset.refl _⟩

lemma closure_faces_subset_of_subset {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))}
  (hAB : A ⊆ B) :
  (S.closure A).faces ⊆ (S.closure B).faces := λ X ⟨hX, Y, hY, hXY⟩, ⟨hX, Y, hAB hY, hXY⟩


lemma mem_of_mem_convex_hull {S : simplicial_complex m} {x : E} {X : finset E} (hx : {x} ∈ S.faces)
  (hX : X ∈ S.faces) (hxX : x ∈ convex_hull (X : set E)) : x ∈ X :=
begin
  have h := S.disjoint hx hX ⟨by simp, hxX⟩,
  by_contra H,
  norm_cast at h,
  rw [finset.inter_comm, finset.disjoint_iff_inter_eq_empty.1 (finset.disjoint_singleton.2 H)] at h,
  simp at h,
  exact h,
end

lemma subset_of_convex_hull_subset_convex_hull {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (hXY : convex_hull (X : set E) ⊆ convex_hull ↑Y) : X ⊆ Y :=
λ x hxX, mem_of_mem_convex_hull (S.down_closed hX (finset.singleton_subset_iff.2 hxX)) hY
  (hXY (subset_convex_hull ↑X hxX))

lemma disjoint_interiors {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (x : E) :
  x ∈ combi_interior X ∩ combi_interior Y → X = Y :=
begin
  rintro ⟨⟨hxX, hXbound⟩, ⟨hyY, hYbound⟩⟩,
  by_contra,
  have hXY : X ∩ Y ⊂ X,
  { use finset.inter_subset_left X Y,
    intro H,
    exact hYbound (set.mem_bUnion ⟨subset.trans H (finset.inter_subset_right X Y),
      (λ H2, h (finset.subset.antisymm (subset.trans H (finset.inter_subset_right X Y)) H2))⟩ hxX) },
  refine hXbound (mem_bUnion hXY _),
  exact_mod_cast S.disjoint hX hY ⟨hxX, hyY⟩,
end

lemma disjoint_interiors_aux {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (h : X ≠ Y) :
  disjoint (combi_interior X) (combi_interior Y) :=
λ x hx, h (disjoint_interiors hX hY _ hx)

lemma eq_singleton_of_singleton_mem_combi_interior {S : simplicial_complex m} {x : E} {X : finset E}
  (hx : {x} ∈ S.faces) (hX : X ∈ S.faces) (hxX : x ∈ combi_interior X) : X = {x} :=
begin
  apply disjoint_interiors hX hx x,
  rw combi_interior_singleton,
  exact ⟨hxX, mem_singleton x⟩,
end

lemma combi_interiors_cover (S : simplicial_complex m) :
  S.space = ⋃ X ∈ S.faces, combi_interior X :=
begin
  apply subset.antisymm _ _,
  { apply bUnion_subset,
    rintro X hX,
    rw simplex_combi_interiors_cover,
    exact Union_subset (λ Y, Union_subset (λ YX, subset_bUnion_of_mem (S.down_closed hX YX)))},
  { apply bUnion_subset,
    rintro Y hY,
    exact subset.trans (diff_subset _ _) (subset_bUnion_of_mem hY) }
end

/- The simplices interiors form a partition of the underlying space (except that they contain the
empty set) -/
lemma combi_interiors_partition {S : simplicial_complex m} {x} (hx : x ∈ S.space) :
  ∃! X, X ∈ S.faces ∧ x ∈ combi_interior X :=
begin
  rw combi_interiors_cover S at hx,
  simp only [set.mem_bUnion_iff] at hx,
  obtain ⟨X, hX, hxX⟩ := hx,
  exact ⟨X, ⟨⟨hX, hxX⟩, (λ Y ⟨hY, hxY⟩, disjoint_interiors hY hX x ⟨hxY, hxX⟩)⟩⟩,
end

lemma mem_convex_hull_iff {X : finset E} {x : E} :
  x ∈ convex_hull (X : set E) ↔ ∃ Y ⊆ X, x ∈ combi_interior Y :=
begin
  simp [simplex_combi_interiors_cover],
end

lemma mem_combi_frontier_iff' {X : finset E} {x : E} :
  x ∈ combi_frontier X ↔ ∃ {Y}, Y ⊂ X ∧ x ∈ combi_interior Y :=
begin
  rw mem_combi_frontier_iff,
  split,
  {
    rintro ⟨Y, hYX, hxY⟩,
    --rw [simplex_combi_interiors_cover, mem_bUnion_iff] at hxY,
    --obtain ⟨Z, hZ⟩ := simplex_combi_interiors_cover
    sorry
  },
  { rintro ⟨Y, hYX, hxY⟩,
    exact ⟨Y, hYX, hxY.1⟩ }
end

lemma subset_of_combi_interior_inter_convex_hull_nonempty {S : simplicial_complex m} {X Y}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces)
  (hXY : (combi_interior X ∩ convex_hull (Y : set E)).nonempty) : X ⊆ Y :=
begin
  obtain ⟨x, hxX, hxY⟩ := hXY,
  obtain ⟨Z, hZY, hxZ⟩ := (mem_convex_hull_iff m).1 hxY,
  rw disjoint_interiors hX (S.down_closed hY hZY) x ⟨hxX, hxZ⟩,
  exact hZY,
end

lemma simplex_combi_interiors_split_interiors {X Y : finset E}
  (hY : affine_independent ℝ (λ p, p : (Y : set E) → E))
  (hXY : convex_hull (X : set E) ⊆ convex_hull ↑Y) :
  ∃ Z ⊆ Y, combi_interior X ⊆ combi_interior Z :=
begin
  let S := simplicial_complex.of_simplex m hY,
  let F := Y.powerset.filter (λ W : finset E, (X : set E) ⊆ convex_hull W),
  obtain ⟨Z, hZ, hZmin⟩ := finset.exists_min
  (begin
    use Y,
    simp,
    exact subset.trans (subset_convex_hull _) hXY
  end : F.nonempty)
  begin
    rintro A B hA hB,
    simp at ⊢ hA hB,
    exact ⟨finset.subset.trans (finset.inter_subset_left _ _) hA.1,
      subset.trans (subset_inter hA.2 hB.2) (S.disjoint ((mem_simplex_complex_iff m hY).2 hA.1)
      ((mem_simplex_complex_iff m hY).2 hB.1))⟩
  end,
  simp at hZ,
  use [Z, hZ.1],
  rintro x hxX,
  use convex_hull_min hZ.2 (convex_convex_hull _) hxX.1,
  rintro hxZ,
  rw mem_combi_frontier_iff' at hxZ,
  obtain ⟨W, hWZ, hxW⟩ := hxZ,
  apply hWZ.2 (hZmin W _),
  simp,
  use [subset.trans hWZ.1 hZ.1],
  rw finset.convex_hull_eq _ at ⊢ hZ,
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combi_interior_subset_positive_weighings hxX,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combi_interior_subset_positive_weighings hxW,
  let u : E → E → ℝ := λ a, if ha : a ∈ X then classical.some (hZ.2 ha) else (λ b, 0),
  have hupos : ∀ {a}, a ∈ X → ∀ (b : fin m → ℝ), b ∈ Z → 0 < u a b,
  {
    rintro a ha,
    have := classical.some_spec (hZ.2 ha),
    sorry
  },
  have husum : ∀ {a}, a ∈ X → ∑ (b : fin m → ℝ) in Z, u a b = 1,
  {
    sorry
  },
  have hucenter : ∀ {a}, a ∈ X → Z.center_mass (u a) id = a,
  {
    sorry
  },
  let t : E → ℝ := λ b, if hb : b ∈ Z then ∑ (a : fin m → ℝ) in X, v a * u a b else 0,
  sorry
  /-rintro y (hyX : y ∈ X),
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combi_interior_subset_positive_weighings hxX,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combi_interior_subset_positive_weighings hxW,-/
  --rw mem_convex_hull,
  /-by_contra hXW,
  obtain ⟨y, hyX, hyW⟩ := not_subset.1 hXW,-/
  /-apply hxX.2,
  rw mem_combi_frontier_iff at ⊢,
  use [X.filter (λ w : E, w ∈ convex_hull (W : set E)), finset.filter_subset _ _],
  {
    rintro hXW,
    apply hWZ.2 (hZmin W _),
    simp,
    use [subset.trans hWZ.1 hZ.1],
    rintro y (hyX : y ∈ X),
    have := hXW hyX,
    simp at this,
    exact this.2,
  },
  {
    simp,
    apply convex_hull_mono (subset_inter (subset.refl _) _) hxX.1,
    by_contra hXW,
    rw not_subset at hXW,
    /-suffices hXW : ↑X ⊆ convex_hull ↑W,
    {
      apply convex_hull_mono (subset_inter (subset.refl _) hXW) hxX.1,
    },-/
    sorry
  }-/
end

end affine
