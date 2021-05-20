import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.simplex
import combinatorics.simplicial_complex.to_move.default
-- import data.nat.parity

open_locale classical affine big_operators
open set

namespace affine

/--
A simplicial complex in `R^m`.
TODO: generalise to normed affine spaces `E`, so this is `simplicial_complex E`.
-/
@[ext] structure simplicial_complex (E : Type*) [normed_group E] [normed_space ℝ E] :=
(faces : set (finset E))
(indep : ∀ {X}, X ∈ faces → affine_independent ℝ (λ p, p : (X : set E) → E))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E))

variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {x y : E} {X Y : finset E} {A : set (finset E)}
--local notation `E` := E

/--
A constructor for simplicial complexes by specifying a surcomplex whose set of faces is
downward closed.
-/
@[simp] def simplicial_complex.of_surcomplex
  (faces : set (finset E)) (subset_surcomplex : faces ⊆ S.faces)
  (down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces) :
  simplicial_complex E :=
{ faces := faces,
  indep := λ X hX, S.indep (subset_surcomplex hX),
  down_closed := λ X Y hX hYX, down_closed hX hYX,
  disjoint := λ X Y hX hY, S.disjoint (subset_surcomplex hX) (subset_surcomplex hY) }

/--
A constructor for simplicial complexes by specifying a set of faces to close downward.
-/
@[simp] def simplicial_complex.of_set_closure
  (indep : ∀ {X}, X ∈ A → affine_independent ℝ (λ p, p : (X : set E) → E))
  (disjoint : ∀ {X Y}, X ∈ A → Y ∈ A →
    convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E)) :
  simplicial_complex E :=
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
@[simp] def simplicial_complex.of_simplex
  (indep : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  simplicial_complex E :=
simplicial_complex.of_set_closure
  begin rintro Y (hY : Y = X), rw hY, exact indep end
  begin rintro Y Z (hY : Y = X) (hZ : Z = X), rw [hY, hZ, inter_self _, inter_self _],
    exact subset.refl _ end

lemma mem_simplex_complex_iff
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  Y ∈ (simplicial_complex.of_simplex hX).faces ↔ Y ⊆ X :=
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
def empty_simplicial_complex (E : Type*) [normed_group E] [normed_space ℝ E] :
  simplicial_complex E :=
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

lemma empty_mem_faces_of_nonempty :
  (S.faces).nonempty → ∅ ∈ S.faces :=
λ ⟨X, hX⟩, S.down_closed hX (empty_subset X)

/--
The underlying space of a simplicial complex.
-/
def simplicial_complex.space (S : simplicial_complex E) :
  set E :=
⋃ X ∈ S.faces, convex_hull (X : set E)

lemma mem_space_iff :
  x ∈ S.space ↔ ∃ X ∈ S.faces, x ∈ convex_hull (X : set E) :=
begin
  unfold simplicial_complex.space,
  rw mem_bUnion_iff,
end

lemma empty_space_of_empty_simplicial_complex :
  (empty_simplicial_complex E).space = ∅ :=
begin
  unfold empty_simplicial_complex simplicial_complex.space,
  simp,
end

lemma convex_hull_face_subset_space (hX : X ∈ S.faces) :
  convex_hull ↑X ⊆ S.space :=
λ x hx, mem_bUnion hX hx

lemma face_subset_space (hX : X ∈ S.faces) :
  (X : set E) ⊆ S.space :=
set.subset.trans (subset_convex_hull _) (convex_hull_face_subset_space hX)

def simplicial_complex.points (S : simplicial_complex E) :
  set E :=
⋃ k ∈ S.faces, (k : set E)

lemma points_subset_space :
  S.points ⊆ S.space :=
bUnion_subset_bUnion_right (λ x hx, subset_convex_hull x)

--noncomputable def simplicial_complex.dim (S : simplicial_complex E) :
--  ℕ :=

-- Dumb bug in mathlib, see
--https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/R.5Em.20is.20finite.20dimensional.20over.20R/near/231748016
--instance {m : ℕ} : finite_dimensional ℝ E := sorry

--Refinement of `size_bound`
lemma face_dimension_le_space_dimension [finite_dimensional ℝ E] (hX : X ∈ S.faces) :
  finset.card X ≤ finite_dimensional.finrank ℝ E + 1 :=
size_bound (S.indep hX)

def simplicial_complex.facets (S : simplicial_complex E) :
  set (finset E) :=
{X | X ∈ S.faces ∧ (∀ {Y}, Y ∈ S.faces → X ⊆ Y → X = Y)}

lemma facets_subset : S.facets ⊆ S.faces := λ X hX, hX.1

lemma not_facet_iff_subface : X ∈ S.faces → (X ∉ S.facets ↔ ∃ {Y}, Y ∈ S.faces ∧ X ⊂ Y) :=
begin
  rintro hX,
  split,
  { rintro (hX' : ¬(X ∈ S.faces ∧ (∀ {Y}, Y ∈ S.faces → X ⊆ Y → X = Y))),
    push_neg at hX',
    obtain ⟨Y, hY⟩ := hX' hX,
    exact ⟨Y, hY.1, ⟨hY.2.1, (λ hYX, hY.2.2 (finset.subset.antisymm hY.2.1 hYX))⟩⟩, },
  rintro ⟨Y, hY⟩ ⟨hX, hX'⟩,
  have := hX' hY.1 hY.2.1,
  rw this at hY,
  exact hY.2.2 (subset.refl Y),
end

lemma subfacet [finite_dimensional ℝ E] (hX : X ∈ S.faces) :
  ∃ {Y}, Y ∈ S.facets ∧ X ⊆ Y :=
begin
  have := id hX,
  revert this,
  apply finset.strong_downward_induction_on X,
  { rintro Y h hYcard hY,
    by_cases hYfacet : Y ∈ S.facets,
    { exact ⟨Y, hYfacet, finset.subset.refl _⟩, },
    obtain ⟨Z, hZ, hYZ⟩ := (not_facet_iff_subface hY).mp hYfacet,
    obtain ⟨W, hW⟩ := h (face_dimension_le_space_dimension hZ) hYZ hZ,
    exact ⟨W, hW.1, finset.subset.trans hYZ.1 hW.2⟩ },
  exact face_dimension_le_space_dimension hX,
end

lemma facets_empty (hS : S.faces = ∅) :
  S.facets = ∅ :=
begin
  rw [←subset_empty_iff, ←hS],
  exact facets_subset,
end

lemma facets_empty_iff_faces_empty [finite_dimensional ℝ E] :
  S.facets = ∅ ↔ S.faces = ∅ :=
begin
  classical,
  split,
  { intro h,
    by_contra h',
    rw [←ne.def, set.ne_empty_iff_nonempty] at h',
    obtain ⟨X, hX⟩ := h',
    obtain ⟨Y, hY, hZ⟩ := subfacet hX,
    rw h at hY,
    apply hY },
  exact facets_empty,
end

lemma facets_singleton (hS : S.faces = {X}) :
  S.facets = {X} :=
begin
  ext X,
  unfold simplicial_complex.facets,
  rw hS,
  simp,
  exact λ hX _, hX,
end

lemma facets_singleton_empty (hS : S.faces = {∅}) :
  S.facets = {∅} :=
facets_singleton hS

/--
The cells of a simplicial complex are its simplices whose dimension matches the one of the space.
-/
def simplicial_complex.cells (S : simplicial_complex E) :
  set (finset E) :=
{X | X ∈ S.faces ∧ X.card = finite_dimensional.finrank ℝ E + 1}

lemma cells_subset_facets [finite_dimensional ℝ E] :
  S.cells ⊆ S.facets :=
begin
  rintro X ⟨hX, hXcard⟩,
  by_contra,
  obtain ⟨Y, hY, hXY⟩ := (not_facet_iff_subface hX).mp h,
  have := finset.card_lt_card hXY,
  have := face_dimension_le_space_dimension hY,
  linarith,
end

/--
The subcells of a simplicial complex are its simplices whose cardinality matches the dimension of
the space. They are thus one smaller than cells.
-/
def simplicial_complex.subcells (S : simplicial_complex E) :
  set (finset E) :=
{X | X ∈ S.faces ∧ X.card = finite_dimensional.finrank ℝ E}

def simplicial_complex.vertices (S : simplicial_complex E) :
  set E :=
{x | {x} ∈ S.faces}

lemma mem_of_mem_convex_hull (hx : {x} ∈ S.faces) (hX : X ∈ S.faces)
  (hxX : x ∈ convex_hull (X : set E)) :
  x ∈ X :=
begin
  have h := S.disjoint hx hX ⟨by simp, hxX⟩,
  by_contra H,
  norm_cast at h,
  rw [finset.inter_comm, finset.disjoint_iff_inter_eq_empty.1 (finset.disjoint_singleton.2 H)] at h,
  simp at h,
  exact h,
end

lemma subset_of_convex_hull_subset_convex_hull (hX : X ∈ S.faces) (hY : Y ∈ S.faces)
  (hXY : convex_hull (X : set E) ⊆ convex_hull ↑Y) :
  X ⊆ Y :=
λ x hxX, mem_of_mem_convex_hull (S.down_closed hX (finset.singleton_subset_iff.2 hxX)) hY
  (hXY (subset_convex_hull ↑X hxX))

lemma disjoint_interiors (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (hxX : x ∈ combi_interior X)
  (hxY : x ∈ combi_interior Y) :
  X = Y :=
begin
  by_contra,
  have hXY : X ∩ Y ⊂ X,
  { use finset.inter_subset_left X Y,
    intro H,
    exact hxY.2 (set.mem_bUnion ⟨subset.trans H (finset.inter_subset_right X Y), (λ H2,
      h (finset.subset.antisymm (subset.trans H (finset.inter_subset_right X Y)) H2))⟩ hxX.1) },
  refine hxX.2 (mem_bUnion hXY _),
  exact_mod_cast S.disjoint hX hY ⟨hxX.1, hxY.1⟩,
end

lemma disjoint_interiors_aux (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (h : X ≠ Y) :
  disjoint (combi_interior X) (combi_interior Y) :=
λ x hx, h (disjoint_interiors hX hY hx.1 hx.2)

lemma eq_singleton_of_singleton_mem_combi_interior (hx : {x} ∈ S.faces) (hX : X ∈ S.faces)
  (hxX : x ∈ combi_interior X) :
    X = {x} :=
begin
  apply disjoint_interiors hX hx hxX,
  rw combi_interior_singleton,
  exact mem_singleton x,
end

lemma combi_interiors_cover :
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
lemma combi_interiors_partition (hx : x ∈ S.space) :
  ∃! X, X ∈ S.faces ∧ x ∈ combi_interior X :=
begin
  rw combi_interiors_cover at hx,
  simp only [set.mem_bUnion_iff] at hx,
  obtain ⟨X, hX, hxX⟩ := hx,
  exact ⟨X, ⟨⟨hX, hxX⟩, (λ Y ⟨hY, hxY⟩, disjoint_interiors hY hX hxY hxX)⟩⟩,
end

lemma mem_convex_hull_iff :
  x ∈ convex_hull (X : set E) ↔ ∃ Y ⊆ X, x ∈ combi_interior Y :=
begin
  simp [simplex_combi_interiors_cover],
end

lemma mem_combi_frontier_iff' :
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

lemma subset_of_combi_interior_inter_convex_hull_nonempty (hX : X ∈ S.faces) (hY : Y ∈ S.faces)
  (hXY : (combi_interior X ∩ convex_hull (Y : set E)).nonempty) :
  X ⊆ Y :=
begin
  obtain ⟨x, hxX, hxY⟩ := hXY,
  obtain ⟨Z, hZY, hxZ⟩ := mem_convex_hull_iff.1 hxY,
  rw disjoint_interiors hX (S.down_closed hY hZY) hxX hxZ,
  exact hZY,
end

lemma simplex_combi_interiors_split_interiors (hY : affine_independent ℝ (λ p, p : (Y : set E) → E))
  (hXY : convex_hull (X : set E) ⊆ convex_hull ↑Y) :
  ∃ Z ⊆ Y, combi_interior X ⊆ combi_interior Z :=
begin
  let S := simplicial_complex.of_simplex hY,
  let F := Y.powerset.filter (λ W : finset E, (X : set E) ⊆ convex_hull W),
  sorry
  /-obtain ⟨Z, hZ, hZmin⟩ := finset.inf' _
  (begin
    use Y,
    simp only [true_and, finset.mem_powerset_self, finset.mem_filter],
    exact subset.trans (subset_convex_hull _) hXY,
  end : F.nonempty)
  begin
    rintro A B hA hB,
    simp at ⊢ hA hB,
    exact ⟨finset.subset.trans (finset.inter_subset_left _ _) hA.1,
      subset.trans (subset_inter hA.2 hB.2) (S.disjoint ((mem_simplex_complex_iff hY).2 hA.1)
      ((mem_simplex_complex_iff hY).2 hB.1))⟩
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
  have hupos : ∀ {a}, a ∈ X → ∀ (b : E), b ∈ Z → 0 < u a b,
  {
    rintro a ha,
    have := classical.some_spec (hZ.2 ha),
    sorry
  },
  have husum : ∀ {a}, a ∈ X → ∑ (b : E) in Z, u a b = 1,
  {
    sorry
  },
  have hucenter : ∀ {a}, a ∈ X → Z.center_mass (u a) id = a,
  {
    sorry
  },
  let t : E → ℝ := λ b, if hb : b ∈ Z then ∑ (a : E) in X, v a * u a b else 0,-/
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
