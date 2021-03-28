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
-- import data.nat.parity

open_locale classical affine big_operators
open set
variables {m n : ℕ}
local notation `E` := fin m → ℝ

namespace affine

/--
A simplicial complex in `R^m`.
TODO: generalise to normed affine spaces `E`, so this is `simplicial_complex E`.
-/
@[ext] structure simplicial_complex (m : ℕ) :=
(faces : set (finset (fin m → ℝ)))
(indep : ∀ {X}, X ∈ faces → affine_independent ℝ (λ p, p : (X : set (fin m → ℝ)) → (fin m → ℝ)))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set (fin m → ℝ)))

variables {S : simplicial_complex m}

/--
A constructor for simplicial complexes by specifying a surcomplex and making the set of faces
downward closed.
-/
@[simp] def simplicial_complex.of_surcomplex {m : ℕ} {S : simplicial_complex m}
  (faces : set (finset (fin m → ℝ))) (subset_surcomplex : faces ⊆ S.faces)
  (down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces) :
  simplicial_complex m :=
{ faces := faces,
  indep := λ X hX, S.indep (subset_surcomplex hX),
  down_closed := λ X Y hX hYX, down_closed hX hYX,
  disjoint := λ X Y hX hY, S.disjoint (subset_surcomplex hX) (subset_surcomplex hY) }

/--
A constructor for simplicial complexes by specifying a set of faces to close downward.
-/
def simplicial_complex.of_set_closure {A : set (finset E)}
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
    {
      have := disjoint_convex_hull_of_subsets (indep hY) hWY (finset.inter_subset_left Y Z),
      norm_cast at this hxYZ,
      exact_mod_cast convex_hull_mono
        (finset.inter_subset_inter_left (finset.inter_subset_right Y Z)) (this ⟨hxW, hxYZ⟩),
    },
    have hxYX : x ∈ convex_hull (Y ∩ X : set E),
    {
      have := disjoint_convex_hull_of_subsets (indep hZ) (finset.inter_subset_right Y Z) hXZ,
      norm_cast at this hxYZ,
      exact_mod_cast convex_hull_mono
        (finset.inter_subset_inter_right (finset.inter_subset_left Y Z)) (this ⟨hxYZ, hxX⟩),
    },
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

/-def simplicial_complex.dimension (S : simplicial_complex m) {X : finset (fin m → ℝ)} : ℕ :=
  Sup {X.card - 1 | X ∈ S.faces}-/

/-The dimension of a simplicial complex is the maximal dimension of its faces-/
/-def simplicial_complex.dimension (S : simplicial_complex m) : ℕ :=
 Sup {finset.card (X : set E) | X ∈ S.faces}-/

--Refinement of `size_bound`
lemma simplex_dimension_le_space_dimension {S : simplicial_complex m} {X : finset E} :
  X ∈ S.faces → finset.card X ≤ m + 1 := λ hX, size_bound (S.indep hX)

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

lemma subfacet {S : simplicial_complex m} {X : finset (fin m → ℝ)} :
  X ∈ S.faces → ∃ {Y}, Y ∈ S.facets ∧ X ⊆ Y :=
begin
  rintro hX,
  apply finset.strong_downward_induction_on (λ Y hY, simplex_dimension_le_space_dimension hY) hX,
  rintro Y hY h,
  by_cases hYfacet : Y ∈ S.facets,
  { exact ⟨Y, hYfacet, finset.subset.refl _⟩, },
  { obtain ⟨Z, hZ₁, hZ₂⟩ := (not_facet_iff_subface hY).mp hYfacet,
    obtain ⟨W, hW⟩ := h hZ₁ hZ₂,
    exact ⟨W, hW.1, finset.subset.trans hZ₂.1 hW.2⟩, }
end

lemma facets_empty {S : simplicial_complex m} : S.faces = ∅ → S.facets = ∅ :=
begin
  intro h,
  rw [←subset_empty_iff, ←h],
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
A simplicial complex is pure of dimension n iff all its facets have dimension n.
-/
def simplicial_complex.pure_of (S : simplicial_complex m) (n : ℕ) : Prop :=
  ∀ ⦃X⦄, X ∈ S.facets → (X : finset _).card = n

/--
A simplicial complex is pure iff all its facets have the same dimension.
-/
def simplicial_complex.pure (S : simplicial_complex m) : Prop := ∃ n : ℕ, S.pure_of n

/--
The pureness of a pure simplicial complex is the cardinality of its facets. Set to 0 for non pure
complexes.
-/
noncomputable def simplicial_complex.pureness (S : simplicial_complex m) : ℕ :=
  if hS : S.pure then classical.some hS else 0

lemma pureness_def {S : simplicial_complex m} (hS : S.pure) : S.pure_of S.pureness :=
begin
  unfold simplicial_complex.pureness,
  rw dif_pos hS,
  exact classical.some_spec hS,
end

lemma pureness_unique_of_nonempty {S : simplicial_complex m} {a b : ℕ} (hS : S.faces.nonempty)
  (ha : S.pure_of a) (hb : S.pure_of b) :
  a = b :=
begin
  obtain ⟨X, hX⟩ := hS,
  obtain ⟨Y, hY, hYX⟩ := subfacet hX,
  rw [←ha hY, ←hb hY],
end

--same below. I really don't get what i'm doing wrong
lemma pureness_def' {S : simplicial_complex m} (hSnonempty : S.faces.nonempty) (hS : S.pure_of n) :
  S.pureness = n :=
pureness_unique_of_nonempty hSnonempty (pureness_def ⟨_, hS⟩) hS

lemma simplex_dimension_le_pureness {S : simplicial_complex m} {n : ℕ} (hS : S.pure_of n)
  {X : finset (fin m → ℝ)} : X ∈ S.faces → X.card ≤ n :=
begin
  rintro hX,
  obtain ⟨Y, hY, hXY⟩ := subfacet hX,
  rw ← hS hY,
  exact finset.card_le_of_subset hXY,
end

lemma facet_iff_dimension_eq_pureness {S : simplicial_complex m} (hS : S.pure)
  {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  X ∈ S.facets ↔ X.card = S.pureness :=
begin
  refine ⟨λ t, pureness_def hS t, λ hXcard, _⟩,
  { refine ⟨hX, λ Y hY hXY, finset.eq_of_subset_of_card_le hXY _⟩,
    rw hXcard,
    exact simplex_dimension_le_pureness (pureness_def hS) hY }
end

/--
A simplicial complex is pure iff there exists n such that all faces are subfaces of some
(n - 1)-dimensional face.
-/
lemma pure_iff {S : simplicial_complex m} : S.pure ↔ ∃ n : ℕ, ∀ {X}, X ∈ S.faces →
  ∃ {Y}, Y ∈ S.faces ∧ finset.card Y = n ∧ X ⊆ Y :=
begin
  split,
  { rintro hS,
    use S.pureness,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := subfacet hX,
    exact ⟨Y, facets_subset hY, pureness_def hS hY, hXY⟩ },
  { rintro ⟨n, hS⟩,
    use n,
    rintro X ⟨hX, hXmax⟩,
    obtain ⟨Y, hY, hYcard, hXY⟩ := hS hX,
    rw hXmax hY hXY,
    exact hYcard, }
end

lemma pure_of_empty {S : simplicial_complex m} (h : S.faces = {∅}) : S.pure :=
begin
  use 0,
  rintro X hX,
  have := facets_subset hX,
  rw h at this,
  change X = ∅ at this,
  rw this,
  exact finset.card_empty,
end

lemma facets_subset_facets_of_pureness_eq_pureness_of_subcomplex {S₁ S₂ : simplicial_complex m}
  (hS : S₁.faces ⊆ S₂.faces) (hS₁ : S₁.pure_of n) (hS₂ : S₂.pure_of n) : S₁.facets ⊆ S₂.facets :=
begin
  rintro X hX,
  use hS hX.1,
  rintro Y hY hXY,
  have : Y.card ≤ X.card,
  { rw hS₁ hX,
    exact simplex_dimension_le_pureness hS₂ hY },
  exact finset.eq_of_subset_of_card_le hXY this,
end

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

def simplicial_complex.skeleton (S : simplicial_complex m) (k : ℕ) :
  simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X ∈ S.faces | finset.card X ≤ k + 1}
  (λ X ⟨hX, _⟩, hX)
  (λ X Y hX hY, ⟨S.down_closed hX.1 hY, le_trans (finset.card_le_of_subset hY) hX.2⟩)

lemma skeleton_subcomplex {S : simplicial_complex m} {k : ℕ} :
  (S.skeleton k).faces ⊆ S.faces :=
λ X ⟨hX, _⟩, hX

lemma pure_skeleton_of_pure {S : simplicial_complex m} (k : ℕ) (hS : S.pure_of n) :
  (S.skeleton k).pure_of (min n (k + 1)) :=
begin
  cases le_or_gt n (k + 1) with hmin hmin,
  {
    rw min_eq_left hmin,
    rintro X hXskel,
    obtain ⟨Y, hY, hXY⟩ := subfacet (skeleton_subcomplex (facets_subset hXskel)),
    have hYskel : Y ∈ (S.skeleton k).faces,
    { use facets_subset hY,
      simp,
      rw hS hY,
      exact hmin, },
    rw hXskel.2 hYskel hXY,
    exact hS hY },
  { rw min_eq_right (le_of_lt hmin),
    rintro X ⟨⟨hX, hXcard⟩, hXmax⟩,
    obtain ⟨Y, hY, hXY⟩ := subfacet hX,
    have : k + 1 - X.card + X.card ≤ Y.card,
    { rw hS hY,
      rw nat.sub_add_cancel hXcard,
      exact le_of_lt hmin, },
    obtain ⟨Z, hXZ, hZY, hZcard⟩ := finset.exists_intermediate_set (k + 1 - X.card) this hXY,
      rw nat.sub_add_cancel hXcard at hZcard,
    rw hXmax ⟨S.down_closed (facets_subset hY) hZY, le_of_eq hZcard⟩ hXZ,
    exact hZcard, }
end

lemma skeleton_pureness_eq_min_pureness_dimension {S : simplicial_complex m} {k : ℕ} (hS : S.pure) :
  (S.skeleton k).pureness = min S.pureness (k + 1) := sorry

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
  {
    rintro ⟨hY, Z, (hZ : Z = {x}), hYZ⟩,
    rw hZ at hYZ,
    simp,
    --exact_mod_cast set.subset_singleton_iff.1 hYZ,
    sorry -- @Bhavik easy but I can't
  },
  {
    have hxS : {x} ∈ (S.closure {{x}}).faces := ⟨hx, {x}, rfl, finset.subset.refl {x}⟩,
    rintro ⟨rfl | rfl⟩,
    exact empty_mem_faces_of_nonempty (nonempty_of_mem hxS),
    rw eq_of_mem_singleton ᾰ,
    exact hxS,
  }
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

lemma closure_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hAB : A ⊆ B) :
  (S.closure A).faces ⊆ (S.closure B).faces := λ X ⟨hX, Y, hY, hXY⟩, ⟨hX, Y, hAB hY, hXY⟩

/--
The open star of a set of faces is the union of their surfaces. Note that the star is all of the
original complex as soon as A contains the empty set.
-/
def simplicial_complex.star (S : simplicial_complex m) : set (finset (fin m → ℝ)) →
  set (finset (fin m → ℝ)) := λ A, {X | X ∈ S.faces ∧ ∃ {Y}, Y ∈ A ∧ Y ⊆ X}

lemma star_empty {S : simplicial_complex m} : S.star ∅ = ∅ :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma star_singleton_empty {S : simplicial_complex m} : S.star {∅} = S.faces :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma mem_star_singleton_iff {S : simplicial_complex m} {X Y : finset (fin m → ℝ)} :
  Y ∈ S.star {X} ↔ Y ∈ S.faces ∧ X ⊆ Y :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma mem_star_iff {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  {X : finset (fin m → ℝ)} : X ∈ S.star A ↔ X ∈ S.faces ∩ ⋃ (Y ∈ A), {Z | Y ⊆ Z} :=
begin
  unfold simplicial_complex.star,
  simp,
end

lemma star_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} : S.star A ⊆ S.faces :=
  λ X hX, hX.1

lemma subset_star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.faces ∩ A ⊆ S.star A := λ X hX, ⟨hX.1, X, hX.2, subset.refl X⟩

lemma star_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hAB : A ⊆ B) :
  S.star A ⊆ S.star B := λ X ⟨hX, Y, hY, hYX⟩, ⟨hX, Y, hAB hY, hYX⟩

lemma star_up_closed {S : simplicial_complex m} {X Y : finset (fin m → ℝ)}
  {A : set (finset (fin m → ℝ))} : X ∈ S.faces → Y ∈ S.star A → Y ⊆ X → X ∈ S.star A :=
  λ hX ⟨hY, Z, hZ, hZY⟩ hYX, ⟨hX, Z, hZ, subset.trans hZY hYX⟩

lemma Union_star_eq_star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (⋃ (X ∈ A), S.star {X}) = S.star A :=
begin
  ext X,
  rw mem_bUnion_iff,
  split,
  {
    rintro ⟨Y', hY, hX, Y, (hYY' : Y = Y'), hYX⟩,
    subst hYY',
    exact ⟨hX, Y, hY, hYX⟩,
  },
  {
    rintro ⟨hX, Y, hY, hYX⟩,
    exact ⟨Y, hY, hX, Y, mem_singleton Y, hYX⟩,
  }
end

--Can maybe get rid of hX?
lemma star_singleton_eq_Inter_star_singleton {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  S.star {X} = ⋂ x ∈ X, S.star {{x}} :=
begin
  ext Y,
  split,
  {
    rintro ⟨hY, Z, (hZ : Z = X), hXY⟩,
    rw hZ at hXY,
    exact mem_bInter (λ x (hx : x ∈ X), ⟨hY, {x}, mem_singleton {x},
      finset.singleton_subset_iff.2 (hXY hx)⟩),
  },
  {
    rintro h,
    rw mem_star_singleton_iff,
    split,
    {
      --rw mem_bInter_iff at h, @Bhavik, bug here, maybe there's a workaround?
      sorry
    },
    rintro x hx,
    obtain ⟨hY, Z, (hZ : Z = {x}), hxY⟩ := mem_bInter_iff.1 h x hx,
    rw hZ at hxY,
    exact finset.singleton_subset_iff.1 hxY,
  }
end

/--
The closed star of a complex S and a set A is the complex whose faces are in S and share a surface
with some face in A
-/
def simplicial_complex.Star (S : simplicial_complex m) : set (finset (fin m → ℝ)) →
  simplicial_complex m := λ A, {
  faces := {X | ∃ {Y Z}, Y ∈ A ∧ Z ∈ S.faces ∧ X ⊆ Z ∧ Y ⊆ Z},
  indep := λ X ⟨_, Z, _, hZ, hXZ, _⟩, S.indep (S.down_closed hZ hXZ),
  down_closed := λ X W ⟨Y, Z, hY, hZ, hXZ, hYZ⟩ hWX, ⟨Y, Z, hY, hZ, subset.trans hWX hXZ, hYZ⟩,
  disjoint := λ X X' ⟨_, Z, _, hZ, hXZ, _⟩ ⟨_, Z', _, hZ', hXZ', _⟩,
    S.disjoint (S.down_closed hZ hXZ) (S.down_closed hZ' hXZ') }

lemma Star_empty {S : simplicial_complex m} : (S.Star ∅).faces = ∅ :=
begin
  unfold simplicial_complex.Star,
  simp,
end

lemma Star_singleton_empty {S : simplicial_complex m} : S.Star {∅} = S :=
begin
  ext X,
  split,
  {
    rintro ⟨Y, Z, (hY : Y = ∅), hZ, hXZ, hYZ⟩,
    exact S.down_closed hZ hXZ,
  },
  {
    rintro hX,
    exact ⟨∅, X, rfl, hX, subset.refl _, empty_subset X⟩,
  }
end

lemma mem_Star_singleton_iff {S : simplicial_complex m} {X Y : finset (fin m → ℝ)} :
  Y ∈ (S.Star {X}).faces ↔ ∃ {Z}, Z ∈ S.faces ∧ Y ⊆ Z ∧ X ⊆ Z :=
begin
  unfold simplicial_complex.Star,
  simp,
end

/--
The closed star of a set is the closure of its open star.
-/
lemma Star_eq_closure_star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.Star A = S.closure (S.star A) :=
begin
  ext X,
  split,
  {
    rintro ⟨Y, Z, hY, hZ, hXZ, hYZ⟩,
    exact ⟨S.down_closed hZ hXZ, Z, ⟨hZ, Y, hY, hYZ⟩, hXZ⟩,
  },
  {
    rintro ⟨hX, Z, ⟨hZ, Y, hY, hYZ⟩, hXZ⟩,
    exact ⟨Y, Z, hY, hZ, hXZ, hYZ⟩,
  }
end

lemma Star_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.Star A).faces ⊆ S.faces := λ X ⟨_, Z, _, hZ, hXZ, _⟩, S.down_closed hZ hXZ

lemma subset_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.faces ∩ A ⊆ (S.Star A).faces :=
  λ X ⟨hXS, hXA⟩, ⟨X, X, hXA, hXS, subset.refl X, subset.refl X⟩

lemma star_subset_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.star A ⊆ (S.Star A).faces := λ X ⟨hX, Y, hY, hYX⟩, ⟨Y, X, hY, hX, subset.refl X, hYX⟩

lemma Star_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hAB : A ⊆ B) :
  (S.Star A).faces ⊆ (S.Star B).faces :=
begin
  rw [Star_eq_closure_star, Star_eq_closure_star],
  exact closure_mono (star_mono hAB),
end

lemma Star_facet_iff {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  {X : finset (fin m → ℝ)} :
  X ∈ (S.Star A).facets ↔ X ∈ S.facets ∧ ∃ {Y}, Y ∈ A ∧ Y ⊆ X :=
begin
  split,
  {
    rintro ⟨⟨Y, Z, hY, hZ, hXZ, hYZ⟩, hXmax⟩,
    have := hXmax ⟨Y, Z, hY, hZ, subset.refl Z, hYZ⟩ hXZ,
    subst this,
    split,
    {
      use hZ,
      rintro W hW hXW,
      exact hXmax (star_subset_Star ⟨hW, Y, hY, subset.trans hYZ hXW⟩) hXW,
    },
    { exact ⟨Y, hY, hYZ⟩, }
  },
  {
    rintro ⟨hX, Y, hY, hYX⟩,
    split,
    exact ⟨Y, X, hY, hX.1, subset.refl X, hYX⟩,
    rintro Z hZ,
    exact hX.2 (Star_subset hZ),
  }
end

lemma pure_Star_of_pure {S : simplicial_complex m} {n : ℕ} {A : set (finset (fin m → ℝ))} :
  S.pure_of n → (S.Star A).pure_of n := λ hS X hX, hS (Star_facet_iff.1 hX).1

lemma Star_pureness_eq_pureness {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hS : S.pure) (hSA : (S.Star A).faces.nonempty) : (S.Star A).pureness = S.pureness :=
begin
  obtain ⟨n, hS⟩ := hS,
  obtain ⟨X, hX⟩ := id hSA,
  rw [pureness_def' hSA (pure_Star_of_pure hS), pureness_def' (hSA.mono Star_subset) hS],
end

def simplicial_complex.link (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m := {
  faces := {X | (∀ {W}, W ∈ A → disjoint W X) ∧ ∃ {Y Z}, Y ∈ A ∧ Z ∈ S.faces ∧ X ⊆ Z ∧ Y ⊆ Z},
  indep := λ X ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩, S.indep (S.down_closed hZ hXZ),
  down_closed := begin
    rintro X W ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩ hWX,
    split,
    { rintro V hV,
      exact finset.disjoint_of_subset_right hWX (hXdisj hV), },
    { exact ⟨Y, Z, hY, hZ, subset.trans hWX hXZ, hYZ⟩ }
  end,
  disjoint := λ X X' ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩ ⟨hXdisj', Y', Z', hY', hZ', hXZ', hYZ'⟩,
    S.disjoint (S.down_closed hZ hXZ) (S.down_closed hZ' hXZ') }

/-Previous def
def simplicial_complex.link (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m := simplicial_complex.of_surcomplex
  ((S.Star A).faces \ S.star (S.closure A).faces) (λ X hX, Star_subset hX.1)
  begin
    rintro X Y hX hYX,
    split,
    { exact (S.Star A).down_closed hX.1 hYX},
    {
      rintro ⟨hY, Z, ⟨W, hW, hZW⟩, hZY⟩,
      apply hX.2,
      apply star_up_closed (Star_subset hX.1) _ (subset.trans hZY hYX),
      apply subset_star,
      use S.down_closed hY hZY,
      apply (S.closure A).down_closed _ hZW,
      apply faces_subset_closure,
      exact hW,
    }
  end-/

lemma link_empty {S : simplicial_complex m} : (S.link ∅).faces = ∅ :=
begin
  unfold simplicial_complex.link,
  simp,
end

lemma link_singleton_empty {S : simplicial_complex m} : S.link {∅} = S :=
begin
  ext X,
  split,
  {
    rintro ⟨_, _, Z, _, hZ, hXZ, _⟩,
    exact S.down_closed hZ hXZ,
  },
  {
    rintro hX,
    split,
    { rintro W (h : W = ∅),
      rw h,
      exact finset.disjoint_empty_left X, },
    exact ⟨∅, X, rfl, hX, subset.refl X, empty_subset X⟩,
  }
end

lemma mem_link_singleton_iff {S : simplicial_complex m} {X Y : finset (fin m → ℝ)} :
  Y ∈ (S.link {X}).faces ↔ disjoint X Y ∧ ∃ {Z}, Z ∈ S.faces ∧ Y ⊆ Z ∧ X ⊆ Z :=
begin
  unfold simplicial_complex.link,
  simp,
end

lemma link_singleton_subset {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ≠ ∅) :
  (S.link {X}).faces ⊆ (S.Star {X}).faces \ S.star {X} :=
begin
  rintro Y ⟨hY, W, Z, (hWX : W = X), hZ, hYZ, hWZ⟩,
  simp at hY,
  subst hWX,
  split,
  { exact ⟨W, Z, mem_singleton W, hZ, hYZ, hWZ⟩, },
  { rintro h,
    rw mem_star_singleton_iff at h,
    exact hX (disjoint_self.1 (finset.disjoint_of_subset_right h.2 hY)), }
end

lemma link_singleton_eq_Star_minus_star_iff_singleton {S : simplicial_complex m}
  {X : finset (fin m → ℝ)} (hX : X ≠ ∅) :
  (S.link {X}).faces = (S.Star {X}).faces \ S.star {X} ↔ X.card = 1 :=
begin
  split,
  {
    sorry --true? The PDF claims so but I'm not sure
  },
  {
    rintro hXcard,
    apply subset.antisymm (link_singleton_subset hX),
    rintro Y ⟨h, hYstar⟩,
    obtain ⟨Z, hZ, hYZ, hXZ⟩ := mem_Star_singleton_iff.1 h,
    split,
    {
      obtain ⟨x, hxX⟩ := finset.card_eq_one.1 hXcard,
      rintro W (hW : W = X),
      subst hW,
      subst hxX,
      rw finset.singleton_disjoint,
      rintro hx,
      apply hYstar,
      rw [mem_star_singleton_iff, finset.singleton_subset_iff],
      exact ⟨S.down_closed hZ hYZ, hx⟩,
    },
    exact ⟨X, Z, rfl, hZ, hYZ, hXZ⟩,
  }
end

lemma link_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.link A).faces ⊆ S.faces := λ X ⟨hXdisj, Y, Z, hY, hZ, hXZ, hYZ⟩, S.down_closed hZ hXZ

lemma link_eq_Star_sub_star_closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.link A).faces = (S.Star A).faces \ S.star ((S.closure A).faces \ {∅}) :=
begin
  ext X,
  split,
  {
    rintro ⟨hXdisj, hXStar⟩,
    use hXStar,
    rintro ⟨hX, Y, ⟨⟨hY, Z, hZ, hYZ⟩, (hYnonempty : Y ≠ ∅)⟩, hYX⟩,
    have hYZX : Y ⊆ Z ∩ X := finset.subset_inter hYZ hYX,
    rw finset.disjoint_iff_inter_eq_empty.mp (hXdisj hZ) at hYZX,
    exact hYnonempty (finset.subset_empty.mp hYZX),
  },
  {
    rintro ⟨hXStar, hX'⟩,
    split,
    {
      rintro W hW,
      rw finset.disjoint_iff_inter_eq_empty,
      apply finset.eq_empty_of_forall_not_mem,
      rintro x hx,
      apply hX',
      use Star_subset hXStar,
      use {x},
      split,
      split,
      {
        unfold simplicial_complex.closure simplicial_complex.of_surcomplex,
        simp,
        exact ⟨S.down_closed (Star_subset hXStar) (subset.trans (finset.singleton_subset_iff.2 hx)
          (finset.inter_subset_right _ _)), W, hW, finset.inter_subset_left _ _ hx⟩,
      },
      rintro (h : {x} = ∅),
      exact (finset.singleton_ne_empty x) h,
      exact finset.singleton_subset_iff.2 (finset.inter_subset_right W X hx),
    },
    { exact hXStar }
  }
end
/-

lemma link_facet_iff {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} {n k : ℕ}
  (hS : S.pure_of n) {X : finset (fin m → ℝ)} (hA : ∀ {W}, W ∈ A → (W : finset _).card = k) :
  X ∈ (S.link A).facets ↔ ∃ {W Y}, W ∈ A ∧ Y ∈ S.facets ∧ W ⊆ Y ∧ X = Y \ W :=-/

lemma link_facet_iff {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} {n k : ℕ}
  (hS : S.pure_of n) {X : finset (fin m → ℝ)}
  (hA : ∀ {V W Y}, V ∈ A → W ∈ A → Y ∈ S.faces → W ⊆ Y → (V ∩ Y : finset _).nonempty → V = W) :
  X ∈ (S.link A).facets ↔ ∃ {W Y}, W ∈ A ∧ Y ∈ S.facets ∧ W ⊆ Y ∧ X = Y \ W :=
begin
  split,
  {
    rintro ⟨⟨hXdisj, W, Z, hW, hZ, hXZ, hWZ⟩, hXmax⟩,
    obtain ⟨Y, hY, hZY⟩ := subfacet hZ,
    use [W, Y, hW, hY, subset.trans hWZ hZY],
    apply hXmax,
    {
      split,
      {
        rintro V hV,
        rw finset.disjoint_iff_inter_eq_empty,
        by_contra hVYW,
        change V ∩ (Y \ W) ≠ ∅ at hVYW,
        obtain ⟨x, hx⟩ := finset.nonempty_iff_ne_empty.2 hVYW,
        rw [finset.mem_inter, finset.mem_sdiff] at hx,
        have := hA hV hW (facets_subset hY) (subset.trans hWZ hZY)
          ⟨x, finset.mem_inter.2 ⟨hx.1, hx.2.1⟩⟩,
        rw this at hx,
        exact hx.2.2 hx.1,
      },
      { exact ⟨W, Y, hW, facets_subset hY, finset.sdiff_subset_self, subset.trans hWZ hZY⟩ }
    },
    {
      rintro x hx,
      rw finset.mem_sdiff,
      use finset.subset.trans hXZ hZY hx,
      rintro hxW,
      have : x ∈ W ∩ X := finset.mem_inter.2 ⟨hxW, hx⟩,
      rw finset.disjoint_iff_inter_eq_empty.1 (hXdisj hW) at this,
      exact finset.not_mem_empty x this,
    }
  },
  {
    rintro ⟨W, Y, hW, hY, hWY, rfl⟩,
    split,
    {
      split,
      {
        rintro V hV,
        rw finset.disjoint_iff_inter_eq_empty,
        by_contra hVYW,
        change V ∩ (Y \ W) ≠ ∅ at hVYW,
        obtain ⟨x, hx⟩ := finset.nonempty_iff_ne_empty.2 hVYW,
        rw [finset.mem_inter, finset.mem_sdiff] at hx,
        have := hA hV hW (facets_subset hY) hWY ⟨x, finset.mem_inter.2 ⟨hx.1, hx.2.1⟩⟩,
        rw this at hx,
        exact hx.2.2 hx.1,
      },
      { exact ⟨W, Y, hW, facets_subset hY, finset.sdiff_subset_self, hWY⟩ }
    },
    {
      rintro X ⟨hXdisj, U, V, hU, hV, hXV, hUV⟩ hYWX,
      apply finset.subset.antisymm hYWX,
      rintro x hx,
      have := hA hU hW (facets_subset hY) hWY,
      rw finset.mem_sdiff,
      --have := hA hV hW (facets_subset hY) hWY ⟨x, finset.mem_inter.2 ⟨hx.1, hx.2.1⟩⟩,
      sorry
      /-apply finset.eq_of_subset_of_card_le hYWX,
      rw finset.card_sdiff hWY,
      have := finset.card_le_of_subset (finset.union_subset hUV hXV),
      rw [finset.card_disjoint_union (hXdisj hU), hA hU] at this,
      rw [hA hW, hS hY],
      exact nat.le_sub_left_of_add_le (le_trans this (simplex_dimension_le_pureness hS hV)),-/
    }
  }
end

lemma pure_link_of_pure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} {n k : ℕ}
  (hA : ∀ {X}, X ∈ A → (X : finset _).card = k) (hS : S.pure_of n) :
  (S.link A).pure_of (n - k) :=
begin
  rintro X ⟨⟨hXdisj, W, Z, hW, hZ, hXZ, hWZ⟩, hXmax⟩, --easy once we have `link_facet_iff`
  sorry
end

/--
The erasure of a simplicial complex S and a set A is the subcomplex obtained after removing all
faces having a vertex in A.
-/
def simplicial_complex.erasure (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m := {
  faces := {X | X ∈ S.faces ∧ ∀ {W}, W ∈ A → disjoint W X},
  indep := λ X hX, S.indep hX.1,
  down_closed := λ X Y ⟨hX, hXA⟩ hYX, ⟨S.down_closed hX hYX, λ Z hZ,
    finset.disjoint_of_subset_right hYX (hXA hZ)⟩,
  disjoint := λ X Y hX hY, S.disjoint hX.1 hY.1 }
/-Previous def
def simplicial_complex.erasure (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X | X ∈ S.faces ∧ ∀ {Y}, Y ∈ A → disjoint X Y}
  (λ X hX, hX.1)
  (λ X Y ⟨hX, hXA⟩ hYX, ⟨S.down_closed hX hYX, λ Z hZ, finset.disjoint_of_subset_left hYX (hXA hZ)⟩)-/

lemma erasure_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.erasure A).faces ⊆ S.faces := λ X hX, hX.1

lemma link_eq_erasure_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.link A = (S.Star A).erasure A :=
begin
  ext X,
  split,
  {
    rintro ⟨hXdisj, hXStar⟩,
    exact ⟨hXStar, (λ W, hXdisj)⟩,
  },
  {
    rintro ⟨hXStar, hXdisj⟩,
    exact ⟨(λ W, hXdisj), hXStar⟩,
  }
end

lemma erasure_and_closure_star_partition {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.faces = (S.erasure A).faces ∪ S.star ((S.closure A).faces \ {∅}) :=
begin
  ext X,
  split,
  {
    rintro hX,
    by_cases (∀ {W}, W ∈ A → disjoint W X),
    {
      left,
      exact ⟨hX, (λ W, h)⟩,
    },
    {
      right,
      push_neg at h,
      obtain ⟨W, hW, hWX⟩ := h,
      rw finset.disjoint_iff_inter_eq_empty at hWX,
      change W ∩ X ≠ ∅ at hWX,
      obtain ⟨x, hx⟩ := finset.nonempty_iff_ne_empty.2 hWX,
      rw ← finset.singleton_subset_iff at hx,
      use [hX, {x}],
      split,
      split,
      exact ⟨S.down_closed hX (subset.trans hx (finset.inter_subset_right W X)), W, hW,
        finset.subset.trans hx (finset.inter_subset_left W X)⟩,
      exact finset.nonempty_iff_ne_empty.1 (finset.singleton_nonempty x),
      exact finset.subset.trans hx (finset.inter_subset_right W X),
    }
  },
  {
    rintro (hX | hX);
    exact hX.1,
  }
end


def simplicial_complex.boundary (S : simplicial_complex m) : simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X | ∃ Y ∈ S.faces, X ⊆ Y ∧ ∃! Z ∈ S.facets, Y ⊂ Z}
  (λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY)
  (λ X W ⟨Y, hY, hXY, ⟨Z, hZ⟩⟩ hWX, ⟨Y, hY, subset.trans hWX hXY, Z, hZ⟩)
/-Previous def
def simplicial_complex.boundary (S : simplicial_complex m) : simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X | ∃ Y ∈ S.faces, X ⊆ Y ∧ ∃! Z ∈ S.facets, Y ⊂ Z}
  (λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY)
  (λ X W ⟨Y, hY, hXY, ⟨Z, hZ⟩⟩ hWX, ⟨Y, hY, subset.trans hWX hXY, Z, hZ⟩)-/

lemma boundary_empty {S : simplicial_complex m} (hS : S.faces = ∅) : S.boundary.faces = ∅ :=
begin
  unfold simplicial_complex.boundary,
  simp,
  rw [hS, facets_empty hS],
  simp,
end

lemma boundary_singleton_empty {S : simplicial_complex m} (hS : S.faces = {∅}) :
  S.boundary.faces = ∅ :=
begin
  ext X,
  unfold simplicial_complex.boundary,
  simp,
  rw [hS, facets_singleton_empty hS],
  rintro _ _ _ ⟨Y, ⟨(hY : Y = ∅), hY'⟩, _⟩,
  rw hY at hY',
  exact hY'.2 (empty_subset _),
end

lemma boundary_subset {S : simplicial_complex m} : S.boundary.faces ⊆ S.faces :=
  λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY

lemma facets_disjoint_boundary {S : simplicial_complex m} : disjoint S.facets S.boundary.faces :=
begin
  rintro X ⟨⟨hX, hXunique⟩, ⟨Y, hY, hXY, ⟨Z, ⟨hZ, hYZ⟩, hZunique⟩⟩⟩,
  simp at *,
  apply hYZ.2,
  rw ← hXunique (facets_subset hZ) (subset.trans hXY hYZ.1),
  exact hXY,
end

lemma pure_boundary_of_pure {S : simplicial_complex m} {n : ℕ} :
  S.pure_of n → S.boundary.pure_of (n - 1) :=
begin
  rintro hS,
  cases n,
  {
    rw nat.zero_sub,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := subfacet (boundary_subset (facets_subset hX)),
    rw finset.card_eq_zero.mp (hS hY) at hXY,
    exact finset.card_eq_zero.2 (finset.subset_empty.1 hXY),
  },
  rintro X ⟨⟨Y, hY, hXY, ⟨Z, ⟨hZ, hYZ⟩, hZunique⟩⟩, hXmax⟩,
  simp at *,
  have hX : Y ∈ S.boundary.faces,
  {
    use [Y, hY, subset.refl Y, Z],
    simp,
    exact ⟨⟨hZ, hYZ⟩, hZunique⟩,
  },
  have hXY := hXmax hX hXY,
  subst hXY,
  clear hXY hY,
  have hZcard := hS hZ,
  have hXcard : X.card ≤ n,
  {
    apply nat.le_of_lt_succ,
    rw ← hZcard,
    exact finset.card_lt_card hYZ,
  },
  have : n - X.card + X.card ≤ Z.card,
  {
    rw hS hZ,
    rw nat.sub_add_cancel hXcard,
    rw nat.succ_eq_add_one,
    linarith,
  },
  obtain ⟨W, hXW, hWZ, hWcard⟩ := finset.exists_intermediate_set (n - X.card) this hYZ.1,
  rw nat.sub_add_cancel hXcard at hWcard,
  have hW : W ∈ S.boundary.faces,
  {
    use [W, S.down_closed (facets_subset hZ) hWZ, subset.refl W, Z],
    simp,
    have : W.card < Z.card,
    {
      rw [hWcard, hZcard, nat.succ_eq_add_one],
      linarith,
    },
    have hWZ' : W ⊂ Z,
    {
      use hWZ,
      rintro hZW,
      have := finset.eq_of_subset_of_card_le hZW (le_of_lt this),
      have : n.succ = n := by rw [← hZcard, ← hWcard, this],
      exact nat.succ_ne_self n this,
    },
    use ⟨hZ, hWZ'⟩,
    rintro Y hY hWY,
    exact hZunique Y hY ⟨subset.trans hXW hWY.1, (λ hYX, hWY.2 (subset.trans hYX hXW))⟩,
  },
  rw hXmax hW hXW,
  exact hWcard,
end

lemma boundary_boundary {S : simplicial_complex m} : S.boundary.boundary.faces = ∅ :=
begin
  sorry
end
--lemma boundary_pureness_eq_pureness_sub_one {S : simplicial_complex m} (hS : S.pure) : pureness (pure_boundary_of_pure hS) = S.pureness - 1 := sorry

lemma boundary_link {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} : --{X : finset (fin m → ℝ)}
  S.boundary.link A = (S.link A).boundary :=
begin
  ext V,
  split,
  {
    rintro ⟨hVdisj, W, X, hW, ⟨Y, hY, hXY, Z, ⟨hZ, hYZ⟩, hZmax⟩, hVX, hWX⟩,
    simp at hYZ hZmax,
    use V,
    split,
    {
      split,
      exact (λ U hU, hVdisj hU),
      exact ⟨W, Z, hW, facets_subset hZ, subset.trans hVX (subset.trans hXY hYZ.1),
        subset.trans hWX (subset.trans hXY hYZ.1)⟩,
    },
    {
      use subset.refl V,
      use Z,
      simp,
      sorry
    }
  },
  {
    sorry
  }
end

def simplicial_complex.boundaryless (S : simplicial_complex m) : Prop := S.boundary.faces = ∅

lemma boundary_boundaryless {S : simplicial_complex m} : S.boundary.boundaryless :=
  boundary_boundary

def simplicial_complex.full_dimensional (S : simplicial_complex m) : Prop :=
  ∃ {X}, X ∈ S.faces ∧ (X : finset _).card = m + 1

end affine
