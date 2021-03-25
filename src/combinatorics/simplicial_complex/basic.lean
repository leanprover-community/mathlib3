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
def simplicial_complex.of_surcomplex {m : ℕ} {S : simplicial_complex m}
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

/-The empty simplicial complex is made up of only the empty simplex-/
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

/--
A simplicial complex is pure of dimension n iff all its facets have dimension n.
-/
def simplicial_complex.pure_of (S : simplicial_complex m) (n : ℕ) : Prop :=
  ∀ {X}, X ∈ S.facets → (X : finset _).card = n

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

lemma pureness_def {S : simplicial_complex m} (hS : S.pure) : S.pure_of S.pureness := sorry
--classical.some_spec hS hX @Bhavik the totalling broke it and I broke it even more :/

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
  refine ⟨pureness_def hS, λ hXcard, _⟩,
  { refine ⟨hX, λ Y hY hXY, _⟩,
    apply finset.eq_of_subset_of_card_le hXY,
    rw hXcard,
    --exact simplex_dimension_le_pureness (pureness_def hS) hY, @Bhavik heeeelp
    sorry
    }
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
  {
    rw hS₁ hX,
    --exact simplex_dimension_le_pureness hS₂ hY, @Bhavik same problem as on l. 187
    sorry
  },
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

lemma pure_skeleton_of_pure {S : simplicial_complex m} (k : ℕ) : S.pure → (S.skeleton k).pure :=
begin
  rintro ⟨n, hS⟩,
  cases le_or_gt n (k + 1) with hmin hmin,
  {
    use n,
    rintro X hXskel,
    obtain ⟨Y, hY, hXY⟩ := subfacet (skeleton_subcomplex (facets_subset hXskel)),
    have hYskel : Y ∈ (S.skeleton k).faces,
    { use facets_subset hY,
      simp,
      rw hS hY,
      exact hmin, },
    rw hXskel.2 hYskel hXY,
    exact hS hY },
  { use k + 1,
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
  simplicial_complex m := simplicial_complex.of_surcomplex
  {X | ∃ {X'}, X' ∈ S.faces ∩ A ∧ X ⊆ X'}
  (λ X ⟨X', hX', hX⟩, S.down_closed hX'.1 hX)
  (λ X Y ⟨X', hX', hX⟩ hY, ⟨X', hX', subset.trans hY hX⟩)

lemma closure_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.closure A).faces ⊆ S.faces := λ X ⟨X', hX', hX⟩, S.down_closed hX'.1 hX

--@Bhavik subset_closure is unfortunately already taken by the topological statement that
--s ⊆ closure s
lemma faces_subset_closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.faces ∩ A ⊆ (S.closure A).faces := λ X hX, ⟨X, hX, subset.refl _⟩

lemma closure_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hAB : A ⊆ B) :
  (S.closure A).faces ⊆ (S.closure B).faces := λ X ⟨Y, hY, hX⟩,
  ⟨Y, inter_subset_inter_right _ hAB hY, hX⟩

/--
The open star of a set of faces is the union of their surfaces
-/
def simplicial_complex.star (S : simplicial_complex m) : set (finset (fin m → ℝ)) →
  set (finset (fin m → ℝ)) := λ A, {X | X ∈ S.faces ∧ ∃ {Y}, Y ∈ A ∧ Y ⊆ X}

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

--Can maybe get rid of hX?
lemma star_eq_Inter_star_singleton {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
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
    unfold simplicial_complex.star,
    simp,
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

/--
The closed star of a set is the closure of its open star.
-/
lemma Star_eq_closure_star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.Star A = S.closure (S.star A) :=
begin
  ext X,
  exact ⟨(λ ⟨Y, Z, hY, hZ, hXZ, hYZ⟩, ⟨Z, ⟨hZ, hZ, Y, hY, hYZ⟩, hXZ⟩),
    (λ ⟨Z, ⟨hZ, _, Y, hY, hYZ⟩, hXZ⟩, ⟨Y, Z, hY, hZ, hXZ, hYZ⟩)⟩,
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

lemma pure_Star_of_pure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  S.pure → (S.Star A).pure :=
begin
  --not hard but I'm tired
  sorry
  /-rintro ⟨n, hS⟩, -- (S.faces ∩ A).nonempty →  rintro ⟨n, hS⟩
  use n,
  rintro X ⟨⟨Y, Z, hY, hZ, hXZ, hYZ⟩, hXmax⟩,
  have hYA : Y ∈ S.star A,
  {
    exact ⟨S.down_closed hZ hYZ, Y, hY, subset.refl Y⟩,
  },
  obtain ⟨W, hW, hYW⟩ := subfacet (star_subset hYA),
  unfold simplicial_complex.pure_of at hS,
  have hW' : W ∈ (S.Star A).facets,
  {
    split,
    {
      apply star_subset_Star,
      sorry
    },
    {
      rintro V ⟨T, U, hT, hU, hVU, hTU⟩ hWV,
      have : V.card ≤ W.card,
      {
        rw hS hW,
        --exact simplex_dimension_le_pureness hS (S.down_closed hU hVU), @Bhavik same problem as on l. 187
        sorry
      },
      exact finset.eq_of_subset_of_card_le hWV this,
    }
  },
  have hW' : W ∈ (S.Star A).faces,
  {
      apply star_subset_Star,
      exact star_up_closed hW.1 hYA hYW,
  },
  rw hXmax (star_subset_Star (star_up_closed hZ hYA hYZ))
    hXZ,
  exact hS hW,-/
end

lemma Star_facet_iff {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  {X : finset (fin m → ℝ)} :
  X ∈ (S.Star A).facets ↔ X ∈ S.facets ∧ ∃ {Y}, Y ∈ A ∧ (X ∩ Y).nonempty :=
begin
  split,
  {
    sorry
  },
  {
    sorry
  }
end

lemma Star_pureness_eq_pureness_of_nonempty {S : simplicial_complex m}
  {A : set (finset (fin m → ℝ))} (hS : S.pure) :
  (S.faces ∩ A).nonempty → (S.Star A).pureness = S.pureness :=
begin
  rintro ⟨X, hX⟩,
  obtain ⟨Y, hY, hXY⟩ := subfacet hX.1,
  apply nat.succ.inj,
  --have := (pureness_def (pure_Star_of_pure hS)),
  have : Y ∈ (S.Star A).facets,
  {
    use star_subset_Star (star_up_closed hY.1 (subset_star hX) hXY),
    rintro Z hZ hYZ,
    exact hY.2 (Star_subset hZ) hYZ,
  },
  rw [nat.succ_eq_add_one, nat.succ_eq_add_one, ← pureness_def hS hY,
    ← pureness_def (pure_Star_of_pure hS) this],
end

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
  end

lemma link_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : (S.link A).faces ⊆ S.faces := λ X hX, Star_subset hX.1

/-lemma pure_link_of_pure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) {n : ℕ} : S.pure → (link hA).pure (n - finset.card  :=
begin
  rintro hS X hX,
end-/

/-
The erasure of a simplicial complex according to a set A is the subcomplex taken-/
def simplicial_complex.erasure (S : simplicial_complex m) (A : set (finset (fin m → ℝ))) :
  simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X | X ∈ S.faces ∧ ∀ {Y}, Y ∈ A → disjoint X Y}
  (λ X hX, hX.1)
  (λ X Y ⟨hX, hXA⟩ hYX, ⟨S.down_closed hX hYX, λ Z hZ, finset.disjoint_of_subset_left hYX (hXA hZ)⟩)

lemma erasure_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} :
  (S.erasure A).faces ⊆ S.faces := λ X hX, hX.1

/-lemma link_eq_erasure_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) :-/

def simplicial_complex.boundary (S : simplicial_complex m) : simplicial_complex m :=
simplicial_complex.of_surcomplex
  {X | ∃ Y ∈ S.faces, X ⊆ Y ∧ ∃! Z ∈ S.facets, Y ⊂ Z}
  (λ X ⟨Y, hY, hXY, _⟩, S.down_closed hY hXY)
  (λ X W ⟨Y, hY, hXY, ⟨Z, hZ⟩⟩ hWX, ⟨Y, hY, subset.trans hWX hXY, Z, hZ⟩)

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

--Probably freaking hard and topology-needy
lemma pure_boundary_of_pure_of_finite {S : simplicial_complex m} : finite S.faces → S.pure →
  S.boundary.pure :=
begin
  rintro hSfinite ⟨n, hS⟩,
  cases n,
  {
    use 0,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := subfacet (boundary_subset (facets_subset hX)),
    rw finset.card_eq_zero.mp (hS hY) at hXY,
    exact finset.card_eq_zero.2 (finset.subset_empty.1 hXY),
  },
  cases S.faces.eq_empty_or_nonempty,
  {
    use 0,
    rintro X hX,
    exfalso,
    have := boundary_subset (facets_subset hX),
    rw h at this,
    exact not_mem_empty X this,
  },
  --hard case
  use n,
  rintro X ⟨⟨Y, hY, hXY, ⟨Z, ⟨hZ, hYZ⟩, hZunique⟩⟩, hX⟩,
  simp at *,
  sorry
end

--lemma boundary_pureness_eq_pureness_sub_one {S : simplicial_complex m} (hS : S.pure) : pureness (pure_boundary_of_pure hS) = S.pureness - 1 := sorry

end affine
