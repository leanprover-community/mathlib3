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
  indep := begin
    rintro X hX,
    --exact affine_independent_of_subsingleton ℝ (λ (p : X), ↑p) hX, @bhavik heeelp
    sorry
  end,
  down_closed := λ X Y hX, hX.symm ▸ finset.subset_empty.1,
  disjoint := begin
    rintro X _ (rfl : X = ∅) (rfl : Y = ∅),
    simp,
    --exact subset.refl _,
  end, }

/-def simplicial_complex.dimension (S : simplicial_complex m) {X : finset (fin m → ℝ)} : ℕ :=
  Sup {X.card - 1 | X ∈ S.faces}-/

/-The dimension of a simplicial complex is the maximal dimension of its faces-/
/-def simplicial_complex.dimension (S : simplicial_complex m) : ℕ :=
 Sup {finset.card (X : set E) | X ∈ S.faces}-/

--Refinement of `size_bound`
lemma simplex_dimension_le_space_dimension {S : simplicial_complex m} {X : finset E} :
  X ∈ S.faces → finset.card X ≤ m + 1 := λ hX, size_bound (S.indep hX)

def simplicial_complex.facets (S : simplicial_complex m) : set (finset (fin m → ℝ))
  := {X | X ∈ S.faces ∧ (∀ {Y}, Y ∈ S.faces → X ⊆ Y → X = Y)}

lemma facets_subset {S : simplicial_complex m} : S.facets ⊆ S.faces := λ X hX, hX.1

lemma not_facet_iff_subface {S : simplicial_complex m} {X : finset (fin m → ℝ)} :
  X ∈ S.faces → (X ∉ S.facets ↔ ∃ {Y}, Y ∈ S.faces ∧ X ⊂ Y) :=
begin
  rintro hX,
  split,
  {
    rintro (hX' : ¬(X ∈ S.faces ∧ (∀ {Y}, Y ∈ S.faces → X ⊆ Y → X = Y))),
    push_neg at hX',
    obtain ⟨Y, hY⟩ := hX' hX,
    exact ⟨Y, hY.1, ⟨hY.2.1, (λ hYX, hY.2.2 (finset.subset.antisymm hY.2.1 hYX))⟩⟩,
  },
  {
    rintro ⟨Y, hY⟩ ⟨hX, hX'⟩,
    have := hX' hY.1 hY.2.1,
    rw this at hY,
    exact hY.2.2 (subset.refl Y),
  }
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
A simplicial complex is pure iff all its facets have the same dimension
-/
def simplicial_complex.pure (S : simplicial_complex m) : Prop := ∃ n : ℕ, ∀ {X}, X ∈ S.facets →
  (X : finset _).card = n + 1

noncomputable def pureness {S : simplicial_complex m} (hS : S.pure) : ℕ := classical.some hS

lemma pureness_def {S : simplicial_complex m} (hS : S.pure) {X : finset E} (hX : X ∈ S.facets) :
  X.card = pureness hS + 1 :=
classical.some_spec hS hX

lemma simplex_dimension_le_pureness {S : simplicial_complex m} (hS : S.pure) {X : finset (fin m → ℝ)} :
  X ∈ S.faces → X.card ≤ pureness hS + 1 :=
begin
  rintro hX,
  obtain ⟨Y, hY, hXY⟩ := subfacet hX,
  rw ← pureness_def hS hY,
  exact finset.card_le_of_subset hXY,
end

lemma facet_iff_dimension_eq_pureness {S : simplicial_complex m} (hS : S.pure)
  {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  X ∈ S.facets ↔ X.card = pureness hS + 1 :=
begin
  refine ⟨pureness_def hS, λ hXcard, _⟩,
  { refine ⟨hX, λ Y hY hXY, _⟩,
    apply finset.eq_of_subset_of_card_le hXY,
    rw hXcard,
    exact simplex_dimension_le_pureness hS hY, }
end

/--
A simplicial complex is pure iff there exists n such that all faces are subfaces of some
n-dimensional face
-/
lemma pure_iff {S : simplicial_complex m} : S.pure ↔ ∃ n : ℕ, ∀ {X}, X ∈ S.faces →
  ∃ {Y}, Y ∈ S.faces ∧ finset.card Y = n + 1 ∧ X ⊆ Y :=
begin
  split,
  { rintro hS,
    use pureness hS,
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

/-The cells of a simplicial complex are its simplices whose dimension matches the one of the space-/
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
  cases le_or_gt (n + 1) (k + 1) with hmin hmin,
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
  { use k,
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
  pureness (pure_skeleton_of_pure k hS) = min (pureness hS) k := sorry

/-The closure of a set of faces is the set of their subfaces-/
def closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) :
  simplicial_complex m := simplicial_complex.of_surcomplex {X | ∃ X' ∈ A, X ⊆ X'}
  (λ X ⟨X', hX', hX⟩, S.down_closed (hA hX') hX)
  (λ X Y ⟨X', hX', hX⟩ hY, ⟨X', hX', subset.trans hY hX⟩)

lemma closure_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : (closure hA).faces ⊆ S.faces := λ X ⟨X', hX', hX⟩, S.down_closed (hA hX') hX

--subset_closure is unfortunately already taken by the topological statement that s ⊆ closure s
lemma faces_subset_closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : A ⊆ (closure hA).faces := λ X hX, ⟨X, hX, subset.refl _⟩

lemma closure_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hB : B ⊆ S.faces)
  (hAB : A ⊆ B) : (closure (subset.trans hAB hB)).faces ⊆ (closure hB).faces :=
  λ X ⟨Y, hY, hX⟩, ⟨Y, hAB hY, hX⟩

/-The open star of a set of faces is the union of their surfaces-/
def star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) :
  set (finset (fin m → ℝ)) :=
⋃ (X ∈ A), {Y | Y ∈ S.faces ∧ X ⊆ Y}

lemma star_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : star hA ⊆ S.faces :=
begin
  rintro Y ⟨_, ⟨X, rfl⟩, hX⟩,
  simp at hX,
  exact hX.2.1,
end

lemma subset_star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : A ⊆ star hA :=
begin
  rintro X hX,
  unfold star,
  rw mem_bUnion_iff,
  exact ⟨X, hX, hA hX, subset.refl _⟩, --golfable?
end

lemma star_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hB : B ⊆ S.faces)
  (hAB : A ⊆ B) : star (subset.trans hAB hB) ⊆ star hB :=
begin
  rintro X hX,
  unfold star at hX ⊢,
  rw mem_bUnion_iff at hX ⊢,
  obtain ⟨Y, hY, hX⟩ := hX,
  exact ⟨Y, hAB hY, hX⟩,
end

lemma star_up_closed {S : simplicial_complex m} {X Y : finset (fin m → ℝ)}
  {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) : X ∈ S.faces → Y ∈ star hA → Y ⊆ X
  → X ∈ star hA :=
begin
  rintro hX hY hXY,
  unfold star at hY ⊢,
  rw mem_bUnion_iff at hY ⊢,
  obtain ⟨Z, hZ, hY⟩ := hY,
  exact ⟨Z, hZ, hX, subset.trans hY.2 hXY⟩,
end

--Ughh, how do I prove stuff on the fly?
/-lemma star_eq_Inter_star {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  star hX = ⋂ x ∈ X, star {x} :=
begin
end-/

/-The closed star of a set is the closure of its open star-/
def Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) :
  simplicial_complex m := closure (star_subset hA)

lemma Star_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : (Star hA).faces ⊆ S.faces := λ X ⟨X', hX', hX⟩, S.down_closed
  ((star_subset hA) hX') hX

lemma subset_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : A ⊆ (Star hA).faces :=
  subset.trans (subset_star hA) (faces_subset_closure (star_subset hA))

lemma star_subset_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : star hA ⊆ (Star hA).faces := faces_subset_closure (star_subset hA)

lemma Star_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hB : B ⊆ S.faces)
  (hAB : A ⊆ B) : (Star (subset.trans hAB hB)).faces ⊆ (Star hB).faces :=
begin
  apply closure_mono,
  apply star_mono,
end

lemma mem_Star_iff {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces)
  {X : finset (fin m → ℝ)} : X ∈ (Star hA).faces ↔ ∃ Y ∈ A, ∃ Z ∈ S.faces, X ⊆ Z ∧ Y ⊆ Z :=
begin --golfable?
  split,
  {
    rintro ⟨Z, hZ, hXZ⟩,
    unfold star at hZ,
    obtain ⟨Y, hY, hZ, hYZ⟩ := mem_bUnion_iff.mp hZ,
    exact ⟨Y, hY, Z, hZ, hXZ, hYZ⟩,
  },
  {
    rintro ⟨Y, hY, Z, hZ, hXZ, hYZ⟩,
    unfold Star closure,
    simp,
    unfold star,
    simp,
    exact ⟨Z, ⟨Y, hY, hZ, hYZ⟩, hXZ⟩,
  }
end

lemma pure_Star_of_pure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : S.pure → (Star hA).pure :=
begin
  rintro ⟨n, hS⟩,
  use n,
  rintro X ⟨⟨Y, hY, hXY⟩, hXmax⟩,
  obtain ⟨Z, hZ, hYZ⟩ := subfacet (star_subset hA hY),
  rw hXmax (star_subset_Star hA (star_up_closed hA (facets_subset hZ) hY hYZ))
    (subset.trans hXY hYZ),
  exact hS hZ,
end

lemma Star_pureness_eq_pureness_of_nonempty {S : simplicial_complex m}
  {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) (hS : S.pure) :
  nonempty A → pureness (pure_Star_of_pure hA hS) = pureness hS :=
begin
  rintro ⟨X, hX⟩,
  obtain ⟨Y, hY, hXY⟩ := subfacet (hA hX),
  apply nat.succ.inj,
  rw [nat.succ_eq_add_one, nat.succ_eq_add_one, ← pureness_def hS hY,
    ← pureness_def (pure_Star_of_pure hA hS) ⟨(mem_Star_iff hA).2 ⟨X, hX, Y, facets_subset hY,
    subset.refl Y, hXY⟩, (λ Z hZ hYZ, hY.2 (Star_subset hA hZ) hYZ)⟩],
end

def link {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) :
  simplicial_complex m := simplicial_complex.of_surcomplex
  ((Star hA).faces \ star (closure_subset hA)) (λ X hX, Star_subset hA hX.1)
  begin
    rintro X Y hX hXY,
    split,
    { exact (Star hA).down_closed hX.1 hXY},
    {
      rintro ⟨_, ⟨Z, rfl⟩, hZ⟩,
      simp at hZ,
      exact hX.2 (star_up_closed (closure_subset hA) (Star_subset hA hX.1)
        (subset_star (closure_subset hA) hZ.1) (subset.trans hZ.2.2 hXY)),
    }
  end

def link_singleton {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  simplicial_complex m :=
link (set.singleton_subset_iff.2 hX)

lemma link_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : (link hA).faces ⊆ S.faces := λ X hX, Star_subset hA hX.1

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

lemma pure_boundary_of_pure {S : simplicial_complex m} : S.pure → S.boundary.pure :=
begin
  rintro ⟨n, hS⟩,
  cases n with n,
  {
    sorry,
  },
  use n,
  rintro X ⟨⟨Y, hY, hXY, ⟨Z, ⟨hZ, hYZ⟩, hZunique⟩⟩, hX⟩,
  simp at *,
  --rintro hS X ⟨Y, hY, hXY, ⟨Z, ⟨hZ, hYZ⟩, hZunique⟩⟩,
  --simp at *,
  /-rintro hS X hX,
  obtain ⟨Y, hY, hYcard, hXY⟩ := hS (boundary_subset hX),
  by_cases hYX : Y ⊆ X,
  {
    sorry
  },-/
  sorry
end

lemma facets_disjoint_boundary {S : simplicial_complex m} : disjoint S.facets S.boundary.faces :=
begin
  rintro X ⟨⟨hX, hXunique⟩, ⟨Y, hY, hXY, ⟨Z, ⟨hZ, hYZ⟩, hZunique⟩⟩⟩,
  simp at *,
  apply hYZ.2,
  rw ← hXunique (facets_subset hZ) (subset.trans hXY hYZ.1),
  exact hXY,
end

end affine
