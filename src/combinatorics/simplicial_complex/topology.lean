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
import combinatorics.simplicial_complex.basic
-- import data.nat.parity

namespace affine

open_locale classical affine big_operators
open set
variables {m n : ℕ} {S : simplicial_complex m}
local notation `E` := fin m → ℝ

/--
The underlying space of a simplicial complex.
-/
def simplicial_complex.space (S : simplicial_complex m) : set E :=
⋃ X ∈ S.faces, convex_hull (X : set E)

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

/--
The combinatorial frontier of a simplex as a subspace.
-/
def combi_frontier (X : finset E) : set E :=
  ⋃ Y ⊂ X, convex_hull Y

lemma mem_combi_frontier_iff {X : finset E} {x : E} :
  x ∈ combi_frontier X ↔ ∃ {Y}, Y ⊂ X ∧ x ∈ convex_hull (Y : set E) := sorry

lemma combi_frontier_eq (X : finset E) :
  combi_frontier X =
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 ≤ w y) (hw₁ : ∑ y in X, w y = 1)
        (hw₂ : ∃ y ∈ X, w y = 0), X.center_mass w id = x} :=
begin
  ext x,
  simp_rw [combi_frontier, mem_Union, set.mem_set_of_eq],
  split,
  { simp only [and_imp, exists_prop, exists_imp_distrib],
    intros Y YX hx,
    rw [finset.convex_hull_eq, set.mem_set_of_eq] at hx,
    rcases hx with ⟨w, hw₀, hw₁, hx⟩,
    rcases finset.exists_of_ssubset YX with ⟨y, hyX, hyY⟩,
    let w' := λ z, if z ∈ Y then w z else 0,
    have hw'₁ : X.sum w' = 1,
    { rwa [←finset.sum_subset YX.1, finset.sum_extend_by_zero],
      simp only [ite_eq_right_iff],
      tauto },
    refine ⟨w', _, hw'₁, ⟨_, ‹y ∈ X›, _⟩, _⟩,
    { intros y hy,
      change 0 ≤ ite (y ∈ Y) (w y) 0,
      split_ifs,
      { apply hw₀ y ‹_› },
      { refl } },
    { apply if_neg ‹y ∉ Y› },
    rw ← finset.center_mass_subset id YX.1,
    { rw [finset.center_mass_eq_of_sum_1],
      { rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hx,
        rw ← hx,
        apply finset.sum_congr rfl,
        intros x hx,
        change ite _ _ _ • _ = _,
        rw if_pos hx },
      rwa finset.sum_extend_by_zero },
    intros i _ hi,
    apply if_neg hi },
  { simp only [and_imp, exists_prop, exists_imp_distrib],
    intros w hw₁ hw₂ y hy₁ hy₂ hy₃,
    refine ⟨X.erase y, finset.erase_ssubset hy₁, _⟩,
    rw [finset.convex_hull_eq, set.mem_set_of_eq],
    refine ⟨w, λ z hz, hw₁ z (X.erase_subset _ hz), _, _⟩,
    rw finset.sum_erase _ hy₂,
    apply hw₂,
    rwa finset.center_mass_subset _ (X.erase_subset _),
    intros i hi₁ hi₂,
    simp only [hi₁, and_true, not_not, finset.mem_erase] at hi₂,
    subst hi₂,
    apply hy₂ }
end

lemma frontiers_agree_of_full_dimensional {X : finset E} (hXcard : X.card = m + 1) :
  combi_frontier X = frontier (convex_hull X) :=
begin
  ext x,
  split,
  {
    unfold combi_frontier,
    simp_rw mem_Union,
    rintro ⟨Y, hYX, hx⟩,
    split,
    { exact subset_closure (convex_hull_mono hYX.1 hx) },
    {
      rintro h,
      sorry,
      --have :=  finset.convex_hull_eq,
    }
  },
  {
    rintro ⟨h, g⟩,
    sorry
  }
end

/--
The interior of a simplex as a subspace. Note this is *not* the same thing as the topological
interior of the underlying space.
-/
def combi_interior (X : finset E) : set E :=
convex_hull X \ combi_frontier X

example {p q : Prop} : (p → ¬q) → q → ¬p :=
function.swap

lemma combi_interior_eq (X : finset E) :
  combi_interior X =
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 < w y) (hw₁ : ∑ y in X, w y = 1),
      X.center_mass w id = x} :=
begin
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  ext x,
  split,
  { simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
    rintro w hw₁ hw₂ hw₃ q,
    refine ⟨w, λ y hy, _, hw₂, hw₃⟩,
    exact lt_of_le_of_ne (hw₁ _ hy) (ne.symm (λ t, q w hw₁ hw₂ y hy t hw₃)) },
  { simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
    intros w hw₁ hw₂ hw₃,
    refine ⟨⟨w, λ y hy, le_of_lt (hw₁ y hy), hw₂, hw₃⟩, _⟩,
    intros w' hw'₁ hw'₂ y hy₁ hy₂,
    sorry }
end

lemma combi_frontier_subset_convex_hull {X : finset E} : combi_frontier X ⊆ convex_hull X :=
  bUnion_subset (λ Y hY, convex_hull_mono hY.1)

lemma convex_hull_eq_interior_union_combi_frontier (X : finset E) :
  convex_hull ↑X = combi_interior X ∪ combi_frontier X :=
(sdiff_union_of_subset combi_frontier_subset_convex_hull).symm

lemma disjoint_interiors {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (x : E) :
  x ∈ combi_interior X ∩ combi_interior Y → X = Y :=
begin
  rintro ⟨⟨hxX, hXbound⟩, ⟨hyY, hYbound⟩⟩,
  by_contra,
  have hXY : X ∩ Y ⊂ X,
  { use finset.inter_subset_left X Y,
    intro H,
    apply hYbound,
    apply set.mem_bUnion _ _,
    exact X,
    exact ⟨subset.trans H (finset.inter_subset_right X Y),
      (λ H2, h (finset.subset.antisymm (subset.trans H (finset.inter_subset_right X Y)) H2))⟩,
    exact hxX },
  refine hXbound (mem_bUnion hXY _),
  exact_mod_cast S.disjoint hX hY ⟨hxX, hyY⟩,
end

lemma disjoint_interiors_aux {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (h : X ≠ Y) :
  disjoint (combi_interior X) (combi_interior Y) :=
λ x hx, h (disjoint_interiors hX hY _ hx)

lemma simplex_interior_covers (X : finset E) :
  convex_hull ↑X = ⋃ (Y ⊆ X), combi_interior Y :=
begin
  apply subset.antisymm _ _,
  { apply X.strong_induction_on,
    rintro s ih x hx,
    by_cases x ∈ combi_frontier s,
    { rw [combi_frontier] at h,
      simp only [exists_prop, set.mem_Union] at h,
      obtain ⟨t, st, ht⟩ := h,
      specialize ih _ st ht,
      simp only [exists_prop, set.mem_Union] at ⊢ ih,
      obtain ⟨Z, Zt, hZ⟩ := ih,
      exact ⟨_, subset.trans Zt st.1, hZ⟩ },
    { exact subset_bUnion_of_mem (λ _ t, t) ⟨hx, h⟩ } },
  { exact bUnion_subset (λ Y hY, subset.trans (diff_subset _ _) (convex_hull_mono hY)) },
end

lemma interiors_cover (S : simplicial_complex m) :
  S.space = ⋃ X ∈ S.faces, combi_interior X :=
begin
  apply subset.antisymm _ _,
  { apply bUnion_subset,
    rintro X hX,
    rw simplex_interior_covers,
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
  rw interiors_cover S at hx,
  simp only [set.mem_bUnion_iff] at hx,
  obtain ⟨X, hX, hxX⟩ := hx,
  exact ⟨X, ⟨⟨hX, hxX⟩, (λ Y ⟨hY, hxY⟩, disjoint_interiors hY hX x ⟨hxY, hxX⟩)⟩⟩,
end

lemma is_closed_convex_hull {X : finset E} : is_closed (convex_hull (X : set E)) :=
X.finite_to_set.is_closed_convex_hull

lemma is_closed_combi_frontier {X : finset E} : is_closed (combi_frontier X) :=
begin
  apply is_closed_bUnion,
  { suffices : set.finite {Y | Y ⊆ X},
    { exact this.subset (λ i h, h.1) },
    convert X.powerset.finite_to_set using 1,
    ext,
    simp },
  { intros i hi,
    apply is_closed_convex_hull }
end

/- combi_interior X is the topological interior iff X is of dimension m -/
lemma interiors_agree_of_full_dimensional {S : simplicial_complex m}
  {X} (hX : X ∈ S.faces) (hXdim : X.card = m + 1) :
  combi_interior X = interior (convex_hull X) :=
begin
  unfold combi_interior interior,
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
      { rintro rfl,
        simp at hXhull,
        exact hXhull },
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
    obtain ⟨x, hx⟩ := finset.nonempty_iff_ne_empty.2 h,
    suffices h : {Y : finset (fin m → ℝ) | Y ∈ S.faces ∧ X ⊆ Y} ⊆
      {Y : finset (fin m → ℝ) | Y ∈ S.faces ∧ x ∈ convex_hull ↑Y},
    { exact finite.subset (hS x) h },
    rintro Y ⟨hY, hXY⟩,
    use hY,
    exact subset_convex_hull Y (hXY hx) }
end

/--
S₁ ≤ S₂ (S₁ is a subdivision of S₂) iff their underlying space is the same and each face of S₁ is
contained in some face of S₂
-/
instance : has_le (simplicial_complex m) := ⟨λ S₁ S₂, S₁.space = S₂.space ∧
  ∀ {X₁ : finset (fin m → ℝ)}, X₁ ∈ S₁.faces → ∃ X₂ ∈ S₂.faces,
  convex_hull (X₁ : set(fin m → ℝ)) ⊆ convex_hull (X₂ : set(fin m → ℝ))⟩

def subdivision_order : partial_order (simplicial_complex m) :=
  {le := λ S₁ S₂, S₁ ≤ S₂,
  le_refl := (λ S, ⟨rfl, (λ X hX, ⟨X, hX, subset.refl _⟩)⟩),
  le_trans := begin
    rintro S₁ S₂ S₃ h₁₂ h₂₃,
    use eq.trans h₁₂.1 h₂₃.1,
    rintro X₁ hX₁,
    obtain ⟨X₂, hX₂, hX₁₂⟩ := h₁₂.2 hX₁,
    obtain ⟨X₃, hX₃, hX₂₃⟩ := h₂₃.2 hX₂,
    exact ⟨X₃, hX₃, subset.trans hX₁₂ hX₂₃⟩,
  end,
  le_antisymm := begin
    have aux_lemma : ∀ {S₁ S₂ : simplicial_complex m}, S₁ ≤ S₂ → S₂ ≤ S₁ → ∀ {X},
      X ∈ S₁.faces → X ∈ S₂.faces,
    { rintro S₁ S₂ h₁ h₂ W hW,
      apply finset.strong_downward_induction_on (λ X hX, simplex_dimension_le_space_dimension hX)
        hW,
      { rintro X hX h,
        obtain ⟨Y, hY, hXYhull⟩ := h₁.2 hX,
        obtain ⟨Z, hZ, hYZhull⟩ := h₂.2 hY,
        have hXZhull := subset.trans (inter_subset_inter_right (convex_hull ↑X)
          (subset.trans hXYhull hYZhull)) (S₁.disjoint hX hZ),
        rw inter_self at hXZhull,
        norm_cast at hXZhull,
        have hXZ : X ⊆ Z := subset.trans
          (subset_of_convex_hull_eq_convex_hull_of_linearly_independent (S₁.indep hX)
          (subset.antisymm hXZhull (convex_hull_mono (finset.inter_subset_left X Z))))
          (finset.inter_subset_right _ _),
        by_cases hZX : Z ⊆ X,
        { rw finset.subset.antisymm hZX hXZ at hYZhull,
          rw eq_of_convex_hull_eq_convex_hull_of_linearly_independent_of_linearly_independent
            (S₁.indep hX) (S₂.indep hY) (subset.antisymm hXYhull hYZhull),
          exact hY },
        { exact S₂.down_closed (h hZ ⟨hXZ, hZX⟩) hXZ }}},
    rintro S₁ S₂ h₁ h₂,
    ext X,
    exact ⟨λ hX, aux_lemma h₁ h₂ hX, λ hX, aux_lemma h₂ h₁ hX⟩,
  end}

lemma subdivision_refinement {S₁ S₂ : simplicial_complex m} (hS : S₁ ≤ S₂) :
  ∀ {X₁}, X₁ ∈ S₁.faces → ∃ {X₂}, X₂ ∈ S₂.faces ∧ combi_interior X₁ ⊆ combi_interior X₂ :=
begin
  rintro X₁ hX₁,
  obtain ⟨X₂, hX₂, hX₁X₂hull⟩ := hS.2 hX₁,
  sorry
end

lemma boundary_mono {S₁ S₂ : simplicial_complex m} (hS : S₁ ≤ S₂) : S₁.boundary ≤ S₂.boundary :=
begin
  split,
  {
    sorry --hard?
  },
  {
    rintro X₁ ⟨Y₁, Z₁, hY₁, hZ₁, hX₁Y₁, hY₁Z₁, hZ₁max⟩,
    obtain ⟨X₂, hX₂, hX₁X₂⟩ := hS.2 (S₁.down_closed hY₁ hX₁Y₁),
    obtain ⟨Y₂, hY₂, hY₁Y₂⟩ := hS.2 hY₁,
    obtain ⟨Z₂, hZ₂, hZ₁Z₂⟩ := hS.2 hZ₁,
    use Y₂,
    split,
    {
      sorry
    },
    sorry
  }
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

lemma locally_compact_realisation_of_locally_finite (S : simplicial_complex m)
  (hS : S.locally_finite) : locally_compact_space S.space :=
  {local_compact_nhds := begin
    rintro x X hX,
    sorry
  end}

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
(realisable : ∃ {S : simplicial_complex m}, S.pure ∧ space = S.space)

def polytope.vertices (P : polytope m n) : set (fin m → ℝ) :=
  ⋂ (S : simplicial_complex m) (H : P.space = S.space), {x | {x} ∈ S.faces}

def polytope.edges (P : polytope m n) : set (finset (fin m → ℝ)) :=
  ⋂ (S : simplicial_complex m) (H : P.space = S.space), {X | X ∈ S.faces ∧ X.card = 2}

noncomputable def polytope.realisation (P : polytope m n) :
  simplicial_complex m := classical.some P.realisable

lemma pure_polytope_realisation (P : polytope m n) : P.realisation.pure :=
begin
  sorry --trivial by definition but I don't know how to do it
end

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
