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
  x ∈ combi_frontier X ↔ ∃ Y, Y ⊂ X ∧ x ∈ convex_hull (Y : set E) :=
by simp [combi_frontier]

lemma combi_frontier_singleton {x : E} : combi_frontier ({x} : finset E) = ∅ :=
begin
  apply eq_empty_of_subset_empty,
  rintro y hy,
  rw mem_combi_frontier_iff at hy,
  obtain ⟨X, hX, hyX⟩ := hy,
  rw finset.eq_empty_of_ssubset_singleton hX at hyX,
  simp at hyX,
  exact hyX,
end

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

lemma combi_interior_singleton {x : E} : combi_interior ({x} : finset E) = {x} :=
begin
  unfold combi_interior,
  rw combi_frontier_singleton,
  simp,
end

lemma combi_interior_subset_positive_weighings {X : finset E} :
  combi_interior X ⊆
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 < w y) (hw₁ : ∑ y in X, w y = 1),
      X.center_mass w id = x} :=
begin
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  rintro x,
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
  rintro w hw₁ hw₂ hw₃ q,
  refine ⟨w, λ y hy, _, hw₂, hw₃⟩,
  exact lt_of_le_of_ne (hw₁ _ hy) (ne.symm (λ t, q w hw₁ hw₂ y hy t hw₃))
end

lemma combi_interior_eq {X : finset E} (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  combi_interior X =
    {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 < w y) (hw₁ : ∑ y in X, w y = 1),
      X.center_mass w id = x} :=
begin
  apply subset.antisymm combi_interior_subset_positive_weighings,
  rintro x,
  rw [combi_interior, finset.convex_hull_eq, combi_frontier_eq],
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, mem_diff, exists_imp_distrib],
  intros w hw₁ hw₂ hw₃,
  refine ⟨⟨w, λ y hy, le_of_lt (hw₁ y hy), hw₂, hw₃⟩, _⟩,
  intros w' hw'₁ hw'₂ y hy₁ hy₂ hw'₃,
  rw ← hw₃ at hw'₃,
  rw (unique_combination hX w' w hw'₂ hw₂ hw'₃) y hy₁ at hy₂,
  exact ne_of_gt (hw₁ y hy₁) hy₂
end

lemma centroid_mem_combi_interior {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) (hXnonempty : X.nonempty) :
  X.centroid ℝ id ∈ combi_interior X :=
begin
  rw finset.centroid_def,
  have hXweights := X.sum_centroid_weights_eq_one_of_nonempty ℝ hXnonempty,
  rw center_mass_eq_affine_combination hXweights,
  rw combi_interior_eq hX,
  refine ⟨_, _, hXweights, rfl⟩,
  intros y hy,
  simpa [finset.card_pos] using hXnonempty,
end

lemma nonempty_combi_interior_of_nonempty {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) (hXnonempty : X.nonempty) :
  (combi_interior X).nonempty :=
⟨X.centroid ℝ id, centroid_mem_combi_interior hX hXnonempty⟩

lemma combi_interior_subset_convex_hull {X : finset E} : combi_interior X ⊆ convex_hull X :=
  diff_subset _ _

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

-- /-- A sequence converges in the sence of topological spaces iff the associated statement for filter
-- holds. -/
-- lemma topological_space.seq_tendsto_iff {x : ℕ → α} {limit : α} :
--   tendsto x at_top (𝓝 limit) ↔
--     ∀ U : set α, limit ∈ U → is_open U → ∃ N, ∀ n ≥ N, (x n) ∈ U :=

-- /-- The sequential closure of a subset M ⊆ α of a topological space α is
-- the set of all p ∈ α which arise as limit of sequences in M. -/
-- def sequential_closure (M : set α) : set α :=
-- {p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ (x ⟶ p)}

-- lemma combi_interior_eq {X : finset E} (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
--   combi_interior X =
--     {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ X, 0 < w y) (hw₁ : ∑ y in X, w y = 1),
--       X.center_mass w id = x} :=

example {n : ℕ} : 1 ≤ n + 2 :=
begin
  apply nat.succ_pos,
end

lemma subset_closure_combi_interior {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  (X : set E) ⊆ closure (combi_interior X) :=
begin
  rintro x (hx : x ∈ X),
  apply sequential_closure_subset_closure,
  have hXnonempty : X.nonempty := ⟨x, hx⟩,
  have centroid_weights : ∑ (i : fin m → ℝ) in X, finset.centroid_weights ℝ X i = 1,
  { apply finset.sum_centroid_weights_eq_one_of_nonempty ℝ _ hXnonempty },
  refine ⟨_, _, _⟩,
  { intro n,
    apply ((n:ℝ)+2)⁻¹ • X.centroid ℝ id + (1-((n:ℝ)+2)⁻¹) • x },
  { intro n,
    rw finset.centroid_def,
    rw center_mass_eq_affine_combination _,
    { rw ←id.def x,
      rw ←finset.center_mass_ite_eq _ _ id hx,
      rw finset.center_mass_segment,
      { rw combi_interior_eq hX,
        refine ⟨_, _, _, rfl⟩,
        { simp only [mul_boole, finset.centroid_weights_apply],
          intros y hy,
          apply add_pos_of_pos_of_nonneg,
          { apply mul_pos,
            { rw inv_pos,
              norm_cast,
              simp, },
            { rw inv_pos,
              norm_cast,
              rwa finset.card_pos } },
          { split_ifs,
            { rw sub_nonneg,
              apply inv_le_one,
              norm_cast,
              apply nat.succ_pos },
            { refl } } },
        rw [finset.sum_add_distrib, ←finset.mul_sum, centroid_weights, ←finset.mul_sum,
          finset.sum_boole, finset.filter_eq],
        simp [hx] },
      { apply centroid_weights },
      { simp [finset.sum_boole, finset.filter_eq, hx] },
      { simp only [add_sub_cancel'_right] } },
    apply finset.sum_centroid_weights_eq_one_of_nonempty ℝ _ hXnonempty },
  { rw tendsto_iff_norm_tendsto_zero,
    convert_to filter.tendsto (λ (e:ℕ), ((e:ℝ)+2)⁻¹ * ∥X.centroid ℝ id - x∥) filter.at_top _,
    { ext n,
      rw [add_sub_assoc, sub_smul, sub_right_comm, one_smul, sub_self, zero_sub, ←smul_neg,
        ←smul_add, norm_smul_of_nonneg, ←sub_eq_add_neg],
      rw inv_nonneg,
      norm_cast,
      apply nat.zero_le },
    suffices : filter.tendsto (λ (e : ℕ), ((↑(e + 2):ℝ))⁻¹) filter.at_top (nhds 0),
    { simpa using this.mul_const _ },
    refine tendsto_inv_at_top_zero.comp _,
    rw tendsto_coe_nat_at_top_iff,
    apply filter.tendsto_add_at_top_nat }
end

lemma convex_combi_interior {X : finset E} (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  convex (combi_interior X) :=
begin
  rw convex_iff_forall_pos,
  intros x y hx hy t₁ t₂ ht₁ ht₂ h,
  rw combi_interior_eq hX at hx hy ⊢,
  rcases hx with ⟨h₁, h₂, h₃, rfl⟩,
  rcases hy with ⟨h₄, h₅, h₆, rfl⟩,
  refine ⟨λ x, t₁ * h₁ x + t₂ * h₄ x, λ x hx, _, _, _⟩,
  { exact add_pos (mul_pos ht₁ (h₂ x hx)) (mul_pos ht₂ (h₅ x hx)) },
  { rw [finset.sum_add_distrib, ←finset.mul_sum, ←finset.mul_sum, h₃, h₆],
    simp [h] },
  rw finset.center_mass_segment _ _ _ _ h₃ h₆ _ _ h,
end

-- Affine indep is necessary, since if not combi_interior can be empty
lemma closure_combi_interior_eq_convex_hull {X : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  closure (combi_interior X) = convex_hull (X : set E) :=
begin
  apply set.subset.antisymm,
  { rw is_closed.closure_subset_iff is_closed_convex_hull,
    apply combi_interior_subset_convex_hull },
  refine convex_hull_min (subset_closure_combi_interior hX) _,
  apply convex.closure,
  apply convex_combi_interior hX,
end

lemma combi_frontier_subset_convex_hull {X : finset E} : combi_frontier X ⊆ convex_hull X :=
  bUnion_subset (λ Y hY, convex_hull_mono hY.1)

lemma convex_hull_eq_interior_union_combi_frontier (X : finset E) :
  convex_hull ↑X = combi_interior X ∪ combi_frontier X :=
(sdiff_union_of_subset combi_frontier_subset_convex_hull).symm

lemma convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hY : affine_independent ℝ (λ p, p : (Y : set E) → E)) :
  combi_interior X ⊆ combi_interior Y → convex_hull (X : set E) ⊆ convex_hull (Y : set E) :=
begin
  rw ← closure_combi_interior_eq_convex_hull hX,
  rw ← closure_combi_interior_eq_convex_hull hY,
  intro h,
  apply closure_mono h,
end

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

lemma simplex_combi_interiors_cover (X : finset E) :
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
  x ∈ convex_hull (X : set E) ↔ ∃ Y ⊆ X, x ∈ combi_interior Y := sorry

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

lemma subdivision_iff_combi_interiors_subset_combi_interiors {S₁ S₂ : simplicial_complex m} :
  S₁ ≤ S₂ ↔ S₂.space ⊆ S₁.space ∧
  ∀ {X₁}, X₁ ∈ S₁.faces → ∃ {X₂}, X₂ ∈ S₂.faces ∧ combi_interior X₁ ⊆ combi_interior X₂ :=
begin
  split,
  { rintro ⟨hspace, hS⟩,
    use ge_of_eq hspace,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := hS hX,
    obtain ⟨Z, hZY, hXZ⟩ := simplex_combi_interiors_split_interiors (S₂.indep hY) hXY,
    exact ⟨Z, S₂.down_closed hY hZY, hXZ⟩ },
  { rintro ⟨hspace, hS⟩,
    split,
    { apply subset.antisymm _ hspace,
      rintro x hx,
      obtain ⟨X₁, hX₁, hx⟩ := mem_space_iff.1 hx,
      obtain ⟨X₂, hX₂, hX₁X₂⟩ := hS hX₁,
      rw mem_space_iff,
      refine ⟨X₂, hX₂, _⟩,
      apply convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior _ _ hX₁X₂ hx,
      { apply S₁.indep hX₁ },
      { apply S₂.indep hX₂ } },
    { rintro X₁ hX₁,
      obtain ⟨X₂, hX₂, hX₁X₂⟩ := hS hX₁,
      refine ⟨_, hX₂, convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior _ _ _⟩,
      { apply S₁.indep hX₁ },
      { apply S₂.indep hX₂ },
      { apply hX₁X₂ }}}
end

lemma subdivision_iff_partition {S₁ S₂ : simplicial_complex m} :
  S₁ ≤ S₂ ↔ (S₁.faces.nonempty → S₂.faces.nonempty) ∧ S₁.space ⊆ S₂.space ∧ ∀ {X₂}, X₂ ∈ S₂.faces →
  ∃ {F}, F ⊆ S₁.faces ∧ combi_interior X₂ = ⋃ (X₁ ∈ F), combi_interior X₁ :=
begin
  split,
  { rintro ⟨hspace, hsubdiv⟩,
    split,
    { rintro ⟨X₁, hX₁⟩,
      obtain ⟨X₂, hX₂, hX₁X₂⟩ := hsubdiv hX₁,
      exact ⟨X₂, hX₂⟩ },
    use le_of_eq hspace,
    rintro X hX,
    use [{Y | Y ∈ S₁.faces ∧ combi_interior Y ⊆ combi_interior X}, (λ Y hY, hY.1)],
    ext x,
    split,
    { rintro hxX,
      have hxspace := mem_space_iff.2 ⟨X, hX, hxX.1⟩,
      rw [←hspace, combi_interiors_cover, mem_bUnion_iff] at hxspace,
      obtain ⟨Y, hY, hxY⟩ := hxspace,
      apply mem_bUnion _ hxY,
      use hY,
      rintro y hyY,
      obtain ⟨Z, hZ, hYZ⟩ := hsubdiv hY,
      obtain ⟨W, hWZ, hYW⟩ := simplex_combi_interiors_split_interiors (S₂.indep hZ) hYZ,
      rw disjoint_interiors hX (S₂.down_closed hZ hWZ) x ⟨hxX, hYW hxY⟩,
      exact hYW hyY },
    { rw mem_bUnion_iff,
      rintro ⟨Y, ⟨hY, hYX⟩, hxY⟩,
      exact hYX hxY }},
  { rintro ⟨hempty, hspace, hpartition⟩,
    have hspace : S₁.space = S₂.space,
    { apply subset.antisymm hspace,
      rintro x hx,
      rw [combi_interiors_cover, mem_bUnion_iff] at ⊢ hx,
      obtain ⟨X, hX, hxX⟩ := hx,
      obtain ⟨F, hF, hXint⟩ := hpartition hX,
      rw [hXint, mem_bUnion_iff] at hxX,
      obtain ⟨Y, hY, hxY⟩ := hxX,
      exact ⟨Y, hF hY, hxY⟩ },
    use hspace,
    rintro X hX,
    cases finset.eq_empty_or_nonempty X with hXempty hXnonempty,
    { obtain ⟨Y, hY⟩ := hempty ⟨X, hX⟩,
      use [Y, hY],
      rw hXempty,
      simp },
    obtain ⟨x, hx⟩ := nonempty_combi_interior_of_nonempty (S₁.indep hX) hXnonempty,
    have hxspace := mem_space_iff.2 ⟨X, hX, hx.1⟩,
    rw [hspace, combi_interiors_cover, mem_bUnion_iff] at hxspace,
    obtain ⟨Y, hY, hxY⟩ := hxspace,
    use [Y, hY],
    rw ← closure_combi_interior_eq_convex_hull,
    apply closure_minimal _ is_closed_convex_hull,
    rintro x' hx',
    have hxspace := mem_space_iff.2 ⟨X, hX, hx'.1⟩,
    rw [hspace, combi_interiors_cover, mem_bUnion_iff] at hxspace,
    obtain ⟨Y', hY', hxY'⟩ := hxspace,
    suffices hYY' : Y = Y',
    { rw hYY',
      exact hxY'.1 },
    obtain ⟨F, hF, hinterior⟩ := hpartition hY,
    obtain ⟨F', hF', hinterior'⟩ := hpartition hY',
    apply disjoint_interiors hY hY' x (mem_inter _ _),
    { rw [hinterior, mem_bUnion_iff] at ⊢ hxY,
      obtain ⟨Z, hZ, hxZ⟩ := hxY,
      use [Z, hZ, hxZ] },
    { rw [hinterior', mem_bUnion_iff] at ⊢ hxY',
      obtain ⟨Z, hZ, hxZ⟩ := hxY',
      use [Z, hZ],
      rw ← disjoint_interiors hX (hF' hZ) x' ⟨hx', hxZ⟩,
      exact hx },
    apply S₁.indep hX }
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
  obtain ⟨X₂, hX₂, hX₁X₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2
    (S₁.down_closed hY₁ hX₁Y₁),
  obtain ⟨Y₂, hY₂, hY₁Y₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2 hY₁,
  obtain ⟨Z₂, hZ₂, hZ₁Z₂⟩ := (subdivision_iff_combi_interiors_subset_combi_interiors.1 hS).2 hZ₁,
  refine ⟨X₂, _, convex_hull_subset_convex_hull_of_combi_interior_subset_combi_interior _ _ hX₁X₂⟩,
  refine ⟨Y₂, hY₂, _, Z₂, hZ₂, _⟩,
  { apply subset_of_convex_hull_subset_convex_hull hX₂ hY₂,
    sorry
  },
  { sorry,
  },
  { apply S₁.indep (S₁.down_closed hY₁ hX₁Y₁), },
  { apply S₂.indep hX₂ }
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
