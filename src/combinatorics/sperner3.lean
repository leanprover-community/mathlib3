import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.basic
-- import data.nat.parity

-- TODO: move to mathlib
lemma subset_iff_inter_eq_left {ι : Type*} {X Y : finset ι} (h : Y ⊆ X) [decidable_eq ι] :
  X ∩ Y = Y :=
begin
  ext t,
  simp only [and_iff_right_iff_imp, finset.mem_inter],
  apply h
end

-- TODO: move to mathlib
theorem sdiff_union_of_subset {α : Type*} {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : (s₂ \ s₁) ∪ s₁ = s₂ :=
set.ext $ λ x, by simpa [em, or_comm, or_and_distrib_left] using or_iff_right_of_imp (@h x)

open_locale classical affine

open set
namespace affine

-- TODO: find in mathlib or move to mathlib
lemma finset.strong_downward_induction_on {α : Type*} {p : finset α → Prop} {A : set (finset α)}
  {n : ℕ} (hA : ∀ {X}, X ∈ A → (X : finset α).card ≤ n) {X : finset α} (hX : X ∈ A) :
  (∀ {Y}, Y ∈ A → (∀ {Z}, Z ∈ A → Y ⊂ Z → p Z) → p Y) → p X := λ h,
begin
  refine (well_founded.induction (subrelation.wf (λ s t, finset.card_lt_card : ∀ s t : A, t.val ⊂ s.val → t.val.card < s.val.card) _ : well_founded (λ s t : A, t.1 ⊂ s.1)) _ (λ x h2, h x.2 $ λ z hzA hxZ, h2 ⟨z, hzA⟩ hxZ) : (λ s, p s.1 : A → Prop) ⟨X, hX⟩),
  convert inv_image.wf (λ s, n-s.val.card : A → ℕ) (is_well_order.wf : well_founded (<)),
  ext s t,
  exact (nat.sub_lt_sub_left_iff (hA s.2)).symm
end

/--
A simplicial complex in `R^m`. TODO: generalise to normed affine spaces `E`, so this is
`simplicial_complex E`.
-/
@[ext] structure simplicial_complex (m : ℕ) :=
(faces : set (finset (fin m → ℝ)))
(indep : ∀ {X}, X ∈ faces → affine_independent ℝ (λ p, p : (X : set (fin m → ℝ)) → (fin m → ℝ)))
(down_closed : ∀ {X Y}, X ∈ faces → Y ⊆ X → Y ∈ faces)
(disjoint : ∀ {X Y}, X ∈ faces → Y ∈ faces →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set (fin m → ℝ)))

variables {m n : ℕ} {S : simplicial_complex m}
local notation `E` := fin m → ℝ

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
def simplicial_complex.of_set_closure {m : ℕ} {A : set (finset (fin m → ℝ))}
  (indep : ∀ {X}, X ∈ A → affine_independent ℝ (λ p, p : (X : set (fin m → ℝ)) → (fin m → ℝ)))
  (disjoint : ∀ {X Y}, X ∈ A → Y ∈ A →
  convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set (fin m → ℝ))) :
  simplicial_complex m := {
  faces := {X | ∃ {Y}, Y ∈ A ∧ X ⊆ Y},
  indep := begin
    rintro X ⟨Y, hY, hXY⟩,
    exact affine_independent_of_subset_affine_independent (indep hY) hXY,
  end,
  down_closed := begin
    rintro X Y ⟨Z, hZ, hXZ⟩ hYX,
    exact ⟨Z, hZ, subset.trans hYX hXZ⟩,
  end,
  disjoint := begin
    rintro W X ⟨Y, hY, hWY⟩ ⟨Z, hZ, hXZ⟩,
    specialize disjoint hY hZ,
    sorry
  end}

/-- The underlying space of a simplicial complex. -/
def simplicial_complex.space (S : simplicial_complex m) : set E :=
⋃ X ∈ S.faces, convex_hull (X : set E)

--I think we should take faces := {∅} instead of faces := ∅
def empty_simplicial_complex (m : ℕ) : simplicial_complex m := {
  faces := ∅,
  indep := begin
    rintro X hX,
    exfalso,
    exact not_mem_empty X hX,
  end,
  down_closed := begin
    rintro X _ hX,
    exfalso,
    exact not_mem_empty X hX,
  end,
  disjoint := begin
    rintro X _ hX,
    exfalso,
    exact not_mem_empty X hX,
  end, }

lemma empty_space_of_empty_simplicial_complex (m : ℕ) : (empty_simplicial_complex m).space = ∅ :=
  set.bUnion_empty _

/-def simplicial_complex.dimension (S : simplicial_complex m) {X : finset (fin m → ℝ)} : ℕ :=
  Sup {X.card - 1 | X ∈ S.faces}-/

/-The dimension of a simplicial complex is the maximal dimension of its faces-/
/-def simplicial_complex.dimension (S : simplicial_complex m) : ℕ :=
 Sup {finset.card (X : set E) | X ∈ S.faces}-/

/--
The boundary of a simplex as a subspace.
-/
def boundary (X : finset E) : set E :=
⋃ Y ⊂ X, convex_hull Y

lemma boundaries_agree_of_high_dimension {X : finset E} (hXcard : X.card = m + 1) : boundary X = frontier (convex_hull X) :=
begin
  ext x,
  split,
  {
    unfold boundary,
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
convex_hull X \ boundary X

lemma boundary_subset_convex_hull {X : finset E} : boundary X ⊆ convex_hull X :=
bUnion_subset (λ Y hY, convex_hull_mono hY.1)

lemma convex_hull_eq_interior_union_boundary (X : finset E) :
  convex_hull ↑X = combi_interior X ∪ boundary X :=
(sdiff_union_of_subset boundary_subset_convex_hull).symm

lemma disjoint_interiors {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (x : E) :
  x ∈ combi_interior X ∩ combi_interior Y → X = Y :=
begin
  rintro ⟨⟨hxX, hXbound⟩, ⟨hyY, hYbound⟩⟩,
  by_contra,
  have hXY : X ∩ Y ⊂ X,
  {
    use finset.inter_subset_left X Y,
    intro H,
    apply hYbound,
    apply set.mem_bUnion _ _,
    exact X,
    exact ⟨subset.trans H (finset.inter_subset_right X Y),
      (λ H2, h (finset.subset.antisymm (subset.trans H (finset.inter_subset_right X Y)) H2))⟩,
    exact hxX,
  },
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
    by_cases x ∈ boundary s,
    { rw [boundary] at h,
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

/- interior X is the topological interior iff X is of dimension m -/
lemma interiors_agree_of_high_dimension {S : simplicial_complex m} :
  ∀ X ∈ S.faces, finset.card X = m + 1 → combi_interior X = interior X :=
begin
  unfold combi_interior,
  rintro X hX hXdim,
  ext x,
  split,
  {
    rintro ⟨hxhull, hxbound⟩,
    unfold convex_hull at hxhull,
    unfold interior,
    sorry
  },
  {
    intro hx,
    split,
    {
      sorry
    },
    {
      intro hxbound,
      sorry
    }
  }
end

local attribute [-instance] real.ring

--To golf down
lemma size_bound {X : finset (fin m → ℝ)} (hX : affine_independent ℝ (λ p, p : (X : set E) → E)) :
  X.card ≤ m+1 :=
begin
  cases X.eq_empty_or_nonempty,
  { simp [h] },
  rcases h with ⟨y, hy⟩,
  have y_mem : y ∈ (X : set (fin m → ℝ)) := hy,
  have Xy : (↑X \ {y}) = (↑(X.erase y) : set (fin m → ℝ)),
  { simp },
  have := hX,
  rw @affine_independent_set_iff_linear_independent_vsub ℝ _ _ _ _ _ _ ↑X y y_mem at this,
  letI q : fintype ↥((λ (p : fin m → ℝ), p -ᵥ y) '' (↑X \ {y})),
  { apply set.fintype_image _ _,
    { apply_instance },
    rw Xy,
    exact finset_coe.fintype _ },
  have hX := finite_dimensional.fintype_card_le_findim_of_linear_independent this,
  simp only [vsub_eq_sub, finite_dimensional.findim_fin_fun, fintype.card_of_finset] at hX,
  rw finset.card_image_of_injective at hX,
  { simp only [set.to_finset_card] at hX,
    rw fintype.card_of_finset' (X.erase y) at hX,
    { rwa [finset.card_erase_of_mem hy, nat.pred_le_iff] at hX },
    { simp [and_comm] } },
  rintro p q h,
  simpa using h,
end

--Refinement of `size_bound`
lemma simplex_dimension_le_space_dimension {S : simplicial_complex m} {X : finset E} :
  X ∈ S.faces → finset.card X ≤ m + 1 := λ hX, size_bound (S.indep hX)

def is_extreme (s : set E) (x : E) : Prop :=
x ∈ s ∧ ∀ (x₁ x₂ ∈ s), x ∈ segment x₁ x₂ → x = x₁ ∨ x = x₂

lemma convex_remove_iff_is_extreme {s : set E} {x : E} (hs : convex s) (hx : x ∈ s) :
  convex (s \ {x}) ↔ is_extreme s x :=
begin
  split,
  { refine λ hsx, ⟨hx, λ y₁ y₂ hy₁ hy₂ hxy, _⟩,
    by_contra,
    push_neg at h,
    rw convex_iff_segment_subset at hsx,
    exact (hsx ⟨hy₁, h.1.symm⟩ ⟨hy₂, h.2.symm⟩ hxy).2 rfl },
  { intro hsx,
    rw convex_iff_segment_subset,
    rintro y₁ y₂ ⟨hy₁, y₁x : _ ≠ _⟩ ⟨hy₂, y₂x : _ ≠ _⟩ z hz,
    refine ⟨hs.segment_subset hy₁ hy₂ hz, λ (t : z = x), _⟩,
    subst t,
    rcases hsx.2 _ _ hy₁ hy₂ hz with (rfl | rfl),
    exacts [y₁x rfl, y₂x rfl] }
end

-- example {a b c d : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d) (h : a * b + c * d = 0) :
--   b = 0 ∧ d = 0 :=
-- begin
--   rw add_eq_zero_iff' at h,
--   rw mul_eq_zero at h,
--   rw mul_eq_zero at h,

-- end

open_locale big_operators

lemma coe_sum {α β : Type*} [add_comm_monoid β] (s : finset α) (f : α → β) :
  ∑ (i : (s : set α)), f i = ∑ i in s, f i :=
finset.sum_bij (λ a _, a) (λ a _, a.prop)
  (λ _ _, rfl)
  (λ _ _ _ _, subtype.ext)
  (λ a ha, ⟨⟨_, ha⟩, finset.mem_univ _, (subtype.coe_mk _ _).symm⟩)

lemma is_extreme_convex_hull_of_affine_independent {s : finset E} {x : E} (hx : x ∈ s)
  (hs : affine_independent ℝ (λ p, p : (s : set E) → E)) :
  is_extreme (convex_hull ↑s) x :=
begin
  -- have := convex_independent_of_affine_independent hs _ hx,

  -- rw ←convex_remove_iff_is_extreme (convex_convex_hull s) (subset_convex_hull _ hx),
  refine ⟨subset_convex_hull _ hx, _⟩,
  rintro y y' hy hy' t,
  rw finset.convex_hull_eq at hy hy',
  rcases hy with ⟨w, hw₀, hw₁, hy⟩,
  rcases hy' with ⟨w', hw'₀, hw'₁, hy'⟩,
  -- rcases hy with ⟨ι, q, w, z, hw₀, hw₁ : q.sum w = 1, hz, _⟩,
  -- rcases hy' with ⟨ι', q', w', z', hw'₀, hw'₁ : q'.sum w' = 1, hz', rfl⟩,
  rw segment_eq_image at t,
  rcases t with ⟨θ, hθ₁, hθ₂ : _ + _ = _⟩,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at hy,
  rw finset.center_mass_eq_of_sum_1 _ _ hw'₁ at hy',
  change s.sum (λ i, w i • i) = y at hy,
  change s.sum (λ i, w' i • i) = y' at hy',
  let w'' : E → ℝ := λ t, (1 - θ) * w t + θ * w' t - if t = x then 1 else 0,
  have hw''₁ : s.sum w'' = 0,
  { rw [finset.sum_sub_distrib, finset.sum_add_distrib, ← finset.mul_sum, ← finset.mul_sum, hw₁,
      hw'₁, finset.sum_ite_eq' s, if_pos hx],
    simp },
  have hw''₂ : s.sum (λ i, w'' i • i) = 0,
  { simp only [sub_smul, add_smul, finset.sum_add_distrib, finset.sum_sub_distrib],
    simp only [mul_smul, ←finset.smul_sum, hy, hy'],
    simp only [ite_smul, zero_smul, one_smul, finset.sum_ite_eq', if_pos hx, hθ₂, sub_self] },
  by_contra t,
  push_neg at t,
  suffices hw''₃ : ∀ q ∈ s, w'' q = 0,
  { have : θ = 0 ∨ θ = 1,
    { by_contra hθ,
      push_neg at hθ,
      have : 0 < θ ∧ 0 < 1 - θ,
      { split,
        { apply lt_of_le_of_ne hθ₁.1 hθ.1.symm },
        { rw sub_pos,
          apply lt_of_le_of_ne hθ₁.2 hθ.2 } },
      have both_zero : ∀ q ∈ s, q ≠ x → w q = 0 ∧ w' q = 0,
      { rintro q hq₁ hq₂,
        specialize hw''₃ q hq₁,
        change _ + _ = _ at hw''₃,
        rw if_neg hq₂ at hw''₃,
        simp only [add_zero, neg_zero] at hw''₃,
        rw add_eq_zero_iff' at hw''₃,
        apply and.imp _ _ hw''₃,
        rw mul_eq_zero,
        intro t,
        exact or.resolve_left t (ne_of_gt this.2),
        rw mul_eq_zero,
        intro t,
        exact or.resolve_left t (ne_of_gt this.1),
        apply mul_nonneg (le_of_lt this.2),
        exact hw₀ q hq₁,
        apply mul_nonneg,
        apply le_of_lt this.1,
        apply hw'₀,
        apply hq₁ },
      have : (1 - θ) * w x + θ * w' x = 1,
      { specialize hw''₃ _ hx,
        change (1 - θ) * w x + θ * w' x - ite _ _ _ = 0 at hw''₃,
        rw if_pos rfl at hw''₃,
        rwa sub_eq_zero at hw''₃ },
      rw finset.sum_eq_single x at hw₁,
      { rw finset.sum_eq_single x at hy,
        { rw hw₁ at hy,
          apply t.1,
          simpa using hy },
        { rintro q hq₁ hq₂,
          rw (both_zero q hq₁ hq₂).1,
          simp },
        { intro t,
          exfalso,
          apply t,
          apply hx } },
      { rintro q hq₁ hq₂,
        apply (both_zero q hq₁ hq₂).1 },
      { intro t,
        exfalso,
        apply t,
        apply hx } },
    rcases this with (rfl | rfl),
    simp at hθ₂,
    apply t.1,
    symmetry,
    assumption,
    simp at hθ₂,
    apply t.2,
    symmetry,
    assumption },
  rw affine_independent_iff_of_fintype at hs,
  let w''' : (s : set E) → ℝ := λ t, w'' (t : E),
  have hw''' : finset.univ.sum w''' = 0,
  { rw coe_sum,
    apply hw''₁ },
  specialize hs w''' hw''' _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw''' (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw coe_sum _ (λ i, w'' i • i),
    apply hw''₂ },
  rintro q hq,
  exact hs ⟨q, hq⟩,
end

--Accurate name?
lemma mem_of_is_extreme_to_convex_hull {X : set E} {x : E} (hx : is_extreme (convex_hull X) x) :
  x ∈ X :=
begin
  have : x ∈ convex_hull (X : set E) := hx.1,
  rw ←convex_remove_iff_is_extreme (convex_convex_hull _) this at hx,
  by_contra,
  have : convex_hull X ⊆ convex_hull X \ {x},
  { apply convex_hull_min _ hx,
    rw subset_diff,
    exact ⟨subset_convex_hull _, disjoint_singleton_right.2 h⟩ },
  rw [subset_diff, disjoint_singleton_right] at this,
  apply this.2 ‹x ∈ convex_hull X›,
end

--probably belongs in the mathlib file of convex hulls
lemma subset_of_convex_hull_eq_convex_hull_of_linearly_independent {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (h : convex_hull ↑X = convex_hull (Y : set E)) :
  X ⊆ Y :=
begin
  rintro x hx,
  have hxextreme := is_extreme_convex_hull_of_affine_independent hx hX,
  rw h at hxextreme,
  exact mem_of_is_extreme_to_convex_hull hxextreme,
end

--Keep two linearly_independent in the name?
lemma eq_of_convex_hull_eq_convex_hull_of_linearly_independent_of_linearly_independent
  {X Y : finset E}
  (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hY : affine_independent ℝ (λ p, p : (Y : set E) → E))
  (h : convex_hull (X : set E) = convex_hull (Y : set E)) :
  X = Y :=
finset.subset.antisymm
  (subset_of_convex_hull_eq_convex_hull_of_linearly_independent hX h)
  (subset_of_convex_hull_eq_convex_hull_of_linearly_independent hY h.symm)

def convex_independent (s : set E) : Prop := ∀ x ∈ s, x ∉ convex_hull (s \ {x})

lemma convex_independent_of_affine_independent {s : set E} :
  affine_independent ℝ (λ p, p : s → E) → convex_independent s :=
begin
  sorry
end


/- S₁ ≤ S₂ (S₁ is a subdivision of S₂) iff their underlying space is the same and each face of S₁
is contained in some face of S₂-/
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
    {
      rintro S₁ S₂ h₁ h₂ W hW,
      apply finset.strong_downward_induction_on (λ X hX, simplex_dimension_le_space_dimension hX)
        hW,
      {
        rintro X hX h,
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
        {
          rw finset.subset.antisymm hZX hXZ at hYZhull,
          rw eq_of_convex_hull_eq_convex_hull_of_linearly_independent_of_linearly_independent
            (S₁.indep hX) (S₂.indep hY) (subset.antisymm hXYhull hYZhull),
          exact hY,
        },
        { exact S₂.down_closed (h hZ ⟨hXZ, hZX⟩) hXZ }
      }
    },
    rintro S₁ S₂ h₁ h₂,
    ext X,
    exact ⟨λ hX, aux_lemma h₁ h₂ hX, λ hX, aux_lemma h₂ h₁ hX⟩,
  end}

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
  {
    obtain ⟨Z, hZ⟩ := (not_facet_iff_subface hY).mp hYfacet,
    obtain ⟨W, hW⟩ := h hZ.1 hZ.2,
    exact ⟨W, hW.1, finset.subset.trans hZ.2.1 hW.2⟩,
  }
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

lemma pureness_le_space_dimension {S : simplicial_complex m} (hS : S.pure) {X : finset (fin m → ℝ)} :
  X ∈ S.faces → X.card ≤ pureness hS + 1 :=
begin
  rintro hX,
  obtain ⟨n, hS⟩ := hS,
  sorry
end

lemma facet_iff_dimension_eq_pureness {S : simplicial_complex m} (hS : S.pure)
  {X : finset (fin m → ℝ)} : X ∈ S.faces → (X ∈ S.facets ↔ X.card = pureness hS + 1) :=
begin
  rintro hX,
  split,
  { exact pureness_def hS },
  {
    rintro hXcard,
    use hX,
    rintro Y hY hXY,
    apply finset.eq_of_subset_of_card_le hXY,
    rw hXcard,
    exact pureness_le_space_dimension hS hY,
  }
end

/--
A simplicial complex is pure iff there exists n such that all faces are subfaces of some
n-dimensional face
-/
lemma pure_iff {S : simplicial_complex m} : S.pure ↔ ∃ n : ℕ, ∀ {X}, X ∈ S.faces →
  ∃ {Y}, Y ∈ S.faces ∧ finset.card Y = n + 1 ∧ X ⊆ Y :=
begin
  split,
  {
    rintro hS,
    use pureness hS,
    rintro X hX,
    obtain ⟨Y, hY, hXY⟩ := subfacet hX,
    exact ⟨Y, facets_subset hY, pureness_def hS hY, hXY⟩,
  },
  {
    rintro ⟨n, hS⟩,
    use n,
    rintro X ⟨hX, hXmax⟩,
    obtain ⟨Y, hY, hYcard, hXY⟩ := hS hX,
    rw hXmax hY hXY,
    exact hYcard,
  }
end

/-The cells of a simplicial complex are its simplices whose dimension matches the one of the space-/
def simplicial_complex.cells (S : simplicial_complex m) : set (finset (fin m → ℝ))
  := {X | X ∈ S.faces ∧ X.card = m + 1}

lemma cells_subset_facets {S : simplicial_complex m} : S.cells ⊆ S.facets :=
begin
  rintro X ⟨hX, hXcard⟩,
  by_contra,
  obtain ⟨Y, hY, hXY⟩ := (not_facet_iff_subface hX).mp h,
  have := finset.card_lt_card hXY,
  have := simplex_dimension_le_space_dimension hY,
  linarith,
end

/-A simplicial complex is connected iff its space is-/
def simplicial_complex.connected (S : simplicial_complex m) : Prop := connected_space S.space

def simplicial_complex.skeleton (S : simplicial_complex m) (k : ℕ) : simplicial_complex m :=
  simplicial_complex.of_surcomplex {X ∈ S.faces | finset.card X ≤ k + 1} (λ X ⟨hX, _⟩, hX)
  (λ X Y hX hY, ⟨S.down_closed hX.1 hY, le_trans (finset.card_le_of_subset hY) hX.2⟩)

--Is this lemma useful?
lemma skeleton_subcomplex_self {S : simplicial_complex m} {k : ℕ} :
  (S.skeleton k).faces ⊆ S.faces := (λ X ⟨hX, _⟩, hX)

lemma pure_skeleton_of_pure {S : simplicial_complex m} (k : ℕ) : S.pure → (S.skeleton k).pure :=
begin
  rintro ⟨n, hS⟩,
  cases le_or_gt (n + 1) (k + 1) with hmin hmin,
  {
    use n,
    rintro X hXskel,
    obtain ⟨Y, hY, hXY⟩ := subfacet (skeleton_subcomplex_self (facets_subset hXskel)),
    have hYskel : Y ∈ (S.skeleton k).faces,
    {
      use facets_subset hY,
      simp,
      rw hS hY,
      exact hmin,
    },
    rw hXskel.2 hYskel hXY,
    exact hS hY,
  },
  {
    use k,
    rintro X ⟨⟨hX, hXcard⟩, hXmax⟩,
    obtain ⟨Y, hY, hXY⟩ := subfacet hX,
    have : k + 1 - X.card + X.card ≤ Y.card,
    {
      rw hS hY,
      rw nat.sub_add_cancel hXcard,
      exact le_of_lt hmin,
    },
    obtain ⟨Z, hXZ, hZY, hZcard⟩ := finset.exists_intermediate_set (k + 1 - X.card) this hXY,
      rw nat.sub_add_cancel hXcard at hZcard,
    rw hXmax ⟨S.down_closed (facets_subset hY) hZY, le_of_eq hZcard⟩ hXZ,
    exact hZcard,
  }
end

lemma skeleton_pureness_eq_min_pureness_dimension {S : simplicial_complex m} {k : ℕ} (hS : S.pure) :
  pureness (pure_skeleton_of_pure k hS) = min (pureness hS) k := sorry

/-A simplicial complex is connected iff its 1-skeleton is-/
lemma connected_iff_one_skeleton_connected {S : simplicial_complex m} :
  S.connected ↔ (S.skeleton 1).connected :=
begin
  split,
  {
    rintro h,
    unfold simplicial_complex.connected,
    sorry
  },
  {
    sorry
  }
end

/-A simplex is locally finite iff each face belongs to finitely many faces-/
def simplicial_complex.locally_finite (S : simplicial_complex m) : Prop :=
  ∀ x : fin m → ℝ, finite {X | X ∈ S.faces ∧ x ∈ convex_hull (X : set(fin m → ℝ))}

lemma locally_compact_realisation_of_locally_finite (S : simplicial_complex m)
  (hS : S.locally_finite) : locally_compact_space S.space :=
  {local_compact_nhds := begin
    rintro x X hX,
    sorry
  end}

/-The closure of a set of faces is the set of their subfaces-/
def closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) :
  simplicial_complex m := simplicial_complex.of_surcomplex {X | ∃ X' ∈ A, X ⊆ X'}
  (λ X ⟨X', hX', hX⟩, S.down_closed (hA hX') hX)
  (λ X Y ⟨X', hX', hX⟩ hY, ⟨X', hX', subset.trans hY hX⟩)

lemma closure_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : (closure hA).faces ⊆ S.faces := λ X ⟨X', hX', hX⟩, S.down_closed (hA hX') hX

lemma subset_closure {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : A ⊆ (closure hA).faces := λ X hX, ⟨X, hX, subset.refl _⟩

lemma closure_mono {S : simplicial_complex m} {A B : set (finset (fin m → ℝ))} (hB : B ⊆ S.faces)
  (hAB : A ⊆ B) : (closure (subset.trans hAB hB)).faces ⊆ (closure hB).faces :=
  λ X ⟨Y, hY, hX⟩, ⟨Y, hAB hY, hX⟩

/-The open star of a set of faces is the s-/
def star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))} (hA : A ⊆ S.faces) :
  set (finset (fin m → ℝ)) := ⋃ (X : finset (fin m → ℝ)) (H : X ∈ A), {Y | Y ∈ S.faces ∧ X ⊆ Y}

lemma star_subset {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : star hA ⊆ S.faces :=
begin
  rintro Y ⟨_, ⟨X, rfl⟩, hX⟩,
  simp at hX,
  exact hX.2.1,
end

lemma self_subset_star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
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
  subset.trans (self_subset_star hA) (subset_closure (star_subset hA))

lemma star_subset_Star {S : simplicial_complex m} {A : set (finset (fin m → ℝ))}
  (hA : A ⊆ S.faces) : star hA ⊆ (Star hA).faces := subset_closure (star_subset hA)

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
        (self_subset_star (closure_subset hA) hZ.1) (subset.trans hZ.2.2 hXY)),
    }
  end

/-
-/
def link_singleton {S : simplicial_complex m} {X : finset (fin m → ℝ)} (hX : X ∈ S.faces) :
  simplicial_complex m := sorry

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

lemma boundary_subset_complex {S : simplicial_complex m} : S.boundary.faces ⊆ S.faces :=
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
  obtain ⟨Y, hY, hYcard, hXY⟩ := hS (boundary_subset_complex hX),
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

--Bad name?
lemma faces_subset_pyramid {S : simplicial_complex m} {v : fin m → ℝ}
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

/-
A polytope of dimension `n` in `R^m` is a subset for which there exists a simplicial complex which
is pure of dimension `n` and has the same underlying space.
-/
@[ext] structure polytope (m n : ℕ) :=
(space : set (fin m → ℝ))
(realisable : ∃ (S : simplicial_complex m), S.pure ∧ space = S.space)

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
    rintro X hX,
    exfalso,
    exact not_mem_empty X hX,
  },
  obtain ⟨x, hx⟩ := hPnonempty,
  --consider the boundary of some realisation of P and remove it x,
  --have := P.realisation.boundary.erasure {x},
  --then add it back by taking the pyramid of this monster with x
  sorry
end

noncomputable def polytope.triangulation_of_convex {P : polytope m n} (hP : convex P.space) :
  simplicial_complex m := classical.some (polytope.triangulable_of_convex hP)





variables {s : set E}

-- TODO: move to mathlib
lemma kenny (M : Type*) [add_comm_group M] [vector_space ℝ M] (s : affine_subspace ℝ M) :
  convex (s : set M) :=
λ x y hxs hys a b ha hb hab,
calc a • x + b • y = b • (y - x) + x : convex.combo_to_vadd hab
               ... ∈ s : s.2 _ hys hxs hxs

-- TODO: move to mathlib
lemma convex_hull_subset_span_points (X : set E) :
  convex_hull X ⊆ affine_span ℝ X :=
begin
  apply convex_hull_min,
  apply subset_affine_span,
  apply kenny,
end

lemma thingy {X Y : set E} (hY₁ : Y ⊆ X) : (λ p, p : X → E) '' {t : X | ↑t ∈ Y} = Y :=
begin
  ext y,
  specialize @hY₁ y,
  simpa [←and_assoc],
end

open_locale big_operators

-- TODO: move to mathlib
lemma center_mass_eq_affine_combination {ι : Type*} {t : finset ι} {p : ι → E} {w : ι → ℝ}
  (hw₂ : ∑ i in t, w i = 1) :
  finset.affine_combination t p w = finset.center_mass t w p :=
begin
  rw finset.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
  simp only [vsub_eq_sub, add_zero, finset.weighted_vsub_of_point_apply, vadd_eq_add, sub_zero],
  rw finset.center_mass_eq_of_sum_1 _ _ hw₂,
end

#exit












-- lemma of_affine_independent_set (X : set E) (hX : affine_independent ℝ (λ p, p : X → E)) :
--   ∀ (s : finset E) (w : E → ℝ), ∑ i in s, w i = 0 → s.weighted_vsub _ w = (0 : E) → ∀ i ∈ s, w i = 0 :=
-- begin
-- end

-- omit V
-- lemma filter_attach {ι : Type*} (s : finset ι) (p : ι → Prop) :
--   s.attach.filter (λ i, p i) = (s.filter p).attach.image (λ k, ⟨k, finset.filter_subset _ _ k.2⟩) :=
-- begin
--   ext ⟨a, ha⟩,
--   simp [ha],
-- end
-- include V

-- lemma of_affine_independent_set (s : set P) (hp : affine_independent k (λ p, p : s → P)) :
--   ∀ (t : finset ι) (w : ι → k) (z : ι → P), ∑ i in t, w i = 0 → (∀ i ∈ t, z i ∈ s) →
--   t.weighted_vsub z w = (0:V) → ∀ i ∈ t, w i = 0 :=
-- begin
--   rintro t w z hw₁ hz hw₂,
--   rw affine_independent_def at hp,
--   let s' : finset s := t.attach.image (λ i, ⟨z i, hz _ i.2⟩),
--   let w' : s → k,
--   { intro x,
--     apply ∑ i in (t.filter (λ j, z j = x)), w i },
--   have : ∑ (i : s) in s', w' i = 0,
--   { change ∑ (i : s) in s', ∑ j in _, _ = _,-- rintro ⟨_, _⟩ ⟨_, _⟩,
--     rw finset.sum_image' (λ (i : {x // x ∈ t}), w i),
--     { dsimp only,
--       rw finset.sum_attach,
--       rw hw₁ },
--     simp only [finset.mem_attach, subtype.mk_eq_mk, forall_true_left, subtype.coe_mk],
--     rintro c,
--     have : finset.filter (λ (c' : {x // x ∈ t}), z ↑c' = z ↑c) t.attach = _,
--     { exact filter_attach t (λ c', z c' = z c) },
--     simp only [finset.filter_congr_decidable],
--     simp only [finset.filter_congr_decidable] at this,
--     rw this,
--     simp [finset.sum_attach] },
--   have : s'.weighted_vsub (λ (p : ↥s), ↑p) w' = (0 : V),
--   { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ this (0:V),
--     rw finset.weighted_vsub_of_point_apply,
--     simp only [vsub_eq_sub, sub_zero],
--     change ∑ (i : s) in s', (∑ j in _, _) • _ = _,
--     simp_rw [finset.sum_smul],
--     rw finset.sum_image' (λ (i : {x // x ∈ t}), _),
--   },
--   -- specialize hp s' w' this,


--   -- sorry,

--   -- have := (t.image z).attach,
--   -- have : finset s := t.
-- end

-- example (X Y : finset E) (h : X ⊆ Y) : X ∩ Y = X :=
-- begin
--   library_search,
-- end

lemma thing {ι β : Type*} [add_comm_monoid β] (X : finset ι) (f : ι → β) :
  ∑ (x : (X : set ι)), f ↑x = ∑ x in X, f x :=
begin
  rw ←finset.sum_image,
  apply finset.sum_congr _ (λ _ _, rfl),
  { ext, simp },
  { simp },
end


lemma disjoint_convex_hulls {X : finset E} (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  {Y₁ Y₂ : finset E} (hY₁ : Y₁ ⊆ X) (hY₂ : Y₂ ⊆ X) :
  convex_hull (Y₁ : set E) ∩ convex_hull (Y₂ : set E) ⊆ convex_hull (Y₁ ∩ Y₂ : set E) :=
begin
  rintro x ⟨hx₁, hx₂⟩,
  rw ←finset.coe_inter,
  rw finset.convex_hull_eq at hx₁ hx₂,
  rcases hx₁ with ⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩,
  rcases hx₂ with ⟨w₂, h₁w₂, h₂w₂, h₃w₂⟩,
  rw finset.center_mass_eq_of_sum_1 _ _ h₂w₁ at h₃w₁,
  rw finset.center_mass_eq_of_sum_1 _ _ h₂w₂ at h₃w₂,
  dsimp at h₃w₁,
  dsimp at h₃w₂,
  rw affine_independent_def at hX,
  let w : E → ℝ,
  { intro x,
    apply (if x ∈ Y₁ then w₁ x else 0) - (if x ∈ Y₂ then w₂ x else 0) },
  have h₁w : ∑ (i : (X : set E)), w i = 0,
  { rw thing,
    rw finset.sum_sub_distrib,
    rw ←finset.sum_filter,
    rw finset.filter_mem_eq_inter,
    rw ←finset.sum_filter,
    rw finset.filter_mem_eq_inter,
    rw subset_iff_inter_eq_left hY₁,
    rw subset_iff_inter_eq_left hY₂,
    rw h₂w₁,
    rw h₂w₂,
    simp only [sub_self] },
  have h₂w : finset.univ.weighted_vsub (λ (p : (X : set E)), (p : E)) (λ (i : (X : set E)), w i) = (0 : E),
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ h₁w (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw thing X (λ i, w i • i),
    dsimp only,
    change ∑ i in X, (_ - _) • i = 0,
    simp_rw sub_smul,
    simp_rw ite_smul,
    simp_rw zero_smul,
    rw [finset.sum_sub_distrib, ←finset.sum_filter, finset.filter_mem_eq_inter,
      subset_iff_inter_eq_left hY₁, ←finset.sum_filter, finset.filter_mem_eq_inter,
      subset_iff_inter_eq_left hY₂, h₃w₁, h₃w₂, sub_self] },
  specialize hX finset.univ _ h₁w h₂w,
  simp only [finset.mem_univ, set_coe.forall, forall_true_left] at hX,
  rw finset.convex_hull_eq,
  have t₁ : ∀ x, x ∈ Y₁ → x ∉ Y₂ → w₁ x = 0,
  { rintro x hx₁ hx₂,
    have : ite (x ∈ Y₁) (w₁ x) 0 - ite (x ∈ Y₂) (w₂ x) 0 = 0 := hX x _,
    rw if_pos hx₁ at this,
    rw if_neg hx₂ at this,
    rw sub_zero at this,
    apply this,
    simp only [finset.mem_coe],
    apply hY₁,
    apply hx₁ },
  have h₄w₁ : ∑ (y : fin m → ℝ) in Y₁ ∩ Y₂, w₁ y = 1,
  { rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₂w₁],
    simp_rintro x hx₁ hx₂,
    specialize hx₂ hx₁,
    apply t₁,
    apply hx₁,
    apply hx₂ },
  refine ⟨w₁, _, h₄w₁, _⟩,
  { simp only [and_imp, finset.mem_inter],
    rintro y hy₁ hy₂,
    apply h₁w₁,
    apply hy₁ },
  { rw finset.center_mass_eq_of_sum_1 _ _ h₄w₁,
    dsimp only [id.def],
    rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₃w₁],
    simp_rintro x hx₁ hx₂,
    left,
    apply t₁,
    apply hx₁,
    apply hx₂,
    apply hx₁ },
end

def triangulation.facets (S : triangulation s) : set (finset E) :=
{X ∈ S.faces | ∀ Y ∈ S.faces, X ⊆ Y → X = Y}

def of_facets (S : set (finset E)) (hS₁ : ∀ X ∈ S, affine_independent ℝ (λ p, p : (X : set E) → E))
  (hS₂ : s = ⋃ (X ∈ S), convex_hull ↑X)
  (disjoint : ∀ (X Y ∈ S), convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E)) :
  triangulation s :=
{ faces := {X | ∃ Y ∈ S, X ⊆ Y},
  indep :=
  begin
    rintro X ⟨Y, YS, XY⟩,
    apply affine_independent_of_subset_affine_independent (hS₁ _ YS),
    rwa finset.coe_subset,
  end,
  covering :=
  begin
    rw hS₂,
    ext x,
    simp only [exists_prop, set.mem_Union, set.mem_set_of_eq],
    split,
    { simp only [and_imp, exists_imp_distrib],
      rintro X hX hx,
      refine ⟨X, ⟨X, hX, set.subset.refl _⟩, hx⟩ },
    { simp only [and_imp, exists_imp_distrib],
      rintro X Y YS XY hx,
      refine ⟨Y, YS, convex_hull_mono XY hx⟩ }
  end,
  down_closed :=
  begin
    rintro X ⟨Y, YS, XY⟩ Z ZX,
    exact ⟨_, YS, set.subset.trans ZX XY⟩,
  end,
  disjoint :=
  begin
    rintro X Y ⟨Z, ZS, XZ⟩ ⟨W, WS, YW⟩,
    rintro x ⟨hx₁, hx₂⟩,
    rw ←finset.coe_inter,
    have : x ∈ convex_hull (Z ∩ W : set E),
      apply disjoint _ _ ZS WS ⟨convex_hull_mono XZ hx₁, convex_hull_mono YW hx₂⟩,
    rw ←finset.coe_inter at this,
    have := disjoint_convex_hulls (hS₁ _ ZS) XZ (finset.inter_subset_left Z W) ⟨hx₁, this⟩,
    rw ←finset.coe_inter at this,
    rw ←finset.inter_assoc at this,
    have := disjoint_convex_hulls (hS₁ _ WS) (finset.inter_subset_right (X ∩ Z) W) YW ⟨this, hx₂⟩,
    rw ←finset.coe_inter at this,
    convert this using 3,
    ext x,
    simp only [finset.inter_assoc, and.congr_right_iff, finset.mem_inter],
    intro hx₁,
    rw ← and_assoc,
    apply iff.symm,
    apply and_iff_right_of_imp,
    intro hx₂,
    refine ⟨XZ hx₁, YW hx₂⟩,
  end }

def std_basis (n : ℕ) : fin n → fin n → ℝ :=
λ i, linear_map.std_basis ℝ (λ i, ℝ) i 1

def basis_with_zero (n : ℕ) : fin (n+1) → fin n → ℝ :=
begin
  refine fin.cases _ _,
  apply (0 : fin n → ℝ),
  apply std_basis n,
end

lemma basis_with_zero_zero {n : ℕ} : basis_with_zero n 0 = 0 :=
by rw [basis_with_zero, fin.cases_zero]

lemma basis_with_zero_succ {n : ℕ} (j : fin n) : basis_with_zero n j.succ = std_basis n j :=
by rw [basis_with_zero, fin.cases_succ]

lemma linear_indep {n : ℕ} : linear_independent ℝ (std_basis n) :=
(pi.is_basis_fun ℝ (fin n)).1

lemma affine_indep {n : ℕ} : affine_independent ℝ (basis_with_zero n) :=
begin
  rw affine_independent_iff_linear_independent_vsub ℝ _ (0 : fin n.succ),
  simp only [basis_with_zero_zero],
  simp only [vsub_eq_sub, sub_zero],
  let g : {x : fin n.succ // x ≠ 0} → fin n := λ (j : {x : fin n.succ // x ≠ 0}), fin.pred j.1 j.2,
  have : std_basis n ∘ g = λ i, basis_with_zero n i,
  { ext j,
    dsimp,
    rw ← basis_with_zero_succ,
    simp },
  rw ← this,
  apply linear_independent.comp linear_indep g _,
  rintro i j hi,
  ext1,
  exact fin.pred_inj.1 hi,
end

def trivial {m : ℕ} : triangulation (std_simplex (fin (m+1))) :=
of_facets
  (singleton (finset.univ.image (std_basis (m+1))))
  (begin
    rintro X hX,
    simp only [set.mem_singleton_iff] at hX,
    subst hX,
    rw fintype.coe_image_univ,
    apply affine_independent_set_of_affine_independent,
    convert affine_independent_embedding_of_affine_independent (fin.succ_embedding _).to_embedding affine_indep,
    ext j x,
    simp only [function.comp_app, fin.coe_succ_embedding, rel_embedding.coe_fn_to_embedding, basis_with_zero_succ, std_basis],
  end)
  (begin
    rw [set.bUnion_singleton, fintype.coe_image_univ],
    rw ← convex_hull_basis_eq_std_simplex,
    rw std_basis,
    congr' 2,
    ext i j,
    rw linear_map.std_basis_apply,
    rw function.update,
    simp [eq_comm],
    convert rfl,
  end)
  (begin
    simp_rintro X Y hX hY,
    substs X Y,
    simp,
    exact set.subset.refl _,
  end)

variables {S : triangulation s}
def triangulation.finite (S : triangulation s) : Prop := S.faces.finite

noncomputable def triangulation.faces_finset (S : triangulation s) (hS : S.finite) :
  finset (finset E) :=
hS.to_finset

@[simp]
lemma mem_faces_finset (hS : S.finite) (X : finset E) :
  X ∈ S.faces_finset hS ↔ X ∈ S.faces :=
set.finite.mem_to_finset

def triangulation.points (S : triangulation s) : set E :=
⋃ k ∈ S.faces, (k : set E)

lemma convex_hull_face_subset (X) (hX : X ∈ S.faces) : convex_hull ↑X ⊆ s :=
begin
  rintro x hx,
  rw S.covering,
  apply set.mem_bUnion hX hx,
end

lemma face_subset {X} (hX : X ∈ S.faces) : ↑X ⊆ s :=
begin
  rintro x hx,
  rw S.covering,
  apply set.mem_bUnion hX,
  apply subset_convex_hull,
  apply hx
end

lemma points_subset : S.points ⊆ s :=
begin
  rintro x hx,
  rw S.covering,
  rw triangulation.points at hx,
  rw set.mem_bUnion_iff at hx,
  rcases hx with ⟨X, hX, hx⟩,
  exact set.mem_bUnion hX (subset_convex_hull X hx)
end

def is_sperner_colouring {s : set (fin (m+1) → ℝ)} (S : triangulation s)
  (f : (fin (m+1) → ℝ) → fin (m+1)) : Prop :=
∀ (X : fin (m+1) → ℝ) i, X ∈ S.points → X i = 0 → f X ≠ i

def panchromatic {n m : ℕ} (f : (fin n → ℝ) → fin m) (X : finset (fin n → ℝ)) :=
  X.image f = finset.univ

lemma panchromatic_iff (f : E → fin m) (X : finset E) :
  panchromatic f X ↔ (X.image f).card = m :=
begin
  rw panchromatic,
  split,
  { intro h,
    simp [h] },
  { intro h,
    refine finset.eq_of_subset_of_card_le (finset.image f X).subset_univ _,
    simp [h] }
end

def edge_of_std_simplex (m) : set (fin (m+1) → ℝ) :=
std_simplex (fin (m+1)) ∩ {x | x 0 = 0}

lemma convex_hull_ne_zero_points (X : set (fin (m+1) → ℝ)) (x : fin (m+1) → ℝ)
  (hX : ∀ (y : fin (m+1) → ℝ), y ∈ X → 0 ≤ y 0)
  (hx : x 0 = 0)
  (hXx : x ∈ convex_hull X) :
x ∈ convex_hull {y : fin (m+1) → ℝ | y ∈ X ∧ y 0 = 0} :=
begin
  rw convex_hull_eq.{37} at hXx,
  rcases hXx with ⟨ι, t, w, z, hw₀, hw₁, hz, x_eq⟩,
  have x_zero : t.center_mass w z 0 = 0,
  { rw [x_eq, hx] },
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at x_zero,
  dsimp only at x_zero,
  rw finset.sum_apply 0 t (λ i, w i • z i) at x_zero,
  dsimp at x_zero,
  have : ∀ (x : ι), x ∈ t → 0 ≤ w x * z x 0,
  { rintro y hy,
    exact mul_nonneg (hw₀ y hy) (hX (z y) (hz y hy)) },
  rw finset.sum_eq_zero_iff_of_nonneg this at x_zero,
  dsimp only at x_zero,
  rw convex_hull_eq.{37},
  refine ⟨ι, t.filter (λ i, w i ≠ 0), w, z, _, _, _, _⟩,
  { simp_rintro i hi only [finset.mem_filter],
    apply hw₀ _ hi.1 },
  { rw ←hw₁,
    exact finset.sum_filter_ne_zero },
  { simp_rintro i hi only [finset.mem_filter, set.mem_set_of_eq],
    refine ⟨hz i hi.1, _⟩,
    have := x_zero i hi.1,
    simp only [mul_eq_zero] at this,
    apply or.resolve_left this hi.2 },
  rw ← x_eq,
  exact finset.center_mass_filter_ne_zero z,
end

def lower_triangulation (S : triangulation (std_simplex (fin (m+1)))) :
  triangulation (edge_of_std_simplex m) :=
{ faces := {X ∈ S.faces | ∀ (x : fin (m+1) → ℝ), x ∈ X → x 0 = 0 },
  indep :=
  begin
    rintro X hX,
    simp only [set.mem_sep_eq] at hX,
    apply S.indep _ hX.1,
  end,
  down_closed :=
  begin
    rintro X hX Y YX,
    simp only [set.mem_sep_eq] at hX ⊢,
    refine ⟨S.down_closed X hX.left Y YX, _⟩,
    rintro x hx,
    apply hX.2,
    apply YX,
    apply hx
  end,
  covering :=
  begin
    rw edge_of_std_simplex,
    ext x,
    split,
    { rintro ⟨hx₁, hx₂⟩,
      rw S.covering at hx₁,
      rw set.mem_bUnion_iff at hx₁,
      rcases hx₁ with ⟨X, hX, hx⟩,
      have := convex_hull_ne_zero_points _ x _ hx₂ hx,
      { rw set.mem_bUnion_iff,
        refine ⟨X.filter (λ p, p 0 = 0), _, _⟩,
        { simp only [and_imp, imp_self, set.mem_sep_eq, and_true, finset.mem_filter,
            forall_true_iff],
          apply S.down_closed _ hX,
          apply finset.filter_subset },
        { convert this,
          simp only [finset.mem_coe, finset.coe_filter],
          ext x,
          simp } },
      rintro y hy,
      have : y ∈ std_simplex (fin (m+1)),
      { apply face_subset hX hy },
      rw std_simplex_eq_inter at this,
      simp only [set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] at this,
      apply this.1 },
    { rw set.mem_bUnion_iff,
      rintro ⟨X, hX₁, hX₂⟩,
      simp only [set.mem_sep_eq] at hX₁,
      refine ⟨convex_hull_face_subset X hX₁.1 hX₂, _⟩,
      have : convex_hull ↑X ⊆ {x : fin (m+1) → ℝ | x 0 = 0},
      { apply convex_hull_min,
        { rintro x hx,
          exact hX₁.2 x hx },
        rintro x₁ x₂ hx₁ hx₂ a b ha hb q,
        simp only [set.mem_set_of_eq] at hx₁ hx₂ ⊢,
        simp [hx₁, hx₂] },
      apply this,
      apply hX₂ }
  end,
  disjoint :=
  begin
    rintro X Y hX hY,
    apply S.disjoint _ _ hX.1 hY.1,
  end }

lemma std_simplex_one : std_simplex (fin 1) = { ![(1 : ℝ)]} :=
begin
  ext x,
  simp [std_simplex_eq_inter],
  split,
  { rintro ⟨-, hx⟩,
    ext i,
    have : i = 0 := subsingleton.elim _ _,
    rw this,
    apply hx },
  { rintro rfl,
    refine ⟨λ _, _, rfl⟩,
    simp only [matrix.cons_val_fin_one],
    apply zero_le_one }
end

lemma subset_singleton_iff {ι : Type*} (x : ι) (X : finset ι) :
  X ⊆ {x} ↔ X = ∅ ∨ X = {x} :=
begin
  split,
  { rcases X.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩),
    { intro,
      left,
      refl },
    { intro hx,
      right,
      apply finset.subset.antisymm hx,
      rw finset.singleton_subset_iff,
      have := hx hy,
      simp only [finset.mem_singleton] at this,
      rwa ← this } },
  { rintro (rfl | rfl),
    { apply finset.empty_subset },
    { refl } }
end

lemma convex_hull_empty : convex_hull (∅ : set E) = ∅ :=
convex_empty.convex_hull_eq

lemma strong_sperner_zero_aux (S : triangulation (std_simplex (fin 1))) :
  S.faces = {∅, { ![1]}} :=
begin
  have X_subs : ∀ X ∈ S.faces, X ⊆ { ![(1:ℝ)]},
  { rintro X hX,
    have := face_subset hX,
    rw std_simplex_one at this,
    rintro x hx,
    simpa using this hx },
  have : ∃ X ∈ S.faces, X = { ![(1:ℝ)]},
  { have std_eq := S.covering,
    have one_mem : ![(1:ℝ)] ∈ std_simplex (fin 1),
    { rw std_simplex_one,
      simp },
    rw [std_eq, set.mem_bUnion_iff] at one_mem,
    rcases one_mem with ⟨X, hX₁, hX₂⟩,
    refine ⟨X, hX₁, _⟩,
    have := X_subs X hX₁,
    rw subset_singleton_iff at this,
    rcases this with (rfl | rfl),
    { simp only [finset.coe_empty] at hX₂,
      rw convex_hull_empty at hX₂,
      apply hX₂.elim },
    { refl } },
  ext X,
  simp only [set.mem_insert_iff, set.mem_singleton_iff, ←subset_singleton_iff],
  split,
  { intro hX,
    apply X_subs _ hX },
  { intro hX,
    rcases this with ⟨Y, hY₁, rfl⟩,
    exact S.down_closed _ hY₁ X hX },
end

theorem strong_sperner_zero (S : triangulation (std_simplex (fin 1))) (hS : S.finite)
  (f : (fin 1 → ℝ) → fin 1) :
  odd ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  have : (S.faces_finset hS).filter (panchromatic f) = {{ ![(1:ℝ)]}},
  { ext X,
    simp only [mem_faces_finset, finset.mem_singleton, finset.mem_filter, strong_sperner_zero_aux],
    simp only [set.mem_insert_iff, set.mem_singleton_iff],
    split,
    { rintro ⟨(rfl | rfl), h⟩,
      { change _ = _ at h,
        rw [univ_unique, fin.default_eq_zero, finset.image_empty, eq_comm] at h,
        simp only [finset.singleton_ne_empty] at h,
        cases h },
      { refl } },
    rintro rfl,
    refine ⟨or.inr rfl, _⟩,
    change _ = _,
    simp only [fin.default_eq_zero, finset.image_singleton, univ_unique],
    rw finset.singleton_inj,
    apply subsingleton.elim },
  rw this,
  simp,
end

-- lemma affine_independent_image {n m : ℕ} {ι : Type*} (f : (fin n → ℝ) →ₗ[ℝ] (fin m → ℝ))
--   (hf : function.injective f)
--   (p : ι → fin n → ℝ)
--   (hp : affine_independent ℝ p) :
--   affine_independent ℝ (f ∘ p) :=
-- begin
--   rw affine_independent_def,
--   rintro s w hw hs i hi,
--   rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin m → ℝ) at hs,
--   rw finset.weighted_vsub_of_point_apply at hs,
--   simp only [vsub_eq_sub, function.comp_app, sub_zero] at hs,
--   have : s.weighted_vsub p w = (0:fin n → ℝ),
--   { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin n → ℝ),
--     rw finset.weighted_vsub_of_point_apply,
--     simp only [vsub_eq_sub, sub_zero],
--     apply hf,
--     simpa },
--   apply hp s w hw this _ hi,
-- end

lemma cons_inj {n : ℕ} (x y : fin (n+1) → ℝ) (h0 : x 0 = y 0)
  (h1 : matrix.vec_tail x = matrix.vec_tail y) :
  x = y :=
begin
  ext i,
  refine fin.cases h0 _ i,
  rw function.funext_iff at h1,
  apply h1,
end

lemma affine_independent_proj {n : ℕ} {ι : Type*}
  {p : ι → fin (n+1) → ℝ}
  (hp₁ : ∀ i, p i 0 = 0)
  (hp₂ : affine_independent ℝ p) :
  affine_independent ℝ (matrix.vec_tail ∘ p) :=
begin
  rw affine_independent_def,
  rintro s w hw hs i hi,
  rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin n → ℝ) at hs,
  rw finset.weighted_vsub_of_point_apply at hs,
  simp only [vsub_eq_sub, function.comp_app, sub_zero] at hs,
  have : s.weighted_vsub p w = (0:fin (n+1) → ℝ),
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin (n+1) → ℝ),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    ext j,
    simp only [pi.zero_apply],
    rw finset.sum_apply _ s (λ i, w i • p i),
    refine fin.cases _ _ j,
    { simp [hp₁] },
    intro j,
    dsimp,
    rw function.funext_iff at hs,
    specialize hs j,
    simp only [pi.zero_apply] at hs,
    rw finset.sum_apply _ s (λ i, w i • matrix.vec_tail (p i)) at hs,
    dsimp [matrix.vec_tail] at hs,
    apply hs },
  exact hp₂ s w hw this i hi,
end

lemma thingy2 {α : Type*} [add_comm_monoid α] {n : ℕ} (k : fin n → α) :
  ∑ (i : fin n), k i = ∑ i in finset.fin_range n, k i :=
begin
  apply finset.sum_congr _ (λ x _, rfl),
  ext x,
  simp only [finset.mem_univ, finset.mem_fin_range],
end

example {α : Type*} {p : α → Prop} : subtype p ↪ α := function.embedding.subtype p

lemma thingy3 {α : Type*} [add_comm_monoid α] {n : ℕ} (k : fin n → α) :
  (∑ (i : fin (n+1)), fin.cases (0:α) k i : α) = ∑ i, k i :=
begin
  have : (fin.cases (0:α) k (0 : fin (n+1)) : α) = (0 : α),
    rw fin.cases_zero,
  rw ←finset.sum_erase finset.univ this,
  symmetry,
  apply finset.sum_bij _ _ _ _ _,
  { rintro a _,
    apply a.succ },
  { rintro a ha,
    simp only [and_true, finset.mem_univ, finset.mem_erase],
    apply fin.succ_ne_zero },
  { rintro a ha,
    symmetry,
    apply fin.cases_succ },
  { rintro a₁ a₂ _ _ h,
    apply fin.succ_injective,
    apply h },
  { rintro b hb,
    simp only [and_true, finset.mem_univ, finset.mem_erase] at hb,
    refine ⟨b.pred hb, by simp, _⟩,
    simp }
end

lemma vec_tail_smul {m : ℕ} (c : ℝ) (x : fin m.succ → ℝ) :
  matrix.vec_tail (c • x) = c • matrix.vec_tail x :=
begin
  ext i,
  simp [matrix.vec_tail],
end

lemma is_linear_map_matrix_vec_tail {n : ℕ} :
  is_linear_map ℝ (matrix.vec_tail : (fin n.succ → ℝ) → (fin n → ℝ)) :=
{ map_add := by simp,
  map_smul := λ c x,
  begin
    ext i,
    simp [matrix.vec_tail],
  end }

lemma vec_tail_mem_simplex_iff {n : ℕ} (y : fin n → ℝ) :
  matrix.vec_cons 0 y ∈ edge_of_std_simplex n ↔ y ∈ std_simplex (fin n) :=
begin
  rw [edge_of_std_simplex, set.mem_inter_eq, set.mem_set_of_eq, matrix.cons_val_zero,
    eq_self_iff_true, and_true, std_simplex, std_simplex, set.mem_set_of_eq, set.mem_set_of_eq,
    fin.forall_fin_succ, matrix.cons_val_zero],
  simp only [matrix.cons_val_succ],
  rw [matrix.vec_cons, fin.cons, thingy3],
  tauto,
end

-- def my_proj : (fin (n+1) → ℝ)
def flatten_triangulation (S : triangulation (edge_of_std_simplex m)) :
  triangulation (std_simplex (fin m)) :=
{ faces := finset.image matrix.vec_tail '' S.faces,
  indep :=
  begin
    rintro X hX,
    simp only [set.mem_image] at hX,
    rcases hX with ⟨X, hX, rfl⟩,
    let f : ((finset.image matrix.vec_tail X : set (fin m → ℝ))) → (X : set (fin (m+1) → ℝ)),
    { intro t,
      refine ⟨matrix.vec_cons 0 t.1, _⟩,
      rcases t with ⟨t, ht⟩,
      simp only [set.mem_image, finset.mem_coe, finset.coe_image] at ht,
      rcases ht with ⟨x, hx, rfl⟩,
      have : matrix.vec_head x = 0 := (face_subset hX hx).2,
      rw ← this,
      simpa },
    have hf : function.injective f,
    { rintro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h,
      rw subtype.ext_iff at h,
      change matrix.vec_cons _ x₁ = matrix.vec_cons _ x₂ at h,
      apply subtype.ext,
      apply_fun matrix.vec_tail at h,
      simpa using h },
    have := affine_independent_proj _ (S.indep X hX),
    { convert affine_independent_embedding_of_affine_independent ⟨f, hf⟩ this,
      ext p,
      dsimp,
      simp },
    rintro ⟨i, hi⟩,
    apply (face_subset hX hi).2,
  end,
  down_closed :=
  begin
    rintro _ ⟨X, hX, rfl⟩ Y YX,
    refine ⟨Y.image (matrix.vec_cons 0), _, _⟩,
    { apply S.down_closed _ hX,
      rw finset.image_subset_iff,
      rintro y hY,
      have := YX hY,
      simp only [exists_prop, finset.mem_image] at this,
      rcases this with ⟨x, hx, rfl⟩,
      have : matrix.vec_head x = 0 := (face_subset hX hx).2,
      rw ←this,
      simpa },
    rw finset.image_image,
    convert finset.image_id,
    { ext x,
      dsimp,
      simp },
    { exact classical.dec_eq (fin m → ℝ) },
  end,
  covering :=
  begin
    ext i,
    rw set.mem_bUnion_iff,
    simp only [exists_prop, set.mem_image, exists_exists_and_eq_and, finset.coe_image],
    split,
    { intro hi,
      have : matrix.vec_cons 0 i ∈ edge_of_std_simplex m,
      { rwa vec_tail_mem_simplex_iff },
      rw [S.covering, set.mem_bUnion_iff] at this,
      rcases this with ⟨x, hx₁, hx₂⟩,
      refine ⟨x, hx₁, _⟩,
      rw ←is_linear_map.image_convex_hull,
      refine ⟨_, hx₂, _⟩,
      simp only [matrix.tail_cons],
      apply is_linear_map_matrix_vec_tail },
    { rintro ⟨X, hX₁, hX₂⟩,
      rw ← is_linear_map.image_convex_hull at hX₂,
      { rcases hX₂ with ⟨y, hy, rfl⟩,
        rcases convex_hull_face_subset _ hX₁ hy with ⟨hy₁, hy₂⟩,
        rw ← vec_tail_mem_simplex_iff,
        have : matrix.vec_head y = 0 := hy₂,
        rw ← this,
        simp only [matrix.cons_head_tail],
        apply convex_hull_face_subset _ hX₁ hy },
      apply is_linear_map_matrix_vec_tail,
    }
    -- },
    -- have : matrix.vec_cons 0 i ∈ std_simplex (fin (m+1)),
    -- have := S.covering,
  end,
  disjoint :=
  begin
    rintro _ _ ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩,
    simp only [finset.coe_image],
    rw ← is_linear_map.image_convex_hull,
    rw ← is_linear_map.image_convex_hull,

    rw set.image_inter_on,
    refine set.subset.trans (set.image_subset matrix.vec_tail (S.disjoint _ _ hX hY)) _,
    rw is_linear_map.image_convex_hull,
    apply convex_hull_mono,
    apply set.image_inter_subset,
    apply is_linear_map_matrix_vec_tail,
    { rintro x hx y hy h,
      rw ← matrix.cons_head_tail x,
      rw ← matrix.cons_head_tail y,
      rw h,
      rw (show matrix.vec_head x = 0, from (convex_hull_face_subset _ hY hx).2),
      rw (show matrix.vec_head y = 0, from (convex_hull_face_subset _ hX hy).2) },
    apply is_linear_map_matrix_vec_tail,
    apply is_linear_map_matrix_vec_tail,
  end }

def induct_down (S : triangulation (std_simplex (fin (m+1)))) :
  triangulation (std_simplex (fin m)) :=
flatten_triangulation (lower_triangulation S)

example {α : Type*} {s : set α} (p : α → Prop) (hs : s.finite) :
  {x ∈ s | p x}.finite :=
set.finite.subset hs (s.sep_subset p)

lemma induct_down_finite (S : triangulation (std_simplex (fin (m+1)))) (hS : S.finite) :
  (induct_down S).finite :=
begin
  rw triangulation.finite,
  rw induct_down,
  rw flatten_triangulation,
  apply set.finite.image,
  rw lower_triangulation,
  apply set.finite.subset hS (S.faces.sep_subset _)
end

lemma test {n m : ℕ} (h : n.pred ≤ m) : n ≤ m + 1 :=
begin
  exact nat.pred_le_iff.mp h,
end

lemma mwe {α : Type*} {n : ℕ} (X : set (finset α)) (bound : ∀ y ∈ X, finset.card y ≤ n) :
  ∀ y ∈ X, ∃ x ∈ X, y ⊆ x ∧ ∀ z ∈ X, x ⊆ z → x = z :=
begin
  rintro y hy,
  classical,
  rcases ((finset.range (n+1)).filter $ λ i, ∃ x ∈ X, y ⊆ x ∧ finset.card x = i).exists_maximal
    ⟨y.card, finset.mem_filter.2 ⟨finset.mem_range_succ_iff.2 $ bound y hy,
      y, hy, finset.subset.refl _, rfl⟩⟩ with ⟨i, hi1, hi2⟩,
  rw [finset.mem_filter, finset.mem_range_succ_iff] at hi1,
  rcases hi1 with ⟨hin, x, hx, hyx, hxi⟩,
  refine ⟨x, hx, hyx, λ z hz hxz, finset.eq_of_subset_of_card_le hxz _⟩,
  rw [hxi, ← not_lt],
  refine hi2 _ _,
  rw [finset.mem_filter, finset.mem_range_succ_iff],
  refine ⟨bound z hz, z, hz, finset.subset.trans hyx hxz, rfl⟩
end

lemma contained_in_facet (S : triangulation s) {X} (hX : X ∈ S.faces) :
  ∃ Y ∈ S.facets, X ⊆ Y :=
begin
  have : ∀ y ∈ S.faces, finset.card y ≤ m+1,
  { rintro y hy,
    apply size_bound (S.indep _ hy) },
  rcases mwe S.faces this X hX with ⟨Y, _, _, h₂⟩,
  refine ⟨Y, ⟨‹Y ∈ S.faces›, h₂⟩, ‹X ⊆ Y›⟩,
end

def is_homogeneous {m : ℕ} {s : set (fin m → ℝ)} (n : ℕ) (S : triangulation s) : Prop :=
∀ X ∈ S.facets, finset.card X = n
-- ∀ X ∈ S.faces, ∃ Y ∈ S.faces, X ⊆ Y ∧ finset.card Y = n

lemma is_homogeneous_induct_down (S : triangulation (std_simplex (fin (m+1))))
  (hS : is_homogeneous (m+1) S) :
  is_homogeneous m (induct_down S) :=
begin
  rintro X hX,
  simp only [induct_down, triangulation.facets, flatten_triangulation, lower_triangulation,
    and_imp, set.mem_sep_eq, set.mem_image, exists_imp_distrib] at hX,
  rcases hX with ⟨⟨X, ⟨hX₂, hX₄⟩, rfl⟩, hX₃⟩,
  have hX₁ : ∀ (Y ∈ S.faces), (∀ (i : fin (m+1) → ℝ), i ∈ Y → i 0 = 0) →
    finset.image matrix.vec_tail X ⊆ finset.image matrix.vec_tail Y →
    finset.image matrix.vec_tail X = finset.image matrix.vec_tail Y,
  { rintro Y hY₁ hY₂ hY₃,
    apply hX₃ _ _ hY₁ hY₂ rfl hY₃ },
  clear hX₃, -- just a less convenient form of hX₁
  have : ∀ (x : fin (m+1) → ℝ), x ∉ X → x 0 = 0 → insert x X ∉ S.faces,
  { rintro x hx₁ hx₂ t,
    have := hX₁ _ t (by simpa [hx₂] using hX₄) (finset.image_subset_image _),


  },
  -- have := set.image_subset,
  -- simp only [induct_down, flatten_triangulation, lower_triangulation, set.mem_image,
  --   set.mem_sep_eq] at hX,

  -- rcases hX with ⟨X, ⟨hX₁, hX₂⟩, rfl⟩,
  -- rcases hS X hX₁ with ⟨Y, hY₁, hY₂, hY₃⟩,
  -- -- refine ⟨sorry, _, _⟩,
  -- simp only [exists_prop, induct_down, flatten_triangulation, lower_triangulation, set.mem_sep_eq,
  --   set.mem_image, exists_exists_and_eq_and],

  -- -- simp only [induct_down],

end

lemma subset_iff_eq_or_ssubset {α : Type*} {s t : finset α} :
  s ⊆ t ↔ s = t ∨ s ⊂ t :=
begin
  split,
  { intro h,
    rw finset.ssubset_iff_of_subset h,
    apply or.imp _ _ (t \ s).eq_empty_or_nonempty,
    { intro q,
      rw finset.sdiff_eq_empty_iff_subset at q,
      apply finset.subset.antisymm h q },
    { rintro ⟨x, hx⟩,
      simp only [finset.mem_sdiff] at hx,
      exact ⟨x, hx.1, hx.2⟩ } },
  { rintro (rfl | ss),
    { apply finset.subset.refl },
    { apply ss.1 } }
end

noncomputable def good_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  (f : (fin (m + 1) → ℝ) → fin (m + 1)) :
  finset (finset (fin (m+1) → ℝ) × finset (fin (m+1) → ℝ)) :=
((S.faces_finset hS).product (S.faces_finset hS)).filter
      (λ (XY : finset _ × finset _),
          XY.2.card = m ∧ XY.1.card = m+1 ∧ XY.2.image f = finset.univ.erase 0 ∧ XY.2 ⊆ XY.1)

@[simp]
lemma mem_good_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  {f} (X Y : finset _) :
  (X,Y) ∈ good_pairs hS f ↔
      X ∈ S.faces
    ∧ Y ∈ S.faces
    ∧ Y.card = m
    ∧ X.card = m+1
    ∧ Y.image f = finset.univ.erase 0
    ∧ Y ⊆ X :=
begin
  simp [good_pairs, and_assoc],
end

noncomputable def panchromatic_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(good_pairs hS f).filter (λ (XY : _ × _), panchromatic f XY.1)

noncomputable def almost_panchromatic_pairs {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(good_pairs hS f).filter (λ (XY : _ × _), XY.1.image f = finset.univ.erase 0)

noncomputable def almost_panchromatic_simplices {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(S.faces_finset hS).filter (λ (X : finset _), X.card = m+1 ∧ X.image f = finset.univ.erase 0)

lemma almost_panchromatic_pairs_card_eq_twice {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :
  (almost_panchromatic_pairs hS f).card = (almost_panchromatic_simplices hS f).card * 2 :=
begin
  have H : ∀ x ∈ almost_panchromatic_pairs hS f, prod.fst x ∈ almost_panchromatic_simplices hS f,
  { rintro ⟨X, Y⟩ h,
    simp only [almost_panchromatic_pairs, mem_good_pairs, finset.mem_filter] at h,
    simp only [almost_panchromatic_simplices, mem_faces_finset, finset.mem_filter],
    tauto },
  rw finset.card_eq_sum_card_fiberwise H,
  apply finset.sum_const_nat,
  rintro X hX,
  simp only [almost_panchromatic_simplices, mem_faces_finset, finset.mem_filter] at hX,
  rcases hX with ⟨hX₁, hX₂, hX₃⟩,
  dsimp,
  suffices : ((almost_panchromatic_pairs hS f).filter (λ (x : _ × _), x.fst = X)).card =
    (X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y)).card,
  { rw this,
    apply non_inj_card_two f,
    rw hX₂,
    rw hX₃,
    simp [finset.card_erase_of_mem] },
  apply (finset.card_congr (λ x hx, (X, X.erase x)) _ _ _).symm,
  { rintro x hx,
    dsimp,
    simp only [exists_prop, finset.mem_filter] at hx,
    simp only [almost_panchromatic_pairs, and_true, eq_self_iff_true, mem_good_pairs,
      finset.mem_filter, hX₃, true_and, hX₂, hX₁, finset.card_erase_of_mem, hx.1, nat.pred_succ,
      finset.erase_subset],
    rw ← hX₃,
    refine ⟨S.down_closed _ hX₁ _ (finset.erase_subset _ _), _⟩,
    conv_rhs {rw ←finset.insert_erase hx.1},
    rw finset.image_insert,
    rw finset.insert_eq_of_mem,
    rw finset.mem_image,
    simp only [exists_prop, finset.mem_erase],
    simpa [and_assoc, and_comm (_ ∈ X), ←ne.def, ne_comm, eq_comm] using hx.2 },
  { rintro a b ha hb h,
    dsimp at h,
    injection h,
    apply erase_inj_on _ (finset.filter_subset _ _ ha) ‹X.erase a = X.erase b› },
  { rintro ⟨X', Y⟩ hX,
    dsimp [←ne.def],
    simp only [finset.mem_filter, almost_panchromatic_pairs, mem_good_pairs] at hX,
    rcases hX with ⟨⟨⟨_, _, _, _, _, _⟩, _⟩, rfl⟩,
    have : (X' \ Y).nonempty,
    { rw [←finset.card_pos, finset.card_sdiff ‹Y ⊆ X'›, ‹X'.card = m + 1›, ‹Y.card = m›],
      simp only [nat.zero_lt_one, nat.add_sub_cancel_left] },
    rcases this with ⟨z, hz⟩,
    simp only [finset.mem_sdiff] at hz,
    rcases hz,
    simp only [true_and, exists_prop, prod.mk.inj_iff, eq_self_iff_true, finset.mem_filter],
    refine ⟨z, ⟨‹_›, _⟩, _⟩,
    { have : f z ∈ Y.image f,
      { rw [‹Y.image f = _›, ←‹X'.image f = _›],
        apply finset.mem_image_of_mem f ‹z ∈ X'› },
      rcases finset.mem_image.1 this with ⟨y, hy₁, hy₂⟩,
      refine ⟨y, ‹Y ⊆ X'› ‹y ∈ Y›, (ne_of_mem_of_not_mem ‹y ∈ Y› ‹z ∉ Y›).symm, ‹f y = f z›.symm⟩ },
    { symmetry,
      apply finset.eq_of_subset_of_card_le,
      simp only [subset_erase_iff, ‹Y ⊆ X'›, ‹z ∉ Y›, not_false_iff, and_self],
      rw [finset.card_erase_of_mem ‹_ ∈ _›, ‹X'.card = _›, nat.pred_succ, ‹Y.card = m›] } }
end

lemma panchromatic_splits {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) {f : (fin (m+1) → ℝ) → (fin (m+1))} :
  panchromatic_pairs hS f ∪ almost_panchromatic_pairs hS f = good_pairs hS f :=
begin
  rw [panchromatic_pairs, almost_panchromatic_pairs, ←finset.filter_or, finset.filter_true_of_mem],
  rintro ⟨X,Y⟩ h,
  simp only [mem_good_pairs] at h,
  rcases h with ⟨hX₁, hY₁, hY₂, hX₂, hY₃, YX⟩,
  have : finset.univ.erase 0 ⊆ X.image f,
  { rw ← hY₃,
    apply finset.image_subset_image,
    apply YX },
  rw subset_iff_eq_or_ssubset at this,
  cases this,
  { right,
    apply this.symm },
  { left,
    apply finset.eq_of_subset_of_card_le,
    apply finset.subset_univ,
    simp only [finset.card_fin],
    rw nat.succ_le_iff,
    apply lt_of_le_of_lt _ (finset.card_lt_card this),
    rw finset.card_erase_of_mem (finset.mem_univ _),
    simp only [finset.card_fin, nat.pred_succ] }
end

lemma disjoint_split {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) {f : (fin (m+1) → ℝ) → (fin (m+1))} :
  disjoint (panchromatic_pairs hS f) (almost_panchromatic_pairs hS f) :=
begin
  rw finset.disjoint_left,
  simp only [panchromatic_pairs, almost_panchromatic_pairs, and_imp, prod.forall, not_and,
    mem_good_pairs, finset.mem_filter],
  rintro X Y - - - - - - (h : _ = _) - - - - - - t,
  rw h at t,
  have : (0 : fin (m+1)) ∉ finset.univ,
  { intro q,
    rw t at q,
    rw finset.mem_erase at q,
    apply q.1 rfl },
  simpa using this
end

-- lemma image_subset_image_iff {α β : Type*}
--   [decidable_eq α] [decidable_eq β] (s t : finset α)
--   {f : α → β} : s.image f ⊆ t.image f → s ⊆ t :=
-- begin
--   rintro h x hx,
--   have : f x ∈ t.image f,
--   sorry,
--   simp at this,

--   -- refine ⟨_, finset.subset_image _⟩,

--   -- refine (iff.symm $ iff.intro (image_subset f) $ assume h, _),
--   -- rw [← preimage_image_eq s hf, ← preimage_image_eq t hf],
--   -- exact preimage_mono h
-- end

lemma subset_erase_iff {α : Type*} [decidable_eq α] (x : α) {s t : finset α} :
  s ⊆ t.erase x ↔ s ⊆ t ∧ x ∉ s :=
⟨λ h, ⟨finset.subset.trans h (finset.erase_subset x t), λ q, by simpa using h q⟩,
 λ ⟨h₁, h₂⟩ y hy, finset.mem_erase_of_ne_of_mem (ne_of_mem_of_not_mem hy h₂) (h₁ hy)⟩

-- lemma sum_mul {α β : Type*} [add_comm_monoid β] {s : finset α} (b : β) (f : α → β) :
--   ∑ x in s, b * f x = _ :=
-- begin
-- end

def plane : affine_subspace ℝ E :=
{ carrier := {X | ∑ i, X i = 1},
  smul_vsub_vadd_mem :=
  begin
    rintro c p₁ p₂ p₃ (hp₁ hp₂ hp₃ : _ = _),
    simp [finset.sum_add_distrib, ←finset.mul_sum, hp₁, hp₂, hp₃],
  end }

lemma obvious {m : ℕ} : ∑ (i : fin m), (0 : fin m → ℝ) i = 1 → false :=
begin
  simp,
end

lemma better_size_bound {X : finset E}
  (hX₁ : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hX₂ : ∀ x ∈ X, x ∈ std_simplex (fin m)) :
  X.card ≤ m :=
begin
  cases nat.eq_or_lt_of_le (size_bound hX₁),
  { have card_eq : fintype.card (X : set E) = finite_dimensional.findim ℝ (fin m → ℝ) + 1,
    { simp [h] },
    have : affine_span ℝ (X : set E) = ⊤,
    { convert affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one hX₁ card_eq,
      simp },
    have zero_mem : (0 : E) ∈ affine_span ℝ (X : set E),
    { rw this,
      apply affine_subspace.mem_top },
    have : (X : set E) ≤ (↑plane : set E),
    { rintro x hx,
      rw affine_subspace.mem_coe,
      apply (hX₂ _ hx).2 },
    rw ←((affine_subspace.gi ℝ (fin m → ℝ) (fin m → ℝ)).gc (X : set E) plane) at this,
    have q : _ = _ := this zero_mem,
    apply (obvious q).elim },
  rwa ← nat.lt_succ_iff,
end

lemma card_eq_of_panchromatic {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) {X} (hX : X ∈ S.faces)
  (hf : panchromatic f X) :
  X.card = m+1 :=
le_antisymm
  (better_size_bound (S.indep X hX) (λ x hx, face_subset hX hx))
  begin
    change _ = _ at hf,
    have : (X.image f).card ≤ X.card := finset.card_image_le,
    simpa [hf] using this,
  end

lemma erase_image_subset_image_erase {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)
  (s : finset α) (a : α) :
  (s.image f).erase (f a) ⊆ finset.image f (s.erase a) :=
begin
  intro b,
  simp only [and_imp, exists_prop, finset.mem_image, exists_imp_distrib, finset.mem_erase],
  rintro hb x hx rfl,
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩,
end

lemma panchromatic_pairs_card_eq_panchromatic_card {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :
  (panchromatic_pairs hS f).card = ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  apply finset.card_congr _ _ _ _,
  { rintro X hX,
    apply X.1 },
  { rintro ⟨X, Y⟩ hX,
    simp only [panchromatic_pairs, mem_good_pairs, finset.mem_filter] at hX,
    simp only [mem_faces_finset, finset.mem_filter],
    tauto },
  { rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ h₁ h₂ (rfl : X₁ = X₂),
    simp only [panchromatic_pairs, finset.mem_filter, mem_good_pairs, and_assoc] at h₁ h₂,
    rcases h₁ with ⟨X₁S, Y₁S, Y₁c, hX₁, hY₁, hY₁X, hX₂ : _ = _⟩,
    rcases h₂ with ⟨-, Y₂S, Y₂c, -, hY₂, hY₂X, -⟩,
    ext1,
    { refl },
    change Y₁ = Y₂,
    have : ∃ x ∈ X₁, f x = 0,
    { suffices : (0 : fin (m+1)) ∈ X₁.image f,
      { simpa using this },
      rw hX₂,
      simp },
    rcases this with ⟨x, hx₁, hx₂⟩,
    have : x ∉ Y₁,
    { intro q,
      simpa [‹f x = 0›, hY₁, fin.succ_ne_zero] using finset.mem_image_of_mem f q },
    have : Y₁ ⊆ X₁.erase x,
    { rw subset_erase_iff,
      exact ⟨‹Y₁ ⊆ X₁›, ‹x ∉ Y₁›⟩ },
    have : Y₁ = X₁.erase x,
    { apply finset.eq_of_subset_of_card_le ‹Y₁ ⊆ X₁.erase x›,
      simp [finset.card_erase_of_mem ‹x ∈ X₁›, ‹X₁.card = m+1›, ‹Y₁.card = m›] },
    have : x ∉ Y₂,
    { intro q,
      simpa [‹f x = 0›, hY₂, fin.succ_ne_zero] using finset.mem_image_of_mem f q },
    have : Y₂ ⊆ X₁.erase x,
    { rw subset_erase_iff,
      exact ⟨‹Y₂ ⊆ X₁›, ‹x ∉ Y₂›⟩ },
    have : Y₂ = X₁.erase x,
    { apply finset.eq_of_subset_of_card_le ‹Y₂ ⊆ X₁.erase x›,
      simp [finset.card_erase_of_mem ‹x ∈ X₁›, ‹X₁.card = m+1›, ‹Y₂.card = m›] },
    rw [‹Y₁ = X₁.erase x›, ‹Y₂ = X₁.erase x›] },
  { simp_rintro X hX only [finset.mem_filter, mem_faces_finset],
    have : ∃ x ∈ X, f x = 0,
    { suffices : (0 : fin (m+1)) ∈ X.image f,
      { simpa using this },
      rw (show _ = _, from hX.2),
      simp },
    rcases this with ⟨x, hx₁, hx₂⟩,
    refine ⟨⟨X, X.erase x⟩, _, rfl⟩,
    have Xc : finset.card X = m+1 := card_eq_of_panchromatic hS f hX.1 hX.2,
    simp only [panchromatic_pairs, hX.1, hX.2, finset.erase_subset, and_true, true_and, Xc,
      finset.card_erase_of_mem hx₁, eq_self_iff_true, mem_good_pairs, finset.mem_filter,
      nat.pred_succ],
    refine ⟨S.down_closed _ hX.1 _ (finset.erase_subset _ _), _⟩,
    symmetry,
    apply finset.eq_of_subset_of_card_le,
    { rw ←(show finset.image f X = finset.univ, from hX.2),
      rw ←hx₂,
      apply erase_image_subset_image_erase f X x },
    rw finset.card_erase_of_mem (finset.mem_univ _),
    simp only [finset.card_fin, nat.pred_succ],
    apply le_trans finset.card_image_le,
    rw finset.card_erase_of_mem hx₁,
    rw Xc,
    simp, }
end

theorem strong_sperner (S : triangulation (std_simplex (fin (m+1)))) (hS : S.finite)
  {f} (hf : is_sperner_colouring S f) (hS₂ : is_homogeneous (m+1) S):
  odd ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  tactic.unfreeze_local_instances,
  induction m with n ih generalizing f,
  { apply strong_sperner_zero _ },
  let f' : (fin (n + 1) → ℝ) → fin (n + 1),
  { intro x,
    apply fin.pred_above 0 (f (matrix.vec_cons 0 x)) },
  have hf' : is_sperner_colouring (induct_down S) f',
  { rintro x i hx hi,
    simp only [induct_down, flatten_triangulation, lower_triangulation, triangulation.points,
      set.mem_bUnion_iff, exists_prop, set.mem_sep_eq, finset.mem_image, set.mem_image,
      finset.mem_coe, finset.mem_image, exists_exists_and_eq_and] at hx,
    rcases hx with ⟨X, ⟨hX₁, hX₂⟩, y, hy, rfl⟩,
    rw matrix.vec_tail at hi,
    dsimp at hi,
    have : y ∈ S.points,
    { apply set.mem_bUnion, apply hX₁, apply hy },
    have : f y ≠ i.succ,
    { apply hf _ _ _ hi,
      apply this },
    change fin.pred_above _ _ ≠ _,
    have : y 0 = 0,
    { apply hX₂,
      apply hy },
    have : matrix.vec_cons 0 (matrix.vec_tail y) = y,
    { rw ← this,
      exact matrix.cons_head_tail y },
    rw this,
    have := ‹is_sperner_colouring S f› _ _ ‹y ∈ S.points› ‹y 0 = 0›,
    rw fin.pred_above_zero this,
    intro q,
    apply ‹f y ≠ i.succ›,
    rw ← q,
    simp },
  specialize ih (induct_down S) (induct_down_finite _ hS) _ hf',





  -- want that the number `x` of (n+2)-sets which are coloured by all n+2 colours is odd
  -- let `y` be the (n+2)-sets coloured by the colours 1..(n+1)
  -- let `p` be the (n+1)-sets coloured by 1..(n+1) on the 0-boundary
  -- let `q` be the (n+1)-sets coloured by 1..(n+1) not on the 0-boundary

  -- we know `p` is odd
  -- we know p + 2 q = x + 2 y
  -- therefore `x` is odd.

  sorry
end

end affine


-- brb
