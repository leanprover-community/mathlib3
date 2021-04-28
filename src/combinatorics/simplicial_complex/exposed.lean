import combinatorics.simplicial_complex.extreme

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

def is_exposed (A B : set E) :
  Prop :=
∃ l : E →L[ℝ] ℝ, B = {x ∈ A | ∀ y ∈ A, l y ≤ l x}

def continuous_linear_map.to_exposed (l : E →L[ℝ] ℝ) (A : set E) :
  set E :=
{x ∈ A | ∀ y ∈ A, l y ≤ l x}

lemma continuous_linear_map.to_exposed.is_exposed :
  is_exposed A (l.to_exposed A) :=
⟨l, rfl⟩

lemma is_exposed_iff_normalized (hAB : ¬A ⊆ B) :
  is_exposed A B ↔ ∃ l : E →L[ℝ] ℝ, ∥l∥ = 1 ∧ B = {x ∈ A | ∀ y ∈ A, l y ≤ l x} :=
begin
  refine ⟨_, λ ⟨l, _, hB⟩, ⟨l, hB⟩⟩,
  rintro ⟨l, hB⟩,
  refine ⟨(1/∥l∥) • l, sorry, _⟩,
  let x : E := sorry,
  let y : E := sorry,
  have : (1 / ∥l∥) • l x ≤ (1 / ∥l∥) • l y ↔ l x ≤ l y,
  {
    refine mul_le_mul_left _,
    refine div_pos _ _,
    sorry,
    sorry
  },
  rw hB,
  ext z,
  split,
  {
    rintro ⟨hzA, h⟩,
    refine ⟨hzA, λ w hw, _⟩,
    simp only [continuous_linear_map.smul_apply],
    sorry--refine submodule.smul_mono_right _ _ _ _,
  },
  sorry
end

lemma is_exposed.subset (hAB : is_exposed A B) :
  B ⊆ A :=
begin
  obtain ⟨_, rfl⟩ := hAB,
  exact λ x hx, hx.1,
end

lemma is_exposed.refl :
  reflexive (is_exposed : set E → set E → Prop) :=
begin
  rintro A,
  use 0,
  ext x,
  exact ⟨λ hx, ⟨hx, λ y hy, le_refl _⟩, λ hx, hx.1⟩,
end

lemma is_exposed.antisymm :
  anti_symmetric (is_exposed : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm hBA.subset hAB.subset

lemma is_exposed.trans :
  transitive (is_exposed : set E → set E → Prop) :=
begin
  rintro A B C hB hC,
  by_cases hAB : A ⊆ B,
  { rw subset.antisymm hAB hB.subset
    exact hC },
  by_cases hBC : B ⊆ C,
  { rw subset.antisymm hC.subset hBC,
    exact hB },
  rw is_exposed_iff_normalized hAB at hB,
  rw is_exposed_iff_normalized hBC at hC,
  obtain ⟨l₁, hl₁, hB⟩ := hB,
  obtain ⟨l₂, hl₂, hC⟩ := hC,
  refine ⟨l₁ + l₂, _⟩,
  rw hC,
  ext x,
  split,
  {
    rintro ⟨hxB, hxl₂⟩,
    rw hB at hxB,
    obtain ⟨hxA, hxl₁⟩ := hxB,
    use hxA,
    rintro y hy,
    have := hxl₁ y hy,
    sorry
  },
  rintro ⟨hxA, hx⟩,
  rw hB,
  refine ⟨⟨hxA, _⟩, _⟩,
  {
    rintro y hy,
    have := hx y hy,
    sorry
  },
  rintro y ⟨hyA, hy⟩,
  apply (add_le_add_iff_left (l₁ y)).1,
  calc
    l₁ y + l₂ y ≤ l₁ x + l₂ x : hx y hyA
            ... ≤ l₁ y + l₂ x : add_le_add_right (hy x hxA) _,
end

instance : is_partial_order (set E) is_exposed :=
{ refl := is_exposed.refl,
  trans := is_exposed.trans,
  antisymm := is_exposed.antisymm }

lemma is_exposed.is_extreme (hAB : is_exposed A B) :
  is_extreme A B :=
begin
  rw extreme_set_iff,
  use subset_of_exposed hAB,
  rintro x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, ha, hb, hab, hx⟩,
  obtain ⟨l, rfl⟩ := hAB,
  have hlx₁ : l x₁ = l x,
  { apply le_antisymm (hxB.2 x₁ hx₁A),
    rw [←smul_le_smul_iff_of_pos ha, ←add_le_add_iff_right (b • l x), ←add_smul, hab, one_smul],
    nth_rewrite 0 ←hx,
    rw [l.map_add, l.map_smul _, l.map_smul _, add_le_add_iff_left, smul_le_smul_iff_of_pos hb],
    exact hxB.2 x₂ hx₂A,
    sorry,
    sorry
    /-rw [←smul_le_smul_iff_of_pos ha, ←add_le_add_iff_right (b • l x), ←add_smul, hab, one_smul,
      ←hx, l.map_add, continuous_linear_map.map_smul, continuous_linear_map.map_smul,
      add_le_add_iff_left, smul_le_smul_iff_of_pos hb],-/
  },
  have hlx₂ : l x₂ = l x,
  { apply le_antisymm (hxB.2 x₂ hx₂A),
    rw [←smul_le_smul_iff_of_pos hb, ←add_le_add_iff_left (a • l x), ←add_smul, hab, one_smul],
    nth_rewrite 0 ←hx,
    rw [l.map_add, l.map_smul _, l.map_smul _, add_le_add_iff_right, smul_le_smul_iff_of_pos ha],
    exact hxB.2 x₁ hx₁A,
    sorry,
    sorry },
  refine ⟨⟨hx₁A, λ y hy, _⟩, ⟨hx₂A, λ y hy, _⟩⟩,
  { rw hlx₁,
    exact hxB.2 y hy },
  rw hlx₂,
  exact hxB.2 y hy,
end

lemma convex_of_exposed (hA : convex A) (hAB : is_exposed A B) :
  convex B :=
begin
  have hBA := hAB.subset,
  obtain ⟨l, rfl⟩ := hAB,
  rw convex_iff_segment_subset at ⊢ hA,
  rintro x₁ x₂ ⟨hx₁A, hx₁⟩ ⟨hx₂A, hx₂⟩ x hx,
  use hA hx₁A hx₂A hx,
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hx,
  rintro y hyA,
  calc
    l y = a • l y + b • l y : by rw [←add_smul, hab, one_smul]
    ... ≤ a • l x₁ + b • l x₂ : add_le_add (mul_le_mul_of_nonneg_left (hx₁ y hyA) ha)
                                           (mul_le_mul_of_nonneg_left (hx₂ y hyA) hb)
    ... = l x : by rw [←hx, l.map_add, l.map_smul _, l.map_smul _],
end

lemma is_exposed.is_closed (hAB : is_exposed A B) (hA : is_closed A) :
  is_closed B :=
begin
  obtain ⟨l, rfl⟩ := hAB,
  apply is_closed_inter hA,
  refine closure_eq_iff_is_closed.1 (subset.antisymm _ subset_closure),
  /-rw sequentie
  rw ←is_seq_closed_iff_is_closed,
  apply is_seq_closed_of_def,
  rintro x y hx hxy z hz,
  suffices h : l '' (closure (x '' univ)) ⊆ closure (Ici (l z)),
  { rw [closure_Ici] at h,
    exact h ⟨z, hz, rfl⟩ },
  refine subset.trans (image_closure_subset_closure_image l.continuous) (closure_mono _),
  rintro _ ⟨w, hw, rfl⟩,
  exact hx w hw,-/
  sorry --@Bhavik, easy now
end

lemma is_exposed.is_compact (hAB : is_exposed A B) (hA : is_compact A) :
  is_compact B :=
compact_of_is_closed_subset hA (hAB.is_closed hA.is_closed) hAB.subset

lemma mem_extreme_set_iff_mem_frontier (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  (∃ B : set E, is_extreme_set A B ∧ B ⊂ A ∧ x ∈ B) ↔ x ∈ A ∧ x ∈ frontier A :=
begin
  use λ ⟨B, hAB, hBA, hxB⟩, ⟨hAB.1 hxB, hAB.subset_frontier hBA hxB⟩,
  rintro ⟨hxA, hxfA⟩,
  obtain ⟨y, hyA⟩ := id hA₂,
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (convex.interior hA₁) is_open_interior hxfA.2,
  refine ⟨{x ∈ A | ∀ y ∈ A, l y ≤ l x}, extreme_of_exposed ⟨l, rfl⟩, ⟨λ x hx, hx.1, λ h,
    not_le.2 (hl y hyA) ((h (interior_subset hyA)).2 x hxA)⟩, ⟨hxA, λ z hzA, _⟩⟩,
  suffices h : l '' closure (interior A) ⊆ closure (Iio (l x)),
  { rw [closure_Iio, ←closure_eq_closure_interior hA₁ hA₂] at h,
    exact h ⟨z, subset_closure hzA, rfl⟩ },
  refine subset.trans (image_closure_subset_closure_image l.continuous) (closure_mono _),
  rintro _ ⟨w, hw, rfl⟩,
  exact hl w hw,
end

lemma mem_exposed_set_iff_mem_frontier (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  (∃ B : set E, is_exposed A B ∧ B ⊂ A ∧ x ∈ B) ↔ x ∈ A ∧ x ∈ frontier A :=
begin
  use λ ⟨B, hAB, hBA, hxB⟩, ⟨hAB.1 hxB, hAB.subset_frontier hBA hxB⟩,
  rintro ⟨hxA, hxfA⟩,
  obtain ⟨y, hyA⟩ := id hA₂,
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (convex.interior hA₁) is_open_interior hxfA.2,
  refine ⟨{x ∈ A | ∀ y ∈ A, l y ≤ l x}, extreme_of_exposed ⟨l, rfl⟩, ⟨λ x hx, hx.1, λ h,
    not_le.2 (hl y hyA) ((h (interior_subset hyA)).2 x hxA)⟩, ⟨hxA, λ z hzA, _⟩⟩,
  suffices h : l '' closure (interior A) ⊆ closure (Iio (l x)),
  { rw [closure_Iio, ←closure_eq_closure_interior hA₁ hA₂] at h,
    exact h ⟨z, subset_closure hzA, rfl⟩ },
  refine subset.trans (image_closure_subset_closure_image l.continuous) (closure_mono _),
  rintro _ ⟨w, hw, rfl⟩,
  exact hl w hw,
end

def set.exposed_points (A : set E) :
  set E :=
{x ∈ A | ∃ l : E →L[ℝ] ℝ, ∀ y ∈ A, l y = l x → y = x}

lemma exposed_point_iff :
  x ∈ A.exposed_points ↔ x ∈ A ∧ ∃ l : E →L[ℝ] ℝ, ∀ y ∈ A, l y = l x → y = x :=
by refl

lemma exposed_point_iff_exposed_singleton :
  x ∈ A.exposed_points ↔ is_exposed A {x} :=
begin
  split,
  { rintro ⟨hxA, l, hl⟩,
    by_cases ∃ y ∈ A, l y < l x,
    {
      obtain ⟨y, hy, hxy⟩ := h,
      use l,
      apply subset.antisymm,
      rintro x (rfl : _ = _),
      use hxA,
      rintro z hz,
      sorry,
      sorry
    },
    push_neg at h,
    use -l,
    apply subset.antisymm,
    { rintro x (rfl : _ = _),
    use hxA,
    rintro y hy,
    sorry
    --simp,
    --exact h y hy
    },
    rintro y ⟨hyA, hy⟩,
    have := hy x hxA,
    sorry
    --simp at this,
    --refine hl y hyA (le_antisymm this (h y hyA)),
    },
  { rintro ⟨l, hl⟩,
    have hx : x ∈ {x} := mem_singleton _,
    rw hl at hx,
    refine ⟨hx.1, l, λ y hy hxy, _⟩,
    rw [←mem_singleton_iff, hl],
    refine ⟨hy, λ z hz, _⟩,
    rw hxy,
    exact hx.2 z hz }
end

lemma exposed_points_subset :
  A.exposed_points ⊆ A :=
λ x hx, hx.1

@[simp]
lemma exposed_points_empty :
  (∅ : set E).exposed_points = ∅ :=
subset_empty_iff.1 exposed_points_subset

/-! # Harder stuff -/

--theorem of S. Straszewicz proved in 1935
lemma limit_extreme_points_of_exposed (hA₁ : convex A) (hA₂ : is_closed A) :
  A.exposed_points ⊆ closure (A.extreme_points) :=
begin
  sorry
end
