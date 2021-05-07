import combinatorics.simplicial_complex.extreme

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B C : set E}
  {X : finset E} {l : E →L[ℝ] ℝ}

def is_exposed (A B : set E) :
  Prop :=
B.nonempty → ∃ l : E →L[ℝ] ℝ, B = {x ∈ A | ∀ y ∈ A, l y ≤ l x}

def continuous_linear_map.to_exposed (l : E →L[ℝ] ℝ) (A : set E) :
  set E :=
{x ∈ A | ∀ y ∈ A, l y ≤ l x}

lemma continuous_linear_map.to_exposed.is_exposed :
  is_exposed A (l.to_exposed A) :=
λ h, ⟨l, rfl⟩

lemma is_exposed_iff_normalized (hAB : ¬A ⊆ B) :
  is_exposed A B ↔ B.nonempty → ∃ l : E →L[ℝ] ℝ, ∥l∥ = 1 ∧ B = {x ∈ A | ∀ y ∈ A, l y ≤ l x} :=
begin
  apply imp_congr iff.rfl,
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

namespace is_exposed

lemma subset (hAB : is_exposed A B) :
  B ⊆ A :=
begin
  cases B.eq_empty_or_nonempty,
  { rw h,
    exact empty_subset _ },
  obtain ⟨_, rfl⟩ := hAB h,
  exact λ x hx, hx.1,
end

@[refl] lemma refl (A : set E) :
  is_exposed A A :=
λ ⟨w, hw⟩, ⟨0, subset.antisymm (λ x hx, ⟨hx, λ y hy, by exact le_refl 0⟩) (λ x hx, hx.1)⟩

lemma antisymm (hB : is_exposed A B) (hA : is_exposed B A) :
  A = B :=
subset.antisymm hA.subset hB.subset

@[trans] lemma trans (hB : is_exposed A B) (hC : is_exposed B C) :
  is_exposed A C :=
begin
  rintro hCnemp,
  by_cases hAB : A ⊆ B,
  { rw subset.antisymm hAB hB.subset,
    exact hC hCnemp },
  by_cases hBC : B ⊆ C,
  { rw subset.antisymm hC.subset hBC,
    exact hB (nonempty.mono hC.subset hCnemp) },
  sorry
  /-
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
            ... ≤ l₁ y + l₂ x : add_le_add_right (hy x hxA) _,-/
end

instance : is_partial_order (set E) is_exposed :=
{ refl := refl,
  trans := λ A B C hB, hB.trans,
  antisymm := λ A B hB, hB.antisymm }

lemma is_exposed_empty : is_exposed A ∅ :=
λ ⟨x, hx⟩, by { exfalso, exact hx }

lemma mono (hC : is_exposed A C) (hBA : B ⊆ A) (hCB : C ⊆ B) :
  is_exposed B C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  refine ⟨l, subset.antisymm _ _⟩,
  rintro x hx,
  exact ⟨hCB hx, λ y hy, hx.2 y (hBA hy)⟩,
  rintro x hx,
  exact ⟨hBA hx.1, λ y hy, (hw.2 y hy).trans (hx.2 w (hCB hw))⟩,
end

lemma inter (hB : is_exposed A B) (hC : is_exposed A C) :
  is_exposed A (B ∩ C) :=
begin
  rintro ⟨x, hxB, hxC⟩,
  obtain ⟨l₁, rfl⟩ := hB ⟨x, hxB⟩,
  obtain ⟨l₂, rfl⟩ := hC ⟨x, hxC⟩,
  refine ⟨l₁ + l₂, subset.antisymm _ _⟩,
  { rintro y ⟨⟨hyA, hyB⟩, ⟨_, hyC⟩⟩,
    exact ⟨hyA, λ z hz, add_le_add (hyB z hz) (hyC z hz)⟩ },
  rintro y ⟨hyA, hy⟩,
  refine ⟨⟨hyA, λ z hz, _⟩, hyA, λ z hz, _⟩,
  { exact (add_le_add_iff_right (l₂ y)).1 (le_trans (add_le_add (hxB.2 z hz) (hxC.2 y hyA))
      (hy x hxB.1)) },
  exact (add_le_add_iff_left (l₁ y)).1 (le_trans (add_le_add (hxB.2 y hyA) (hxC.2 z hz))
    (hy x hxB.1)),
end

lemma Inter {ι : Type*} [nonempty ι] {F : ι → set E}
  (hAF : ∀ i : ι, is_exposed A (F i)) :
  is_exposed A (⋂ i : ι, F i) :=
begin
  rintro ⟨x, hx⟩,
  obtain i := classical.arbitrary ι,
  rw mem_Inter at hx,
  sorry
end

lemma bInter {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_exposed A B) :
  is_exposed A (⋂ B ∈ F, B) :=
begin
  sorry
end

lemma sInter {F : set (set E)} (hF : F.nonempty)
  (hAF : ∀ B ∈ F, is_exposed A B) :
  is_exposed A (⋂₀ F) :=
begin
  sorry
end

lemma inter_left (hC : is_exposed A C) (hCB : C ⊆ B) :
  is_exposed (A ∩ B) C :=
begin
  rintro ⟨w, hw⟩,
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩,
  refine ⟨l, subset.antisymm _ _⟩,
  rintro x hx,
  exact ⟨⟨hx.1, hCB hx⟩, λ y hy, hx.2 y hy.1⟩,
  rintro x ⟨⟨hxC, _⟩, hx⟩,
  exact ⟨hxC, λ y hy, (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩,
end

lemma inter_right (hC : is_exposed B C) (hCA : C ⊆ A) :
  is_exposed (A ∩ B) C :=
begin
  rw inter_comm,
  exact hC.inter_left hCA,
end

instance : bounded_lattice (set_of (is_exposed A)) :=
{ sup := λ ⟨B, hB⟩ ⟨C, hC⟩, ⟨(⋂ (D : set E) (hD : is_exposed A D) (hDB : B ⊆ D) (hCB : C ⊆ D), D),
    begin
      apply Inter,
      sorry
    end⟩,
  le := λ ⟨B, hB⟩ ⟨C, hC⟩, is_exposed C B,
  le_refl := λ ⟨B, hB⟩, refl B,
  le_trans := λ ⟨B, hB⟩ ⟨C, hC⟩ ⟨D, hD⟩ (hBC : is_exposed _ _) (hCD : is_exposed _ _), hCD.trans hBC,
  le_antisymm := λ ⟨B, hB⟩ ⟨C, hC⟩ (hCB : is_exposed _ _) hBC, hBC.antisymm hCB,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf := λ ⟨B, hB⟩ ⟨C, hC⟩, ⟨B ∩ C, hB.inter hC⟩,
  inf_le_left := begin -- λ ⟨B, hB⟩ ⟨C, hC⟩, (refl B).inter
    rintro ⟨B, hB⟩ ⟨C, hC⟩,
    rintro ⟨x, hxB, hxC⟩,
    obtain ⟨l, rfl⟩ := hC ⟨x, hxC⟩,
    refine ⟨l, subset.antisymm _ _⟩,
    rintro y ⟨hyB, ⟨_, hy⟩⟩,
    exact ⟨hyB, λ z hz, hy z (hB.subset hz)⟩,
    rintro y ⟨hyB, hy⟩,
    exact ⟨hyB, (hB.subset hyB), λ z hz, (hxC.2 z hz).trans (hy x hxB)⟩,
  end,
  inf_le_right := λ ⟨B, hB⟩ ⟨C, hC⟩, begin
    simp *,
  end,
  le_inf := λ ⟨B, hB⟩ ⟨C, hC⟩ ⟨D, hD⟩ (hBC : is_exposed _ _) (hBD : is_exposed _ _), hBC.inter_left
    hBD.subset,
  top := ⟨A, refl A⟩,
  le_top := λ ⟨B, hB⟩, hB,
  bot := ⟨∅, is_exposed_empty⟩,
  bot_le := λ ⟨B, hB⟩, is_exposed_empty }

--@Bhavik, I don't know how to use the right instances
lemma is_extreme (hAB : is_exposed A B) :
  is_extreme A B :=
begin
  use hAB.subset,
  rintro x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, ha, hb, hab, hx⟩,
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩,
  have hlx₁ : l x₁ = l x,
  { apply le_antisymm (hxB.2 x₁ hx₁A),
    rw [←smul_le_smul_iff_of_pos ha, ←add_le_add_iff_right (b • l x), ←add_smul, hab, one_smul],
    nth_rewrite 0 ←hx,
    rw [l.map_add, l.map_smul, l.map_smul, add_le_add_iff_left, smul_le_smul_iff_of_pos hb],
    exact hxB.2 x₂ hx₂A,
    sorry,
    sorry
  },
  have hlx₂ : l x₂ = l x,
  { apply le_antisymm (hxB.2 x₂ hx₂A),
    rw [←smul_le_smul_iff_of_pos hb, ←add_le_add_iff_left (a • l x), ←add_smul, hab, one_smul],
    nth_rewrite 0 ←hx,
    rw [l.map_add, l.map_smul, l.map_smul, add_le_add_iff_right, smul_le_smul_iff_of_pos ha],
    exact hxB.2 x₁ hx₁A,
    sorry,
    sorry },
  refine ⟨⟨hx₁A, λ y hy, _⟩, ⟨hx₂A, λ y hy, _⟩⟩,
  { rw hlx₁,
    exact hxB.2 y hy },
  rw hlx₂,
  exact hxB.2 y hy,
end

lemma  is_convex (hAB : is_exposed A B) (hA : convex A) :
  convex B :=
begin
  cases B.eq_empty_or_nonempty,
  { rw h,
    exact convex_empty },
  have hBA := hAB.subset,
  obtain ⟨l, rfl⟩ := hAB h,
  rw convex_iff_segment_subset at ⊢ hA,
  rintro x₁ x₂ ⟨hx₁A, hx₁⟩ ⟨hx₂A, hx₂⟩ x hx,
  use hA hx₁A hx₂A hx,
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hx,
  rintro y hyA,
  calc
    l y = a • l y + b • l y : by rw [←add_smul, hab, one_smul]
    ... ≤ a • l x₁ + b • l x₂ : add_le_add (mul_le_mul_of_nonneg_left (hx₁ y hyA) ha)
                                           (mul_le_mul_of_nonneg_left (hx₂ y hyA) hb)
    ... = l x : by rw [←hx, l.map_add, l.map_smul, l.map_smul],
end

lemma is_closed (hAB : is_exposed A B) (hA : is_closed A) :
  is_closed B :=
begin
  cases B.eq_empty_or_nonempty with hB hB,
  { rw hB,
    exact is_closed_empty },
  obtain ⟨l, rfl⟩ := hAB hB,
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

lemma is_compact (hAB : is_exposed A B) (hA : is_compact A) :
  is_compact B :=
compact_of_is_closed_subset hA (hAB.is_closed hA.is_closed) hAB.subset

lemma subset_frontier (hAB : is_exposed A B) (hBA : ¬ A ⊆ B) :
  B ⊆ frontier A :=
hAB.is_extreme.subset_frontier hBA

lemma span_lt (hAB : is_exposed A B) (hBA : ¬ A ⊆ B) :
  affine_span ℝ B < affine_span ℝ A :=
begin
  apply (affine_span_mono _ hAB.subset).lt_of_ne,
  rintro h,
  sorry
end

end is_exposed

/-lemma is_exposed.dim_lt (hAB : is_exposed A B) (hBA : ¬ A ⊆ B) :
  (affine_span ℝ B).rank < (affine_span ℝ A).rank :=
begin

end-/

lemma mem_exposed_set_iff_mem_frontier (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  (∃ B : set E, is_exposed A B ∧ ¬A ⊆ B ∧ x ∈ B) ↔ x ∈ A ∧ x ∈ frontier A :=
begin
  use λ ⟨B, hAB, hBA, hxB⟩, ⟨hAB.subset hxB, hAB.subset_frontier hBA hxB⟩,
  rintro ⟨hxA, hxfA⟩,
  obtain ⟨y, hyA⟩ := id hA₂,
  obtain ⟨l, hl⟩ := geometric_hahn_banach_open_point (convex.interior hA₁) is_open_interior hxfA.2,
  refine ⟨{x ∈ A | ∀ y ∈ A, l y ≤ l x}, ⟨l, rfl⟩, λ h,
    not_le.2 (hl y hyA) ((h (interior_subset hyA)).2 x hxA), hxA, λ z hzA, _⟩,
  suffices h : l '' closure (interior A) ⊆ closure (Iio (l x)),
  { rw [closure_Iio, ←closure_eq_closure_interior hA₁ hA₂] at h,
    exact h ⟨z, subset_closure hzA, rfl⟩ },
  refine subset.trans (image_closure_subset_closure_image l.continuous) (closure_mono _),
  rintro _ ⟨w, hw, rfl⟩,
  exact hl w hw,
end

lemma mem_extreme_set_iff_mem_frontier (hA₁ : convex A) (hA₂ : (interior A).nonempty) :
  (∃ B : set E, is_extreme A B ∧ ¬A ⊆ B ∧ x ∈ B) ↔ x ∈ A ∧ x ∈ frontier A :=
begin
  use λ ⟨B, hAB, hBA, hxB⟩, ⟨hAB.1 hxB, hAB.subset_frontier hBA hxB⟩,
  rintro h,
  obtain ⟨B, hAB, hBA, hxB⟩ := (mem_exposed_set_iff_mem_frontier hA₁ hA₂).2 h,
  exact ⟨B, hAB.is_extreme, hBA, hxB⟩,
end

def set.exposed_points (A : set E) :
  set E :=
{x ∈ A | ∃ l : E →L[ℝ] ℝ, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x)}

lemma exposed_point_def :
  x ∈ A.exposed_points ↔ x ∈ A ∧ ∃ l : E →L[ℝ] ℝ, ∀ y ∈ A, l y ≤ l x ∧ (l x ≤ l y → y = x) :=
iff.rfl

lemma mem_exposed_points_iff_exposed_singleton :
  x ∈ A.exposed_points ↔ is_exposed A {x} :=
begin
  use λ ⟨hxA, l, hl⟩ h, ⟨l, eq.symm $ eq_singleton_iff_unique_mem.2 ⟨⟨hxA, λ y hy, (hl y hy).1⟩, λ z hz,
    (hl z hz.1).2 (hz.2 x hxA)⟩⟩,
  rintro h,
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩,
  rw [eq_comm, eq_singleton_iff_unique_mem] at hl,
  exact ⟨hl.1.1, l, λ y hy, ⟨hl.1.2 y hy, λ hxy, hl.2 y ⟨hy, λ z hz, le_trans (hl.1.2 z hz) hxy⟩⟩⟩,
end

lemma exposed_points_subset :
  A.exposed_points ⊆ A :=
λ x hx, hx.1

lemma exposed_points_subset_extreme_points :
  A.exposed_points ⊆ A.extreme_points :=
λ x hx, mem_extreme_points_iff_extreme_singleton.2
  (mem_exposed_points_iff_exposed_singleton.1 hx).is_extreme

@[simp]
lemma exposed_points_empty :
  (∅ : set E).exposed_points = ∅ :=
subset_empty_iff.1 exposed_points_subset

/-! # Harder stuff -/

lemma closed_extreme_points [finite_dimensional ℝ E] (hE : finite_dimensional.finrank ℝ E = 2)
(hA₁ : convex A) (hA₂ : is_closed A) :
  is_closed A.extreme_points :=
begin
  sorry
end

--theorem of S. Straszewicz proved in 1935
lemma limit_exposed_points_of_extreme (hA₁ : convex A) (hA₂ : is_closed A) :
  A.extreme_points ⊆ closure (A.exposed_points) :=
begin
  sorry
end
