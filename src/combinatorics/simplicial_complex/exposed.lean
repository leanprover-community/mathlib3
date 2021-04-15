import combinatorics.simplicial_complex.extreme

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}
  {X : finset E}

def is_exposed_set (A B : set E) :
  Prop :=
∃ l : E →L[ℝ] ℝ, B = {x ∈ A | ∀ y ∈ A, l y ≤ l x}

lemma is_exposed_iff_normalized :
  is_exposed_set A B ↔ ∃ l : E →L[ℝ] ℝ, ∥l∥ = 1 ∧ B = {x ∈ A | ∀ y ∈ A, l y ≤ l x} :=
begin
  sorry
end

lemma subset_of_exposed (hAB : is_exposed_set A B) :
  B ⊆ A :=
begin
  obtain ⟨_, rfl⟩ := hAB,
  exact λ x hx, hx.1,
end

lemma is_exposed_set.refl :
  reflexive (is_exposed_set : set E → set E → Prop) :=
begin
  rintro A,
  use 0,
  ext x,
  exact ⟨λ hx, ⟨hx, λ y hy, le_refl _⟩, λ hx, hx.1⟩,
end

lemma is_exposed_set.antisymm :
  anti_symmetric (is_exposed_set : set E → set E → Prop) :=
λ A B hAB hBA, subset.antisymm (subset_of_exposed hBA) (subset_of_exposed hAB)

lemma is_exposed_set.trans :
  transitive (is_exposed_set : set E → set E → Prop) :=
begin
  rintro A B C hB hC,
  rw is_exposed_iff_normalized at hB hC,
  obtain ⟨l₁, hl₁, hB⟩ := hB,
  obtain ⟨l₂, hl₂, hC⟩ := hC,
  let l : E →L[ℝ] ℝ := l₁ + l₂,
  refine ⟨l, _⟩,
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
  simp,
  refine ⟨⟨hxA, _⟩, _⟩,
  {
    rintro y hy,
    have := hx y hy,
    sorry
  },
  rintro y hyA hy,
  apply (add_le_add_iff_left (l₁ y)).1,
  calc
    l₁ y + l₂ y ≤ l₁ x + l₂ x : hx y hyA
            ... ≤ l₁ y + l₂ x : add_le_add_right (hy x hxA) _,
end

lemma extreme_of_exposed (hAB : is_exposed_set A B) :
  is_extreme_set A B :=
begin
  use subset_of_exposed hAB,
  rintro x₁ x₂ hx₁A hx₂A x hxB ⟨a, b, ha, hb, hab, hx⟩ hx₁x hx₂x,
  obtain ⟨l, rfl⟩ := hAB,
  simp at *,
  have : l x = a • l x₁ + b • l x₂,
  { rw ←hx,
    simp },
  refine ⟨⟨hx₁A, _⟩, ⟨hx₂A, _⟩⟩,
  rintro y hy,
  have := hxB.2 y hy,--@Bhavik
  sorry,
  sorry
end

lemma triv (l : E →L[ℝ] ℝ) (a : ℝ) (x : E) :
  l (a • x) = a • l x :=
begin
    rw l.map_smul_of_tower,
end

lemma convex_of_exposed (hA : convex A) (hAB : is_exposed_set A B) :
  convex B :=
begin
  have hBA := subset_of_exposed hAB,
  obtain ⟨l, rfl⟩ := hAB,
  rw convex_iff_segment_subset at ⊢ hA,
  rintro x₁ x₂ ⟨hx₁A, hx₁⟩ ⟨hx₂A, hx₂⟩ x hx,
  use hA hx₁A hx₂A hx,
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hx,
  rintro y hyA,
  have : l x = a • l x₁ + b • l x₂,
  { rw ←hx,
    rw l.map_add,
    sorry
    --rw l.map_smul,
    --rw l.map_smul,
  },
  calc
    l y = a • l y + b • l y : by rw [←add_smul, hab, one_smul]
    ... ≤ a • l x₁ + b • l x₂ : add_le_add (mul_le_mul_of_nonneg_left (hx₁ y hyA) ha)
      (mul_le_mul_of_nonneg_left (hx₂ y hyA) hb)
    ... = l x : by rw [←hx, l.map_add, l.map_smul, l.map_smul],
end

lemma closed_of_exposed (hA : is_closed A) (hAB : is_exposed_set A B) :
  is_closed B :=
begin

end

lemma compact_of_exposed (hA : is_compact A) (hAB : is_exposed_set A B) :
  is_compact B :=
compact_of_is_closed_subset hA (closed_of_exposed (is_compact.is_closed hA) hAB)
  (subset_of_exposed hAB)
