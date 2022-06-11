/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simplicial_complex.extreme

/-!
# Intrinsic frontier and interior
-/

open set
open_locale affine big_operators classical

--TODO: Generalise to LCTVS
variables {𝕜 E : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {A B : set E}
  {x y : E}

variables (𝕜)

def intrinsic_interior (A : set E) : set E :=
{x ∈ A | ∃ (ι : Type*) (s : finset ι) (w : ι → 𝕜) (z : ι → E) (hs : A ⊆ affine_span 𝕜 (z '' s))
  (hw₀ : ∀ i ∈ s, 0 < w i) (hw₁ : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, z i ∈ A),
  s.center_mass w z = x}

def intrinsic_frontier (A : set E) : set E :=
{x ∈ A | ∀ (ι : Type*) (s : finset ι) (w : ι → 𝕜) (z : ι → E) (hs : A ⊆ affine_span 𝕜 (z '' s))
  (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, z i ∈ A)
  (hx : s.center_mass w z = x), ∃ i : ι, w i = 0}

lemma intrinsic_interior_subset (A : set E) : intrinsic_interior 𝕜 A ⊆ A := λ x hx, hx.1
lemma intrinsic_frontier_subset (A : set E) : intrinsic_frontier 𝕜 A ⊆ A := λ x hx, hx.1

variables {𝕜}

lemma convex.open_segment_subset_intrinsic_interior_of_mem_left (hA : convex 𝕜 A)
  (x ∈ intrinsic_interior 𝕜 A) (y ∈ A) :
  open_segment 𝕜 x y ⊆ intrinsic_interior 𝕜 A :=
begin
  rintro z hz,
  split,
  { sorry },
  dsimp,
  --obtain ⟨x₁, x₂, hx₁, hx₂, x, ⟨hxA, ι, t, hw₀, hw₁, hyA, hy⟩, hx⟩ := sorry,
  sorry
end

@[simp] lemma intrinsic_interior_union_intrinsic_frontier :
  intrinsic_interior 𝕜 A ∪ intrinsic_frontier 𝕜 A = A := sorry

lemma is_extreme_intrinsic_frontier : is_extreme 𝕜 A (intrinsic_frontier 𝕜 A) :=
begin
  refine ⟨intrinsic_frontier_subset _ _, λ x₁ x₂ hx₁ hx₂ x hxA hx, _⟩,
  sorry
end

/-def intrinsic_interior (A : set E) :
  set E :=
{x ∈ A | ∀ y ∈ A, ∃ z ∈ A, x ∈ open_segment y z}

def intrinsic_frontier (A : set E) :
  set E :=
{x ∈ A | ∃ y ∈ A, ∀ z ∈ A, x ∉ open_segment y z}

lemma intrinsic_interior_subset (A : set E) :
  intrinsic_interior A ⊆ A :=
λ x hx, hx.1

lemma intrinsic_frontier_subset (A : set E) :
  intrinsic_frontier A ⊆ A :=
λ x hx, hx.1

lemma intrinsic_frontier.is_extreme :
  is_extreme A (intrinsic_frontier A) :=
begin
  use intrinsic_frontier_subset _,
  rintro x₁ x₂ hx₁ hx₂ x ⟨hxA, y, hyA, hy⟩ hx,
  split,
  { use [hx₁, y, hyA],
    rintro z hz,
  }
end-/

/-
def intrinsic_frontier (A : set E) :
  set E :=
coe '' (frontier {x : affine_span 𝕜 A | ↑x ∈ A})

def intrinsic_interior (A : set E) :
  set E :=
coe '' (interior {x : affine_span 𝕜 A | ↑x ∈ A})

def intrinsic_closure (A : set E) :
  set E :=
coe '' (closure {x : affine_span 𝕜 A | ↑x ∈ A})

lemma intrinsic_frontier_empty :
  intrinsic_frontier (∅ : set E) = ∅ :=
begin
  apply subset_empty_iff.1,
  rintro x ⟨x', hx', hxx'⟩,
  simp at hx',
  exact hx',
end

lemma intrinsic_interior_empty :
  intrinsic_frontier (∅ : set E) = ∅ :=
begin
  apply subset_empty_iff.1,
  rintro x ⟨x', hx', hxx'⟩,
  simp at hx',
  exact hx',
end

lemma nonempty_intrinsic_interior (hA : A.nonempty) :
  (intrinsic_interior A).nonempty :=
begin

end

lemma coe_closure_subset_closure_aux (B : set E) :
  coe '' closure {x : affine_span 𝕜 A | ↑x ∈ B} ⊆ closure B :=
begin
  rintro _ ⟨x, hx, rfl⟩,
  rw mem_closure_iff_seq_limit at ⊢ hx,
  obtain ⟨f, hfB, hflim⟩ := hx,
  exact ⟨λ y, f y, hfB, by rwa ←embedding.tendsto_nhds_iff embedding_subtype_coe⟩,
end

lemma closure_eq_intrinsic_closure :
  closure A = coe '' (closure {x : affine_span 𝕜 A | ↑x ∈ A}) :=
begin
  refine subset.antisymm _ (coe_closure_subset_closure_aux A),
  rintro x hxA,
  rw mem_closure_iff_seq_limit at hxA,
  obtain ⟨f, hfA, hflim⟩ := hxA,
  simp_rw [mem_image, closure_induced],
  split,
  sorry,
  sorry,
end

lemma closure_eq_intrinsic_interior_union_intrinsic_frontier :
  closure A = intrinsic_interior A ∪ intrinsic_frontier A :=
begin
  ext x,
  rw [closure_eq_intrinsic_closure, closure_eq_interior_union_frontier],
  split,
  { rintro ⟨x', (hx' | hx'), rfl⟩,
    { left,
      exact ⟨x', hx', rfl⟩ },
    right,
    exact ⟨x', hx', rfl⟩ },
  rintro (⟨x', hx', rfl⟩ | ⟨x', hx', rfl⟩),
  exacts [⟨x', by {left, exact hx'}, rfl⟩, ⟨x', by {right, exact hx'}, rfl⟩],
end

lemma intrinsic_interior_subset_closure :
  intrinsic_interior A ⊆ closure A :=
begin
  rw closure_eq_intrinsic_interior_union_intrinsic_frontier,
  exact subset_union_left _ _,
end

lemma intrinsic_frontier_subset_closure :
  intrinsic_frontier A ⊆ closure A :=
begin
  rw closure_eq_intrinsic_interior_union_intrinsic_frontier,
  exact subset_union_right _ _,
end

lemma disjoint_intrinsic_interior_intrinsic_frontier :
  disjoint (intrinsic_interior A) (intrinsic_frontier A) :=
begin
  rintro x ⟨⟨x₁, hx₁, rfl⟩, x₂, hx₂, hx₁x₂⟩,
  rw subtype.ext hx₁x₂ at hx₂,
  exact hx₂.2 hx₁,
end

lemma intrinsic_frontier_eq_closure_diff_intrinsic_interior :
  intrinsic_frontier A = closure A \ intrinsic_interior A :=
by rw [closure_eq_intrinsic_interior_union_intrinsic_frontier,
  set.union_diff_cancel_left disjoint_intrinsic_interior_intrinsic_frontier]

lemma intrinsic_interior_eq_closure_diff_intrinsic_frontier :
  intrinsic_interior A = closure A \ intrinsic_frontier A :=
by rw [intrinsic_frontier_eq_closure_diff_intrinsic_interior, diff_diff_right, diff_self,
  empty_union, inter_eq_self_of_subset_right intrinsic_interior_subset_closure]

lemma intrinsic_frontier_subset_frontier :
  intrinsic_frontier A ⊆ frontier A :=
begin
  rintro x hx,
  unfold intrinsic_frontier at hx,
  rw frontier_eq_closure_inter_closure at ⊢ hx,
  obtain ⟨x', hx', rfl⟩ := hx,
  exact ⟨coe_closure_subset_closure_aux _ ⟨x', hx'.1, rfl⟩, coe_closure_subset_closure_aux Aᶜ
    ⟨x', hx'.2, rfl⟩⟩,
end

lemma interior_subset_intrinsic_interior :
  interior A ⊆ intrinsic_interior A :=
begin
  rw [interior_eq_closure_diff_frontier, intrinsic_interior_eq_closure_diff_intrinsic_frontier],
  exact diff_subset_diff_right intrinsic_frontier_subset_frontier,
end

--rewrite the condition to something about dimension?
lemma intrinsic_frontier_eq_frontier (hA : affine_span 𝕜 A = ⊤) :
  intrinsic_frontier A = frontier A :=
begin
  apply subset.antisymm intrinsic_frontier_subset_frontier,
  rintro x hx,
  have hxA : x ∈ affine_span 𝕜 A,
  { rw hA,
    sorry,
  },
  refine ⟨⟨x, hxA⟩, _, rfl⟩,
  sorry
end

lemma intrinsic_frontier_convex_hull_eq (hA : affine_independent 𝕜 (λ p, p : A → E)) :
  intrinsic_frontier (convex_hull 𝕜 A) = ⋃ B ⊂ A, convex_hull 𝕜 B :=
begin
  sorry --damn hard
end-/
