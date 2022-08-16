/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.affine_space.independent
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.determinant

/-!
# Affine bases and barycentric coordinates

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

 * `affine_basis`: a structure representing an affine basis of an affine space.
 * `affine_basis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
 * `affine_basis.coord_apply_eq`: the behaviour of `affine_basis.coord i` on `p i`.
 * `affine_basis.coord_apply_neq`: the behaviour of `affine_basis.coord i` on `p j` when `j ≠ i`.
 * `affine_basis.coord_apply`: the behaviour of `affine_basis.coord i` on `p j` for general `j`.
 * `affine_basis.coord_apply_combination`: the characterisation of `affine_basis.coord i` in terms
    of affine combinations, i.e., `affine_basis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

 * Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/

open_locale affine big_operators matrix
open set

universes u₁ u₂ u₃ u₄

/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
structure affine_basis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄)
  [add_comm_group V] [affine_space V P] [ring k] [module k V] :=
(points : ι → P)
(ind : affine_independent k points)
(tot : affine_span k (range points) = ⊤)

variables {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variables [add_comm_group V] [affine_space V P]

namespace affine_basis

section ring

variables [ring k] [module k V] (b : affine_basis ι k P)

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
instance : inhabited (affine_basis punit k punit) :=
⟨{ points := id,
   ind    := affine_independent_of_subsingleton k id,
   tot    := by simp }⟩

/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis correpsonding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `points j -ᵥ points i`. (See `basis_of_apply`.) -/
noncomputable def basis_of (i : ι) : basis {j : ι // j ≠ i} k V :=
basis.mk ((affine_independent_iff_linear_independent_vsub k b.points i).mp b.ind)
begin
  suffices : submodule.span k (range (λ (j : {x // x ≠ i}), b.points ↑j -ᵥ b.points i)) =
             vector_span k (range b.points),
  { rw [this, ← direction_affine_span, b.tot, affine_subspace.direction_top], exact le_rfl },
  conv_rhs { rw ← image_univ, },
  rw vector_span_image_eq_span_vsub_set_right_ne k b.points (mem_univ i),
  congr,
  ext v,
  simp,
end

@[simp] lemma basis_of_apply (i : ι) (j : {j : ι // j ≠ i}) :
  b.basis_of i j = b.points ↑j -ᵥ b.points i :=
by simp [basis_of]

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def coord (i : ι) : P →ᵃ[k] k :=
{ to_fun    := λ q, 1 - (b.basis_of i).sum_coords (q -ᵥ b.points i),
  linear    := -(b.basis_of i).sum_coords,
  map_vadd' := λ q v, by rw [vadd_vsub_assoc, linear_map.map_add, vadd_eq_add, linear_map.neg_apply,
    sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg], }

@[simp] lemma linear_eq_sum_coords (i : ι) :
  (b.coord i).linear = -(b.basis_of i).sum_coords :=
rfl

@[simp] lemma coord_apply_eq (i : ι) :
  b.coord i (b.points i) = 1 :=
by simp only [coord, basis.coe_sum_coords, linear_equiv.map_zero, linear_equiv.coe_coe,
  sub_zero, affine_map.coe_mk, finsupp.sum_zero_index, vsub_self]

@[simp] lemma coord_apply_neq (i j : ι) (h : j ≠ i) :
  b.coord i (b.points j) = 0 :=
by rw [coord, affine_map.coe_mk, ← subtype.coe_mk j h, ← b.basis_of_apply i ⟨j, h⟩,
  basis.sum_coords_self_apply, sub_self]

lemma coord_apply [decidable_eq ι] (i j : ι) :
  b.coord i (b.points j) = if i = j then 1 else 0 :=
by { cases eq_or_ne i j; simp [h.symm], simp [h], }

@[simp] lemma coord_apply_combination_of_mem
  {s : finset ι} {i : ι} (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
  b.coord i (s.affine_combination b.points w) = w i :=
begin
  classical,
  simp only [coord_apply, hi, finset.affine_combination_eq_linear_combination, if_true, mul_boole,
    hw, function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination b.points w hw],
end

@[simp] lemma coord_apply_combination_of_not_mem
  {s : finset ι} {i : ι} (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
  b.coord i (s.affine_combination b.points w) = 0 :=
begin
  classical,
  simp only [coord_apply, hi, finset.affine_combination_eq_linear_combination, if_false, mul_boole,
    hw, function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination b.points w hw],
end

@[simp] lemma sum_coord_apply_eq_one [fintype ι] (q : P) :
  ∑ i, b.coord i q = 1 :=
begin
  have hq : q ∈ affine_span k (range b.points), { rw b.tot, exact affine_subspace.mem_top k V q, },
  obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq,
  convert hw,
  ext i,
  exact b.coord_apply_combination_of_mem (finset.mem_univ i) hw,
end

@[simp] lemma affine_combination_coord_eq_self [fintype ι] (q : P) :
  finset.univ.affine_combination b.points (λ i, b.coord i q) = q :=
begin
  have hq : q ∈ affine_span k (range b.points), { rw b.tot, exact affine_subspace.mem_top k V q, },
  obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq,
  congr,
  ext i,
  exact b.coord_apply_combination_of_mem (finset.mem_univ i) hw,
end

/-- A variant of `affine_basis.affine_combination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp] lemma linear_combination_coord_eq_self [fintype ι] (b : affine_basis ι k V) (v : V) :
  ∑ i, (b.coord i v) • (b.points i) = v :=
begin
  have hb := b.affine_combination_coord_eq_self v,
  rwa finset.univ.affine_combination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v) at hb,
end

lemma ext_elem [fintype ι] {q₁ q₂ : P} (h : ∀ i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ :=
begin
  rw [← b.affine_combination_coord_eq_self q₁, ← b.affine_combination_coord_eq_self q₂],
  simp only [h],
end

@[simp] lemma coe_coord_of_subsingleton_eq_one [subsingleton ι] (i : ι) :
  (b.coord i : P → k) = 1 :=
begin
  ext q,
  have hp : (range b.points).subsingleton,
  { rw ← image_univ,
    apply subsingleton.image,
    apply subsingleton_of_subsingleton, },
  haveI := affine_subspace.subsingleton_of_subsingleton_span_eq_top hp b.tot,
  let s : finset ι := {i},
  have hi : i ∈ s, { simp, },
  have hw : s.sum (function.const ι (1 : k)) = 1, { simp, },
  have hq : q = s.affine_combination b.points (function.const ι (1 : k)), { simp, },
  rw [pi.one_apply, hq, b.coord_apply_combination_of_mem hi hw],
end

lemma surjective_coord [nontrivial ι] (i : ι) :
  function.surjective $ b.coord i :=
begin
  classical,
  intros x,
  obtain ⟨j, hij⟩ := exists_ne i,
  let s : finset ι := {i, j},
  have hi : i ∈ s, { simp, },
  have hj : j ∈ s, { simp, },
  let w : ι → k := λ j', if j' = i then x else 1-x,
  have hw : s.sum w = 1, { simp [hij, finset.sum_ite, finset.filter_insert, finset.filter_eq'], },
  use s.affine_combination b.points w,
  simp [b.coord_apply_combination_of_mem hi hw],
end

/-- Barycentric coordinates as an affine map. -/
noncomputable def coords : P →ᵃ[k] ι → k :=
{ to_fun    := λ q i, b.coord i q,
  linear    :=
  { to_fun    := λ v i, -(b.basis_of i).sum_coords v,
    map_add'  := λ v w, by { ext i, simp only [linear_map.map_add, pi.add_apply, neg_add], },
    map_smul' := λ t v, by { ext i, simpa only [linear_map.map_smul, pi.smul_apply, smul_neg] } },
  map_vadd' := λ p v, by
    { ext i,
      simp only [linear_eq_sum_coords, linear_map.coe_mk, linear_map.neg_apply, pi.vadd_apply',
        affine_map.map_vadd], }, }

@[simp] lemma coords_apply (q : P) (i : ι) :
  b.coords q i = b.coord i q :=
rfl

/-- Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matrix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `basis.to_matrix`. -/
noncomputable def to_matrix {ι' : Type*} (q : ι' → P) : matrix ι' ι k :=
λ i j, b.coord j (q i)

@[simp] lemma to_matrix_apply {ι' : Type*} (q : ι' → P) (i : ι') (j : ι) :
  b.to_matrix q i j = b.coord j (q i) :=
rfl

@[simp] lemma to_matrix_self [decidable_eq ι] :
  b.to_matrix b.points = (1 : matrix ι ι k) :=
begin
  ext i j,
  rw [to_matrix_apply, coord_apply, matrix.one_eq_pi_single, pi.single_apply],
end

variables {ι' : Type*} [fintype ι'] [fintype ι] (b₂ : affine_basis ι k P)

lemma to_matrix_row_sum_one {ι' : Type*} (q : ι' → P) (i : ι') :
  ∑ j, b.to_matrix q i j = 1 :=
by simp

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine independent. -/
lemma affine_independent_of_to_matrix_right_inv [decidable_eq ι']
  (p : ι' → P) {A : matrix ι ι' k} (hA : (b.to_matrix p) ⬝ A = 1) : affine_independent k p :=
begin
  rw affine_independent_iff_eq_of_fintype_affine_combination_eq,
  intros w₁ w₂ hw₁ hw₂ hweq,
  have hweq' : (b.to_matrix p).vec_mul w₁ = (b.to_matrix p).vec_mul w₂,
  { ext j,
    change ∑ i, (w₁ i) • (b.coord j (p i)) = ∑ i, (w₂ i) • (b.coord j (p i)),
    rw [← finset.univ.affine_combination_eq_linear_combination _ _ hw₁,
        ← finset.univ.affine_combination_eq_linear_combination _ _ hw₂,
        ← finset.univ.map_affine_combination p w₁ hw₁,
        ← finset.univ.map_affine_combination p w₂ hw₂, hweq], },
  replace hweq' := congr_arg (λ w, A.vec_mul w) hweq',
  simpa only [matrix.vec_mul_vec_mul, ← matrix.mul_eq_mul, hA, matrix.vec_mul_one] using hweq',
end

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the entire space. -/
lemma affine_span_eq_top_of_to_matrix_left_inv [decidable_eq ι] [nontrivial k]
  (p : ι' → P) {A : matrix ι ι' k} (hA : A ⬝ b.to_matrix p = 1) : affine_span k (range p) = ⊤ :=
begin
  suffices : ∀ i, b.points i ∈ affine_span k (range p),
  { rw [eq_top_iff, ← b.tot, affine_span_le],
    rintros q ⟨i, rfl⟩,
    exact this i, },
  intros i,
  have hAi : ∑ j, A i j = 1,
  { calc ∑ j, A i j = ∑ j, (A i j) * ∑ l, b.to_matrix p j l : by simp
                ... = ∑ j, ∑ l, (A i j) * b.to_matrix p j l : by simp_rw finset.mul_sum
                ... = ∑ l, ∑ j, (A i j) * b.to_matrix p j l : by rw finset.sum_comm
                ... = ∑ l, (A ⬝ b.to_matrix p) i l : rfl
                ... = 1 : by simp [hA, matrix.one_apply, finset.filter_eq], },
  have hbi : b.points i = finset.univ.affine_combination p (A i),
  { apply b.ext_elem,
    intros j,
    rw [b.coord_apply, finset.univ.map_affine_combination _ _ hAi,
      finset.univ.affine_combination_eq_linear_combination _ _ hAi],
    change _ = (A ⬝ b.to_matrix p) i j,
    simp_rw [hA, matrix.one_apply, @eq_comm _ i j] },
  rw hbi,
  exact affine_combination_mem_affine_span hAi p,
end

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_inv_mul_affine_basis_to_matrix`. -/
@[simp] lemma to_matrix_vec_mul_coords (x : P) :
  (b.to_matrix b₂.points).vec_mul (b₂.coords x) = b.coords x :=
begin
  ext j,
  change _ = b.coord j x,
  conv_rhs { rw ← b₂.affine_combination_coord_eq_self x, },
  rw finset.map_affine_combination _ _ _ (b₂.sum_coord_apply_eq_one x),
  simp [matrix.vec_mul, matrix.dot_product, to_matrix_apply, coords],
end

variables [decidable_eq ι]

lemma to_matrix_mul_to_matrix :
  (b.to_matrix b₂.points) ⬝ (b₂.to_matrix b.points) = 1 :=
begin
  ext l m,
  change (b₂.to_matrix b.points).vec_mul (b.coords (b₂.points l)) m = _,
  rw [to_matrix_vec_mul_coords, coords_apply, ← to_matrix_apply, to_matrix_self],
end

lemma is_unit_to_matrix :
  is_unit (b.to_matrix b₂.points) :=
⟨{ val     := b.to_matrix b₂.points,
   inv     := b₂.to_matrix b.points,
   val_inv := b.to_matrix_mul_to_matrix b₂,
   inv_val := b₂.to_matrix_mul_to_matrix b, }, rfl⟩

lemma is_unit_to_matrix_iff [nontrivial k] (p : ι → P) :
  is_unit (b.to_matrix p) ↔ affine_independent k p ∧ affine_span k (range p) = ⊤ :=
begin
  split,
  { rintros ⟨⟨B, A, hA, hA'⟩, (rfl : B = b.to_matrix p)⟩,
    rw matrix.mul_eq_mul at hA hA',
    exact ⟨b.affine_independent_of_to_matrix_right_inv p hA,
           b.affine_span_eq_top_of_to_matrix_left_inv p hA'⟩, },
  { rintros ⟨h_tot, h_ind⟩,
    let b' : affine_basis ι k P := ⟨p, h_tot, h_ind⟩,
    change is_unit (b.to_matrix b'.points),
    exact b.is_unit_to_matrix b', },
end

end ring

section comm_ring

variables [comm_ring k] [module k V] [decidable_eq ι] [fintype ι]
variables (b b₂ : affine_basis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_vec_mul_coords`. -/
@[simp] lemma to_matrix_inv_vec_mul_to_matrix (x : P) :
  (b.to_matrix b₂.points)⁻¹.vec_mul (b.coords x) = b₂.coords x :=
begin
  have hu := b.is_unit_to_matrix b₂,
  rw matrix.is_unit_iff_is_unit_det at hu,
  rw [← b.to_matrix_vec_mul_coords b₂, matrix.vec_mul_vec_mul, matrix.mul_nonsing_inv _ hu,
    matrix.vec_mul_one],
end

/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
lemma det_smul_coords_eq_cramer_coords (x : P) :
  (b.to_matrix b₂.points).det • b₂.coords x = (b.to_matrix b₂.points)ᵀ.cramer (b.coords x) :=
begin
  have hu := b.is_unit_to_matrix b₂,
  rw matrix.is_unit_iff_is_unit_det at hu,
  rw [← b.to_matrix_inv_vec_mul_to_matrix, matrix.det_smul_inv_vec_mul_eq_cramer_transpose _ _ hu],
end

end comm_ring

section division_ring

variables [division_ring k] [module k V]
include V

variables (k V P)

lemma exists_affine_basis : ∃ (s : set P), nonempty (affine_basis ↥s k P) :=
begin
  obtain ⟨s, -, h_tot, h_ind⟩ := exists_affine_independent k V (set.univ : set P),
  refine ⟨s, ⟨⟨(coe : s → P), h_ind, _⟩⟩⟩,
  rw [subtype.range_coe, h_tot, affine_subspace.span_univ],
end

variables {k V P}

lemma exists_affine_basis_of_finite_dimensional {ι : Type*} [fintype ι] [finite_dimensional k V]
  (h : fintype.card ι = finite_dimensional.finrank k V + 1) :
  nonempty (affine_basis ι k P) :=
begin
  obtain ⟨s, ⟨⟨incl, h_ind, h_tot⟩⟩⟩ := affine_basis.exists_affine_basis k V P,
  haveI : fintype s := fintype_of_fin_dim_affine_independent k h_ind,
  have hs : fintype.card ι = fintype.card s,
  { rw h, exact (h_ind.affine_span_eq_top_iff_card_eq_finrank_add_one.mp h_tot).symm, },
  rw ← affine_independent_equiv (fintype.equiv_of_card_eq hs) at h_ind,
  refine ⟨⟨_, h_ind, _⟩⟩,
  rw range_comp,
  simp [h_tot],
end

end division_ring

end affine_basis
