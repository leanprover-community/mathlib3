/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.affine_space.independent

/-!
# Barycentric coordinates

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

 * `barycentric_coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
 * `barycentric_coord_apply_eq`: the behaviour of `barycentric_coord i` on `p i`.
 * `barycentric_coord_apply_neq`: the behaviour of `barycentric_coord i` on `p j` when `j ≠ i`.
 * `barycentric_coord_apply`: the behaviour of `barycentric_coord i` on `p j` for general `j`.
 * `barycentric_coord_apply_combination`: the characterisation of `barycentric_coord i` in terms
    of affine combinations, i.e., `barycentric_coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

 * Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/

open_locale affine big_operators
open set

universes u₁ u₂ u₃ u₄

variables {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}
variables [ring k] [add_comm_group V] [module k V] [affine_space V P]
variables {p : ι → P} (h_ind : affine_independent k p) (h_tot : affine_span k (range p) = ⊤)
include V h_ind h_tot

/-- Given an affine-independent family of points spanning the point space `P`, if we single out one
member of the family, we obtain a basis for the model space `V`.

The basis correpsonding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}` and its
`j`th element is `p j -ᵥ p i`. (See `basis_of_aff_ind_span_eq_top_apply`.) -/
noncomputable def basis_of_aff_ind_span_eq_top (i : ι) : basis {j : ι // j ≠ i} k V :=
basis.mk ((affine_independent_iff_linear_independent_vsub k p i).mp h_ind)
begin
  suffices : submodule.span k (range (λ (j : {x // x ≠ i}), p ↑j -ᵥ p i)) = vector_span k (range p),
  { rw [this, ← direction_affine_span, h_tot, affine_subspace.direction_top], },
  conv_rhs { rw ← image_univ, },
  rw vector_span_image_eq_span_vsub_set_right_ne k p (mem_univ i),
  congr,
  ext v,
  simp,
end

local notation `basis_of` := basis_of_aff_ind_span_eq_top h_ind h_tot

@[simp] lemma basis_of_aff_ind_span_eq_top_apply (i : ι) (j : {j : ι // j ≠ i}) :
  basis_of i j = p ↑j -ᵥ p i :=
by simp [basis_of_aff_ind_span_eq_top]

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def barycentric_coord (i : ι) : P →ᵃ[k] k :=
{ to_fun    := λ q, 1 - (basis_of i).sum_coords (q -ᵥ p i),
  linear    := -(basis_of i).sum_coords,
  map_vadd' := λ q v, by rw [vadd_vsub_assoc, linear_map.map_add, vadd_eq_add, linear_map.neg_apply,
    sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg], }

@[simp] lemma barycentric_coord_apply_eq (i : ι) :
  barycentric_coord h_ind h_tot i (p i) = 1 :=
by simp only [barycentric_coord, basis.coe_sum_coords, linear_equiv.map_zero, linear_equiv.coe_coe,
  sub_zero, affine_map.coe_mk, finsupp.sum_zero_index, vsub_self]

@[simp] lemma barycentric_coord_apply_neq (i j : ι) (h : j ≠ i) :
  barycentric_coord h_ind h_tot i (p j) = 0 :=
by rw [barycentric_coord, affine_map.coe_mk, ← subtype.coe_mk j h,
  ← basis_of_aff_ind_span_eq_top_apply h_ind h_tot i ⟨j, h⟩, basis.sum_coords_self_apply, sub_self]

lemma barycentric_coord_apply [decidable_eq ι] (i j : ι) :
  barycentric_coord h_ind h_tot i (p j) = if i = j then 1 else 0 :=
by { cases eq_or_ne i j; simp [h.symm], simp [h], }

@[simp] lemma barycentric_coord_apply_combination_of_mem
  {s : finset ι} {i : ι} (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
  barycentric_coord h_ind h_tot i (s.affine_combination p w) = w i :=
begin
  classical,
  simp only [barycentric_coord_apply, hi, finset.affine_combination_eq_linear_combination, if_true,
    hw, mul_boole, function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination p w hw],
end

@[simp] lemma barycentric_coord_apply_combination_of_not_mem
  {s : finset ι} {i : ι} (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
  barycentric_coord h_ind h_tot i (s.affine_combination p w) = 0 :=
begin
  classical,
  simp only [barycentric_coord_apply, hi, finset.affine_combination_eq_linear_combination, if_false,
    hw, mul_boole, function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination p w hw],
end

@[simp] lemma coe_barycentric_coord_of_subsingleton_eq_one [subsingleton ι] (i : ι) :
  (barycentric_coord h_ind h_tot i : P → k) = 1 :=
begin
  ext q,
  have hp : (range p).subsingleton,
  { rw ← image_univ,
    apply subsingleton.image,
    apply subsingleton_of_subsingleton, },
  haveI := affine_subspace.subsingleton_of_subsingleton_span_eq_top hp h_tot,
  let s : finset ι := {i},
  have hi : i ∈ s, { simp, },
  have hw : s.sum (function.const ι (1 : k)) = 1, { simp, },
  have hq : q = s.affine_combination p (function.const ι (1 : k)), { simp, },
  rw [pi.one_apply, hq, barycentric_coord_apply_combination_of_mem h_ind h_tot hi hw],
end

lemma surjective_barycentric_coord [nontrivial ι] (i : ι) :
  function.surjective $ barycentric_coord h_ind h_tot i :=
begin
  classical,
  intros x,
  obtain ⟨j, hij⟩ := exists_ne i,
  let s : finset ι := {i, j},
  have hi : i ∈ s, { simp, },
  have hj : j ∈ s, { simp, },
  let w : ι → k := λ j', if j' = i then x else 1-x,
  have hw : s.sum w = 1, { simp [hij, finset.sum_ite, finset.filter_insert, finset.filter_eq'], },
  use s.affine_combination p w,
  simp [barycentric_coord_apply_combination_of_mem h_ind h_tot hi hw],
end
