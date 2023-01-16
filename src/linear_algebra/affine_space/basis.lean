/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.affine_space.independent
import linear_algebra.basis

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
 * `affine_basis.coord_apply_ne`: the behaviour of `affine_basis.coord i` on `p j` when `j ≠ i`.
 * `affine_basis.coord_apply`: the behaviour of `affine_basis.coord i` on `p j` for general `j`.
 * `affine_basis.coord_apply_combination`: the characterisation of `affine_basis.coord i` in terms
    of affine combinations, i.e., `affine_basis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

 * Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/

namespace set
variables {α β γ : Type*} (f : β → γ) (e : α ≃ β)

@[simp] lemma range_comp_equiv : range (f ∘ e) = range f := e.surjective.range_comp _

end set

namespace basis
variables {𝕜 V ι ι' : Type*} [semiring 𝕜] [add_comm_monoid V] [module 𝕜 V] [fintype ι] [fintype ι']

@[simp] lemma sum_coords_reindex (b : basis ι 𝕜 V) (e : ι ≃ ι') :
  (b.reindex e).sum_coords = b.sum_coords :=
begin
  ext x,
  simp only [coe_sum_coords_of_fintype, fintype.sum_apply, basis.coord_apply, reindex_repr],
  exact e.symm.sum_comp _,
end

end basis

open_locale affine big_operators
open set

universes u₁ u₂ u₃ u₄

/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
@[protect_proj]
structure affine_basis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄)
  [add_comm_group V] [affine_space V P] [ring k] [module k V] :=
(to_fun : ι → P)
(ind' : affine_independent k to_fun)
(tot' : affine_span k (range to_fun) = ⊤)

variables {ι ι' k V P : Type*} [add_comm_group V] [affine_space V P]

namespace affine_basis

section ring

variables [ring k] [module k V] (b : affine_basis ι k P) {s : finset ι} {i j : ι} (e : ι ≃ ι')
include V

instance fun_like : fun_like (affine_basis ι k P) ι (λ _, P) :=
{ coe := affine_basis.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

@[ext]
lemma ext {b₁ b₂ : affine_basis ι k P} (h : (b₁ : ι → P) = b₂) : b₁ = b₂ := fun_like.coe_injective h

lemma ind : affine_independent k b := b.ind'
lemma tot : affine_span k (range b) = ⊤ := b.tot'

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
instance : inhabited (affine_basis punit k punit) :=
⟨⟨id, affine_independent_of_subsingleton k id, by simp⟩⟩

include b

protected lemma nonempty : nonempty ι :=
not_is_empty_iff.mp $ λ hι,
  by simpa only [@range_eq_empty _ _ hι, affine_subspace.span_empty, bot_ne_top] using b.tot

/-- Composition of an affine basis and an equivalence of index types. -/
def reindex (e : ι ≃ ι') : affine_basis ι' k P :=
⟨b ∘ e.symm, b.ind.comp_embedding e.symm.to_embedding,
  by { rw [e.symm.surjective.range_comp], exact b.3 }⟩

@[simp] lemma reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') := rfl

@[simp, norm_cast] lemma coe_reindex : ⇑(b.reindex e) = b ∘ e.symm := rfl

@[simp] lemma reindex_refl : b.reindex (equiv.refl _) = b := ext rfl

/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis corresponding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `b j -ᵥ b i`. (See `basis_of_apply`.) -/
noncomputable def basis_of (i : ι) : basis {j : ι // j ≠ i} k V :=
basis.mk ((affine_independent_iff_linear_independent_vsub k b i).mp b.ind)
begin
  suffices : submodule.span k (range (λ (j : {x // x ≠ i}), b ↑j -ᵥ b i)) =
             vector_span k (range b),
  { rw [this, ← direction_affine_span, b.tot, affine_subspace.direction_top], exact le_rfl },
  conv_rhs { rw ← image_univ, },
  rw vector_span_image_eq_span_vsub_set_right_ne k b (mem_univ i),
  congr,
  ext v,
  simp,
end

@[simp] lemma basis_of_apply (i : ι) (j : {j : ι // j ≠ i}) :
  b.basis_of i j = b ↑j -ᵥ b i :=
by simp [basis_of]

@[simp] lemma basis_of_reindex (i : ι') :
  (b.reindex e).basis_of i =
    (b.basis_of $ e.symm i).reindex (e.subtype_equiv $ λ _, e.eq_symm_apply.not) :=
by { ext j, simp }

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def coord (i : ι) : P →ᵃ[k] k :=
{ to_fun    := λ q, 1 - (b.basis_of i).sum_coords (q -ᵥ b i),
  linear    := -(b.basis_of i).sum_coords,
  map_vadd' := λ q v, by rw [vadd_vsub_assoc, linear_map.map_add, vadd_eq_add, linear_map.neg_apply,
    sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg], }

@[simp] lemma linear_eq_sum_coords (i : ι) :
  (b.coord i).linear = -(b.basis_of i).sum_coords :=
rfl

@[simp] lemma coord_reindex [fintype ι] [fintype ι'] (i : ι') :
  (b.reindex e).coord i = b.coord (e.symm i) :=
by { ext, classical, simp [affine_basis.coord] }

@[simp] lemma coord_apply_eq (i : ι) : b.coord i (b i) = 1 :=
by simp only [coord, basis.coe_sum_coords, linear_equiv.map_zero, linear_equiv.coe_coe,
  sub_zero, affine_map.coe_mk, finsupp.sum_zero_index, vsub_self]

@[simp] lemma coord_apply_ne (h : i ≠ j) : b.coord i (b j) = 0 :=
by rw [coord, affine_map.coe_mk, ← subtype.coe_mk j h.symm, ← b.basis_of_apply,
  basis.sum_coords_self_apply, sub_self]

lemma coord_apply [decidable_eq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 else 0 :=
by cases eq_or_ne i j; simp [h]

@[simp] lemma coord_apply_combination_of_mem (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
  b.coord i (s.affine_combination b w) = w i :=
begin
  classical,
  simp only [coord_apply, hi, finset.affine_combination_eq_linear_combination, if_true, mul_boole,
    hw, function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination b w hw],
end

@[simp] lemma coord_apply_combination_of_not_mem (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
  b.coord i (s.affine_combination b w) = 0 :=
begin
  classical,
  simp only [coord_apply, hi, finset.affine_combination_eq_linear_combination, if_false, mul_boole,
    hw, function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination b w hw],
end

@[simp] lemma sum_coord_apply_eq_one [fintype ι] (q : P) :
  ∑ i, b.coord i q = 1 :=
begin
  have hq : q ∈ affine_span k (range b), { rw b.tot, exact affine_subspace.mem_top k V q, },
  obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq,
  convert hw,
  ext i,
  exact b.coord_apply_combination_of_mem (finset.mem_univ i) hw,
end

@[simp] lemma affine_combination_coord_eq_self [fintype ι] (q : P) :
  finset.univ.affine_combination b (λ i, b.coord i q) = q :=
begin
  have hq : q ∈ affine_span k (range b), { rw b.tot, exact affine_subspace.mem_top k V q, },
  obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq,
  congr,
  ext i,
  exact b.coord_apply_combination_of_mem (finset.mem_univ i) hw,
end

/-- A variant of `affine_basis.affine_combination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp] lemma linear_combination_coord_eq_self [fintype ι] (b : affine_basis ι k V) (v : V) :
  ∑ i, b.coord i v • b i = v :=
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
  have hp : (range b).subsingleton,
  { rw ← image_univ,
    apply subsingleton.image,
    apply subsingleton_of_subsingleton, },
  haveI := affine_subspace.subsingleton_of_subsingleton_span_eq_top hp b.tot,
  let s : finset ι := {i},
  have hi : i ∈ s, { simp, },
  have hw : s.sum (function.const ι (1 : k)) = 1, { simp, },
  have hq : q = s.affine_combination b (function.const ι (1 : k)), { simp, },
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
  use s.affine_combination b w,
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

end ring

section division_ring

variables [division_ring k] [module k V]
include V

@[simp] lemma coord_apply_centroid [char_zero k] (b : affine_basis ι k P) {s : finset ι} {i : ι}
  (hi : i ∈ s) :
  b.coord i (s.centroid k b) = (s.card : k) ⁻¹ :=
by rw [finset.centroid, b.coord_apply_combination_of_mem hi
  (s.sum_centroid_weights_eq_one_of_nonempty _ ⟨i, hi⟩), finset.centroid_weights]

lemma exists_affine_subbasis {t : set P} (ht : affine_span k t = ⊤) :
  ∃ (s ⊆ t) (b : affine_basis ↥s k P), ⇑b = coe :=
begin
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affine_independent k V t,
  refine ⟨s, hst, ⟨coe, h_ind, _⟩, rfl⟩,
  rw [subtype.range_coe, h_tot, ht]
end

variables (k V P)

lemma exists_affine_basis : ∃ (s : set P) (b : affine_basis ↥s k P), ⇑b = coe :=
let ⟨s, _, hs⟩ := exists_affine_subbasis (affine_subspace.span_univ k V P) in ⟨s, hs⟩

end division_ring

end affine_basis
