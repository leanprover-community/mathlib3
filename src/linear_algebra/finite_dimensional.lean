/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import ring_theory.noetherian linear_algebra.dimension
import ring_theory.principal_ideal_domain

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a field `K`. There are (at least) three equivalent definitions of
finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `finite_dimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the third point of view, i.e., as `is_noetherian`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `finite_dimensional`):

- `exists_is_basis_finite` states that a finite-dimensional vector space has a finite basis
- `of_finite_basis` states that the existence of a finite basis implies finite-dimensionality
- `iff_fg` states that the space is finite-dimensional if and only if it is finitely generated

Also defined is `findim`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `dim`, which returns a `cardinal`. When the space has infinite dimension, its
`findim` is by convention set to `0`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `findim_quotient_add_findim`)
- linear equivs, in `linear_equiv.finite_dimensional` and `linear_equiv.findim_eq`
- image under a linear map (the rank-nullity formula is in `findim_range_add_findim_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `mul_eq_one_comm` and
`comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `submodule.fg_iff_finite_dimensional`.
-/

universes u v v' w
open_locale classical

open vector_space cardinal submodule module function

variables {K : Type u} {V : Type v} [discrete_field K] [add_comm_group V] [vector_space K V]
{V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂]

/-- `finite_dimensional` vector spaces are defined to be noetherian modules.
Use `finite_dimensional.iff_fg` or `finite_dimensional.of_finite_basis` to prove finite dimension
from a conventional definition. -/
@[reducible] def finite_dimensional (K V : Type*) [discrete_field K]
  [add_comm_group V] [vector_space K V] := is_noetherian K V

namespace finite_dimensional

open is_noetherian

/-- A vector space is finite-dimensional if and only if its dimension (as a cardinal) is strictly
less than the first infinite cardinal `omega`. -/
lemma finite_dimensional_iff_dim_lt_omega : finite_dimensional K V ↔ dim K V < omega.{v} :=
begin
  cases exists_is_basis K V with b hb,
  have := is_basis.mk_eq_dim hb,
  simp only [lift_id] at this,
  rw [← this, lt_omega_iff_fintype, ← @set.set_of_mem_eq _ b, ← subtype.val_range],
  split,
  { intro, resetI, convert finite_of_linear_independent hb.1, simp },
  { assume hbfinite,
    refine @is_noetherian_of_linear_equiv K (⊤ : submodule K V) V _
      _ _ _ _ (linear_equiv.of_top _ rfl) (id _),
    refine is_noetherian_of_fg_of_noetherian _ ⟨set.finite.to_finset hbfinite, _⟩,
    rw [set.finite.coe_to_finset, ← hb.2], refl }
end

/-- The dimension of a finite-dimensional vector space, as a cardinal, is strictly less than the
first infinite cardinal `omega`. -/
lemma dim_lt_omega (K V : Type*) [discrete_field K] [add_comm_group V] [vector_space K V] :
  ∀ [finite_dimensional K V], dim K V < omega.{v} :=
finite_dimensional_iff_dim_lt_omega.1

/-- In a finite dimensional space, there exists a finite basis. A basis is in general given as a
function from an arbitrary type to the vector space. Here, we think of a basis as a set (instead of
a function), and use as parametrizing type this set (and as a function the function `subtype.val`).
-/
variables (K V)
lemma exists_is_basis_finite [finite_dimensional K V] :
  ∃ s : set V, (is_basis K (subtype.val : s → V)) ∧ s.finite :=
begin
  cases exists_is_basis K V with s hs,
  exact ⟨s, hs, finite_of_linear_independent hs.1⟩
end
variables {K V}

/-- A vector space is finite-dimensional if and only if it is finitely generated. As the
finitely-generated property is a property of submodules, we formulate this in terms of the
maximal submodule, equal to the whole space as a set by definition.-/
lemma iff_fg :
  finite_dimensional K V ↔ (⊤ : submodule K V).fg :=
begin
  split,
  { introI h,
    rcases exists_is_basis_finite K V with ⟨s, s_basis, s_finite⟩,
    exact ⟨s_finite.to_finset, by { convert s_basis.2, simp }⟩ },
  { rintros ⟨s, hs⟩,
    rw [finite_dimensional_iff_dim_lt_omega, ← dim_top, ← hs],
    exact lt_of_le_of_lt (dim_span_le _) (lt_omega_iff_finite.2 (set.finite_mem_finset s)) }
end

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
lemma of_finite_basis {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) :
  finite_dimensional K V :=
iff_fg.2 $ ⟨finset.univ.image b, by {convert h.2, simp} ⟩

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_submodule [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K S :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_omega K V))

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_quotient [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K (quotient S) :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_quotient_le _) (dim_lt_omega K V))

/-- The dimension of a finite-dimensional vector space as a natural number. Defined by convention to
be `0` if the space is infinite-dimensional. -/
noncomputable def findim (K V : Type*) [discrete_field K]
  [add_comm_group V] [vector_space K V] : ℕ :=
if h : dim K V < omega.{v} then classical.some (lt_omega.1 h) else 0

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its `findim`. -/
lemma findim_eq_dim (K : Type u) (V : Type v) [discrete_field K]
  [add_comm_group V] [vector_space K V] [finite_dimensional K V] :
  (findim K V : cardinal.{v}) = dim K V :=
begin
  have : findim K V = classical.some (lt_omega.1 (dim_lt_omega K V)) :=
    dif_pos (dim_lt_omega K V),
  rw this,
  exact (classical.some_spec (lt_omega.1 (dim_lt_omega K V))).symm
end

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
lemma dim_eq_card_basis {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) :
  dim K V = fintype.card ι :=
by rw [←h.mk_range_eq_dim, cardinal.fintype_card,
       set.card_range_of_injective (h.injective zero_ne_one)]


/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
lemma findim_eq_card_basis {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) :
  findim K V = fintype.card ι :=
begin
  haveI : finite_dimensional K V := of_finite_basis h,
  have := dim_eq_card_basis h,
  rw ← findim_eq_dim at this,
  exact_mod_cast this
end

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`findim`. -/
lemma findim_eq_card_basis' [finite_dimensional K V] {ι : Type w} {b : ι → V} (h : is_basis K b) :
  (findim K V : cardinal.{w}) = cardinal.mk ι  :=
begin
  rcases exists_is_basis_finite K V with ⟨s, s_basis, s_finite⟩,
  letI: fintype s := s_finite.fintype,
  have A : cardinal.mk s = fintype.card s := fintype_card _,
  have B : findim K V = fintype.card s := findim_eq_card_basis s_basis,
  have C : cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk s) :=
    mk_eq_mk_of_basis h s_basis,
  rw [A, ← B, lift_nat_cast] at C,
  have : cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{w v} (findim K V),
    by { simp, exact C },
  exact (lift_inj.mp this).symm
end

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
lemma eq_top_of_findim_eq [finite_dimensional K V] {S : submodule K V}
  (h : findim K S = findim K V) : S = ⊤ :=
begin
  cases exists_is_basis K S with bS hbS,
  have : linear_independent K (subtype.val : (subtype.val '' bS : set V) → V),
    from @linear_independent.image_subtype _ _ _ _ _ _ _ _ _
      (submodule.subtype S) hbS.1 (by simp),
  cases exists_subset_is_basis this with b hb,
  letI : fintype b := classical.choice (finite_of_linear_independent hb.2.1),
  letI : fintype (subtype.val '' bS) := classical.choice (finite_of_linear_independent this),
  letI : fintype bS := classical.choice (finite_of_linear_independent hbS.1),
  have : subtype.val '' bS = b, from set.eq_of_subset_of_card_le hb.1
    (by rw [set.card_image_of_injective _ subtype.val_injective, ← findim_eq_card_basis hbS,
         ← findim_eq_card_basis hb.2, h]; apply_instance),
  erw [← hb.2.2, subtype.val_range, ← this, set.set_of_mem_eq, ← subtype_eq_val, span_image],
  have := hbS.2,
  erw [subtype.val_range, set.set_of_mem_eq] at this,
  rw [this, map_top (submodule.subtype S), range_subtype],
end

variable (K)
/-- A field is one-dimensional as a vector space over itself. -/
@[simp] lemma findim_of_field : findim K K = 1 :=
begin
  have := dim_of_field K,
  rw [← findim_eq_dim] at this,
  exact_mod_cast this
end

/-- The vector space of functions on a fintype has finite dimension. -/
instance finite_dimensional_fintype_fun {ι : Type*} [fintype ι] :
  finite_dimensional K (ι → K) :=
by { rw [finite_dimensional_iff_dim_lt_omega, dim_fun'], exact nat_lt_omega _ }

/-- The vector space of functions on a fintype ι has findim equal to the cardinality of ι. -/
@[simp] lemma findim_fintype_fun_eq_card {ι : Type v} [fintype ι] :
  findim K (ι → K) = fintype.card ι :=
begin
  have : vector_space.dim K (ι → K) = fintype.card ι := dim_fun',
  rwa [← findim_eq_dim, nat_cast_inj] at this,
end

/-- The vector space of functions on `fin n` has findim equal to `n`. -/
@[simp] lemma findim_fin_fun {n : ℕ} : findim K (fin n → K) = n :=
by simp

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : set V} (hA : set.finite A) : finite_dimensional K (submodule.span K A) :=
is_noetherian_span_of_finite K hA

end finite_dimensional

namespace submodule
open finite_dimensional

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional (s : submodule K V) :
  s.fg ↔ finite_dimensional K s :=
⟨λh, is_noetherian_of_fg_of_noetherian s h,
 λh, by { rw ← map_subtype_top s, exact fg_map (iff_fg.1 h) }⟩

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem findim_quotient_add_findim [finite_dimensional K V] (s : submodule K V) :
  findim K s.quotient + findim K s = findim K V :=
begin
  have := dim_quotient_add_dim s,
  rw [← findim_eq_dim, ← findim_eq_dim, ← findim_eq_dim] at this,
  exact_mod_cast this
end

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
lemma findim_le [finite_dimensional K V] (s : submodule K V) : findim K s ≤ findim K V :=
by { rw ← s.findim_quotient_add_findim, exact nat.le_add_left _ _ }

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
lemma findim_quotient_le [finite_dimensional K V] (s : submodule K V) :
  findim K s.quotient ≤ findim K V :=
by { rw ← s.findim_quotient_add_findim, exact nat.le_add_right _ _ }

end submodule

namespace linear_equiv
open finite_dimensional

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finite_dimensional (f : V ≃ₗ[K] V₂) [finite_dimensional K V] :
  finite_dimensional K V₂ :=
is_noetherian_of_linear_equiv f

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem findim_eq (f : V ≃ₗ[K] V₂) [finite_dimensional K V] :
  findim K V = findim K V₂ :=
begin
  haveI : finite_dimensional K V₂ := f.finite_dimensional,
  rcases exists_is_basis_finite K V with ⟨s, s_basis, s_finite⟩,
  letI : fintype s := s_finite.fintype,
  have A : findim K V = fintype.card s := findim_eq_card_basis s_basis,
  have : is_basis K (λx:s, f (subtype.val x)) := f.is_basis s_basis,
  have B : findim K V₂ = fintype.card s := findim_eq_card_basis this,
  rw [A, B]
end

end linear_equiv

namespace linear_map
open finite_dimensional

/-- On a finite-dimensional space, an injective linear map is surjective. -/
lemma surjective_of_injective [finite_dimensional K V] {f : V →ₗ[K] V}
  (hinj : injective f) : surjective f :=
begin
  have h := dim_eq_injective _ hinj,
  rw [← findim_eq_dim, ← findim_eq_dim, nat_cast_inj] at h,
  exact range_eq_top.1 (eq_top_of_findim_eq h.symm)
end

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
lemma injective_iff_surjective [finite_dimensional K V] {f : V →ₗ[K] V} :
  injective f ↔ surjective f :=
⟨surjective_of_injective,
  λ hsurj, let ⟨g, hg⟩ := exists_right_inverse_linear_map_of_surjective
    (range_eq_top.2 hsurj) in
  have function.right_inverse g f,
    from λ x, show (linear_map.comp f g) x = (@linear_map.id K V _ _ _ : V → V) x, by rw hg,
  injective_of_has_left_inverse ⟨g, left_inverse_of_surjective_of_right_inverse
    (surjective_of_injective (injective_of_has_left_inverse ⟨_, this⟩))
      this⟩⟩

lemma ker_eq_bot_iff_range_eq_top [finite_dimensional K V] {f : V →ₗ[K] V} :
  f.ker = ⊥ ↔ f.range = ⊤ :=
by rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
lemma mul_eq_one_of_mul_eq_one [finite_dimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) :
  g * f = 1 :=
have ginj : injective g, from injective_of_has_left_inverse
  ⟨f, λ x, show (f * g) x = (1 : V →ₗ[K] V) x, by rw hfg; refl⟩,
let ⟨i, hi⟩ := exists_right_inverse_linear_map_of_surjective
  (range_eq_top.2 (injective_iff_surjective.1 ginj)) in
have f * (g * i) = f * 1, from congr_arg _ hi,
by rw [← mul_assoc, hfg, one_mul, mul_one] at this; rwa ← this

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
lemma mul_eq_one_comm [finite_dimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
lemma comp_eq_id_comm [finite_dimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
mul_eq_one_comm

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
lemma finite_dimensional_of_surjective [h : finite_dimensional K V]
  (f : V →ₗ[K] V₂) (hf : f.range = ⊤) : finite_dimensional K V₂ :=
is_noetherian_of_surjective V f hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_range [h : finite_dimensional K V] (f : V →ₗ[K] V₂) :
  finite_dimensional K f.range :=
f.quot_ker_equiv_range.finite_dimensional

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem findim_range_add_findim_ker [finite_dimensional K V] (f : V →ₗ[K] V₂) :
  findim K f.range + findim K f.ker = findim K V :=
by { rw [← f.quot_ker_equiv_range.findim_eq], exact submodule.findim_quotient_add_findim _ }

end linear_map
