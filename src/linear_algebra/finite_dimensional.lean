/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.algebra.subalgebra.basic
import field_theory.finiteness

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
proof, it is defined using the second point of view, i.e., as `finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `finite_dimensional`):

- `fintype_basis_index` states that a finite-dimensional
  vector space has a finite basis
- `finite_dimensional.fin_basis` and `finite_dimensional.fin_basis_of_finrank_eq`
  are bases for finite dimensional vector spaces, where the index type
  is `fin`
- `of_fintype_basis` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finset_basis` states that the existence of a basis indexed by a
  `finset` implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `is_noetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian

Also defined is `finrank`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `module.rank`, which returns a `cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `finrank_quotient_add_finrank`)
- linear equivs, in `linear_equiv.finite_dimensional` and `linear_equiv.finrank_eq`
- image under a linear map (the rank-nullity formula is in `finrank_range_add_finrank_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `linear_map.mul_eq_one_comm`
and `linear_map.comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

Much of this file could be generalised away from fields or division rings.
You should not assume that there has been any effort to state lemmas as generally as possible.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `submodule.fg_iff_finite_dimensional`.
-/

universes u v v' w
open_locale classical cardinal

open cardinal submodule module function

/-- `finite_dimensional` vector spaces are defined to be finite modules.
Use `finite_dimensional.of_fintype_basis` to prove finite dimension from another definition. -/
@[reducible] def finite_dimensional (K V : Type*) [division_ring K]
  [add_comm_group V] [module K V] := module.finite K V

variables {K : Type u} {V : Type v}

namespace finite_dimensional

open is_noetherian

section division_ring

variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/-- If the codomain of an injective linear map is finite dimensional, the domain must be as well. -/
lemma of_injective (f : V →ₗ[K] V₂) (w : function.injective f)
  [finite_dimensional K V₂] : finite_dimensional K V :=
have is_noetherian K V₂ := is_noetherian.iff_fg.mpr ‹_›, by exactI module.finite.of_injective f w

/-- If the domain of a surjective linear map is finite dimensional, the codomain must be as well. -/
lemma of_surjective (f : V →ₗ[K] V₂) (w : function.surjective f)
  [finite_dimensional K V] : finite_dimensional K V₂ :=
module.finite.of_surjective f w

variables (K V)

instance finite_dimensional_pi {ι} [fintype ι] : finite_dimensional K (ι → K) :=
iff_fg.1 is_noetherian_pi

instance finite_dimensional_pi' {ι} [fintype ι] (M : ι → Type*)
  [∀ i, add_comm_group (M i)] [∀ i, module K (M i)] [I : ∀ i, finite_dimensional K (M i)] :
  finite_dimensional K (Π i, M i) :=
begin
  haveI : ∀ i : ι, is_noetherian K (M i) := λ i, iff_fg.2 (I i),
  exact iff_fg.1 is_noetherian_pi
end

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintype_of_fintype [fintype K] [finite_dimensional K V] : fintype V :=
module.fintype_of_fintype (@finset_basis K V _ _ _ (iff_fg.2 infer_instance))

variables {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
lemma of_fintype_basis {ι : Type w} [fintype ι] (h : basis ι K V) :
  finite_dimensional K V :=
⟨⟨finset.univ.image h, by { convert h.span_eq, simp } ⟩⟩

/-- If a vector space is `finite_dimensional`, all bases are indexed by a finite type -/
noncomputable
def fintype_basis_index {ι : Type*} [finite_dimensional K V] (b : basis ι K V) : fintype ι :=
begin
  letI : is_noetherian K V := is_noetherian.iff_fg.2 infer_instance,
  exact is_noetherian.fintype_basis_index b,
end

/-- If a vector space is `finite_dimensional`, `basis.of_vector_space` is indexed by
  a finite type.-/
noncomputable instance [finite_dimensional K V] : fintype (basis.of_vector_space_index K V) :=
begin
  letI : is_noetherian K V := is_noetherian.iff_fg.2 infer_instance,
  apply_instance
end

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
lemma of_finite_basis {ι : Type w} {s : set ι} (h : basis s K V) (hs : set.finite s) :
  finite_dimensional K V :=
by haveI := hs.fintype; exact of_fintype_basis h

/-- If a vector space has a finite basis, then it is finite-dimensional, finset style. -/
lemma of_finset_basis {ι : Type w} {s : finset ι} (h : basis s K V) :
  finite_dimensional K V :=
of_finite_basis h s.finite_to_set

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_submodule [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K S :=
begin
  letI : is_noetherian K V := iff_fg.2 _,
  exact iff_fg.1
    (is_noetherian.iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_omega K V))),
  apply_instance,
end

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_quotient [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K (V ⧸ S) :=
finite.of_surjective (submodule.mkq S) $ surjective_quot_mk _

/-- The rank of a module as a natural number.

Defined by convention to be `0` if the space has infinite rank.

For a vector space `V` over a field `K`, this is the same as the finite dimension
of `V` over `K`.
-/
noncomputable def finrank (R V : Type*) [semiring R]
  [add_comm_group V] [module R V] : ℕ :=
(module.rank R V).to_nat

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. -/
lemma finrank_eq_dim (K : Type u) (V : Type v) [division_ring K]
  [add_comm_group V] [module K V] [finite_dimensional K V] :
  (finrank K V : cardinal.{v}) = module.rank K V :=
begin
  letI : is_noetherian K V := iff_fg.2 infer_instance,
  rw [finrank, cast_to_nat_of_lt_omega (dim_lt_omega K V)]
end

lemma finrank_eq_of_dim_eq {n : ℕ} (h : module.rank K V = ↑ n) : finrank K V = n :=
begin
  apply_fun to_nat at h,
  rw to_nat_cast at h,
  exact_mod_cast h,
end

lemma finrank_of_infinite_dimensional
  {K V : Type*} [division_ring K] [add_comm_group V] [module K V]
  (h : ¬finite_dimensional K V) : finrank K V = 0 :=
dif_neg $ mt is_noetherian.iff_dim_lt_omega.2 $ (not_iff_not.2 iff_fg).2 h

lemma finite_dimensional_of_finrank {K V : Type*} [division_ring K] [add_comm_group V] [module K V]
  (h : 0 < finrank K V) : finite_dimensional K V :=
by { contrapose h, simp [finrank_of_infinite_dimensional h] }

lemma finite_dimensional_of_finrank_eq_succ {K V : Type*} [field K] [add_comm_group V] [module K V]
  {n : ℕ} (hn : finrank K V = n.succ) : finite_dimensional K V :=
finite_dimensional_of_finrank $ by rw hn; exact n.succ_pos

/-- We can infer `finite_dimensional K V` in the presence of `[fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
lemma fact_finite_dimensional_of_finrank_eq_succ {K V : Type*} [field K] [add_comm_group V]
  [module K V] (n : ℕ) [fact (finrank K V = n + 1)] :
  finite_dimensional K V :=
finite_dimensional_of_finrank $ by convert nat.succ_pos n; apply fact.out

lemma finite_dimensional_iff_of_rank_eq_nsmul
  {K V W : Type*} [field K] [add_comm_group V] [add_comm_group W] [module K V] [module K W]
  {n : ℕ} (hn : n ≠ 0) (hVW : module.rank K V = n • module.rank K W) :
  finite_dimensional K V ↔ finite_dimensional K W :=
by simp only [finite_dimensional, ← is_noetherian.iff_fg, is_noetherian.iff_dim_lt_omega, hVW,
  cardinal.nsmul_lt_omega_iff_of_ne_zero hn]

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
lemma finrank_eq_card_basis {ι : Type w} [fintype ι] (h : basis ι K V) :
  finrank K V = fintype.card ι :=
begin
  haveI : finite_dimensional K V := of_fintype_basis h,
  have := dim_eq_card_basis h,
  rw ← finrank_eq_dim at this,
  exact_mod_cast this
end

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
lemma finrank_eq_card_basis' [finite_dimensional K V] {ι : Type w} (h : basis ι K V) :
  (finrank K V : cardinal.{w}) = #ι :=
begin
  haveI : is_noetherian K V := iff_fg.2 infer_instance,
  haveI : fintype ι := fintype_basis_index h,
  rw [cardinal.mk_fintype, finrank_eq_card_basis h]
end

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. This lemma uses a `finset` instead of indexed types. -/
lemma finrank_eq_card_finset_basis {ι : Type w} {b : finset ι}
  (h : basis.{w} b K V) :
  finrank K V = finset.card b :=
by rw [finrank_eq_card_basis h, fintype.card_coe]

variables (K V)

/-- A finite dimensional vector space has a basis indexed by `fin (finrank K V)`. -/
noncomputable def fin_basis [finite_dimensional K V] : basis (fin (finrank K V)) K V :=
have h : fintype.card (@finset_basis_index K V _ _ _ (iff_fg.2 infer_instance)) = finrank K V,
from (finrank_eq_card_basis (@finset_basis K V _ _ _ (iff_fg.2 infer_instance))).symm,
(@finset_basis K V _ _ _ (iff_fg.2 infer_instance)).reindex (fintype.equiv_fin_of_card_eq h)

/-- An `n`-dimensional vector space has a basis indexed by `fin n`. -/
noncomputable def fin_basis_of_finrank_eq [finite_dimensional K V] {n : ℕ} (hn : finrank K V = n) :
  basis (fin n) K V :=
(fin_basis K V).reindex (fin.cast hn).to_equiv

variables {K V}

/-- A module with dimension 1 has a basis with one element. -/
noncomputable def basis_unique (ι : Type*) [unique ι] (h : finrank K V = 1) :
  basis ι K V :=
begin
  haveI := finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le),
  exact (fin_basis_of_finrank_eq K V h).reindex equiv_of_unique_of_unique
end

@[simp]
lemma basis_unique.repr_eq_zero_iff {ι : Type*} [unique ι] {h : finrank K V = 1}
  {v : V} {i : ι} : (basis_unique ι h).repr v i = 0 ↔ v = 0 :=
⟨λ hv, (basis_unique ι h).repr.map_eq_zero_iff.mp (finsupp.ext $ λ j, subsingleton.elim i j ▸ hv),
 λ hv, by rw [hv, linear_equiv.map_zero, finsupp.zero_apply]⟩

lemma cardinal_mk_le_finrank_of_linear_independent
  [finite_dimensional K V] {ι : Type w} {b : ι → V} (h : linear_independent K b) :
  #ι ≤ finrank K V :=
begin
  rw ← lift_le.{_ (max v w)},
  simpa [← finrank_eq_dim K V] using
    cardinal_lift_le_dim_of_linear_independent.{_ _ _ (max v w)} h
end

lemma fintype_card_le_finrank_of_linear_independent
  [finite_dimensional K V] {ι : Type*} [fintype ι] {b : ι → V} (h : linear_independent K b) :
  fintype.card ι ≤ finrank K V :=
by simpa using cardinal_mk_le_finrank_of_linear_independent h

lemma finset_card_le_finrank_of_linear_independent [finite_dimensional K V] {b : finset V}
  (h : linear_independent K (λ x, x : b → V)) :
  b.card ≤ finrank K V :=
begin
  rw ←fintype.card_coe,
  exact fintype_card_le_finrank_of_linear_independent h,
end

lemma lt_omega_of_linear_independent {ι : Type w} [finite_dimensional K V]
  {v : ι → V} (h : linear_independent K v) :
  #ι < ω :=
begin
  apply cardinal.lift_lt.1,
  apply lt_of_le_of_lt,
  apply cardinal_lift_le_dim_of_linear_independent h,
  rw [←finrank_eq_dim, cardinal.lift_omega, cardinal.lift_nat_cast],
  apply cardinal.nat_lt_omega,
end

lemma not_linear_independent_of_infinite {ι : Type w} [inf : infinite ι] [finite_dimensional K V]
  (v : ι → V) : ¬ linear_independent K v :=
begin
  intro h_lin_indep,
  have : ¬ ω ≤ #ι := not_le.mpr (lt_omega_of_linear_independent h_lin_indep),
  have : ω ≤ #ι := infinite_iff.mp inf,
  contradiction
end

/-- A finite dimensional space has positive `finrank` iff it has a nonzero element. -/
lemma finrank_pos_iff_exists_ne_zero [finite_dimensional K V] : 0 < finrank K V ↔ ∃ x : V, x ≠ 0 :=
iff.trans (by { rw ← finrank_eq_dim, norm_cast }) (@dim_pos_iff_exists_ne_zero K V _ _ _ _ _)

/-- A finite dimensional space has positive `finrank` iff it is nontrivial. -/
lemma finrank_pos_iff [finite_dimensional K V] : 0 < finrank K V ↔ nontrivial V :=
iff.trans (by { rw ← finrank_eq_dim, norm_cast }) (@dim_pos_iff_nontrivial K V _ _ _ _ _)

/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
lemma nontrivial_of_finrank_pos (h : 0 < finrank K V) : nontrivial V :=
begin
  haveI : finite_dimensional K V := finite_dimensional_of_finrank h,
  rwa finrank_pos_iff at h
end

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
lemma nontrivial_of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) : nontrivial V :=
nontrivial_of_finrank_pos (by rw hn; exact n.succ_pos)

/-- A nontrivial finite dimensional space has positive `finrank`. -/
lemma finrank_pos [finite_dimensional K V] [h : nontrivial V] : 0 < finrank K V :=
finrank_pos_iff.mpr h

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `dim_zero_iff`. -/
lemma finrank_zero_iff [finite_dimensional K V] :
  finrank K V = 0 ↔ subsingleton V :=
iff.trans (by { rw ← finrank_eq_dim, norm_cast }) (@dim_zero_iff K V _ _ _ _ _)

/-- A finite dimensional space that is a subsingleton has zero `finrank`. -/
lemma finrank_zero_of_subsingleton [h : subsingleton V] :
  finrank K V = 0 :=
finrank_zero_iff.2 h

lemma basis.subset_extend {s : set V} (hs : linear_independent K (coe : s → V)) :
  s ⊆ hs.extend (set.subset_univ _) :=
hs.subset_extend _

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
lemma eq_top_of_finrank_eq [finite_dimensional K V] {S : submodule K V}
  (h : finrank K S = finrank K V) : S = ⊤ :=
begin
  haveI : is_noetherian K V := iff_fg.2 infer_instance,
  set bS := basis.of_vector_space K S with bS_eq,
  have : linear_independent K (coe : (coe '' basis.of_vector_space_index K S : set V) → V),
    from @linear_independent.image_subtype _ _ _ _ _ _ _ _ _
      (submodule.subtype S) (by simpa using bS.linear_independent) (by simp),
  set b := basis.extend this with b_eq,
  letI : fintype (this.extend _) :=
    (finite_of_linear_independent (by simpa using b.linear_independent)).fintype,
  letI : fintype (coe '' basis.of_vector_space_index K S) :=
    (finite_of_linear_independent this).fintype,
  letI : fintype (basis.of_vector_space_index K S) :=
    (finite_of_linear_independent (by simpa using bS.linear_independent)).fintype,
  have : coe '' (basis.of_vector_space_index K S) = this.extend (set.subset_univ _),
  from set.eq_of_subset_of_card_le (this.subset_extend _)
    (by rw [set.card_image_of_injective _ subtype.coe_injective, ← finrank_eq_card_basis bS,
         ← finrank_eq_card_basis b, h]; apply_instance),
  rw [← b.span_eq, b_eq, basis.coe_extend, subtype.range_coe, ← this, ← submodule.coe_subtype,
    span_image],
  have := bS.span_eq,
  rw [bS_eq, basis.coe_of_vector_space, subtype.range_coe] at this,
  rw [this, map_top (submodule.subtype S), range_subtype],
end

variable (K)
/-- A division_ring is one-dimensional as a vector space over itself. -/
@[simp] lemma finrank_self : finrank K K = 1 :=
begin
  have := dim_self K,
  rw [←finrank_eq_dim] at this,
  exact_mod_cast this
end

instance finite_dimensional_self : finite_dimensional K K :=
by apply_instance

/-- The vector space of functions on a fintype ι has finrank equal to the cardinality of ι. -/
@[simp] lemma finrank_fintype_fun_eq_card {ι : Type v} [fintype ι] :
  finrank K (ι → K) = fintype.card ι :=
begin
  have : module.rank K (ι → K) = fintype.card ι := dim_fun',
  rwa [← finrank_eq_dim, nat_cast_inj] at this,
end

/-- The vector space of functions on `fin n` has finrank equal to `n`. -/
@[simp] lemma finrank_fin_fun {n : ℕ} : finrank K (fin n → K) = n :=
by simp

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : set V} (hA : set.finite A) :
  finite_dimensional K (submodule.span K A) :=
iff_fg.1 $ is_noetherian_span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
instance span_singleton (x : V) : finite_dimensional K (K ∙ x) :=
span_of_finite K $ set.finite_singleton _

/-- The submodule generated by a finset is finite-dimensional. -/
instance span_finset (s : finset V) : finite_dimensional K (span K (s : set V)) :=
span_of_finite K $ s.finite_to_set

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V →ₗ[K] V₂) (p : submodule K V) [h : finite_dimensional K p] :
  finite_dimensional K (p.map f) :=
begin
  unfreezingI { rw [finite_dimensional, ← iff_fg, is_noetherian.iff_dim_lt_omega] at h ⊢ },
  rw [← cardinal.lift_lt.{v' v}],
  rw [← cardinal.lift_lt.{v v'}] at h,
  rw [cardinal.lift_omega] at h ⊢,
  exact (lift_dim_map_le f p).trans_lt h
end

/-- Pushforwards of finite-dimensional submodules have a smaller finrank. -/
lemma finrank_map_le (f : V →ₗ[K] V₂) (p : submodule K V) [finite_dimensional K p] :
  finrank K (p.map f) ≤ finrank K p :=
by simpa [← finrank_eq_dim] using lift_dim_map_le f p

variable {K}

lemma _root_.complete_lattice.independent.subtype_ne_bot_le_finrank_aux [finite_dimensional K V]
  {ι : Type w} {p : ι → submodule K V} (hp : complete_lattice.independent p) :
  #{i // p i ≠ ⊥} ≤ (finrank K V : cardinal.{w}) :=
begin
  suffices : cardinal.lift.{v} (#{i // p i ≠ ⊥}) ≤ cardinal.lift.{v} (finrank K V : cardinal.{w}),
  { rwa cardinal.lift_le at this },
  calc cardinal.lift.{v} (# {i // p i ≠ ⊥})
      ≤ cardinal.lift.{w} (module.rank K V) : hp.subtype_ne_bot_le_rank
  ... = cardinal.lift.{w} (finrank K V : cardinal.{v}) : by rw finrank_eq_dim
  ... = cardinal.lift.{v} (finrank K V : cardinal.{w}) : by simp
end

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def _root_.complete_lattice.independent.fintype_ne_bot_of_finite_dimensional
  [finite_dimensional K V] {ι : Type w} {p : ι → submodule K V}
  (hp : complete_lattice.independent p) :
  fintype {i : ι // p i ≠ ⊥} :=
begin
  suffices : #{i // p i ≠ ⊥} < (ω : cardinal.{w}),
  { rw cardinal.lt_omega_iff_fintype at this,
    exact this.some },
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux _,
  simp [cardinal.nat_lt_omega],
end

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `V`.

Note that the `fintype` hypothesis required here can be provided by
`complete_lattice.independent.fintype_ne_bot_of_finite_dimensional`. -/
lemma _root_.complete_lattice.independent.subtype_ne_bot_le_finrank
  [finite_dimensional K V] {ι : Type w} {p : ι → submodule K V}
  (hp : complete_lattice.independent p) [fintype {i // p i ≠ ⊥}] :
  fintype.card {i // p i ≠ ⊥} ≤ finrank K V :=
by simpa using hp.subtype_ne_bot_le_finrank_aux

section
open_locale big_operators
open finset

/--
If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
lemma exists_nontrivial_relation_of_dim_lt_card
  [finite_dimensional K V] {t : finset V} (h : finrank K V < t.card) :
  ∃ f : V → K, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  have := mt finset_card_le_finrank_of_linear_independent (by { simpa using h }),
  rw not_linear_independent_iff at this,
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this,
  -- Now we have to extend `g` to all of `t`, then to all of `V`.
  let f : V → K :=
    λ x, if h : x ∈ t then if (⟨x, h⟩ : t) ∈ s then g ⟨x, h⟩ else 0 else 0,
  -- and finally clean up the mess caused by the extension.
  refine ⟨f, _, _⟩,
  { dsimp [f],
    rw ← sum,
    fapply sum_bij_ne_zero (λ v hvt _, (⟨v, hvt⟩ : {v // v ∈ t})),
    { intros v hvt H, dsimp,
      rw [dif_pos hvt] at H,
      contrapose! H,
      rw [if_neg H, zero_smul], },
    { intros _ _ _ _ _ _, exact subtype.mk.inj, },
    { intros b hbs hb,
      use b,
      simpa only [hbs, exists_prop, dif_pos, finset.mk_coe, and_true, if_true, finset.coe_mem,
        eq_self_iff_true, exists_prop_of_true, ne.def] using hb, },
    { intros a h₁, dsimp, rw [dif_pos h₁],
      intro h₂, rw [if_pos], contrapose! h₂,
      rw [if_neg h₂, zero_smul], }, },
  { refine ⟨z, z.2, _⟩, dsimp only [f], erw [dif_pos z.2, if_pos]; rwa [subtype.coe_eta] },
end

/--
If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
lemma exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card
  [finite_dimensional K V] {t : finset V} (h : finrank K V + 1 < t.card) :
  ∃ f : V → K, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  -- Pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_trans (nat.succ_pos _) h,
  obtain ⟨x₀, m⟩ := (finset.card_pos.1 card_pos).bex,
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨λ x, x - x₀, sub_left_injective⟩,
  let t' := (t.erase x₀).map shift,
  have h' : finrank K V < t'.card,
  { simp only [t', card_map, finset.card_erase_of_mem m],
    exact nat.lt_pred_iff.mpr h, },
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_dim_lt_card h',
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → K := λ z, if z = x₀ then - ∑ z in (t.erase x₀), g (z - x₀) else g (z - x₀),
  refine ⟨f, _ ,_ ,_⟩,
  -- After this, it's a matter of verifiying the properties,
  -- based on the corresponding properties for `g`.
  { show ∑ (e : V) in t, f e • e = 0,
    -- We prove this by splitting off the `x₀` term of the sum,
    -- which is itself a sum over `t.erase x₀`,
    -- combining the two sums, and
    -- observing that after reindexing we have exactly
    -- ∑ (x : V) in t', g x • x = 0.
    simp only [f],
    conv_lhs { apply_congr, skip, rw [ite_smul], },
    rw [finset.sum_ite],
    conv { congr, congr, apply_congr, simp [filter_eq', m], },
    conv { congr, congr, skip, apply_congr, simp [filter_ne'], },
    rw [sum_singleton, neg_smul, add_comm, ←sub_eq_add_neg, sum_smul, ←sum_sub_distrib],
    simp only [←smul_sub],
    -- At the end we have to reindex the sum, so we use `change` to
    -- express the summand using `shift`.
    change (∑ (x : V) in t.erase x₀, (λ e, g e • e) (shift x)) = 0,
    rw ←sum_map _ shift,
    exact gsum, },
  { show ∑ (e : V) in t, f e = 0,
    -- Again we split off the `x₀` term,
    -- observing that it exactly cancels the other terms.
    rw [← insert_erase m, sum_insert (not_mem_erase x₀ t)],
    dsimp [f],
    rw [if_pos rfl],
    conv_lhs { congr, skip, apply_congr, skip, rw if_neg (show x ≠ x₀, from (mem_erase.mp H).1), },
    exact neg_add_self _, },
  { show ∃ (x : V) (H : x ∈ t), f x ≠ 0,
    -- We can use x₁ + x₀.
    refine ⟨x₁ + x₀, _, _⟩,
    { rw finset.mem_map at x₁_mem,
      rcases x₁_mem with ⟨x₁, x₁_mem, rfl⟩,
      rw mem_erase at x₁_mem,
      simp only [x₁_mem, sub_add_cancel, function.embedding.coe_fn_mk], },
    { dsimp only [f],
      rwa [if_neg, add_sub_cancel],
      rw [add_left_eq_self], rintro rfl,
      simpa only [sub_eq_zero, exists_prop, finset.mem_map, embedding.coe_fn_mk, eq_self_iff_true,
        mem_erase, not_true, exists_eq_right, ne.def, false_and] using x₁_mem, } },
end

section
variables {L : Type*} [linear_ordered_field L]
variables {W : Type v} [add_comm_group W] [module L W]

/--
A slight strengthening of `exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
lemma exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card
  [finite_dimensional L W] {t : finset W} (h : finrank L W + 1 < t.card) :
  ∃ f : W → L, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, 0 < f x :=
begin
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h,
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩,
end

end

end

/-- In a vector space with dimension 1, each set {v} is a basis for `v ≠ 0`. -/
@[simps]
noncomputable def basis_singleton (ι : Type*) [unique ι]
  (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
  basis ι K V :=
let b := basis_unique ι h in
let h : b.repr v default ≠ 0 := mt basis_unique.repr_eq_zero_iff.mp hv in
basis.of_repr
{ to_fun := λ w, finsupp.single default (b.repr w default / b.repr v default),
  inv_fun := λ f, f default • v,
  map_add' := by simp [add_div],
  map_smul' := by simp [mul_div],
  left_inv := λ w, begin
    apply_fun b.repr using b.repr.to_equiv.injective,
    apply_fun equiv.finsupp_unique,
    simp only [linear_equiv.map_smulₛₗ, finsupp.coe_smul, finsupp.single_eq_same, ring_hom.id_apply,
      smul_eq_mul, pi.smul_apply, equiv.finsupp_unique_apply],
    exact div_mul_cancel _ h,
  end ,
  right_inv := λ f, begin
    ext,
    simp only [linear_equiv.map_smulₛₗ, finsupp.coe_smul, finsupp.single_eq_same, ring_hom.id_apply,
      smul_eq_mul, pi.smul_apply],
    exact mul_div_cancel _ h,
  end, }

@[simp] lemma basis_singleton_apply (ι : Type*) [unique ι]
  (h : finrank K V = 1) (v : V) (hv : v ≠ 0) (i : ι) :
  basis_singleton ι h v hv i = v :=
by { cases unique.uniq ‹unique ι› i, simp [basis_singleton], }

@[simp] lemma range_basis_singleton (ι : Type*) [unique ι]
  (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
  set.range (basis_singleton ι h v hv) = {v} :=
by rw [set.range_unique, basis_singleton_apply]

end division_ring

end finite_dimensional

variables {K V}

section zero_dim

variables [division_ring K] [add_comm_group V] [module K V]

open finite_dimensional

lemma finite_dimensional_of_dim_eq_zero (h : module.rank K V = 0) : finite_dimensional K V :=
begin
  dsimp [finite_dimensional],
  rw [← is_noetherian.iff_fg, is_noetherian.iff_dim_lt_omega, h],
  exact cardinal.omega_pos
end

lemma finite_dimensional_of_dim_eq_one (h : module.rank K V = 1) : finite_dimensional K V :=
begin
  dsimp [finite_dimensional],
  rw [← is_noetherian.iff_fg, is_noetherian.iff_dim_lt_omega, h],
  exact one_lt_omega
end

lemma finrank_eq_zero_of_dim_eq_zero [finite_dimensional K V] (h : module.rank K V = 0) :
  finrank K V = 0 :=
begin
  convert finrank_eq_dim K V,
  rw h, norm_cast
end

lemma finrank_eq_zero_of_basis_imp_not_finite
  (h : ∀ s : set V, basis.{v} (s : set V) K V → ¬ s.finite) : finrank K V = 0 :=
dif_neg (λ dim_lt,
  h _ (basis.of_vector_space K V) ((basis.of_vector_space K V).finite_index_of_dim_lt_omega dim_lt))

lemma finrank_eq_zero_of_basis_imp_false
  (h : ∀ s : finset V, basis.{v} (s : set V) K V → false) : finrank K V = 0 :=
finrank_eq_zero_of_basis_imp_not_finite (λ s b hs, h hs.to_finset (by { convert b, simp }))

lemma finrank_eq_zero_of_not_exists_basis
  (h : ¬ (∃ s : finset V, nonempty (basis (s : set V) K V))) : finrank K V = 0 :=
finrank_eq_zero_of_basis_imp_false (λ s b, h ⟨s, ⟨b⟩⟩)

lemma finrank_eq_zero_of_not_exists_basis_finite
  (h : ¬ ∃ (s : set V) (b : basis.{v} (s : set V) K V), s.finite) : finrank K V = 0 :=
finrank_eq_zero_of_basis_imp_not_finite (λ s b hs, h ⟨s, b, hs⟩)

lemma finrank_eq_zero_of_not_exists_basis_finset
  (h : ¬ ∃ (s : finset V), nonempty (basis s K V)) : finrank K V = 0 :=
finrank_eq_zero_of_basis_imp_false (λ s b, h ⟨s, ⟨b⟩⟩)

variables (K V)

instance finite_dimensional_bot : finite_dimensional K (⊥ : submodule K V) :=
finite_dimensional_of_dim_eq_zero $ by simp

@[simp] lemma finrank_bot : finrank K (⊥ : submodule K V) = 0 :=
begin
  convert finrank_eq_dim K (⊥ : submodule K V),
  rw dim_bot, norm_cast
end

variables {K V}

lemma bot_eq_top_of_dim_eq_zero (h : module.rank K V = 0) : (⊥ : submodule K V) = ⊤ :=
begin
  haveI := finite_dimensional_of_dim_eq_zero h,
  apply eq_top_of_finrank_eq,
  rw [finrank_bot, finrank_eq_zero_of_dim_eq_zero h]
end

@[simp] theorem dim_eq_zero {S : submodule K V} : module.rank K S = 0 ↔ S = ⊥ :=
⟨λ h, (submodule.eq_bot_iff _).2 $ λ x hx, congr_arg subtype.val $
  ((submodule.eq_bot_iff _).1 $ eq.symm $ bot_eq_top_of_dim_eq_zero h) ⟨x, hx⟩ submodule.mem_top,
λ h, by rw [h, dim_bot]⟩

@[simp] theorem finrank_eq_zero {S : submodule K V} [finite_dimensional K S] :
  finrank K S = 0 ↔ S = ⊥ :=
by rw [← dim_eq_zero, ← finrank_eq_dim, ← @nat.cast_zero cardinal, cardinal.nat_cast_inj]

end zero_dim

namespace submodule
open is_noetherian finite_dimensional

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional (s : submodule K V) :
  s.fg ↔ finite_dimensional K s :=
⟨λ h, module.finite_def.2 $ (fg_top s).2 h, λ h, (fg_top s).1 $ module.finite_def.1 h⟩

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
lemma finite_dimensional_of_le {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (h : S₁ ≤ S₂) :
  finite_dimensional K S₁ :=
begin
  haveI : is_noetherian K S₂ := iff_fg.2 infer_instance,
  exact iff_fg.1 (is_noetherian.iff_dim_lt_omega.2
    (lt_of_le_of_lt (dim_le_of_submodule _ _ h) (dim_lt_omega K S₂))),
end

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_left (S₁ S₂ : submodule K V) [finite_dimensional K S₁] :
  finite_dimensional K (S₁ ⊓ S₂ : submodule K V) :=
finite_dimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_right (S₁ S₂ : submodule K V) [finite_dimensional K S₂] :
  finite_dimensional K (S₁ ⊓ S₂ : submodule K V) :=
finite_dimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finite_dimensional_sup (S₁ S₂ : submodule K V) [h₁ : finite_dimensional K S₁]
  [h₂ : finite_dimensional K S₂] : finite_dimensional K (S₁ ⊔ S₂ : submodule K V) :=
begin
  unfold finite_dimensional at *,
  rw [finite_def] at *,
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂)),
end

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, finite_dimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finite_dimensional_finset_sup {ι : Type*} (s : finset ι) (S : ι → submodule K V)
  [Π i, finite_dimensional K (S i)] : finite_dimensional K (s.sup S : submodule K V) :=
begin
  refine @finset.sup_induction _ _ _ _ s S (λ i, finite_dimensional K ↥i)
    (finite_dimensional_bot K V) _ (λ i hi, by apply_instance),
  { introsI S₁ hS₁ S₂ hS₂,
    exact submodule.finite_dimensional_sup S₁ S₂ },
end

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
type is finite-dimensional. -/
instance finite_dimensional_supr {ι : Type*} [fintype ι] (S : ι → submodule K V)
  [Π i, finite_dimensional K (S i)] : finite_dimensional K ↥(⨆ i, S i) :=
begin
  rw ←finset.sup_univ_eq_supr,
  exact submodule.finite_dimensional_finset_sup _ _,
end

/-- The submodule generated by a supremum indexed by a proposition is finite-dimensional if
the submodule is. -/
instance finite_dimensional_supr_prop {P : Prop} (S : P → submodule K V)
  [Π h, finite_dimensional K (S h)] : finite_dimensional K ↥(⨆ h, S h) :=
begin
  by_cases hp : P,
  { rw supr_pos hp,
    apply_instance },
  { rw supr_neg hp,
    apply_instance },
end

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
lemma finrank_le [finite_dimensional K V] (s : submodule K V) : finrank K s ≤ finrank K V :=
by simpa only [cardinal.nat_cast_le, ←finrank_eq_dim] using
  s.subtype.dim_le_of_injective (injective_subtype s)

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
lemma finrank_quotient_le [finite_dimensional K V] (s : submodule K V) :
  finrank K (V ⧸ s) ≤ finrank K V :=
by simpa only [cardinal.nat_cast_le, ←finrank_eq_dim] using
  (mkq s).dim_le_of_surjective (surjective_quot_mk _)

end division_ring

section field
variables [field K] [add_comm_group V] [module K V]

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem finrank_quotient_add_finrank [finite_dimensional K V] (s : submodule K V) :
  finrank K (V ⧸ s) + finrank K s = finrank K V :=
begin
  have := dim_quotient_add_dim s,
  rw [← finrank_eq_dim, ← finrank_eq_dim, ← finrank_eq_dim] at this,
  exact_mod_cast this
end

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space. -/
lemma finrank_lt [finite_dimensional K V] {s : submodule K V} (h : s < ⊤) :
  finrank K s < finrank K V :=
begin
  rw [← s.finrank_quotient_add_finrank, add_comm],
  exact nat.lt_add_of_zero_lt_left _ _ (finrank_pos_iff.mpr (quotient.nontrivial_of_lt_top _ h))
end

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem dim_sup_add_dim_inf_eq (s t : submodule K V)
  [finite_dimensional K s] [finite_dimensional K t] :
  finrank K ↥(s ⊔ t) + finrank K ↥(s ⊓ t) = finrank K ↥s + finrank K ↥t :=
begin
  have key : module.rank K ↥(s ⊔ t) + module.rank K ↥(s ⊓ t) =
    module.rank K s + module.rank K t := dim_sup_add_dim_inf_eq s t,
  repeat { rw ←finrank_eq_dim at key },
  norm_cast at key,
  exact key
end

lemma eq_top_of_disjoint [finite_dimensional K V] (s t : submodule K V)
  (hdim : finrank K s + finrank K t = finrank K V)
  (hdisjoint : disjoint s t) : s ⊔ t = ⊤ :=
begin
  have h_finrank_inf : finrank K ↥(s ⊓ t) = 0,
  { rw [disjoint, le_bot_iff] at hdisjoint,
    rw [hdisjoint, finrank_bot] },
  apply eq_top_of_finrank_eq,
  rw ←hdim,
  convert s.dim_sup_add_dim_inf_eq t,
  rw h_finrank_inf,
  refl,
end

end field

end submodule

namespace linear_equiv
open finite_dimensional

variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finite_dimensional (f : V ≃ₗ[K] V₂) [finite_dimensional K V] :
  finite_dimensional K V₂ :=
module.finite.equiv f

variables {R M M₂ : Type*} [ring R] [add_comm_group M] [add_comm_group M₂]
variables [module R M] [module R M₂]

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem finrank_eq (f : M ≃ₗ[R] M₂) : finrank R M = finrank R M₂ :=
by { unfold finrank, rw [← cardinal.to_nat_lift, f.lift_dim_eq, cardinal.to_nat_lift] }

/-- Pushforwards of finite-dimensional submodules along a `linear_equiv` have the same finrank. -/
lemma finrank_map_eq (f : M ≃ₗ[R] M₂) (p : submodule R M) :
  finrank R (p.map (f : M →ₗ[R] M₂)) = finrank R p :=
(f.submodule_map p).finrank_eq.symm

end linear_equiv

section
variables [division_ring K] [add_comm_group V] [module K V]

instance finite_dimensional_finsupp {ι : Type*} [fintype ι] [h : finite_dimensional K V] :
  finite_dimensional K (ι →₀ V) :=
begin
  letI : is_noetherian K V := is_noetherian.iff_fg.2 infer_instance,
  exact (finsupp.linear_equiv_fun_on_fintype K V ι).symm.finite_dimensional
end

end

namespace finite_dimensional

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_of_finrank_eq [finite_dimensional K V] [finite_dimensional K V₂]
  (cond : finrank K V = finrank K V₂) : nonempty (V ≃ₗ[K] V₂) :=
nonempty_linear_equiv_of_lift_dim_eq $ by simp only [← finrank_eq_dim, cond, lift_nat_cast]

/--
Two finite-dimensional vector spaces are isomorphic if and only if they have the same (finite)
dimension.
-/
theorem nonempty_linear_equiv_iff_finrank_eq [finite_dimensional K V] [finite_dimensional K V₂] :
   nonempty (V ≃ₗ[K] V₂) ↔ finrank K V = finrank K V₂ :=
⟨λ ⟨h⟩, h.finrank_eq, λ h, nonempty_linear_equiv_of_finrank_eq h⟩

variables (V V₂)

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
noncomputable def linear_equiv.of_finrank_eq [finite_dimensional K V] [finite_dimensional K V₂]
  (cond : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
classical.choice $ nonempty_linear_equiv_of_finrank_eq cond

variables {V}

lemma eq_of_le_of_finrank_le {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (hle : S₁ ≤ S₂)
  (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ :=
begin
  rw ←linear_equiv.finrank_eq (submodule.comap_subtype_equiv_of_le hle) at hd,
  exact le_antisymm hle (submodule.comap_subtype_eq_top.1 (eq_top_of_finrank_eq
    (le_antisymm (comap (submodule.subtype S₂) S₁).finrank_le hd))),
end

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
lemma eq_of_le_of_finrank_eq {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (hle : S₁ ≤ S₂)
  (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
eq_of_le_of_finrank_le hle hd.ge

@[simp]
lemma finrank_map_subtype_eq (p : submodule K V) (q : submodule K p) :
  finite_dimensional.finrank K (q.map p.subtype) = finite_dimensional.finrank K q :=
(submodule.equiv_subtype_map p q).symm.finrank_eq

end division_ring

section field
variables [field K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

variables [finite_dimensional K V] [finite_dimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def linear_equiv.quot_equiv_of_equiv
  {p : subspace K V} {q : subspace K V₂}
  (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] (V₂ ⧸ q) :=
linear_equiv.of_finrank_eq _ _
begin
  rw [← @add_right_cancel_iff _ _ (finrank K p), submodule.finrank_quotient_add_finrank,
      linear_equiv.finrank_eq f₁, submodule.finrank_quotient_add_finrank,
      linear_equiv.finrank_eq f₂],
end

/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def linear_equiv.quot_equiv_of_quot_equiv
  {p q : subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) : (V ⧸ q) ≃ₗ[K] p :=
linear_equiv.of_finrank_eq _ _
begin
  rw [← @add_right_cancel_iff _ _ (finrank K q), submodule.finrank_quotient_add_finrank,
      ← linear_equiv.finrank_eq f, add_comm, submodule.finrank_quotient_add_finrank]
end

end field

end finite_dimensional

namespace linear_map
open finite_dimensional

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/-- On a finite-dimensional space, an injective linear map is surjective. -/
lemma surjective_of_injective [finite_dimensional K V] {f : V →ₗ[K] V}
  (hinj : injective f) : surjective f :=
begin
  have h := dim_eq_of_injective _ hinj,
  rw [← finrank_eq_dim, ← finrank_eq_dim, nat_cast_inj] at h,
  exact range_eq_top.1 (eq_top_of_finrank_eq h.symm)
end

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
lemma finite_dimensional_of_surjective [h : finite_dimensional K V]
  (f : V →ₗ[K] V₂) (hf : f.range = ⊤) : finite_dimensional K V₂ :=
module.finite.of_surjective f $ range_eq_top.1 hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_range [h : finite_dimensional K V] (f : V →ₗ[K] V₂) :
  finite_dimensional K f.range :=
f.quot_ker_equiv_range.finite_dimensional

/-- The dimensions of the domain and range of an injective linear map are equal. -/
lemma finrank_range_of_inj {f : V →ₗ[K] V₂} (hf : function.injective f) :
  finrank K f.range = finrank K V :=
by rw (linear_equiv.of_injective f hf).finrank_eq

end division_ring

section field
variables [field K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
lemma injective_iff_surjective [finite_dimensional K V] {f : V →ₗ[K] V} :
  injective f ↔ surjective f :=
⟨surjective_of_injective,
  λ hsurj, let ⟨g, hg⟩ := f.exists_right_inverse_of_surjective (range_eq_top.2 hsurj) in
  have function.right_inverse g f, from linear_map.ext_iff.1 hg,
  (left_inverse_of_surjective_of_right_inverse
    (surjective_of_injective this.injective) this).injective⟩

lemma ker_eq_bot_iff_range_eq_top [finite_dimensional K V] {f : V →ₗ[K] V} :
  f.ker = ⊥ ↔ f.range = ⊤ :=
by rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
lemma mul_eq_one_of_mul_eq_one [finite_dimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) :
  g * f = 1 :=
have ginj : injective g, from has_left_inverse.injective
  ⟨f, (λ x, show (f * g) x = (1 : V →ₗ[K] V) x, by rw hfg; refl)⟩,
let ⟨i, hi⟩ := g.exists_right_inverse_of_surjective
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

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem finrank_range_add_finrank_ker [finite_dimensional K V] (f : V →ₗ[K] V₂) :
  finrank K f.range + finrank K f.ker = finrank K V :=
by { rw [← f.quot_ker_equiv_range.finrank_eq], exact submodule.finrank_quotient_add_finrank _ }

end field
end linear_map

namespace linear_equiv
open finite_dimensional

variables [field K] [add_comm_group V] [module K V]
variables [finite_dimensional K V]

/-- The linear equivalence corresponging to an injective endomorphism. -/
noncomputable def of_injective_endo (f : V →ₗ[K] V) (h_inj : injective f) : V ≃ₗ[K] V :=
linear_equiv.of_bijective f h_inj $ linear_map.injective_iff_surjective.mp h_inj

@[simp] lemma coe_of_injective_endo (f : V →ₗ[K] V) (h_inj : injective f) :
  ⇑(of_injective_endo f h_inj) = f := rfl

@[simp] lemma of_injective_endo_right_inv (f : V →ₗ[K] V) (h_inj : injective f) :
  f * (of_injective_endo f h_inj).symm = 1 :=
linear_map.ext $ (of_injective_endo f h_inj).apply_symm_apply

@[simp] lemma of_injective_endo_left_inv (f : V →ₗ[K] V) (h_inj : injective f) :
  ((of_injective_endo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
linear_map.ext $ (of_injective_endo f h_inj).symm_apply_apply

end linear_equiv

namespace linear_map

variables [field K] [add_comm_group V] [module K V]

lemma is_unit_iff_ker_eq_bot [finite_dimensional K V] (f : V →ₗ[K] V): is_unit f ↔ f.ker = ⊥ :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    exact linear_map.ker_eq_bot_of_inverse u.inv_mul },
  { intro h_inj, rw ker_eq_bot at h_inj,
    exact ⟨⟨f, (linear_equiv.of_injective_endo f h_inj).symm.to_linear_map,
      linear_equiv.of_injective_endo_right_inv f h_inj,
      linear_equiv.of_injective_endo_left_inv f h_inj⟩, rfl⟩ }
end

lemma is_unit_iff_range_eq_top [finite_dimensional K V] (f : V →ₗ[K] V): is_unit f ↔ f.range = ⊤ :=
by rw [is_unit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top]

end linear_map

open module finite_dimensional

section
variables [division_ring K] [add_comm_group V] [module K V]

section top

@[simp]
theorem finrank_top : finrank K (⊤ : submodule K V) = finrank K V :=
by { unfold finrank, simp [dim_top] }

end top

lemma finrank_zero_iff_forall_zero [finite_dimensional K V] :
  finrank K V = 0 ↔ ∀ x : V, x = 0 :=
finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
noncomputable def basis_of_finrank_zero [finite_dimensional K V]
  {ι : Type*} [is_empty ι] (hV : finrank K V = 0) :
  basis ι K V :=
begin
  haveI : subsingleton V := finrank_zero_iff.1 hV,
  exact basis.empty _
end

end

namespace linear_map

variables [field K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

theorem injective_iff_surjective_of_finrank_eq_finrank [finite_dimensional K V]
  [finite_dimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
  function.injective f ↔ function.surjective f :=
begin
  have := finrank_range_add_finrank_ker f,
  rw [← ker_eq_bot, ← range_eq_top], refine ⟨λ h, _, λ h, _⟩,
  { rw [h, finrank_bot, add_zero, H] at this, exact eq_top_of_finrank_eq this },
  { rw [h, finrank_top, H] at this, exact finrank_eq_zero.1 (add_right_injective _ this) }
end

lemma ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [finite_dimensional K V]
  [finite_dimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
  f.ker = ⊥ ↔ f.range = ⊤ :=
by rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]

theorem finrank_le_finrank_of_injective [finite_dimensional K V] [finite_dimensional K V₂]
  {f : V →ₗ[K] V₂} (hf : function.injective f) : finrank K V ≤ finrank K V₂ :=
calc  finrank K V
    = finrank K f.range + finrank K f.ker : (finrank_range_add_finrank_ker f).symm
... = finrank K f.range : by rw [ker_eq_bot.2 hf, finrank_bot, add_zero]
... ≤ finrank K V₂ : submodule.finrank_le _

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linear_equiv_of_injective` is the induced isomorphism
between the two vector spaces. -/
noncomputable def linear_equiv_of_injective
  [finite_dimensional K V] [finite_dimensional K V₂]
  (f : V →ₗ[K] V₂) (hf : injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
linear_equiv.of_bijective f hf $
  (linear_map.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf

@[simp] lemma linear_equiv_of_injective_apply
  [finite_dimensional K V] [finite_dimensional K V₂]
  {f : V →ₗ[K] V₂} (hf : injective f) (hdim : finrank K V = finrank K V₂) (x : V) :
  f.linear_equiv_of_injective hf hdim x = f x := rfl

end linear_map

namespace alg_hom

lemma bijective {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
  [finite_dimensional F E] (ϕ : E →ₐ[F] E) : function.bijective ϕ :=
have inj : function.injective ϕ.to_linear_map := ϕ.to_ring_hom.injective,
⟨inj, (linear_map.injective_iff_surjective_of_finrank_eq_finrank rfl).mp inj⟩

end alg_hom

/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable def alg_equiv_equiv_alg_hom (F : Type u) [field F] (E : Type v) [field E]
  [algebra F E] [finite_dimensional F E] : (E ≃ₐ[F] E) ≃ (E →ₐ[F] E) :=
{ to_fun := λ ϕ, ϕ.to_alg_hom,
  inv_fun := λ ϕ, alg_equiv.of_bijective ϕ ϕ.bijective,
  left_inv := λ _, by {ext, refl},
  right_inv := λ _, by {ext, refl} }

section

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def division_ring_of_finite_dimensional
  (F K : Type*) [field F] [ring K] [is_domain K]
  [algebra F K] [finite_dimensional F K] : division_ring K :=
{ inv := λ x, if H : x = 0 then 0 else classical.some $
    (show function.surjective (algebra.lmul_left F x), from
      linear_map.injective_iff_surjective.1 $ λ _ _, (mul_right_inj' H).1) 1,
  mul_inv_cancel := λ x hx, show x * dite _ _ _ = _, by { rw dif_neg hx,
    exact classical.some_spec ((show function.surjective (algebra.lmul_left F x), from
      linear_map.injective_iff_surjective.1 $ λ _ _, (mul_right_inj' hx).1) 1) },
  inv_zero := dif_pos rfl,
  .. ‹is_domain K›,
  .. ‹ring K› }

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def field_of_finite_dimensional
  (F K : Type*) [field F] [comm_ring K] [is_domain K]
  [algebra F K] [finite_dimensional F K] : field K :=
{ .. division_ring_of_finite_dimensional F K,
  .. ‹comm_ring K› }

end

namespace submodule

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

lemma lt_of_le_of_finrank_lt_finrank {s t : submodule K V}
  (le : s ≤ t) (lt : finrank K s < finrank K t) : s < t :=
lt_of_le_of_ne le (λ h, ne_of_lt lt (by rw h))

lemma lt_top_of_finrank_lt_finrank {s : submodule K V}
  (lt : finrank K s < finrank K V) : s < ⊤ :=
begin
  rw ← @finrank_top K V at lt,
  exact lt_of_le_of_finrank_lt_finrank le_top lt
end

lemma finrank_mono [finite_dimensional K V] :
  monotone (λ (s : submodule K V), finrank K s) :=
λ s t hst,
calc finrank K s = finrank K (comap t.subtype s)
  : linear_equiv.finrank_eq (comap_subtype_equiv_of_le hst).symm
... ≤ finrank K t : submodule.finrank_le _

end division_ring

section field
variables [field K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

lemma finrank_lt_finrank_of_lt [finite_dimensional K V] {s t : submodule K V} (hst : s < t) :
  finrank K s < finrank K t :=
begin
  rw linear_equiv.finrank_eq (comap_subtype_equiv_of_le (le_of_lt hst)).symm,
  refine finrank_lt (lt_of_le_of_ne le_top _),
  intro h_eq_top,
  rw comap_subtype_eq_top at h_eq_top,
  apply not_le_of_lt hst h_eq_top,
end

lemma finrank_add_eq_of_is_compl
  [finite_dimensional K V] {U W : submodule K V} (h : is_compl U W) :
  finrank K U + finrank K W = finrank K V :=
begin
  rw [← submodule.dim_sup_add_dim_inf_eq, top_le_iff.1 h.2, le_bot_iff.1 h.1,
      finrank_bot, add_zero],
  exact finrank_top
end

end field

end submodule

section span

open submodule

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]

variable (K)

/-- The rank of a set of vectors as a natural number. -/
protected noncomputable def set.finrank (s : set V) : ℕ := finrank K (span K s)

variable {K}

lemma finrank_span_le_card (s : set V) [fin : fintype s] :
  finrank K (span K s) ≤ s.to_finset.card :=
begin
  haveI := span_of_finite K ⟨fin⟩,
  have : module.rank K (span K s) ≤ #s := dim_span_le s,
  rw [←finrank_eq_dim, cardinal.mk_fintype, ←set.to_finset_card] at this,
  exact_mod_cast this,
end

lemma finrank_span_finset_le_card (s : finset V)  :
  (s : set V).finrank K ≤ s.card :=
calc (s : set V).finrank K ≤ (s : set V).to_finset.card : finrank_span_le_card s
                                ... = s.card : by simp

lemma finrank_span_eq_card {ι : Type*} [fintype ι] {b : ι → V}
  (hb : linear_independent K b) :
  finrank K (span K (set.range b)) = fintype.card ι :=
begin
  haveI : finite_dimensional K (span K (set.range b)) := span_of_finite K (set.finite_range b),
  have : module.rank K (span K (set.range b)) = #(set.range b) := dim_span hb,
  rwa [←finrank_eq_dim, ←lift_inj, mk_range_eq_of_injective hb.injective,
    cardinal.mk_fintype, lift_nat_cast, lift_nat_cast, nat_cast_inj] at this,
end

lemma finrank_span_set_eq_card (s : set V) [fin : fintype s]
  (hs : linear_independent K (coe : s → V)) :
  finrank K (span K s) = s.to_finset.card :=
begin
  haveI := span_of_finite K ⟨fin⟩,
  have : module.rank K (span K s) = #s := dim_span_set hs,
  rw [←finrank_eq_dim, cardinal.mk_fintype, ←set.to_finset_card] at this,
  exact_mod_cast this,
end

lemma finrank_span_finset_eq_card (s : finset V)
  (hs : linear_independent K (coe : s → V)) :
  finrank K (span K (s : set V)) = s.card :=
begin
  convert finrank_span_set_eq_card ↑s hs,
  ext,
  simp,
end

lemma span_lt_of_subset_of_card_lt_finrank {s : set V} [fintype s] {t : submodule K V}
  (subset : s ⊆ t) (card_lt : s.to_finset.card < finrank K t) : span K s < t :=
lt_of_le_of_finrank_lt_finrank
  (span_le.mpr subset)
  (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

lemma span_lt_top_of_card_lt_finrank {s : set V} [fintype s]
  (card_lt : s.to_finset.card < finrank K V) : span K s < ⊤ :=
lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

lemma finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 :=
begin
  apply le_antisymm,
  { exact finrank_span_le_card ({v} : set V) },
  { rw [nat.succ_le_iff, finrank_pos_iff],
    use [⟨v, mem_span_singleton_self v⟩, 0],
    simp [hv] }
end

end division_ring

section field
variables [field K] [add_comm_group V] [module K V]

lemma set.finrank_mono [finite_dimensional K V] {s t : set V} (h : s ⊆ t) :
  s.finrank K ≤ t.finrank K := finrank_mono (span_mono h)

end field

end span

section basis

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]

lemma linear_independent_of_span_eq_top_of_card_eq_finrank {ι : Type*} [fintype ι] {b : ι → V}
  (span_eq : span K (set.range b) = ⊤) (card_eq : fintype.card ι = finrank K V) :
  linear_independent K b :=
linear_independent_iff'.mpr $ λ s g dependent i i_mem_s,
begin
  by_contra gx_ne_zero,
  -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
  -- spans a vector space of dimension `n`.
  refine ne_of_lt (span_lt_top_of_card_lt_finrank
    (show (b '' (set.univ \ {i})).to_finset.card < finrank K V, from _)) _,
  { calc (b '' (set.univ \ {i})).to_finset.card = ((set.univ \ {i}).to_finset.image b).card
      : by rw [set.to_finset_card, fintype.card_of_finset]
    ... ≤ (set.univ \ {i}).to_finset.card : finset.card_image_le
    ... = (finset.univ.erase i).card : congr_arg finset.card (finset.ext (by simp [and_comm]))
    ... < finset.univ.card : finset.card_erase_lt_of_mem (finset.mem_univ i)
    ... = finrank K V : card_eq },

  -- We already have that `b '' univ` spans the whole space,
  -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
  refine trans (le_antisymm (span_mono (set.image_subset_range _ _)) (span_le.mpr _)) span_eq,
  rintros _ ⟨j, rfl, rfl⟩,
  -- The case that `j ≠ i` is easy because `b j ∈ b '' (univ \ {i})`.
  by_cases j_eq : j = i,
  swap,
  { refine subset_span ⟨j, (set.mem_diff _).mpr ⟨set.mem_univ _, _⟩, rfl⟩,
    exact mt set.mem_singleton_iff.mp j_eq },

  -- To show `b i ∈ span (b '' (univ \ {i}))`, we use that it's a weighted sum
  -- of the other `b j`s.
  rw [j_eq, set_like.mem_coe, show b i = -((g i)⁻¹ • (s.erase i).sum (λ j, g j • b j)), from _],
  { refine neg_mem (smul_mem _ _ (sum_mem (λ k hk, _))),
    obtain ⟨k_ne_i, k_mem⟩ := finset.mem_erase.mp hk,
    refine smul_mem _ _ (subset_span ⟨k, _, rfl⟩),
    simpa using k_mem },

  -- To show `b i` is a weighted sum of the other `b j`s, we'll rewrite this sum
  -- to have the form of the assumption `dependent`.
  apply eq_neg_of_add_eq_zero_left,
  calc b i + (g i)⁻¹ • (s.erase i).sum (λ j, g j • b j)
      = (g i)⁻¹ • (g i • b i + (s.erase i).sum (λ j, g j • b j))
    : by rw [smul_add, ←mul_smul, inv_mul_cancel gx_ne_zero, one_smul]
  ... = (g i)⁻¹ • 0 : congr_arg _ _
  ... = 0           : smul_zero _,
  -- And then it's just a bit of manipulation with finite sums.
  rwa [← finset.insert_erase i_mem_s, finset.sum_insert (finset.not_mem_erase _ _)] at dependent
end

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
lemma linear_independent_iff_card_eq_finrank_span {ι : Type*} [fintype ι] {b : ι → V} :
  linear_independent K b ↔ fintype.card ι = (set.range b).finrank K :=
begin
  split,
  { intro h,
    exact (finrank_span_eq_card h).symm },
  { intro hc,
    let f := (submodule.subtype (span K (set.range b))),
    let b' : ι → span K (set.range b) :=
      λ i, ⟨b i, mem_span.2 (λ p hp, hp (set.mem_range_self _))⟩,
    have hs : span K (set.range b') = ⊤,
    { rw eq_top_iff',
      intro x,
      have h : span K (f '' (set.range b')) = map f (span K (set.range b')) := span_image f,
      have hf : f '' (set.range b') = set.range b, { ext x, simp [set.mem_image, set.mem_range] },
      rw hf at h,
      have hx : (x : V) ∈ span K (set.range b) := x.property,
      conv at hx { congr, skip, rw h },
      simpa [mem_map] using hx },
    have hi : f.ker = ⊥ := ker_subtype _,
    convert (linear_independent_of_span_eq_top_of_card_eq_finrank hs hc).map' _ hi }
end

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basis_of_span_eq_top_of_card_eq_finrank {ι : Type*} [fintype ι] (b : ι → V)
  (span_eq : span K (set.range b) = ⊤) (card_eq : fintype.card ι = finrank K V) :
  basis ι K V :=
basis.mk (linear_independent_of_span_eq_top_of_card_eq_finrank span_eq card_eq) span_eq

@[simp] lemma coe_basis_of_span_eq_top_of_card_eq_finrank {ι : Type*} [fintype ι] (b : ι → V)
  (span_eq : span K (set.range b) = ⊤) (card_eq : fintype.card ι = finrank K V) :
   ⇑(basis_of_span_eq_top_of_card_eq_finrank b span_eq card_eq) = b :=
basis.coe_mk _ _

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def finset_basis_of_span_eq_top_of_card_eq_finrank {s : finset V}
  (span_eq : span K (s : set V) = ⊤) (card_eq : s.card = finrank K V) :
  basis (s : set V) K V :=
basis_of_span_eq_top_of_card_eq_finrank (coe : (s : set V) → V)
  ((@subtype.range_coe_subtype _ (λ x, x ∈ s)).symm ▸ span_eq)
  (trans (fintype.card_coe _) card_eq)

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def set_basis_of_span_eq_top_of_card_eq_finrank {s : set V} [fintype s]
  (span_eq : span K s = ⊤) (card_eq : s.to_finset.card = finrank K V) :
  basis s K V :=
basis_of_span_eq_top_of_card_eq_finrank (coe : s → V)
  ((@subtype.range_coe_subtype _ s).symm ▸ span_eq)
  (trans s.to_finset_card.symm card_eq)

end division_ring

section field
variables [field K] [add_comm_group V] [module K V]

lemma span_eq_top_of_linear_independent_of_card_eq_finrank
  {ι : Type*} [hι : nonempty ι] [fintype ι] {b : ι → V}
  (lin_ind : linear_independent K b) (card_eq : fintype.card ι = finrank K V) :
  span K (set.range b) = ⊤ :=
begin
  by_cases fin : (finite_dimensional K V),
  { haveI := fin,
    by_contra ne_top,
    have lt_top : span K (set.range b) < ⊤ := lt_of_le_of_ne le_top ne_top,
    exact ne_of_lt (submodule.finrank_lt lt_top) (trans (finrank_span_eq_card lin_ind) card_eq) },
  { exfalso,
    apply ne_of_lt (fintype.card_pos_iff.mpr hι),
    symmetry,
    replace fin := (not_iff_not.2 is_noetherian.iff_fg).2 fin,
    calc fintype.card ι = finrank K V : card_eq
                    ... = 0 : dif_neg (mt is_noetherian.iff_dim_lt_omega.mpr fin) }
end

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def basis_of_linear_independent_of_card_eq_finrank
  {ι : Type*} [nonempty ι] [fintype ι] {b : ι → V}
  (lin_ind : linear_independent K b) (card_eq : fintype.card ι = finrank K V) :
  basis ι K V :=
basis.mk lin_ind $
span_eq_top_of_linear_independent_of_card_eq_finrank lin_ind card_eq

@[simp] lemma coe_basis_of_linear_independent_of_card_eq_finrank
  {ι : Type*} [nonempty ι] [fintype ι] {b : ι → V}
  (lin_ind : linear_independent K b) (card_eq : fintype.card ι = finrank K V) :
  ⇑(basis_of_linear_independent_of_card_eq_finrank lin_ind card_eq) = b :=
basis.coe_mk _ _

/-- A linear independent finset of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def finset_basis_of_linear_independent_of_card_eq_finrank
  {s : finset V} (hs : s.nonempty)
  (lin_ind : linear_independent K (coe : s → V)) (card_eq : s.card = finrank K V) :
  basis s K V :=
@basis_of_linear_independent_of_card_eq_finrank _ _ _ _ _ _
  ⟨(⟨hs.some, hs.some_spec⟩ : s)⟩ _ _
  lin_ind
  (trans (fintype.card_coe _) card_eq)

@[simp] lemma coe_finset_basis_of_linear_independent_of_card_eq_finrank
  {s : finset V} (hs : s.nonempty)
  (lin_ind : linear_independent K (coe : s → V)) (card_eq : s.card = finrank K V) :
  ⇑(finset_basis_of_linear_independent_of_card_eq_finrank hs lin_ind card_eq) = coe :=
basis.coe_mk _ _

/-- A linear independent set of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def set_basis_of_linear_independent_of_card_eq_finrank
  {s : set V} [nonempty s] [fintype s]
  (lin_ind : linear_independent K (coe : s → V)) (card_eq : s.to_finset.card = finrank K V) :
  basis s K V :=
basis_of_linear_independent_of_card_eq_finrank lin_ind (trans s.to_finset_card.symm card_eq)

@[simp] lemma coe_set_basis_of_linear_independent_of_card_eq_finrank
  {s : set V} [nonempty s] [fintype s]
  (lin_ind : linear_independent K (coe : s → V)) (card_eq : s.to_finset.card = finrank K V) :
  ⇑(set_basis_of_linear_independent_of_card_eq_finrank lin_ind card_eq) = coe :=
basis.coe_mk _ _

end field

end basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/
section finrank_eq_one

variables [division_ring K] [add_comm_group V] [module K V]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
lemma finrank_eq_one (v : V) (n : v ≠ 0) (h : ∀ w : V, ∃ c : K, c • v = w) :
  finrank K V = 1 :=
begin
  obtain ⟨b⟩ := (basis.basis_singleton_iff punit).mpr ⟨v, n, h⟩,
  rw [finrank_eq_card_basis b, fintype.card_punit]
end

/--
If every vector is a multiple of some `v : V`, then `V` has dimension at most one.
-/
lemma finrank_le_one (v : V) (h : ∀ w : V, ∃ c : K, c • v = w) :
  finrank K V ≤ 1 :=
begin
  by_cases n : v = 0,
  { subst n,
    convert zero_le_one,
    haveI := subsingleton_of_forall_eq (0 : V) (λ w, by { obtain ⟨c, rfl⟩ := h w, simp, }),
    exact finrank_zero_of_subsingleton, },
  { exact (finrank_eq_one v n h).le, }
end

/--
A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
lemma finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) :
  finrank K V = 1 ↔ span K ({v} : set V) = ⊤ :=
⟨λ h, by simpa using (basis_singleton punit h v nz).span_eq,
  λ s, finrank_eq_card_basis (basis.mk (linear_independent_singleton nz) (by { convert s, simp }))⟩

/--
A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
lemma finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) :
  finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w :=
begin
  rw finrank_eq_one_iff_of_nonzero v nz,
  apply span_singleton_eq_top_iff,
end

/--
A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.
-/
lemma finrank_eq_one_iff (ι : Type*) [unique ι] :
  finrank K V = 1 ↔ nonempty (basis ι K V) :=
begin
  fsplit,
  { intro h,
    haveI := finite_dimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le),
    exact ⟨basis_unique ι h⟩ },
  { rintro ⟨b⟩,
    simpa using finrank_eq_card_basis b }
end

/--
A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
lemma finrank_eq_one_iff' :
  finrank K V = 1 ↔ ∃ (v : V) (n : v ≠ 0), ∀ w : V, ∃ c : K, c • v = w :=
begin
  convert finrank_eq_one_iff punit,
  simp only [exists_prop, eq_iff_iff, ne.def],
  convert (basis.basis_singleton_iff punit).symm,
  funext v,
  simp,
  apply_instance, apply_instance, -- Not sure why this aren't found automatically.
end

/--
A finite dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
lemma finrank_le_one_iff [finite_dimensional K V] :
  finrank K V ≤ 1 ↔ ∃ (v : V), ∀ w : V, ∃ c : K, c • v = w :=
begin
  fsplit,
  { intro h,
    by_cases h' : finrank K V = 0,
    { use 0, intro w, use 0, haveI := finrank_zero_iff.mp h', apply subsingleton.elim, },
    { replace h' := zero_lt_iff.mpr h', have : finrank K V = 1, { linarith },
      obtain ⟨v, -, p⟩ := finrank_eq_one_iff'.mp this,
      use ⟨v, p⟩, }, },
  { rintro ⟨v, p⟩,
    exact finrank_le_one v p, }
end

-- We use the `linear_map.compatible_smul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[field K] [algebra K A] [is_scalar_tower K A V] [is_scalar_tower K A W]`
lemma surjective_of_nonzero_of_finrank_eq_one
  {K : Type*} [division_ring K] {A : Type*} [semiring A]
  [module K V] [module A V]
  {W : Type*} [add_comm_group W] [module K W] [module A W] [linear_map.compatible_smul V W K A]
  (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : surjective f :=
begin
  change surjective (f.restrict_scalars K),
  obtain ⟨v, n⟩ := fun_like.ne_iff.mp w,
  intro z,
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z,
  exact ⟨c • v, by simp⟩,
end

end finrank_eq_one

section subalgebra_dim
open module
variables {F E : Type*} [field F] [field E] [algebra F E]

lemma subalgebra.dim_eq_one_of_eq_bot {S : subalgebra F E} (h : S = ⊥) : module.rank F S = 1 :=
begin
  rw [← S.to_submodule_equiv.dim_eq, h,
    (linear_equiv.of_eq (⊥ : subalgebra F E).to_submodule _ algebra.to_submodule_bot).dim_eq,
    dim_span_set],
  exacts [mk_singleton _, linear_independent_singleton one_ne_zero]
end

@[simp]
lemma subalgebra.dim_bot : module.rank F (⊥ : subalgebra F E) = 1 :=
subalgebra.dim_eq_one_of_eq_bot rfl

lemma subalgebra_top_dim_eq_submodule_top_dim :
  module.rank F (⊤ : subalgebra F E) = module.rank F (⊤ : submodule F E) :=
by { rw ← algebra.top_to_submodule, refl }

lemma subalgebra_top_finrank_eq_submodule_top_finrank :
  finrank F (⊤ : subalgebra F E) = finrank F (⊤ : submodule F E) :=
by { rw ← algebra.top_to_submodule, refl }

lemma subalgebra.dim_top : module.rank F (⊤ : subalgebra F E) = module.rank F E :=
by { rw subalgebra_top_dim_eq_submodule_top_dim, exact dim_top F E }

instance subalgebra.finite_dimensional_bot : finite_dimensional F (⊥ : subalgebra F E) :=
finite_dimensional_of_dim_eq_one subalgebra.dim_bot

@[simp]
lemma subalgebra.finrank_bot : finrank F (⊥ : subalgebra F E) = 1 :=
begin
  have : module.rank F (⊥ : subalgebra F E) = 1 := subalgebra.dim_bot,
  rw ← finrank_eq_dim at this,
  norm_cast at *,
  simp *,
end

lemma subalgebra.finrank_eq_one_of_eq_bot {S : subalgebra F E} (h : S = ⊥) : finrank F S = 1 :=
by { rw h, exact subalgebra.finrank_bot }

lemma subalgebra.eq_bot_of_finrank_one {S : subalgebra F E} (h : finrank F S = 1) : S = ⊥ :=
begin
  rw eq_bot_iff,
  let b : set S := {1},
  have : fintype b := unique.fintype,
  have b_lin_ind : linear_independent F (coe : b → S) := linear_independent_singleton one_ne_zero,
  have b_card : fintype.card b = 1 := fintype.card_of_subsingleton _,
  let hb := set_basis_of_linear_independent_of_card_eq_finrank
    b_lin_ind (by simp only [*, set.to_finset_card]),
  have b_spans := hb.span_eq,
  intros x hx,
  rw [algebra.mem_bot],
  have x_in_span_b : (⟨x, hx⟩ : S) ∈ submodule.span F b,
  { rw [coe_set_basis_of_linear_independent_of_card_eq_finrank, subtype.range_coe] at b_spans,
    rw b_spans,
    exact submodule.mem_top, },
  obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_b,
  replace ha : a • 1 = x := by injections with ha,
  exact ⟨a, by rw [← ha, algebra.smul_def, mul_one]⟩,
end

lemma subalgebra.eq_bot_of_dim_one {S : subalgebra F E} (h : module.rank F S = 1) : S = ⊥ :=
begin
  haveI : finite_dimensional F S := finite_dimensional_of_dim_eq_one h,
  rw ← finrank_eq_dim at h,
  norm_cast at h,
  exact subalgebra.eq_bot_of_finrank_one h,
end

@[simp]
lemma subalgebra.bot_eq_top_of_dim_eq_one (h : module.rank F E = 1) : (⊥ : subalgebra F E) = ⊤ :=
begin
  rw [← dim_top, ← subalgebra_top_dim_eq_submodule_top_dim] at h,
  exact eq.symm (subalgebra.eq_bot_of_dim_one h),
end

@[simp]
lemma subalgebra.bot_eq_top_of_finrank_eq_one (h : finrank F E = 1) : (⊥ : subalgebra F E) = ⊤ :=
begin
  rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank] at h,
  exact eq.symm (subalgebra.eq_bot_of_finrank_one h),
end

@[simp]
theorem subalgebra.dim_eq_one_iff {S : subalgebra F E} : module.rank F S = 1 ↔ S = ⊥ :=
⟨subalgebra.eq_bot_of_dim_one, subalgebra.dim_eq_one_of_eq_bot⟩

@[simp]
theorem subalgebra.finrank_eq_one_iff {S : subalgebra F E} : finrank F S = 1 ↔ S = ⊥ :=
⟨subalgebra.eq_bot_of_finrank_one, subalgebra.finrank_eq_one_of_eq_bot⟩

end subalgebra_dim

namespace module
namespace End

variables [field K] [add_comm_group V] [module K V]

lemma exists_ker_pow_eq_ker_pow_succ [finite_dimensional K V] (f : End K V) :
  ∃ (k : ℕ), k ≤ finrank K V ∧ (f ^ k).ker = (f ^ k.succ).ker :=
begin
  classical,
  by_contradiction h_contra,
  simp_rw [not_exists, not_and] at h_contra,
  have h_le_ker_pow : ∀ (n : ℕ), n ≤ (finrank K V).succ → n ≤ finrank K (f ^ n).ker,
  { intros n hn,
    induction n with n ih,
    { exact zero_le (finrank _ _) },
    { have h_ker_lt_ker : (f ^ n).ker < (f ^ n.succ).ker,
      { refine lt_of_le_of_ne _ (h_contra n (nat.le_of_succ_le_succ hn)),
        rw pow_succ,
        apply linear_map.ker_le_ker_comp },
      have h_finrank_lt_finrank : finrank K (f ^ n).ker < finrank K (f ^ n.succ).ker,
      { apply submodule.finrank_lt_finrank_of_lt h_ker_lt_ker },
      calc
        n.succ ≤ (finrank K ↥(linear_map.ker (f ^ n))).succ :
            nat.succ_le_succ (ih (nat.le_of_succ_le hn))
        ... ≤ finrank K ↥(linear_map.ker (f ^ n.succ)) :
            nat.succ_le_of_lt h_finrank_lt_finrank } },
  have h_le_finrank_V : ∀ n, finrank K (f ^ n).ker ≤ finrank K V :=
    λ n, submodule.finrank_le _,
  have h_any_n_lt: ∀ n, n ≤ (finrank K V).succ → n ≤ finrank K V :=
    λ n hn, (h_le_ker_pow n hn).trans (h_le_finrank_V n),
  show false,
    from nat.not_succ_le_self _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl),
end

lemma ker_pow_constant {f : End K V} {k : ℕ} (h : (f ^ k).ker = (f ^ k.succ).ker) :
  ∀ m, (f ^ k).ker = (f ^ (k + m)).ker
| 0 := by simp
| (m + 1) :=
  begin
    apply le_antisymm,
    { rw [add_comm, pow_add],
      apply linear_map.ker_le_ker_comp },
    { rw [ker_pow_constant m, add_comm m 1, ←add_assoc, pow_add, pow_add f k m],
      change linear_map.ker ((f ^ (k + 1)).comp (f ^ m)) ≤ linear_map.ker ((f ^ k).comp (f ^ m)),
      rw [linear_map.ker_comp, linear_map.ker_comp, h, nat.add_one],
      exact le_rfl, }
  end

lemma ker_pow_eq_ker_pow_finrank_of_le [finite_dimensional K V]
  {f : End K V} {m : ℕ} (hm : finrank K V ≤ m) :
  (f ^ m).ker = (f ^ finrank K V).ker :=
begin
  obtain ⟨k, h_k_le, hk⟩ :
    ∃ k, k ≤ finrank K V ∧ linear_map.ker (f ^ k) = linear_map.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f,
  calc (f ^ m).ker = (f ^ (k + (m - k))).ker :
      by rw add_tsub_cancel_of_le (h_k_le.trans hm)
    ...  = (f ^ k).ker : by rw ker_pow_constant hk _
    ...  = (f ^ (k + (finrank K V - k))).ker : ker_pow_constant hk (finrank K V - k)
    ...  = (f ^ finrank K V).ker : by rw add_tsub_cancel_of_le h_k_le
end

lemma ker_pow_le_ker_pow_finrank [finite_dimensional K V] (f : End K V) (m : ℕ) :
  (f ^ m).ker ≤ (f ^ finrank K V).ker :=
begin
  by_cases h_cases: m < finrank K V,
  { rw [←add_tsub_cancel_of_le (nat.le_of_lt h_cases), add_comm, pow_add],
    apply linear_map.ker_le_ker_comp },
  { rw [ker_pow_eq_ker_pow_finrank_of_le (le_of_not_lt h_cases)],
    exact le_rfl }
end

end End
end module
