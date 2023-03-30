/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.algebra.subalgebra.basic
import field_theory.finiteness
import linear_algebra.free_module.finite.rank
import tactic.interval_cases

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a division ring `K`. There are (at least) three equivalent
definitions of finite-dimensionality of `V`:

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
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `is_noetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian

We make use of `finrank`, the dimension of a finite dimensional space, returning a `nat`, as
opposed to `module.rank`, which returns a `cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`. `finrank` is not defined using `finite_dimensional`.
For basic results that do not need the `finite_dimensional` class, import `linear_algebra.finrank`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `finrank_quotient_add_finrank`)
- linear equivs, in `linear_equiv.finite_dimensional`
- image under a linear map (the rank-nullity formula is in `finrank_range_add_finrank_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `linear_map.mul_eq_one_comm`
and `linear_map.comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

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

instance finite_dimensional_pi {ι : Type*} [_root_.finite ι] : finite_dimensional K (ι → K) :=
iff_fg.1 is_noetherian_pi

instance finite_dimensional_pi' {ι : Type*} [_root_.finite ι] (M : ι → Type*)
  [∀ i, add_comm_group (M i)] [∀ i, module K (M i)] [I : ∀ i, finite_dimensional K (M i)] :
  finite_dimensional K (Π i, M i) :=
begin
  haveI : ∀ i : ι, is_noetherian K (M i) := λ i, iff_fg.2 (I i),
  exact iff_fg.1 is_noetherian_pi
end

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintype_of_fintype [fintype K] [finite_dimensional K V] : fintype V :=
module.fintype_of_fintype (@finset_basis K V _ _ _ (iff_fg.2 infer_instance))

lemma finite_of_finite [_root_.finite K] [finite_dimensional K V] : _root_.finite V :=
by { casesI nonempty_fintype K, haveI := fintype_of_fintype K V, apply_instance }

variables {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
lemma of_fintype_basis {ι : Type w} [_root_.finite ι] (h : basis ι K V) : finite_dimensional K V :=
by { casesI nonempty_fintype ι, exact ⟨⟨finset.univ.image h, by { convert h.span_eq, simp } ⟩⟩ }

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

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_submodule [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K S :=
begin
  letI : is_noetherian K V := iff_fg.2 _,
  exact iff_fg.1
    (is_noetherian.iff_dim_lt_aleph_0.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_aleph_0 K V))),
  apply_instance,
end

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_quotient [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K (V ⧸ S) :=
module.finite.of_surjective (submodule.mkq S) $ surjective_quot_mk _

variables (K V)
/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. -/
lemma finrank_eq_dim [finite_dimensional K V] :
  (finrank K V : cardinal.{v}) = module.rank K V :=
begin
  letI : is_noetherian K V := iff_fg.2 infer_instance,
  rw [finrank, cast_to_nat_of_lt_aleph_0 (dim_lt_aleph_0 K V)]
end
variables {K V}

lemma finrank_of_infinite_dimensional (h : ¬finite_dimensional K V) : finrank K V = 0 :=
dif_neg $ mt is_noetherian.iff_dim_lt_aleph_0.2 $ (not_iff_not.2 iff_fg).2 h

lemma finite_dimensional_of_finrank (h : 0 < finrank K V) : finite_dimensional K V :=
by { contrapose h, simp [finrank_of_infinite_dimensional h] }

lemma finite_dimensional_of_finrank_eq_succ
  {n : ℕ} (hn : finrank K V = n.succ) : finite_dimensional K V :=
finite_dimensional_of_finrank $ by rw hn; exact n.succ_pos

/-- We can infer `finite_dimensional K V` in the presence of `[fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
lemma fact_finite_dimensional_of_finrank_eq_succ
  (n : ℕ) [fact (finrank K V = n + 1)] : finite_dimensional K V :=
finite_dimensional_of_finrank $ by convert nat.succ_pos n; apply fact.out

lemma finite_dimensional_iff_of_rank_eq_nsmul {W} [add_comm_group W] [module K W]
  {n : ℕ} (hn : n ≠ 0) (hVW : module.rank K V = n • module.rank K W) :
  finite_dimensional K V ↔ finite_dimensional K W :=
by simp only [finite_dimensional, ← is_noetherian.iff_fg, is_noetherian.iff_dim_lt_aleph_0, hVW,
  cardinal.nsmul_lt_aleph_0_iff_of_ne_zero hn]

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
lemma finrank_eq_card_basis' [finite_dimensional K V] {ι : Type w} (h : basis ι K V) :
  (finrank K V : cardinal.{w}) = #ι :=
begin
  haveI : is_noetherian K V := iff_fg.2 infer_instance,
  haveI : fintype ι := fintype_basis_index h,
  rw [cardinal.mk_fintype, finrank_eq_card_basis h]
end

/-- Given a basis of a division ring over itself indexed by a type `ι`, then `ι` is `unique`. -/
noncomputable def _root_.basis.unique {ι : Type*} (b : basis ι K K) : unique ι :=
begin
  have A : cardinal.mk ι = ↑(finite_dimensional.finrank K K) :=
    (finite_dimensional.finrank_eq_card_basis' b).symm,
  simp only [cardinal.eq_one_iff_unique, finite_dimensional.finrank_self, algebra_map.coe_one] at A,
  exact nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 A),
end

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
  exact (fin_basis_of_finrank_eq K V h).reindex (equiv.equiv_of_unique _ _)
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
  simpa [← finrank_eq_dim, -module.free.finrank_eq_rank] using
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

lemma lt_aleph_0_of_linear_independent {ι : Type w} [finite_dimensional K V]
  {v : ι → V} (h : linear_independent K v) :
  #ι < ℵ₀ :=
begin
  apply cardinal.lift_lt.1,
  apply lt_of_le_of_lt,
  apply cardinal_lift_le_dim_of_linear_independent h,
  rw [←finrank_eq_dim, cardinal.lift_aleph_0, cardinal.lift_nat_cast],
  apply cardinal.nat_lt_aleph_0,
end

lemma _root_.linear_independent.finite [finite_dimensional K V] {b : set V}
  (h : linear_independent K (λ (x:b), (x:V))) : b.finite :=
cardinal.lt_aleph_0_iff_set_finite.mp (finite_dimensional.lt_aleph_0_of_linear_independent h)

lemma not_linear_independent_of_infinite {ι : Type w} [inf : infinite ι] [finite_dimensional K V]
  (v : ι → V) : ¬ linear_independent K v :=
begin
  intro h_lin_indep,
  have : ¬ ℵ₀ ≤ #ι := not_le.mpr (lt_aleph_0_of_linear_independent h_lin_indep),
  have : ℵ₀ ≤ #ι := infinite_iff.mp inf,
  contradiction
end

/-- A finite dimensional space has positive `finrank` iff it has a nonzero element. -/
lemma finrank_pos_iff_exists_ne_zero [finite_dimensional K V] : 0 < finrank K V ↔ ∃ x : V, x ≠ 0 :=
iff.trans (by { rw ← finrank_eq_dim, norm_cast }) (@dim_pos_iff_exists_ne_zero K V _ _ _ _ _)

/-- A finite dimensional space has positive `finrank` iff it is nontrivial. -/
lemma finrank_pos_iff [finite_dimensional K V] : 0 < finrank K V ↔ nontrivial V :=
iff.trans (by { rw ← finrank_eq_dim, norm_cast }) (@dim_pos_iff_nontrivial K V _ _ _ _ _)

/-- A nontrivial finite dimensional space has positive `finrank`. -/
lemma finrank_pos [finite_dimensional K V] [h : nontrivial V] : 0 < finrank K V :=
finrank_pos_iff.mpr h

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `dim_zero_iff`. -/
lemma finrank_zero_iff [finite_dimensional K V] :
  finrank K V = 0 ↔ subsingleton V :=
iff.trans (by { rw ← finrank_eq_dim, norm_cast }) (@dim_zero_iff K V _ _ _ _ _)

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

instance finite_dimensional_self : finite_dimensional K K :=
by apply_instance

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
  unfreezingI { rw [finite_dimensional, ← iff_fg, is_noetherian.iff_dim_lt_aleph_0] at h ⊢ },
  rw [← cardinal.lift_lt.{v' v}],
  rw [← cardinal.lift_lt.{v v'}] at h,
  rw [cardinal.lift_aleph_0] at h ⊢,
  exact (lift_dim_map_le f p).trans_lt h
end

/-- Pushforwards of finite-dimensional submodules have a smaller finrank. -/
lemma finrank_map_le (f : V →ₗ[K] V₂) (p : submodule K V) [finite_dimensional K p] :
  finrank K (p.map f) ≤ finrank K p :=
by simpa [← finrank_eq_dim, -module.free.finrank_eq_rank] using lift_dim_map_le f p

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
  suffices : #{i // p i ≠ ⊥} < (ℵ₀ : cardinal.{w}),
  { rw cardinal.lt_aleph_0_iff_fintype at this,
    exact this.some },
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux _,
  simp [cardinal.nat_lt_aleph_0],
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

lemma finite_dimensional_of_dim_eq_nat {n : ℕ} (h : module.rank K V = n) : finite_dimensional K V :=
begin
  rw [finite_dimensional, ← is_noetherian.iff_fg, is_noetherian.iff_dim_lt_aleph_0, h],
  exact nat_lt_aleph_0 n,
end
/- TODO: generalize to free modules over general rings. -/

lemma finite_dimensional_of_dim_eq_zero (h : module.rank K V = 0) : finite_dimensional K V :=
finite_dimensional_of_dim_eq_nat $ h.trans nat.cast_zero.symm

lemma finite_dimensional_of_dim_eq_one (h : module.rank K V = 1) : finite_dimensional K V :=
finite_dimensional_of_dim_eq_nat $ h.trans nat.cast_one.symm

lemma finrank_eq_zero_of_dim_eq_zero [finite_dimensional K V] (h : module.rank K V = 0) :
  finrank K V = 0 :=
begin
  convert finrank_eq_dim K V,
  rw h, norm_cast
end

variables (K V)

instance finite_dimensional_bot : finite_dimensional K (⊥ : submodule K V) :=
finite_dimensional_of_dim_eq_zero $ by simp

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
  exact iff_fg.1 (is_noetherian.iff_dim_lt_aleph_0.2
    (lt_of_le_of_lt (dim_le_of_submodule _ _ h) (dim_lt_aleph_0 K S₂))),
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
instance finite_dimensional_supr {ι : Type*} [_root_.finite ι] (S : ι → submodule K V)
  [Π i, finite_dimensional K (S i)] : finite_dimensional K ↥(⨆ i, S i) :=
begin
  casesI nonempty_fintype ι,
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

lemma dim_add_le_dim_add_dim (s t : submodule K V)
  [finite_dimensional K s] [finite_dimensional K t] :
  finrank K (s ⊔ t : submodule K V) ≤ finrank K s + finrank K t :=
by { rw [← dim_sup_add_dim_inf_eq], exact self_le_add_right _ _ }

lemma eq_top_of_disjoint [finite_dimensional K V] (s t : submodule K V)
  (hdim : finrank K s + finrank K t = finrank K V)
  (hdisjoint : disjoint s t) : s ⊔ t = ⊤ :=
begin
  have h_finrank_inf : finrank K ↥(s ⊓ t) = 0,
  { rw [disjoint_iff_inf_le, le_bot_iff] at hdisjoint,
    rw [hdisjoint, finrank_bot] },
  apply eq_top_of_finrank_eq,
  rw ←hdim,
  convert s.dim_sup_add_dim_inf_eq t,
  rw h_finrank_inf,
  refl,
end

end division_ring

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

end linear_equiv

section
variables [division_ring K] [add_comm_group V] [module K V]

instance finite_dimensional_finsupp {ι : Type*} [_root_.finite ι] [h : finite_dimensional K V] :
  finite_dimensional K (ι →₀ V) :=
(finsupp.linear_equiv_fun_on_finite K V ι).symm.finite_dimensional

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

variables {V₂} [finite_dimensional K V] [finite_dimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def linear_equiv.quot_equiv_of_equiv
  {p : subspace K V} {q : subspace K V₂}
  (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] (V₂ ⧸ q) :=
linear_equiv.of_finrank_eq _ _
begin
  rw [← @add_right_cancel_iff _ _ _ (finrank K p), submodule.finrank_quotient_add_finrank,
      linear_equiv.finrank_eq f₁, submodule.finrank_quotient_add_finrank,
      linear_equiv.finrank_eq f₂],
end
/- TODO: generalize to the case where one of `p` and `q` is finite-dimensional. -/

/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def linear_equiv.quot_equiv_of_quot_equiv
  {p q : subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) : (V ⧸ q) ≃ₗ[K] p :=
linear_equiv.of_finrank_eq _ _ $ add_right_cancel $ by rw [submodule.finrank_quotient_add_finrank,
  ← linear_equiv.finrank_eq f, add_comm, submodule.finrank_quotient_add_finrank]

end division_ring

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
lemma finite_dimensional_of_surjective [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (hf : f.range = ⊤) : finite_dimensional K V₂ :=
module.finite.of_surjective f $ range_eq_top.1 hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_range [finite_dimensional K V] (f : V →ₗ[K] V₂) :
  finite_dimensional K f.range :=
f.quot_ker_equiv_range.finite_dimensional

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

end division_ring
end linear_map

namespace linear_equiv
open finite_dimensional

variables [division_ring K] [add_comm_group V] [module K V]
variables [finite_dimensional K V]

/-- The linear equivalence corresponging to an injective endomorphism. -/
noncomputable def of_injective_endo (f : V →ₗ[K] V) (h_inj : injective f) : V ≃ₗ[K] V :=
linear_equiv.of_bijective f ⟨h_inj, linear_map.injective_iff_surjective.mp h_inj⟩

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

variables [division_ring K] [add_comm_group V] [module K V]

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

variables [division_ring K] [add_comm_group V] [module K V]
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
linear_equiv.of_bijective f ⟨hf,
  (linear_map.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

@[simp] lemma linear_equiv_of_injective_apply
  [finite_dimensional K V] [finite_dimensional K V₂]
  {f : V →ₗ[K] V₂} (hf : injective f) (hdim : finrank K V = finrank K V₂) (x : V) :
  f.linear_equiv_of_injective hf hdim x = f x := rfl

end linear_map

section

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def division_ring_of_finite_dimensional
  (F K : Type*) [field F] [ring K] [is_domain K]
  [algebra F K] [finite_dimensional F K] : division_ring K :=
{ inv := λ x, if H : x = 0 then 0 else classical.some $
    (show function.surjective (linear_map.mul_left F x), from
      linear_map.injective_iff_surjective.1 $ λ _ _, (mul_right_inj' H).1) 1,
  mul_inv_cancel := λ x hx, show x * dite _ _ _ = _, by { rw dif_neg hx,
    exact classical.some_spec ((show function.surjective (linear_map.mul_left F x), from
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

lemma eq_top_of_finrank_eq [finite_dimensional K V] {S : submodule K V}
  (h : finrank K S = finrank K V) :
  S = ⊤ := finite_dimensional.eq_of_le_of_finrank_eq le_top (by simp [h, finrank_top])

lemma finrank_le_finrank_of_le {s t : submodule K V} [finite_dimensional K t]
  (hst : s ≤ t) : finrank K s ≤ finrank K t :=
calc  finrank K s = finrank K (comap t.subtype s) : (comap_subtype_equiv_of_le hst).finrank_eq.symm
... ≤ finrank K t : finrank_le _

lemma finrank_mono [finite_dimensional K V] :
  monotone (λ (s : submodule K V), finrank K s) :=
λ s t, finrank_le_finrank_of_le

lemma finrank_lt_finrank_of_lt {s t : submodule K V} [finite_dimensional K t]
  (hst : s < t) : finrank K s < finrank K t :=
(comap_subtype_equiv_of_le hst.le).finrank_eq.symm.trans_lt $
  finrank_lt (le_top.lt_of_ne $ hst.not_le ∘ comap_subtype_eq_top.1)

lemma finrank_strict_mono [finite_dimensional K V] :
  strict_mono (λ s : submodule K V, finrank K s) :=
λ s t, finrank_lt_finrank_of_lt

lemma finrank_add_eq_of_is_compl
  [finite_dimensional K V] {U W : submodule K V} (h : is_compl U W) :
  finrank K U + finrank K W = finrank K V :=
begin
  rw [← dim_sup_add_dim_inf_eq, h.codisjoint.eq_top, h.disjoint.eq_bot, finrank_bot, add_zero],
  exact finrank_top
end

end division_ring

end submodule

section division_ring

variables [division_ring K] [add_comm_group V] [module K V]

section span
open submodule

lemma finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 :=
begin
  apply le_antisymm,
  { exact finrank_span_le_card ({v} : set V) },
  { rw [nat.succ_le_iff, finrank_pos_iff],
    use [⟨v, mem_span_singleton_self v⟩, 0],
    simp [hv] }
end

lemma set.finrank_mono [finite_dimensional K V] {s t : set V} (h : s ⊆ t) :
  s.finrank K ≤ t.finrank K := finrank_mono (span_mono h)

end span

section basis

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
                    ... = 0 : dif_neg (mt is_noetherian.iff_dim_lt_aleph_0.mpr fin) }
end

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps]
noncomputable def basis_of_linear_independent_of_card_eq_finrank
  {ι : Type*} [nonempty ι] [fintype ι] {b : ι → V}
  (lin_ind : linear_independent K b) (card_eq : fintype.card ι = finrank K V) :
  basis ι K V :=
basis.mk lin_ind $
(span_eq_top_of_linear_independent_of_card_eq_finrank lin_ind card_eq).ge

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

end basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/
section finrank_eq_one

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

lemma submodule.finrank_le_one_iff_is_principal (W : submodule K V) [finite_dimensional K W] :
  finrank K W ≤ 1 ↔ W.is_principal :=
by rw [← W.rank_le_one_iff_is_principal, ← finrank_eq_dim, ← cardinal.nat_cast_le, nat.cast_one]

lemma module.finrank_le_one_iff_top_is_principal [finite_dimensional K V] :
  finrank K V ≤ 1 ↔ (⊤ : submodule K V).is_principal :=
by rw [← module.rank_le_one_iff_top_is_principal, ← finrank_eq_dim,
  ← cardinal.nat_cast_le, nat.cast_one]

-- We use the `linear_map.compatible_smul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[field K] [algebra K A] [is_scalar_tower K A V] [is_scalar_tower K A W]`
lemma surjective_of_nonzero_of_finrank_eq_one {W A : Type*} [semiring A]
  [module A V] [add_comm_group W] [module K W] [module A W] [linear_map.compatible_smul V W K A]
  (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : surjective f :=
begin
  change surjective (f.restrict_scalars K),
  obtain ⟨v, n⟩ := fun_like.ne_iff.mp w,
  intro z,
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z,
  exact ⟨c • v, by simp⟩,
end

/-- Any `K`-algebra module that is 1-dimensional over `K` is simple. -/
lemma is_simple_module_of_finrank_eq_one {A} [semiring A] [module A V] [has_smul K A]
  [is_scalar_tower K A V] (h : finrank K V = 1) : is_simple_order (submodule A V) :=
begin
  haveI := nontrivial_of_finrank_eq_succ h,
  refine ⟨λ S, or_iff_not_imp_left.2 (λ hn, _)⟩,
  rw ← restrict_scalars_inj K at hn ⊢,
  haveI := finite_dimensional_of_finrank_eq_succ h,
  refine eq_top_of_finrank_eq ((submodule.finrank_le _).antisymm _),
  simpa only [h, finrank_bot] using submodule.finrank_strict_mono (ne.bot_lt hn),
end

end finrank_eq_one

end division_ring

section subalgebra_dim
open module
variables {F E : Type*} [field F] [ring E] [algebra F E]

/-- A `subalgebra` is `finite_dimensional` iff it is finite_dimensional as a submodule. -/
lemma subalgebra.finite_dimensional_to_submodule {S : subalgebra F E} :
  finite_dimensional F S.to_submodule ↔ finite_dimensional F S := iff.rfl

alias subalgebra.finite_dimensional_to_submodule ↔
  finite_dimensional.of_subalgebra_to_submodule finite_dimensional.subalgebra_to_submodule

instance finite_dimensional.finite_dimensional_subalgebra [finite_dimensional F E]
  (S : subalgebra F E) : finite_dimensional F S :=
finite_dimensional.of_subalgebra_to_submodule infer_instance

instance subalgebra.finite_dimensional_bot : finite_dimensional F (⊥ : subalgebra F E) :=
by { nontriviality E, exact finite_dimensional_of_dim_eq_one subalgebra.dim_bot }

lemma subalgebra.eq_bot_of_dim_le_one {S : subalgebra F E} (h : module.rank F S ≤ 1) : S = ⊥ :=
begin
  nontriviality E,
  obtain ⟨m, hm, he⟩ := cardinal.exists_nat_eq_of_le_nat (h.trans_eq nat.cast_one.symm),
  haveI := finite_dimensional_of_dim_eq_nat he,
  rw [← not_bot_lt_iff, ← subalgebra.to_submodule.lt_iff_lt],
  haveI := (S.to_submodule_equiv).symm.finite_dimensional,
  refine λ hl, (submodule.finrank_lt_finrank_of_lt hl).not_le (nat_cast_le.1 _),
  iterate 2 { rw [subalgebra.finrank_to_submodule, finrank_eq_dim] },
  exact h.trans_eq subalgebra.dim_bot.symm,
end

lemma subalgebra.eq_bot_of_finrank_one {S : subalgebra F E} (h : finrank F S = 1) : S = ⊥ :=
subalgebra.eq_bot_of_dim_le_one $
  by { haveI := finite_dimensional_of_finrank_eq_succ h, rw [← finrank_eq_dim, h, nat.cast_one] }

@[simp]
theorem subalgebra.dim_eq_one_iff [nontrivial E] {S : subalgebra F E} :
  module.rank F S = 1 ↔ S = ⊥ :=
⟨λ h, subalgebra.eq_bot_of_dim_le_one h.le, λ h, h.symm ▸ subalgebra.dim_bot⟩

@[simp]
theorem subalgebra.finrank_eq_one_iff [nontrivial E] {S : subalgebra F E} :
  finrank F S = 1 ↔ S = ⊥ :=
⟨subalgebra.eq_bot_of_finrank_one, λ h, h.symm ▸ subalgebra.finrank_bot⟩

lemma subalgebra.bot_eq_top_iff_dim_eq_one [nontrivial E] :
  (⊥ : subalgebra F E) = ⊤ ↔ module.rank F E = 1 :=
by rw [← dim_top, ← subalgebra_top_dim_eq_submodule_top_dim, subalgebra.dim_eq_one_iff, eq_comm]

lemma subalgebra.bot_eq_top_iff_finrank_eq_one [nontrivial E] :
  (⊥ : subalgebra F E) = ⊤ ↔ finrank F E = 1 :=
by rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank,
       subalgebra.finrank_eq_one_iff, eq_comm]

alias subalgebra.bot_eq_top_iff_dim_eq_one ↔ _ subalgebra.bot_eq_top_of_dim_eq_one
alias subalgebra.bot_eq_top_iff_finrank_eq_one ↔ _ subalgebra.bot_eq_top_of_finrank_eq_one
attribute [simp] subalgebra.bot_eq_top_of_finrank_eq_one subalgebra.bot_eq_top_of_dim_eq_one

lemma subalgebra.is_simple_order_of_finrank (hr : finrank F E = 2) :
  is_simple_order (subalgebra F E) :=
let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm) in by exactI
{ to_nontrivial :=
    ⟨⟨⊥, ⊤, λ h, by cases hr.symm.trans (subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩,
  eq_bot_or_eq_top :=
  begin
    intro S,
    haveI : finite_dimensional F E := finite_dimensional_of_finrank_eq_succ hr,
    haveI : finite_dimensional F S :=
      finite_dimensional.finite_dimensional_submodule S.to_submodule,
    have : finrank F S ≤ 2 := hr ▸ S.to_submodule.finrank_le,
    have : 0 < finrank F S := finrank_pos_iff.mpr infer_instance,
    interval_cases (finrank F S),
    { left, exact subalgebra.eq_bot_of_finrank_one h, },
    { right, rw ← hr at h,
      rw ← algebra.to_submodule_eq_top,
      exact submodule.eq_top_of_finrank_eq h, },
  end }

end subalgebra_dim

namespace module
namespace End

variables [division_ring K] [add_comm_group V] [module K V]

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

section module

open module

open_locale cardinal

lemma cardinal_mk_eq_cardinal_mk_field_pow_dim
  (K V : Type u) [division_ring K] [add_comm_group V] [module K V] [finite_dimensional K V] :
  #V = #K ^ module.rank K V :=
begin
  let s := basis.of_vector_space_index K V,
  let hs := basis.of_vector_space K V,
  calc #V = #(s →₀ K) : quotient.sound ⟨hs.repr.to_equiv⟩
    ... = #(s → K) : quotient.sound ⟨finsupp.equiv_fun_on_finite⟩
    ... = _ : by rw [← cardinal.lift_inj.1 hs.mk_eq_dim, cardinal.power_def]
end

lemma cardinal_lt_aleph_0_of_finite_dimensional
  (K V : Type u) [division_ring K] [add_comm_group V] [module K V]
  [_root_.finite K] [finite_dimensional K V] :
  #V < ℵ₀ :=
begin
  letI : is_noetherian K V := is_noetherian.iff_fg.2 infer_instance,
  rw cardinal_mk_eq_cardinal_mk_field_pow_dim K V,
  exact cardinal.power_lt_aleph_0 (cardinal.lt_aleph_0_of_finite K)
    (is_noetherian.dim_lt_aleph_0 K V),
end

end module
