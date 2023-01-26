/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
import linear_algebra.dimension

/-!
# Finite dimension of vector spaces

Definition of the rank of a module, or dimension of a vector space, as a natural number.

## Main definitions

Defined is `finite_dimensional.finrank`, the dimension of a finite dimensional space, returning a
`nat`, as opposed to `module.rank`, which returns a `cardinal`. When the space has infinite
dimension, its `finrank` is by convention set to `0`.

The definition of `finrank` does not assume a `finite_dimensional` instance, but lemmas might.
Import `linear_algebra.finite_dimensional` to get access to these additional lemmas.

Formulas for the dimension are given for linear equivs, in `linear_equiv.finrank_eq`

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.
-/

universes u v v' w
open_locale classical cardinal

open cardinal submodule module function

variables {K : Type u} {V : Type v}

namespace finite_dimensional

open is_noetherian

section division_ring

variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/-- The rank of a module as a natural number.

Defined by convention to be `0` if the space has infinite rank.

For a vector space `V` over a field `K`, this is the same as the finite dimension
of `V` over `K`.
-/
noncomputable def finrank (R V : Type*) [semiring R]
  [add_comm_group V] [module R V] : ℕ :=
(module.rank R V).to_nat

lemma finrank_eq_of_dim_eq {n : ℕ} (h : module.rank K V = ↑ n) : finrank K V = n :=
begin
  apply_fun to_nat at h,
  rw to_nat_cast at h,
  exact_mod_cast h,
end

lemma finrank_le_of_dim_le {n : ℕ} (h : module.rank K V ≤ ↑ n) : finrank K V ≤ n :=
begin
  rwa [← cardinal.to_nat_le_iff_le_of_lt_aleph_0, to_nat_cast] at h,
  { exact h.trans_lt (nat_lt_aleph_0 n) },
  { exact nat_lt_aleph_0 n },
end

lemma finrank_lt_of_dim_lt {n : ℕ} (h : module.rank K V < ↑ n) : finrank K V < n :=
begin
  rwa [← cardinal.to_nat_lt_iff_lt_of_lt_aleph_0, to_nat_cast] at h,
  { exact h.trans (nat_lt_aleph_0 n) },
  { exact nat_lt_aleph_0 n },
end

lemma dim_lt_of_finrank_lt {n : ℕ} (h : n < finrank K V) : ↑n < module.rank K V :=
begin
  rwa [← cardinal.to_nat_lt_iff_lt_of_lt_aleph_0, to_nat_cast],
  { exact nat_lt_aleph_0 n },
  { contrapose! h,
    rw [finrank, cardinal.to_nat_apply_of_aleph_0_le h],
    exact n.zero_le },
end

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
lemma finrank_eq_card_basis {ι : Type w} [fintype ι] (h : basis ι K V) :
  finrank K V = fintype.card ι :=
finrank_eq_of_dim_eq (dim_eq_card_basis h)

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. This lemma uses a `finset` instead of indexed types. -/
lemma finrank_eq_card_finset_basis {ι : Type w} {b : finset ι}
  (h : basis.{w} b K V) :
  finrank K V = finset.card b :=
by rw [finrank_eq_card_basis h, fintype.card_coe]

/-- A finite dimensional space is nontrivial if it has positive `finrank`. -/
lemma nontrivial_of_finrank_pos (h : 0 < finrank K V) : nontrivial V :=
dim_pos_iff_nontrivial.mp (dim_lt_of_finrank_lt h)

/-- A finite dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
lemma nontrivial_of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) : nontrivial V :=
nontrivial_of_finrank_pos (by rw hn; exact n.succ_pos)

/-- A (finite dimensional) space that is a subsingleton has zero `finrank`. -/
lemma finrank_zero_of_subsingleton [h : subsingleton V] :
  finrank K V = 0 :=
begin
  by_contra h0,
  obtain ⟨x, y, hxy⟩ := (nontrivial_of_finrank_pos (nat.pos_of_ne_zero h0)),
  exact hxy (subsingleton.elim _ _)
end

lemma basis.subset_extend {s : set V} (hs : linear_independent K (coe : s → V)) :
  s ⊆ hs.extend (set.subset_univ _) :=
hs.subset_extend _

variable (K)
/-- A division_ring is one-dimensional as a vector space over itself. -/
@[simp] lemma finrank_self : finrank K K = 1 :=
finrank_eq_of_dim_eq (by simp)

/-- The vector space of functions on a fintype ι has finrank equal to the cardinality of ι. -/
@[simp] lemma finrank_fintype_fun_eq_card {ι : Type v} [fintype ι] :
  finrank K (ι → K) = fintype.card ι :=
finrank_eq_of_dim_eq dim_fun'

/-- The vector space of functions on `fin n` has finrank equal to `n`. -/
@[simp] lemma finrank_fin_fun {n : ℕ} : finrank K (fin n → K) = n :=
by simp

end division_ring

end finite_dimensional

variables {K V}

section zero_dim

variables [division_ring K] [add_comm_group V] [module K V]

open finite_dimensional

lemma finrank_eq_zero_of_basis_imp_not_finite
  (h : ∀ s : set V, basis.{v} (s : set V) K V → ¬ s.finite) : finrank K V = 0 :=
dif_neg (λ dim_lt, h _ (basis.of_vector_space K V)
  ((basis.of_vector_space K V).finite_index_of_dim_lt_aleph_0 dim_lt))

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

@[simp] lemma finrank_bot : finrank K (⊥ : submodule K V) = 0 :=
finrank_eq_of_dim_eq (dim_bot _ _)

end zero_dim

namespace linear_equiv
open finite_dimensional

variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

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

namespace linear_map
open finite_dimensional

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]
{V₂ : Type v'} [add_comm_group V₂] [module K V₂]

/-- The dimensions of the domain and range of an injective linear map are equal. -/
lemma finrank_range_of_inj {f : V →ₗ[K] V₂} (hf : function.injective f) :
  finrank K f.range = finrank K V :=
by rw (linear_equiv.of_injective f hf).finrank_eq

end division_ring

end linear_map

open module finite_dimensional

section
variables [division_ring K] [add_comm_group V] [module K V]

@[simp]
theorem finrank_top : finrank K (⊤ : submodule K V) = finrank K V :=
by { unfold finrank, simp [dim_top] }

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

end division_ring

end submodule

section span

open submodule

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]

variable (K)

/-- The rank of a set of vectors as a natural number. -/
protected noncomputable def set.finrank (s : set V) : ℕ := finrank K (span K s)

variable {K}

lemma finrank_span_le_card (s : set V) [fintype s] :
  finrank K (span K s) ≤ s.to_finset.card :=
finrank_le_of_dim_le (by simpa using dim_span_le s)

lemma finrank_span_finset_le_card (s : finset V)  :
  (s : set V).finrank K ≤ s.card :=
calc (s : set V).finrank K ≤ (s : set V).to_finset.card : finrank_span_le_card s
                                ... = s.card : by simp

lemma finrank_range_le_card {ι : Type*} [fintype ι] {b : ι → V} :
  (set.range b).finrank K ≤ fintype.card ι :=
(finrank_span_le_card _).trans $ by { rw set.to_finset_range, exact finset.card_image_le }

lemma finrank_span_eq_card {ι : Type*} [fintype ι] {b : ι → V}
  (hb : linear_independent K b) :
  finrank K (span K (set.range b)) = fintype.card ι :=
finrank_eq_of_dim_eq
begin
  have : module.rank K (span K (set.range b)) = #(set.range b) := dim_span hb,
  rwa [←lift_inj, mk_range_eq_of_injective hb.injective, cardinal.mk_fintype, lift_nat_cast,
       lift_eq_nat_iff] at this,
end

lemma finrank_span_set_eq_card (s : set V) [fintype s]
  (hs : linear_independent K (coe : s → V)) :
  finrank K (span K s) = s.to_finset.card :=
finrank_eq_of_dim_eq
begin
  have : module.rank K (span K s) = #s := dim_span_set hs,
  rwa [cardinal.mk_fintype, ←set.to_finset_card] at this,
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

end division_ring

end span

section basis

section division_ring
variables [division_ring K] [add_comm_group V] [module K V]

lemma linear_independent_of_top_le_span_of_card_eq_finrank {ι : Type*} [fintype ι] {b : ι → V}
  (spans : ⊤ ≤ span K (set.range b)) (card_eq : fintype.card ι = finrank K V) :
  linear_independent K b :=
linear_independent_iff'.mpr $ λ s g dependent i i_mem_s,
begin
  by_contra gx_ne_zero,
  -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
  -- spans a vector space of dimension `n`.
  refine not_le_of_gt (span_lt_top_of_card_lt_finrank
    (show (b '' (set.univ \ {i})).to_finset.card < finrank K V, from _)) _,
  { calc (b '' (set.univ \ {i})).to_finset.card = ((set.univ \ {i}).to_finset.image b).card
      : by rw [set.to_finset_card, fintype.card_of_finset]
    ... ≤ (set.univ \ {i}).to_finset.card : finset.card_image_le
    ... = (finset.univ.erase i).card : congr_arg finset.card (finset.ext (by simp [and_comm]))
    ... < finset.univ.card : finset.card_erase_lt_of_mem (finset.mem_univ i)
    ... = finrank K V : card_eq },

  -- We already have that `b '' univ` spans the whole space,
  -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
  refine spans.trans (span_le.mpr _),
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
    have hs : ⊤ ≤ span K (set.range b'),
    { intro x,
      have h : span K (f '' (set.range b')) = map f (span K (set.range b')) := span_image f,
      have hf : f '' (set.range b') = set.range b, { ext x, simp [set.mem_image, set.mem_range] },
      rw hf at h,
      have hx : (x : V) ∈ span K (set.range b) := x.property,
      conv at hx { congr, skip, rw h },
      simpa [mem_map] using hx },
    have hi : f.ker = ⊥ := ker_subtype _,
    convert (linear_independent_of_top_le_span_of_card_eq_finrank hs hc).map' _ hi }
end

lemma linear_independent_iff_card_le_finrank_span {ι : Type*} [fintype ι] {b : ι → V} :
  linear_independent K b ↔ fintype.card ι ≤ (set.range b).finrank K :=
by rw [linear_independent_iff_card_eq_finrank_span, finrank_range_le_card.le_iff_eq]

/-- A family of `finrank K V` vectors forms a basis if they span the whole space. -/
noncomputable def basis_of_top_le_span_of_card_eq_finrank {ι : Type*} [fintype ι] (b : ι → V)
  (le_span : ⊤ ≤ span K (set.range b)) (card_eq : fintype.card ι = finrank K V) :
  basis ι K V :=
basis.mk (linear_independent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp] lemma coe_basis_of_top_le_span_of_card_eq_finrank {ι : Type*} [fintype ι] (b : ι → V)
  (le_span : ⊤ ≤ span K (set.range b)) (card_eq : fintype.card ι = finrank K V) :
   ⇑(basis_of_top_le_span_of_card_eq_finrank b le_span card_eq) = b :=
basis.coe_mk _ _

/-- A finset of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def finset_basis_of_top_le_span_of_card_eq_finrank {s : finset V}
  (le_span : ⊤ ≤ span K (s : set V)) (card_eq : s.card = finrank K V) :
  basis (s : set V) K V :=
basis_of_top_le_span_of_card_eq_finrank (coe : (s : set V) → V)
  ((@subtype.range_coe_subtype _ (λ x, x ∈ s)).symm ▸ le_span)
  (trans (fintype.card_coe _) card_eq)

/-- A set of `finrank K V` vectors forms a basis if they span the whole space. -/
@[simps]
noncomputable def set_basis_of_top_le_span_of_card_eq_finrank {s : set V} [fintype s]
  (le_span : ⊤ ≤ span K s) (card_eq : s.to_finset.card = finrank K V) :
  basis s K V :=
basis_of_top_le_span_of_card_eq_finrank (coe : s → V)
  ((@subtype.range_coe_subtype _ s).symm ▸ le_span)
  (trans s.to_finset_card.symm card_eq)

end division_ring

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
  rcases eq_or_ne v 0 with rfl | hn,
  { haveI := subsingleton_of_forall_eq (0 : V) (λ w, by { obtain ⟨c, rfl⟩ := h w, simp }),
    rw finrank_zero_of_subsingleton,
    exact zero_le_one },
  { exact (finrank_eq_one v hn h).le }
end

end finrank_eq_one

section subalgebra_dim
open module
variables {F E : Type*} [field F] [ring E] [algebra F E]

@[simp] lemma subalgebra.dim_bot [nontrivial E] : module.rank F (⊥ : subalgebra F E) = 1 :=
((subalgebra.to_submodule_equiv (⊥ : subalgebra F E)).symm.trans $
  linear_equiv.of_eq _ _ algebra.to_submodule_bot).dim_eq.trans $
  by { rw dim_span_set, exacts [mk_singleton _, linear_independent_singleton one_ne_zero] }

@[simp] lemma subalgebra.dim_to_submodule (S : subalgebra F E) :
  module.rank F S.to_submodule = module.rank F S := rfl

@[simp] lemma subalgebra.finrank_to_submodule (S : subalgebra F E) :
  finrank F S.to_submodule = finrank F S := rfl

lemma subalgebra_top_dim_eq_submodule_top_dim :
  module.rank F (⊤ : subalgebra F E) = module.rank F (⊤ : submodule F E) :=
by { rw ← algebra.top_to_submodule, refl }

lemma subalgebra_top_finrank_eq_submodule_top_finrank :
  finrank F (⊤ : subalgebra F E) = finrank F (⊤ : submodule F E) :=
by { rw ← algebra.top_to_submodule, refl }

lemma subalgebra.dim_top : module.rank F (⊤ : subalgebra F E) = module.rank F E :=
by { rw subalgebra_top_dim_eq_submodule_top_dim, exact dim_top F E }

@[simp]
lemma subalgebra.finrank_bot [nontrivial E] : finrank F (⊥ : subalgebra F E) = 1 :=
finrank_eq_of_dim_eq (by simp)

end subalgebra_dim
