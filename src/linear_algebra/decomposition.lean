/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import algebra.direct_sum.module

/-!
# Decompositions of Modules
This file talks about decompositions of modules.
-/

universes u v w

open_locale direct_sum classical big_operators
open classical linear_map dfinsupp direct_sum

namespace submodule

/--
A `decomposition ι R M` for a module `M` is the type of `ι`-indexed decompositions of `M`.
The factors are available as `factors : ι → submodule R M`.
To create a decomposition of `M`, one furthermore must provide data that the
factors satisfy `∀ i : ι, disjoint (factors i) (⨆ (j ≠ i), factors j)` and
that their union is the whole module `M`.

Note: Why not say `set (submodule R M)`? Then one could get rid of explicitly
identifying `ι`. But I think it's better to follow the `basis` design,
which phased out of the `set` design because of problems with it.
-/
@[nolint has_inhabited_instance]
structure decomposition (ι : Type u) (R : Type v) (M : Type w)
  [semiring R] [add_comm_monoid M] [module R M] : Type (max u v w) :=
(factors : ι → submodule R M)
(is_internal : submodule_is_internal factors)


namespace decomposition
variables {ι : Type u} {R : Type v} {M : Type w}


/- Stuff in here doesn't require `add_comm_group M`. -/
section monoid
variables [semiring R] [add_comm_monoid M] [module R M]

/--
Given an `ι`-indexed collection of submodules, build the map of their direct sum into `M`.
-/
def to_direct_sum_map [dec_ι : decidable_eq ι] (p : ι → submodule R M) :
  (⨁ i, p i) →ₗ[R] (supr p : submodule R M) :=
(direct_sum.to_module R ι _ (λ i, submodule.of_le (le_supr p i : p i ≤ supr p)))

@[simp] lemma to_direct_sum_map_apply (p : ι → submodule R M) (x : ⨁ (i : ι), (p i)) :
  to_direct_sum_map p x = ∑ i in x.support, ⟨(x i).1, (le_supr p i : p i ≤ supr p) (x i).2⟩ :=
begin
  simp only [to_direct_sum_map, direct_sum.to_module, sum_add_hom_apply, to_add_monoid_hom_coe,
    linear_map.coe_mk, dfinsupp.lsum_apply_apply, subtype.val_eq_coe],
  refine finset.sum_congr rfl (λ i hi, _),
  congr,
end

lemma support_mk_support
  (p : ι → submodule R M) (v : ι →₀ M) (hv: ∀ (i : ι), v i ∈ p i) :
  dfinsupp.support (direct_sum.mk (λ i, p i) v.support (λ i, ⟨v i, hv i⟩)) = v.support :=
begin
  simp only [direct_sum.mk, add_monoid_hom.coe_mk],
  ext i, split,
  { intro hi,
    rw dfinsupp.mem_support_iff at hi,
    simp only [dfinsupp.mk_apply, finsupp.mem_support_iff, subtype.coe_mk, dite_not] at hi,
    split_ifs at hi,
    exact h,
    contradiction, },
  intro hi,
  rw dfinsupp.mem_support_iff,
  simp only [dfinsupp.mk_apply, finsupp.mem_support_iff, subtype.coe_mk, dite_not],
  split_ifs,
  simp only [ne.def, submodule.mk_eq_zero],
  rw ← ne.def,
  rwa finsupp.mem_support_iff at hi,
end

end monoid

section group
variables [ring R] [add_comm_group M] [module R M]

lemma to_direct_sum_map_ker
  (p : ι → submodule R M) (h : complete_lattice.independent p) : (to_direct_sum_map p).ker = ⊥ :=
begin
  rw ker_eq_bot',
  intros x hx,
  ext i,
  simp only [to_direct_sum_map_apply, ← set_like.coe_eq_coe,
    submodule.coe_sum, submodule.coe_mk] at hx,
  revert i,
  by_contra,
  push_neg at h,
  cases h with j hj,
  have : j ∈ dfinsupp.support x, { rw dfinsupp.mem_support_iff, exact_mod_cast hj },
  rw ← finset.sum_erase_add _ _ this at hx,
  simp only [submodule.coe_zero, subtype.val_eq_coe, ← neg_eq_iff_add_eq_zero] at hx,
  simp only [← hx, pi.zero_apply, submodule.coe_zero] at hj,
  have := submodule.disjoint_def.mp (complete_lattice.independent_def.mp h j) (x j) (x j).2,
  have h2 : ∑ (k : ι) in (dfinsupp.support x).erase j,
    ↑(x k) ∈ ⨆ (k : ι) (H : k ∈ (dfinsupp.support x).erase j), p k,
  { apply submodule.sum_mem_bsupr,
    intros c hc,
    exact (x c).2, },
  have h3 : (⨆ (k : ι) (H : k ∈ (dfinsupp.support x).erase j), p k : submodule R M) ≤
    ⨆ (k : ι) (H : k ≠ j), p k,
    { refine bsupr_le_bsupr' (λ i hi, finset.ne_of_mem_erase hi), },
  have h4 := h3 h2,
  rw ← submodule.neg_mem_iff at h4,
  rw hx at h4,
  rw hx at hj,
  have h5 := this h4,
  contradiction,
end

lemma to_direct_sum_map_range (p : ι → submodule R M) : (to_direct_sum_map p).range = ⊤ :=
begin
  ext,
  cases x with x hx,
  simp only [linear_map.coe_fn_sum, submodule.mem_top, mem_range,
    linear_map.lsum_apply, coe_proj, function.comp_app, function.eval_apply,
    iff_true, coe_comp, subtype.val_eq_coe],
  rw submodule.mem_supr' at hx,
  rcases hx with ⟨v, hv, hvs⟩,
  use direct_sum.mk (λ i, p i) v.support (λ i, ⟨v i, hv i⟩),
  simp only [to_direct_sum_map_apply, subtype.val_eq_coe],
  rw support_mk_support,
  rw [← set_like.coe_eq_coe, set_like.coe_mk, ← hvs],
  rw submodule.coe_sum,
  refine finset.sum_congr rfl (λ i hi, _),
  simp [direct_sum.mk],
  split_ifs,
  exact h.symm,
  exact set_like.coe_mk _ _,
end

/--
Given an indexed collection of submodules `p i : submodule R M` and
a proof that they are independent, build the obvious equivalence between
the direct sum of the `p i`'s and `supr p : submodule R M`.
-/
noncomputable def direct_sum_equiv_of_independent
  (p : ι → submodule R M) (h : complete_lattice.independent p) :
  (⨁ i, p i) ≃ₗ[R] (supr p : submodule R M) :=
begin
  letI : add_comm_group (⨁ (i : ι), (p i)) := direct_sum.add_comm_group (λ i, p i),
  convert @linear_equiv.of_bijective R (⨁ i, p i) (supr p : submodule R M) _ _ _ _ _ _ _ _,
  convert to_direct_sum_map p,
  dsimp,
  convert to_direct_sum_map_ker p h,
  dsimp,
  convert to_direct_sum_map_range p,
end

@[simp] lemma direct_sum_equiv_of_independent_apply
  (p : ι → submodule R M) (h : complete_lattice.independent p) (x : ⨁ i, p i) :
  direct_sum_equiv_of_independent p h x = to_direct_sum_map p x :=
rfl

variables {R M}

/--
Given an decomposition `D`, build an equivalence between the direct sum of `D.factors` and `M`.
-/
noncomputable def to_equiv (D : decomposition ι R M) : (⨁ i, D.factors i) ≃ₗ[R] M :=
submodule_is_internal.to_equiv _ D.is_internal

lemma to_equiv_apply (D : decomposition ι R M) (x : ⨁ i, D.factors i) :
  D.to_equiv x = ∑ i in x.support, x i :=
begin
  rw [to_equiv, submodule_is_internal.to_equiv_apply, submodule_is_internal.apply],
end

lemma to_equiv_apply' (D : decomposition ι R M) (x : ⨁ i, D.factors i) :
  D.to_equiv x = direct_sum.to_module R ι M (λ i, (D.factors i).subtype) x :=
begin
  rw to_equiv_apply,
  rw submodule_is_internal.apply,
end

lemma to_equiv_symm_single_apply
  (D : decomposition ι R M) (i : ι) (x : M) (hx : x ∈ D.factors i) :
  D.to_equiv.symm x = single i ⟨x, hx⟩ :=
begin
  apply_fun D.to_equiv using linear_equiv.injective _,
  rw [linear_equiv.apply_symm_apply],
  rw to_equiv_apply,
  by_cases h : x = 0,
  { have h₀ : subtype.mk x hx = 0, { rwa ← submodule.coe_eq_zero },
    rwa [h₀, single_zero, support_zero, finset.sum_empty] },
  rw [support_single_ne_zero, finset.sum_singleton, single_eq_same, submodule.coe_mk],
  refine λ h', h _,
  rw [← submodule.coe_eq_zero.mpr h', submodule.coe_mk]
end

lemma injective_of_independent (p : ι → submodule R M) (h_ind : complete_lattice.independent p) :
  function.injective ⇑(to_module R ι M (λ (i : ι), (p i).subtype)) :=
begin
  letI : add_comm_group (⨁ i, p i) := direct_sum.add_comm_group (λ i, p i),
  rw ← ker_eq_bot,
  rw ker_eq_bot',
  intros x hx,
  ext i,
  rw [submodule_is_internal.apply] at hx,
  rw [dfinsupp.zero_apply, coe_zero, coe_eq_zero],
  revert i,
  by_contra,
  push_neg at h,
  cases h with j hj,
  have : j ∈ dfinsupp.support x, { rw dfinsupp.mem_support_iff, exact_mod_cast hj },
  rw ← finset.sum_erase_add _ _ this at hx,
  simp only [submodule.coe_zero, subtype.val_eq_coe, ← neg_eq_iff_add_eq_zero] at hx,
  simp only [← hx, pi.zero_apply, submodule.coe_zero] at hj,
  have := submodule.disjoint_def.mp (complete_lattice.independent_def.mp h_ind j) (x j) (x j).2,
  have h2 : ∑ (k : ι) in (dfinsupp.support x).erase j,
    ↑(x k) ∈ ⨆ (k : ι) (H : k ∈ (dfinsupp.support x).erase j), p k,
  { apply submodule.sum_mem_bsupr,
    intros c hc,
    exact (x c).2, },
  have h3 : (⨆ (k : ι) (H : k ∈ (dfinsupp.support x).erase j), p k : submodule R M) ≤
    ⨆ (k : ι) (H : k ≠ j), p k,
    { refine bsupr_le_bsupr' (λ i hi, finset.ne_of_mem_erase hi), },
  have h4 := h3 h2,
  rw ← submodule.neg_mem_iff at h4,
  rw hx at h4,
  have h5 := submodule.coe_eq_zero.1 (this h4),
  contradiction
end

lemma surjective_of_supr_eq_top (p : ι → submodule R M) (h_supr : supr p = ⊤) :
  function.surjective ⇑(to_module R ι M (λ (i : ι), (p i).subtype)) :=
begin
  rwa [to_module, ← range_eq_top, ← supr_eq_range_dfinsupp_lsum p],
end

/--
Given an indexed collection of submodules of `M` and a proof that they form an internal
direct sum, construct a decomposition.
-/
def of_factors_independent_and_supr_eq_top
  (p : ι → submodule R M) (h_ind : complete_lattice.independent p) (h_supr : supr p = ⊤) :
  decomposition ι R M :=
{ factors := p,
  is_internal := ⟨injective_of_independent p h_ind, surjective_of_supr_eq_top p h_supr⟩ }

end group

end decomposition

end submodule
