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
direct_sum.to_module R ι _ (λ i, submodule.of_le (le_supr p i : p i ≤ supr p))

lemma supr_subtype_comp_direct_sum_map (p : ι → submodule R M) :
  (supr p).subtype.comp (to_direct_sum_map p) = to_module R ι _ (λ i, (p i).subtype) :=
begin
  ext i x : 2,
  dsimp only [linear_map.comp_apply, to_direct_sum_map],
  simp only [to_module_lof, submodule.subtype_apply, submodule.coe_of_le],
end

@[simp] lemma to_direct_sum_map_apply (p : ι → submodule R M) (x : ⨁ (i : ι), (p i)) :
  to_direct_sum_map p x = ∑ i in x.support, ⟨x i, (le_supr p i : p i ≤ supr p) (x i).2⟩ :=
begin
  simp only [to_direct_sum_map, direct_sum.to_module, sum_add_hom_apply, to_add_monoid_hom_coe,
    linear_map.coe_mk, dfinsupp.lsum_apply_apply],
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

lemma to_direct_sum_map_injective
  (p : ι → submodule R M) (h : complete_lattice.independent p) :
  function.injective (to_direct_sum_map p) :=
begin
  suffices : function.injective ((supr p).subtype.comp $ to_direct_sum_map p),
  { exact this.of_comp, },
  rw supr_subtype_comp_direct_sum_map,
  exact h.dfinsupp_lsum_injective,
end

lemma to_direct_sum_map_range (p : ι → submodule R M) : (to_direct_sum_map p).range = ⊤ :=
begin
  have : function.injective (supr p).subtype := subtype.coe_injective,
  apply map_injective_of_injective this,
  rw [submodule.map_subtype_top, ←submodule.map_top, ←map_comp, submodule.map_top,
    supr_subtype_comp_direct_sum_map],
  exact (supr_eq_range_dfinsupp_lsum p).symm,
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
  refine linear_equiv.of_bijective (to_direct_sum_map p) _ _,
  exact to_direct_sum_map_injective p h,
  exact range_eq_top.1 (to_direct_sum_map_range p),
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
submodule_is_internal.apply _ _

lemma to_equiv_apply' (D : decomposition ι R M) (x : ⨁ i, D.factors i) :
  D.to_equiv x = direct_sum.to_module R ι M (λ i, (D.factors i).subtype) x :=
rfl

lemma to_equiv_symm_single_apply
  (D : decomposition ι R M) (i : ι) (x : M) (hx : x ∈ D.factors i) :
  D.to_equiv.symm x = single i ⟨x, hx⟩ :=
submodule_is_internal.to_equiv_symm_single_apply _ _ _ _

/--
Given an indexed collection of submodules of `M` and a proof that they form an internal
direct sum, construct a decomposition.
-/
def of_factors_independent_and_supr_eq_top
  (p : ι → submodule R M) (h_ind : complete_lattice.independent p) (h_supr : supr p = ⊤) :
  decomposition ι R M :=
{ factors := p,
  is_internal := submodule_is_internal_of_independent_of_supr_eq_top h_ind h_supr }

end group

end decomposition

end submodule
