/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Dimension of modules and vector spaces.
-/
import linear_algebra.basis
import set_theory.ordinal
noncomputable theory

local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β γ : Type v}

section vector_space
variables [discrete_field α] [add_comm_group β] [vector_space α β]
include α
open submodule lattice

variables (α β)
def vector_space.dim : cardinal :=
cardinal.min
  (nonempty_subtype.2 (exists_is_basis β))
  (λ b, cardinal.mk b.1)
variables {α β}
open vector_space

theorem is_basis.le_span {I J : set β} (hI : is_basis I) (hJ : span J = ⊤) : cardinal.mk I ≤ cardinal.mk J :=
begin
  cases le_or_lt cardinal.omega (cardinal.mk J) with oJ oJ,
  { refine le_of_not_lt (λ IJ, _),
    let S : J → set β := λ j, ↑(hI.repr j).support,
    have hs : I ⊆ ⋃ j, S j,
    { intros i hi,
      have : span J ≤ comap hI.repr (lc.supported (⋃ j, S j)) :=
        span_le.2 (λ j hj x hx, ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩),
      rw hJ at this, replace : hI.repr i ∈ _ := this trivial,
      rw hI.repr_eq_single hi at this,
      apply this, simp },
    suffices : cardinal.mk (⋃ j, S j) < cardinal.mk I,
      from not_le_of_lt this ⟨set.embedding_of_subset hs⟩,
    refine lt_of_le_of_lt (le_trans cardinal.mk_Union_le_sum_mk
      (cardinal.sum_le_sum _ (λ _, cardinal.omega) _)) _,
    { exact λ j, le_of_lt (cardinal.lt_omega_iff_finite.2 $ finset.finite_to_set _) },
    { rwa [cardinal.sum_const, cardinal.mul_eq_max oJ (le_refl _), max_eq_left oJ] } },
  { rcases exists_finite_card_le_of_finite_of_linear_independent_of_span
      (cardinal.lt_omega_iff_finite.1 oJ) hI.1 _ with ⟨fI, hi⟩,
    { rwa [← cardinal.nat_cast_le, cardinal.finset_card, finset.coe_to_finset,
        cardinal.finset_card, finset.coe_to_finset] at hi },
    { rw hJ, apply set.subset_univ } },
end

/-- dimension theorem -/
theorem mk_eq_mk_of_basis {I J : set β} (hI : is_basis I) (hJ : is_basis J) : cardinal.mk I = cardinal.mk J :=
le_antisymm (hI.le_span hJ.2) (hJ.le_span hI.2)

theorem is_basis.mk_eq_dim {b : set β} (h : is_basis b) : cardinal.mk b = dim α β :=
let ⟨b', e⟩ := show ∃ b', dim α β = _, from cardinal.min_eq _ _ in
mk_eq_mk_of_basis h (subtype.property _)

variables [add_comm_group γ] [vector_space α γ]

theorem linear_equiv.dim_eq (f : β ≃ₗ γ) : dim α β = dim α γ :=
let ⟨b, hb⟩ := exists_is_basis β in
hb.mk_eq_dim.symm.trans $
  (cardinal.mk_eq_of_injective f.to_equiv.bijective.1).symm.trans $
(f.is_basis hb).mk_eq_dim

theorem dim_prod : dim α (β × γ) = dim α β + dim α γ :=
begin
  rcases exists_is_basis β with ⟨b, hb⟩,
  rcases exists_is_basis γ with ⟨c, hc⟩,
  rw [← @is_basis.mk_eq_dim _ (β × γ) _ _ _ _ (is_basis_inl_union_inr hb hc),
    ← hb.mk_eq_dim, ← hc.mk_eq_dim, cardinal.mk_union_of_disjoint,
    cardinal.mk_eq_of_injective, cardinal.mk_eq_of_injective],
  { exact prod.injective_inr },
  { exact prod.injective_inl },
  { rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, ⟨⟩⟩⟩,
    exact zero_not_mem_of_linear_independent (@zero_ne_one α _) hb.1 hx }
end

theorem dim_quotient (p : submodule α β) : dim α p.quotient + dim α p = dim α β :=
let ⟨f⟩ := quotient_prod_linear_equiv p in dim_prod.symm.trans f.dim_eq

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker (f : linear_map β γ) : dim α f.range + dim α f.ker = dim α β :=
by rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient]

end vector_space
