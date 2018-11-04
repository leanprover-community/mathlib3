/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Dimension of modules and vector spaces.
-/
import linear_algebra.basic
import linear_algebra.linear_map_module
import linear_algebra.prod_module
import linear_algebra.quotient_module
import set_theory.ordinal
noncomputable theory

local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β γ : Type v}

namespace vector_space
variables [field α] [vector_space α β]

variables (α β)
def dim : cardinal :=
cardinal.min
  (nonempty_subtype.2 (@exists_is_basis α β _ _))
  (λ b, cardinal.mk b.1)
variables {α β}

include α
theorem basis_le_span (I J : set β) (h1 : is_basis I) (h2 : ∀x, x ∈ span J) : cardinal.mk I ≤ cardinal.mk J :=
or.cases_on (le_or_lt cardinal.omega $ cardinal.mk J)
(assume h4 : cardinal.omega ≤ cardinal.mk J,
le_of_not_lt $ assume h3 : cardinal.mk I > cardinal.mk J,
let h5 : J → set β := λ j, (h1.1.repr j).support.to_set in
have h6 : ¬I ⊆ ⋃ j, h5 j,
  from λ H, @not_lt_of_le _ _ (cardinal.mk I) (cardinal.mk (⋃ j, h5 j))
    (⟨set.embedding_of_subset H⟩) $
  calc  cardinal.mk (⋃ j, h5 j)
      ≤ cardinal.sum (λ j, cardinal.mk (h5 j)) : cardinal.mk_Union_le_sum_mk
  ... ≤ cardinal.sum (λ j : J, cardinal.omega.{v}) : cardinal.sum_le_sum _ _ $ λ j,
    le_of_lt $ cardinal.lt_omega_iff_finite.2 $ finset.finite_to_set _
  ... = cardinal.mk J * cardinal.omega : cardinal.sum_const _ _
  ... = max (cardinal.mk J) (cardinal.omega) : cardinal.mul_eq_max h4 (le_refl _)
  ... = cardinal.mk J : max_eq_left h4
  ... < cardinal.mk I : h3,
let ⟨i₀, h7⟩ := not_forall.1 h6 in
let ⟨h7, h8⟩ := not_imp.1 h7 in
have h9 : _ := λ j : J, not_exists.1 (mt set.mem_Union.2 h8) j,
have h9 : _ := λ j : J, finsupp.not_mem_support_iff.1 $ h9 j,
let ⟨h10, h11, h12⟩ := h2 i₀ in
have h13 : _ := (repr_eq_single h1.1 h7).symm.trans $
  (congr_arg h1.1.repr h12).trans $
  repr_finsupp_sum _ $ λ j _, h1.2 _,
have h14 : ((finsupp.single i₀ (1:α) : lc α β) : β → α) i₀ = _,
  from congr_fun (congr_arg finsupp.to_fun h13) i₀,
begin
  rw [finsupp.sum_apply, finsupp.single_eq_same, finsupp.sum] at h14,
  rw [← finset.sum_subset (finset.empty_subset _), finset.sum_empty] at h14,
  { exact zero_ne_one h14.symm },
  intros v h15 h16,
  have h17 := by_contradiction (mt (h11 v) (finsupp.mem_support_iff.1 h15)),
  have h18 : (linear_independent.repr (h1.left) v) i₀ = 0 := h9 ⟨v, h17⟩,
  rw [repr_smul h1.1 (h1.2 _), finsupp.smul_apply, h18, smul_eq_mul, mul_zero]
end)
(assume h4 : cardinal.mk J < cardinal.omega,
let ⟨h5, h6⟩ := exists_finite_card_le_of_finite_of_linear_independent_of_span
  (cardinal.lt_omega_iff_finite.1 h4) h1.1 (λ _ _, h2 _) in
by rwa [← cardinal.nat_cast_le, cardinal.finset_card, cardinal.finset_card, finset.coe_to_finset, finset.coe_to_finset] at h6)

/-- dimension theorem -/
theorem mk_eq_mk_of_basis {I J : set β} (h1 : is_basis I) (h2 : is_basis J) : cardinal.mk I = cardinal.mk J :=
le_antisymm (basis_le_span _ _ h1 h2.2) (basis_le_span _ _ h2 h1.2)

theorem mk_basis {b : set β} (h : is_basis b) : cardinal.mk b = dim α β :=
begin
  cases (show ∃ b', dim α β = _, from cardinal.min_eq _ _) with b' e,
  refine mk_eq_mk_of_basis h _,
  generalize : classical.some _ = b1,
  exact b1.2,
end

variables [vector_space α γ]

theorem dim_eq_of_linear_equiv (f : β ≃ₗ γ) : dim α β = dim α γ :=
let ⟨b, hb⟩ := exists_is_basis β in
(mk_basis hb).symm.trans $ (cardinal.mk_eq_of_injective f.to_equiv.bijective.1).symm.trans $
mk_basis $ hb.linear_equiv

theorem dim_prod : dim α (β × γ) = dim α β + dim α γ :=
let ⟨b, hb⟩ := exists_is_basis β in
let ⟨c, hc⟩ := exists_is_basis γ in
have H1 : _ := prod.is_basis_inl_union_inr hb hc,
have H2 : _ := @mk_basis.{u v} _ (β × γ) _ _ _ H1,
begin
  rw [← mk_basis hb, ← mk_basis hc, ← H2, cardinal.mk_union_of_disjiont],
  rw [cardinal.mk_eq_of_injective prod.injective_inl.{v v}],
  rw [cardinal.mk_eq_of_injective prod.injective_inr.{v v}],
  intros z h,
  rcases h with ⟨⟨x, h1, h2⟩, ⟨y, h3, h4⟩⟩,
  subst h4,
  cases prod.inl_eq_inr.1 h2 with h4 h5,
  substs h4 h5,
  exact zero_not_mem_of_linear_independent (@zero_ne_one α _) hb.1 h1
end

theorem dim_quotient {s : set β} [is_submodule s] : dim α (quotient_module.quotient β s) + dim α s = dim α β :=
nonempty.rec_on (quotient_module.quotient_prod_linear_equiv s) $ λ f,
dim_prod.symm.trans $ dim_eq_of_linear_equiv f

/-- rank-nullity theorem -/
theorem dim_im_add_dim_ker (f : linear_map β γ) : dim α f.im + dim α f.ker = dim α β :=
by rw [← dim_eq_of_linear_equiv (linear_map.quot_ker_equiv_im f), dim_quotient]

end vector_space
