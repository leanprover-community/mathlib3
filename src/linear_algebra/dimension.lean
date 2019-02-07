/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Johannes Hölzl, Sander Dahmen

Dimension of modules and vector spaces.
-/
import linear_algebra.basis
import set_theory.ordinal
noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable

universes u v w
variables {α : Type u} {β γ δ : Type v}

section vector_space
variables [discrete_field α] [add_comm_group β] [vector_space α β]
include α
open submodule lattice function set

variables (α β)
def vector_space.dim : cardinal :=
cardinal.min
  (nonempty_subtype.2 (exists_is_basis α β))
  (λ b, cardinal.mk b.1)
variables {α β}
open vector_space

theorem is_basis.le_span {I J : set β} (hI : is_basis α I) (hJ : span α J = ⊤) : cardinal.mk I ≤ cardinal.mk J :=
begin
  cases le_or_lt cardinal.omega (cardinal.mk J) with oJ oJ,
  { refine le_of_not_lt (λ IJ, _),
    let S : J → set β := λ j, ↑(hI.repr j).support,
    have hs : I ⊆ ⋃ j, S j,
    { intros i hi,
      have : span α J ≤ comap hI.repr (lc.supported α (⋃ j, S j)) :=
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
theorem mk_eq_mk_of_basis {I J : set β} (hI : is_basis α I) (hJ : is_basis α J) : cardinal.mk I = cardinal.mk J :=
le_antisymm (hI.le_span hJ.2) (hJ.le_span hI.2)

theorem is_basis.mk_eq_dim {b : set β} (h : is_basis α b) : cardinal.mk b = dim α β :=
let ⟨b', e⟩ := show ∃ b', dim α β = _, from cardinal.min_eq _ _ in
mk_eq_mk_of_basis h (subtype.property _)

variables [add_comm_group γ] [vector_space α γ]

theorem linear_equiv.dim_eq (f : β ≃ₗ[α] γ) : dim α β = dim α γ :=
let ⟨b, hb⟩ := exists_is_basis α β in
hb.mk_eq_dim.symm.trans $
  (cardinal.mk_eq_of_injective f.to_equiv.bijective.1).symm.trans $
(f.is_basis hb).mk_eq_dim

lemma dim_bot : dim α (⊥ : submodule α β) = 0 :=
begin
  rw [← (@is_basis_empty_bot α β _ _ _).mk_eq_dim],
  exact cardinal.mk_emptyc (⊥ : submodule α β)
end

lemma dim_of_field (α : Type*) [discrete_field α] : dim α α = 1 :=
by rw [← (is_basis_singleton_one α).mk_eq_dim, cardinal.mk_singleton]

set_option class.instance_max_depth 37
lemma dim_span {s : set β} (hs : linear_independent α s) : dim α ↥(span α s) = cardinal.mk s :=
have (span α s).subtype '' ((span α s).subtype ⁻¹' s) = s :=
  image_preimage_eq_of_subset $ by rw [← linear_map.range_coe, range_subtype]; exact subset_span,
begin
  rw [← (is_basis_span hs).mk_eq_dim],
  calc cardinal.mk ↥(⇑(submodule.subtype (span α s)) ⁻¹' s) =
      cardinal.mk ↥((submodule.subtype (span α s)) '' ((submodule.subtype (span α s)) ⁻¹' s)) :
      (cardinal.mk_eq_of_injective subtype.val_injective).symm
    ... = cardinal.mk ↥s : by rw this
end
set_option class.instance_max_depth 32

theorem dim_prod : dim α (β × γ) = dim α β + dim α γ :=
begin
  rcases exists_is_basis α β with ⟨b, hb⟩,
  rcases exists_is_basis α γ with ⟨c, hc⟩,
  rw [← @is_basis.mk_eq_dim α (β × γ) _ _ _ _ (is_basis_inl_union_inr hb hc),
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
theorem dim_range_add_dim_ker (f : β →ₗ[α] γ) : dim α f.range + dim α f.ker = dim α β :=
by rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient]

lemma dim_range_le (f : β →ₗ[α] γ) : dim α f.range ≤ dim α β :=
by rw ← dim_range_add_dim_ker f; exact le_add_right (le_refl _)

lemma dim_map_le (f : β →ₗ γ) (p : submodule α β): dim α (p.map f) ≤ dim α p :=
begin
  have h := dim_range_le (f.comp (submodule.subtype p)),
  rwa [linear_map.range_comp, range_subtype] at h,
end

lemma dim_range_of_surjective (f : β →ₗ[α] γ) (h : surjective f) :
  dim α f.range = dim α γ :=
begin
  refine linear_equiv.dim_eq (linear_equiv.of_bijective (submodule.subtype _) _ _),
  exact linear_map.ker_eq_bot.2 subtype.val_injective,
  rwa [range_subtype, linear_map.range_eq_top]
end

lemma dim_eq_surjective (f : β →ₗ[α] γ) (h : surjective f) : dim α β = dim α γ + dim α f.ker :=
by rw [← dim_range_add_dim_ker f, ← dim_range_of_surjective f h]

lemma dim_le_surjective (f : β →ₗ[α] γ) (h : surjective f) : dim α γ ≤ dim α β :=
by rw [dim_eq_surjective f h]; refine le_add_right (le_refl _)

lemma dim_eq_injective (f : β →ₗ[α] γ) (h : injective f) : dim α β = dim α f.range :=
by rw [← dim_range_add_dim_ker f, linear_map.ker_eq_bot.2 h]; simp [dim_bot]

set_option class.instance_max_depth 37
lemma dim_submodule_le (s : submodule α β) : dim α s ≤ dim α β :=
begin
  rcases exists_is_basis α s with ⟨bs, hbs⟩,
  have : linear_independent α (submodule.subtype s '' bs) :=
    hbs.1.image (linear_map.disjoint_ker'.2 $ assume x y _ _ eq, subtype.val_injective eq),
  have : linear_independent α ((coe : s → β) '' bs) := this,
  rcases exists_subset_is_basis this with ⟨b, hbs_b, hb⟩,
  rw [← is_basis.mk_eq_dim hbs, ← is_basis.mk_eq_dim hb],
  calc cardinal.mk ↥bs = cardinal.mk ((coe : s → β) '' bs) :
      (cardinal.mk_eq_of_injective $ subtype.val_injective).symm
    ... ≤ cardinal.mk ↥b :
      nonempty.intro (embedding_of_subset hbs_b)
end
set_option class.instance_max_depth 32

lemma dim_le_injective (f : β →ₗ[α] γ) (h : injective f) : dim α β ≤ dim α γ :=
by rw [dim_eq_injective f h]; exact dim_submodule_le _

lemma dim_le_of_submodule (s t : submodule α β) (h : s ≤ t) : dim α s ≤ dim α t :=
dim_le_injective (of_le h) $ assume ⟨x, hx⟩ ⟨y, hy⟩ eq,
  subtype.eq $ show x = y, from subtype.ext.1 eq

set_option class.instance_max_depth 37
lemma dim_add_le_dim_add_dim (s t : submodule α β) :
  dim α (s ⊔ t : submodule α β) ≤ dim α s + dim α t :=
calc dim α (s ⊔ t : submodule α β) ≤ dim α (s × t) :
  dim_le_surjective
    (linear_map.copair (of_le $ le_sup_left) (of_le $ le_sup_right))
    (assume ⟨b, (hb : b ∈ (s ⊔ t : submodule α β))⟩,
      let ⟨x, hx, y, hy, eq⟩ := mem_sup.1 hb in
      ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, subtype.eq $ by simp [eq.symm]; refl⟩)
  ... = dim α s + dim α t : dim_prod

def rank (f : β →ₗ[α] γ) : cardinal := dim α f.range

lemma rank_le_domain (f : β →ₗ[α] γ) : rank f ≤ dim α β :=
by rw [← dim_range_add_dim_ker f]; exact le_add_right (le_refl _)

lemma rank_le_range (f : β →ₗ[α] γ) : rank f ≤ dim α γ :=
dim_submodule_le _

lemma rank_add_le (f g : β →ₗ[α] γ) : rank (f + g) ≤ rank f + rank g :=
calc rank (f + g) ≤ dim α (f.range ⊔ g.range : submodule α γ) :
  begin
    refine dim_le_of_submodule _ _ _,
    exact (linear_map.range_le_iff_comap.2 $ eq_top_iff'.2 $
      assume x, show f x + g x ∈ (f.range ⊔ g.range : submodule α γ), from
        mem_sup.2 ⟨_, mem_image_of_mem _ (mem_univ _), _, mem_image_of_mem _ (mem_univ _), rfl⟩)
  end
  ... ≤ rank f + rank g : dim_add_le_dim_add_dim _ _

variables [add_comm_group δ] [vector_space α δ]

lemma rank_comp_le1 (g : β →ₗ[α] γ) (f : γ →ₗ[α] δ) : rank (f.comp g) ≤ rank f :=
begin
  refine dim_le_of_submodule _ _ _,
  rw [linear_map.range_comp],
  exact image_subset _ (subset_univ _)
end

lemma rank_comp_le2 (g : β →ₗ[α] γ) (f : γ →ₗ δ) : rank (f.comp g) ≤ rank g :=
by rw [rank, rank, linear_map.range_comp]; exact dim_map_le _ _

end vector_space
