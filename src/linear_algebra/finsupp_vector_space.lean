/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear structures on function with finite support `α →₀ β`.
-/
import data.finsupp data.mv_polynomial linear_algebra.dimension
noncomputable theory

open lattice set linear_map submodule

namespace finsupp

section module
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [ring γ] [add_comm_group β] [module γ β]

lemma linear_independent_single [decidable_eq γ] {φ : α → Type*} [∀ a, decidable_eq (φ a)]
  {f : Π α, φ α → β} (hf : ∀a, linear_independent γ (f a)) :
  linear_independent γ (λ ax : Σ a, φ a, single ax.1 (f ax.1 ax.2)) :=
begin
  apply @linear_independent_Union_finite γ _ _ _ _ _ _ α φ _ _ (λ a x, single a (f a x)),
  { assume a,
    have h_disjoint : disjoint (span γ (range (f a))) (ker (lsingle a)),
    { rw ker_lsingle,
      exact disjoint_bot_right },
    apply linear_independent.image (hf a) h_disjoint },
  { intros i t ht hit,
    apply disjoint_mono _ _ (disjoint_lsingle_lsingle {i} t (disjoint_singleton_left.2 hit)),
    { rw span_le,
      simp only [supr_singleton],
      rw range_coe,
      apply range_comp_subset_range },
    { refine supr_le_supr (λ i, supr_le_supr _),
      intros hi,
      rw span_le,
      rw range_coe,
      apply range_comp_subset_range } }
end

end module

section vector_space
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [discrete_field γ] [add_comm_group β] [vector_space γ β]

open linear_map submodule

lemma is_basis_single {φ : α → Type*} [∀ a, decidable_eq (φ a)] (f : Π α, φ α → β)
  (hf : ∀a, is_basis γ (f a)) :
  is_basis γ (λ ax : Σ a, φ a, single ax.1 (f ax.1 ax.2)) :=
begin
  split,
  { apply linear_independent_single,
    exact λ a, (hf a).1 },
  { rw [range_sigma_eq_Union_range, span_Union],
    simp only [image_univ.symm, λ i, image_comp (single i) (f i), span_single_image],
    simp only [image_univ, (hf _).2, map_top, supr_lsingle_range] }
end

end vector_space

section dim
universes u v
variables {α : Type u} {β : Type u} {γ : Type v}
variables [decidable_eq α] [decidable_eq β] [discrete_field γ] [add_comm_group β] [vector_space γ β]

lemma dim_eq : vector_space.dim γ (α →₀ β) = cardinal.mk α * vector_space.dim γ β :=
begin
  rcases exists_is_basis γ β with ⟨bs, hbs⟩,
  rw [← cardinal.lift_inj, cardinal.lift_mul, ← hbs.mk_eq_dim,
      ← (is_basis_single _ (λa:α, hbs)).mk_eq_dim, ← cardinal.sum_mk,
      ← cardinal.lift_mul, cardinal.lift_inj],
  { simp only [cardinal.mk_image_eq (injective_single.{u u} _), cardinal.sum_const] }
end

end dim

end finsupp

section vector_space
universe variables u v w
variables {α : Type u} {β γ : Type v} {β' : Type v} {γ' : Type w}
variables [discrete_field α]
variables [add_comm_group β] [vector_space α β]
variables [add_comm_group γ] [vector_space α γ]
variables [add_comm_group β'] [vector_space α β']
variables [add_comm_group γ'] [vector_space α γ']

open vector_space

set_option class.instance_max_depth 70

lemma equiv_of_dim_eq_lift_dim [decidable_eq β'] [decidable_eq γ']
  (h : cardinal.lift.{v w} (dim α β') = cardinal.lift.{w v} (dim α γ')) :
  nonempty (β' ≃ₗ[α] γ') :=
begin
  rcases exists_is_basis α β' with ⟨b, hb⟩,
  rcases exists_is_basis α γ' with ⟨c, hc⟩,
  rw [←cardinal.lift_inj.1 hb.mk_eq_dim, ←cardinal.lift_inj.1 hc.mk_eq_dim] at h,
  rcases quotient.exact h with ⟨e⟩,
  let e := (equiv.ulift.symm.trans e).trans equiv.ulift,
  exact ⟨((module_equiv_finsupp hb).trans
      (finsupp.dom_lcongr e)).trans
      (module_equiv_finsupp hc).symm⟩,
end

lemma equiv_of_dim_eq_dim [decidable_eq β] [decidable_eq γ] (h : dim α β = dim α γ) :
  nonempty (β ≃ₗ[α] γ) :=
equiv_of_dim_eq_lift_dim (cardinal.lift_inj.2 h)

lemma fin_dim_vectorspace_equiv [decidable_eq β] (n : ℕ)
  (hn : (dim α β) = n) :
  nonempty (β ≃ₗ[α] (fin n → α)) :=
begin
  have : cardinal.lift.{v u} (n : cardinal.{v}) = cardinal.lift.{u v} (n : cardinal.{u}),
    by simp,
  have hn := cardinal.lift_inj.{v u}.2 hn,
  rw this at hn,
  rw ←@dim_fin_fun α _ n at hn,
  exact equiv_of_dim_eq_lift_dim hn,
end

lemma eq_bot_iff_dim_eq_zero [decidable_eq β] (p : submodule α β) (h : dim α p = 0) : p = ⊥ :=
begin
  have : dim α p = dim α (⊥ : submodule α β) := by rwa [dim_bot],
  rcases equiv_of_dim_eq_dim this with ⟨e⟩,
  exact e.eq_bot_of_equiv _
end

lemma injective_of_surjective [decidable_eq β] [decidable_eq γ] (f : β →ₗ[α] γ)
  (hβ : dim α β < cardinal.omega) (heq : dim α γ = dim α β) (hf : f.range = ⊤) : f.ker = ⊥ :=
have hk : dim α f.ker < cardinal.omega := lt_of_le_of_lt (dim_submodule_le _) hβ,
begin
  rcases cardinal.lt_omega.1 hβ with ⟨d₁, eq₁⟩,
  rcases cardinal.lt_omega.1 hk with ⟨d₂, eq₂⟩,
  have : 0 = d₂,
  { have := dim_eq_surjective f (linear_map.range_eq_top.1 hf),
    rw [heq, eq₁, eq₂, ← nat.cast_add, cardinal.nat_cast_inj] at this,
    exact nat.add_left_cancel this },
  refine eq_bot_iff_dim_eq_zero _ _,
  rw [eq₂, ← this, nat.cast_zero]
end

end vector_space

section vector_space
universes u

open vector_space
set_option class.instance_max_depth 50
local attribute [instance] submodule.module

set_option pp.universes false

lemma cardinal_mk_eq_cardinal_mk_field_pow_dim
  {α β : Type u} [decidable_eq β] [discrete_field α] [add_comm_group β] [vector_space α β]
  (h : dim α β < cardinal.omega) : cardinal.mk β = cardinal.mk α ^ dim α β  :=
begin
  rcases exists_is_basis α β with ⟨s, hs⟩,
  have : nonempty (fintype s),
  { rwa [← cardinal.lt_omega_iff_fintype, cardinal.lift_inj.1 hs.mk_eq_dim] },
  cases this with hsf, letI := hsf,
  calc cardinal.mk β = cardinal.mk (s →₀ α) : quotient.sound ⟨(module_equiv_finsupp hs).to_equiv⟩
    ... = cardinal.mk (s → α) : quotient.sound ⟨finsupp.equiv_fun_on_fintype⟩
    ... = _ : by rw [← cardinal.lift_inj.1 hs.mk_eq_dim, cardinal.power_def]
end

lemma cardinal_lt_omega_of_dim_lt_omega
  {α β : Type u} [decidable_eq β] [discrete_field α] [add_comm_group β] [vector_space α β] [fintype α]
  (h : dim α β < cardinal.omega) : cardinal.mk β < cardinal.omega :=
begin
  rw [cardinal_mk_eq_cardinal_mk_field_pow_dim h],
  exact cardinal.power_lt_omega (cardinal.lt_omega_iff_fintype.2 ⟨infer_instance⟩) h
end

end vector_space
