/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear structures on function with finite support `α →₀ β`.
-/
import data.finsupp data.mv_polynomial linear_algebra.dimension
noncomputable theory

local attribute [instance] classical.prop_decidable

open lattice set linear_map submodule

namespace finsupp

section module
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [ring γ] [add_comm_group β] [module γ β]

local attribute [instance] finsupp.to_module

lemma linear_independent_single {f : α → set β}
  (hf : ∀a, linear_independent γ β id (f a)) : linear_independent γ _ id (⋃a, single a '' f a) :=
begin
  refine linear_independent_Union_finite _ _ ,
  { refine assume a, @linear_independent.image _ _ _ _ _ _ _ _ _ (lsingle a) (hf a) _,
    rw ker_lsingle,
    exact disjoint_bot_right },
  { assume a s hs hat,
    have : ∀a, span γ (single a '' f a) ≤ range (lsingle a),
    { simp only [span_single_image],
      exact assume a, map_mono le_top },
    refine disjoint_mono _ _ (disjoint_lsingle_lsingle {a} s _),
    { simp only [set.image_id, supr_singleton, this] },
    { exact supr_le_supr (assume a, by rw set.image_id; exact supr_le_supr (assume ha, this a)) },
    { rwa [disjoint_singleton_left] } }
end

end module

section vector_space
variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [discrete_field γ] [add_comm_group β] [vector_space γ β]

open linear_map submodule

local attribute [instance] finsupp.to_vector_space

lemma is_basis_single {f : α → set β} (hf : ∀a, is_basis γ (f a)) :
  is_basis γ (⋃a, single a '' f a) :=
⟨linear_independent_single $ assume a, (hf a).1,
  by simp only [span_Union, span_single_image, (hf _).2, map_top, supr_lsingle_range]⟩

end vector_space

section dim
universes u v
variables {α : Type u} {β : Type u} {γ : Type v}
variables [decidable_eq α] [decidable_eq β] [discrete_field γ] [add_comm_group β] [vector_space γ β]

local attribute [instance] finsupp.to_vector_space

lemma dim_eq : @vector_space.dim γ (α →₀ β) _ _ (finsupp.to_vector_space _ _) = cardinal.mk α * vector_space.dim γ β :=
begin
  rcases exists_is_basis γ β with ⟨bs, hbs⟩,
  rw [← hbs.mk_eq_dim, ← (is_basis_single (λa:α, hbs)).mk_eq_dim, cardinal.mk_Union_eq_sum_mk],
  { simp only [cardinal.mk_eq_of_injective (injective_single.{u u} _), cardinal.sum_const] },
  { refine assume i j h, disjoint_image_image (assume b hb c hc, _),
    simp only [(≠), single_eq_single_iff, not_or_distrib, not_and_distrib],
    have : (0:β) ∉ bs := zero_not_mem_of_linear_independent (zero_ne_one : (0:γ) ≠ 1) hbs.1 rfl,
    exact ⟨or.inl h, or.inl (assume eq, this $ eq ▸ hb)⟩ }
end

end dim

end finsupp

section vector_space
universes u v
variables {α : Type u} {β γ : Type v}
variables [discrete_field α]
variables [add_comm_group β] [vector_space α β]
variables [add_comm_group γ] [vector_space α γ]

open vector_space

set_option class.instance_max_depth 70
local attribute [instance] finsupp.to_vector_space

lemma equiv_of_dim_eq_dim (h : dim α β = dim α γ) : nonempty (β ≃ₗ[α] γ) :=
begin
  rcases exists_is_basis α β with ⟨b, hb⟩,
  rcases exists_is_basis α γ with ⟨c, hc⟩,
  rw [← hb.mk_eq_dim, ← hc.mk_eq_dim] at h,
  rcases quotient.exact h with ⟨e⟩,
  exact ⟨ (module_equiv_finsupp hb).trans
      (linear_equiv.trans (finsupp.congr b c e) (module_equiv_finsupp hc).symm) ⟩
end

lemma eq_bot_iff_dim_eq_zero (p : submodule α β) (h : dim α p = 0) : p = ⊥ :=
begin
  have : dim α p = dim α (⊥ : submodule α β) := by rwa [dim_bot],
  rcases equiv_of_dim_eq_dim this with ⟨e⟩,
  exact e.eq_bot_of_equiv _
end

lemma injective_of_surjective (f : β →ₗ[α] γ)
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
set_option class.instance_max_depth 40
local attribute [instance] finsupp.add_comm_group
local attribute [instance] finsupp.to_module
local attribute [instance] submodule.module

lemma cardinal_mk_eq_cardinal_mk_field_pow_dim
  {α β : Type u} [discrete_field α] [add_comm_group β] [vector_space α β]
  (h : dim α β < cardinal.omega) : cardinal.mk β = cardinal.mk α ^ dim α β  :=
begin
  rcases exists_is_basis α β with ⟨s, hs⟩,
  have : nonempty (fintype s),
  { rwa [← cardinal.lt_omega_iff_fintype, hs.mk_eq_dim] },
  cases this with hsf, letI := hsf,
  calc cardinal.mk β = cardinal.mk (↥(finsupp.supported α α s)) :
    quotient.sound ⟨(module_equiv_finsupp hs).to_equiv⟩
    ... = cardinal.mk (s →₀ α) :
    begin
      refine quotient.sound ⟨@linear_equiv.to_equiv α _ _ _ _ _ _ _ _⟩,
      convert @finsupp.supported_equiv_finsupp β α α _ _ _ _ _ s _,
      { funext, exact subsingleton.elim _ _ },
    end
    ... = cardinal.mk (s → α) : quotient.sound ⟨finsupp.equiv_fun_on_fintype⟩
    ... = _ : by rw [← hs.mk_eq_dim, cardinal.power_def]
end

lemma cardinal_lt_omega_of_dim_lt_omega
  {α β : Type u} [discrete_field α] [add_comm_group β] [vector_space α β] [fintype α]
  (h : dim α β < cardinal.omega) : cardinal.mk β < cardinal.omega :=
begin
  rw [cardinal_mk_eq_cardinal_mk_field_pow_dim h],
  exact cardinal.power_lt_omega (cardinal.lt_omega_iff_fintype.2 ⟨infer_instance⟩) h
end

end vector_space
