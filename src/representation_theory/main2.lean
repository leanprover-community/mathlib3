/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import representation_theory.pi_map
import linear_algebra.finite_dimensional

open_locale direct_sum classical big_operators
open classical linear_map finite_dimensional
noncomputable theory
/-!
# Simple Modules



-/

def linear_map.End_prod_linear_map (R M N : Type*)
  [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (h1 : ∀ f : M →ₗ[R] N, f = 0) (h2 : ∀ f : N →ₗ[R] M, f = 0) :
  module.End R (M × N) →+* module.End R M × module.End R N :=
{ to_fun := λ x,
  ⟨(linear_map.fst R M N).comp (x.comp (linear_map.inl R M N)),
  (linear_map.snd R M N).comp (x.comp (linear_map.inr R M N))⟩,
  map_zero' := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  map_add' := sorry }

lemma useful_lemma (R M N : Type*)
  [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (h : ∀ f : N →ₗ[R] M, f = 0) (φ : module.End R (M × N)) (x : N) :
  ((fst R M N).comp (φ.comp (inr R M N))) x = (φ (0, x)).fst := rfl

lemma linear_map.End_prod_linear_map_apply (R M N : Type*)
  [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (h1 : ∀ f : M →ₗ[R] N, f = 0) (h2 : ∀ f : N →ₗ[R] M, f = 0) (φ : module.End R (M × N)) :
  ((fst R M N).comp (φ.comp (inl R M N))).prod_map ((snd R M N).comp (φ.comp (inr R M N))) = φ :=
begin
  ext,
  simp only [prod_map_apply, function.comp_app, inl_apply, coe_comp, fst_apply],
  simp only [snd_apply, prod_map_apply, function.comp_app, inl_apply, coe_comp, inr_apply],
  change (φ 0).snd = (φ (x, 0)).snd,
  rw [map_zero φ, prod.snd_zero],
  have := ext_iff.mp (h1 ((snd R M N).comp (φ.comp (inl R M N)))) x,
  exact this.symm,
  simp only [prod_map_apply, function.comp_app, inl_apply, coe_comp, fst_apply, inr_apply],
  change (φ 0).fst = (φ (0, x)).fst,
  rw [map_zero φ, prod.fst_zero],
  have := ext_iff.mp (h2 ((fst R M N).comp (φ.comp (inr R M N)))) x,
  exact this.symm,
  simp only [prod_map_apply, function.comp_app, inr_apply, coe_comp, snd_apply],
end


def linear_map.End_prod_equiv (R M N : Type*)
  [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (h1 : ∀ f : M →ₗ[R] N, f = 0) (h2 : ∀ f : N →ₗ[R] M, f = 0) :
  module.End R (M × N) ≃+* module.End R M × module.End R N :=
ring_equiv.of_bijective (linear_map.End_prod_linear_map R M N h1 h2)
begin
  split,
  { intros x y hxy,
    rw ← linear_map.End_prod_linear_map_apply R M N h1 h2 x,
    rw ← linear_map.End_prod_linear_map_apply R M N h1 h2 y,
    simp only [linear_map.End_prod_linear_map, ring_hom.coe_mk, prod.mk.inj_iff] at hxy,
    cases hxy,
    congr' 1 },
  intro φ,
  refine ⟨linear_map.prod_map φ.1 φ.2, _⟩,
  ext,
  simp [linear_map.End_prod_linear_map],
  simp [linear_map.End_prod_linear_map],
end

@[simps] def linear_map_pi {R : Type*} {ι : Type*} [fintype ι] [decidable_eq ι] [semiring R]
  {φ : ι → Type*} [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)]
  {ψ : ι → Type*} [Π (i : ι), add_comm_monoid (ψ i)] [Π (i : ι), module R (ψ i)]
  (e : Π i, φ i →ₗ[R] ψ i) : (Π i, φ i) →ₗ[R] (Π i, ψ i) :=
{ to_fun := λ f i, e i (f i),
  map_add' := λ f g, by { ext, simp },
  map_smul' := λ c f, by { ext, simp }, }

def linear_map.End_pi_linear_map (R : Type*) {ι : Type*} [fintype ι] [decidable_eq ι] [semiring R]
  (φ : ι → Type*) [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)]
  (h1 : pairwise (λ i j, ∀ f : φ i →ₗ[R] φ j, f = 0)) :
  module.End R (Π i, φ i) →+* Π i, module.End R (φ i) :=
{ to_fun := λ x i, (linear_map.proj i).comp (x.comp (linear_map.single i)),
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _ }

def linear_map.End_pi_linear_map_apply (R : Type*) {ι : Type*} [fintype ι] [decidable_eq ι]
  [semiring R] (φ : ι → Type*) [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)]
  (hp : pairwise (λ i j, ∀ f : φ i →ₗ[R] φ j, f = 0)) (φ : module.End R (Π i, φ i)) :
  linear_map_pi (λ i, (linear_map.proj i).comp (φ.comp (linear_map.single i))) = φ :=
begin
  ext i x j,
  by_cases h : i = j,
  cases h,
  simp only [coe_single, linear_map_pi_apply, coe_proj, function.comp_app, pi.single_eq_same, coe_comp],
  rw ← ne.def at h,
  simp [pi.single_eq_of_ne h.symm _],
  have := ext_iff.mp (hp i j h ((linear_map.proj j).comp (φ.comp (linear_map.single i)))) x,
  exact this.symm,
end

def linear_map.End_pi_linear_equiv
  (R : Type*) {ι : Type*} [fintype ι] [decidable_eq ι] [semiring R]
  (φ : ι → Type*) [Π (i : ι), add_comm_monoid (φ i)] [Π (i : ι), module R (φ i)]
  (hp : pairwise (λ i j, ∀ f : φ i →ₗ[R] φ j, f = 0)) :
  module.End R (Π i, φ i) ≃+* Π i, module.End R (φ i) :=
ring_equiv.of_bijective (linear_map.End_pi_linear_map R φ hp)
begin
  split,
  { intros x y f,
    rw ← linear_map.End_pi_linear_map_apply R φ hp x,
    rw ← linear_map.End_pi_linear_map_apply R φ hp y,
    rw function.funext_iff at f,
    congr, ext i z,
    have := f i,
    rw ext_iff at this,
    exact this z },
  intro f,
  use linear_map_pi f,
  ext,
  simp [linear_map.End_pi_linear_map],
end
