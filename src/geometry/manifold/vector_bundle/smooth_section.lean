/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/

import geometry.manifold.cont_mdiff_mfderiv
import topology.continuous_function.basic
import geometry.manifold.algebra.lie_group

/-!
# Smooth sections

In this file we define the type `cont_mdiff_section` of `n` times continuously differentiable
sections of a smooth vector bundle over a manifold `M` and prove that it's a module.
-/
open bundle filter function
open_locale manifold

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
{M : Type*} [topological_space M] [charted_space H M]
{M' : Type*} [topological_space M'] [charted_space H' M']
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H'']
{I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
[smooth_manifold_with_corners I M]


variables (F : Type*) [normed_add_comm_group F] [normed_space 𝕜 F] -- `F` model fiber
  (n : ℕ∞)
  (V : M → Type*) [topological_space (total_space V)] -- `V` vector bundle
  [Π x, add_comm_group (V x)] [Π x, module 𝕜 (V x)]
variables [Π x : M, topological_space (V x)]
  [fiber_bundle F V]
  [vector_bundle 𝕜 F V]
  [smooth_vector_bundle F V I]

/-- Bundled `n` times continuously differentiable maps. -/
@[protect_proj]
structure cont_mdiff_section :=
(to_fun            : Π x, V x)
(cont_mdiff_to_fun : cont_mdiff I (I.prod 𝓘(𝕜, F)) n (λ x, total_space_mk x (to_fun x)))

/-- Bundled smooth maps. -/
@[reducible] def smooth_section := cont_mdiff_section I F ⊤ V

localized "notation (name := cont_mdiff_section) `Cₛ^` n `⟮` I `; ` F `, ` V `⟯` :=
  cont_mdiff_section I F n V" in manifold

namespace cont_mdiff_section

variables {I} {I'} {n} {F} {V}

instance : has_coe_to_fun Cₛ^n⟮I; F, V⟯ (λ s, Π x, V x) := ⟨cont_mdiff_section.to_fun⟩

variables {s t : Cₛ^n⟮I; F, V⟯}

@[simp] lemma coe_fn_mk (s : Π x, V x)
  (hs : cont_mdiff I (I.prod 𝓘(𝕜, F)) n (λ x, total_space_mk x (s x))) :
  (mk s hs : Π x, V x) = s :=
rfl

protected lemma cont_mdiff (s : Cₛ^n⟮I; F, V⟯) :
  cont_mdiff I (I.prod 𝓘(𝕜, F)) n (λ x, total_space_mk x (s x : V x)) := s.cont_mdiff_to_fun

protected lemma smooth (s : Cₛ^∞⟮I; F, V⟯) :
  smooth I (I.prod 𝓘(𝕜, F)) (λ x, total_space_mk x (s x : V x)) := s.cont_mdiff_to_fun

protected lemma mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
  mdifferentiable I (I.prod 𝓘(𝕜, F)) (λ x, total_space_mk x (s x : V x)) :=
s.cont_mdiff.mdifferentiable hn

protected lemma mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
  mdifferentiable I (I.prod 𝓘(𝕜, F)) (λ x, total_space_mk x (s x : V x)) :=
s.cont_mdiff.mdifferentiable le_top

protected lemma mdifferentiable_at (s : Cₛ^∞⟮I; F, V⟯) {x} :
  mdifferentiable_at I (I.prod 𝓘(𝕜, F)) (λ x, total_space_mk x (s x : V x)) x :=
s.mdifferentiable x

lemma coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : Π x, V x) = t) : s = t :=
by cases s; cases t; cases h; refl

lemma coe_injective : injective (coe_fn : Cₛ^n⟮I; F, V⟯ → Π x, V x) :=
coe_inj

@[ext] theorem ext (h : ∀ x, s x = t x) : s = t :=
by cases s; cases t; congr'; exact funext h

-- duped with open PR #18877
instance has_smooth_add_self : has_smooth_add 𝓘(𝕜, E) E :=
⟨by { convert cont_diff_add.cont_mdiff, exact model_with_corners_self_prod.symm,
  exact charted_space_self_prod }⟩

instance has_add : has_add Cₛ^n⟮I; F, V⟯ :=
begin
  refine ⟨λ s t, ⟨s + t, _⟩⟩,
  intro x₀,
  have hs := s.cont_mdiff x₀,
  have ht := t.cont_mdiff x₀,
  rw [cont_mdiff_at_section] at hs ht ⊢,
  set e := trivialization_at F V x₀,
  refine (hs.add ht).congr_of_eventually_eq _,
  refine eventually_of_mem (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at F V x₀) _,
  intros x hx,
  apply (e.linear 𝕜 hx).1,
end

@[simp]
lemma coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = s + t := rfl

instance has_sub : has_sub Cₛ^n⟮I; F, V⟯ :=
begin
  refine ⟨λ s t, ⟨s - t, _⟩⟩,
  intro x₀,
  have hs := s.cont_mdiff x₀,
  have ht := t.cont_mdiff x₀,
  rw [cont_mdiff_at_section] at hs ht ⊢,
  set e := trivialization_at F V x₀,
  refine (hs.sub ht).congr_of_eventually_eq _,
  refine eventually_of_mem (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at F V x₀) _,
  intros x hx,
  apply (e.linear 𝕜 hx).map_sub,
end

@[simp]
lemma coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t := rfl

instance has_zero : has_zero Cₛ^n⟮I; F, V⟯ :=
⟨⟨λ x, 0, (smooth_zero_section 𝕜 V).of_le le_top⟩⟩

@[simp]
lemma coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 := rfl

instance has_smul : has_smul 𝕜 Cₛ^n⟮I; F, V⟯ :=
begin
  refine ⟨λ c s, ⟨c • s, _⟩⟩,
  intro x₀,
  have hs := s.cont_mdiff x₀,
  rw [cont_mdiff_at_section] at hs ⊢,
  set e := trivialization_at F V x₀,
  refine (cont_mdiff_at_const.smul hs).congr_of_eventually_eq _, -- todo: hs.const_smul
  { exact c },
  refine eventually_of_mem (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at F V x₀) _,
  intros x hx,
  apply (e.linear 𝕜 hx).2,
end

@[simp]
lemma coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • s := rfl

instance has_neg : has_neg Cₛ^n⟮I; F, V⟯ :=
begin
  refine ⟨λ s, ⟨- s, _⟩⟩,
  intro x₀,
  have hs := s.cont_mdiff x₀,
  rw [cont_mdiff_at_section] at hs ⊢,
  set e := trivialization_at F V x₀,
  refine hs.neg.congr_of_eventually_eq _,
  refine eventually_of_mem (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at F V x₀) _,
  intros x hx,
  apply (e.linear 𝕜 hx).map_neg
end

@[simp]
lemma coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(- s : Cₛ^n⟮I; F, V⟯) = - s := rfl

instance has_nsmul : has_smul ℕ  Cₛ^n⟮I; F, V⟯ :=
⟨nsmul_rec⟩

@[simp]
lemma coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • s :=
begin
  induction k with k ih,
  { simp_rw [zero_smul], refl },
  simp_rw [succ_nsmul, ← ih], refl,
end

instance has_zsmul : has_smul ℤ Cₛ^n⟮I; F, V⟯ :=
⟨zsmul_rec⟩

@[simp]
lemma coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • s :=
begin
  cases z with n n,
  refine (coe_nsmul s n).trans _,
  simp only [int.of_nat_eq_coe, coe_nat_zsmul],
  refine (congr_arg has_neg.neg (coe_nsmul s (n+1))).trans _,
  simp only [zsmul_neg_succ_of_nat, neg_inj]
end

instance add_comm_group : add_comm_group Cₛ^n⟮I; F, V⟯ :=
coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

variables (I F V n)
def coe_add_hom : Cₛ^n⟮I; F, V⟯ →+ Π x, V x :=
{ to_fun := coe_fn,
  map_zero' := coe_zero,
  map_add' := coe_add }

variables {I F V n}

instance module : module 𝕜 Cₛ^n⟮I; F, V⟯ :=
coe_injective.module 𝕜 (coe_add_hom I F n V) coe_smul

end cont_mdiff_section
