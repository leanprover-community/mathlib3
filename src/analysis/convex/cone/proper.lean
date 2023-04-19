/-
Copyright (c) 2020 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.inner_product_space.adjoint

/-!
## References

* https://ti.inf.ethz.ch/ew/lehre/ApproxSDP09/notes/conelp.pdf

We define a proper cone as a nonempty, closed, convex cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once have the definitions of conic programs and
linear programs, the results from this file can be used to prove duality theorems.

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

open continuous_linear_map filter

namespace convex_cone

variables {E : Type*} [add_comm_monoid E] [has_smul ℝ E] [topological_space E]
  [has_continuous_const_smul ℝ E] [has_continuous_add E]

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure ↑K,
  smul_mem' :=
    λ c hc _ h₁, map_mem_closure (continuous_id'.const_smul c) h₁ (λ _ h₂, K.smul_mem hc h₂),
  add_mem' := λ _ h₁ _ h₂, map_mem_closure₂ continuous_add h₁ h₂ K.add_mem }

@[simp, norm_cast] lemma coe_closure (K : convex_cone ℝ E) : (K.closure : set E) = closure K := rfl

protected lemma mem_closure {K : convex_cone ℝ E} {a : E} :
  a ∈ K.closure ↔ a ∈ closure (K : set E) :=
iff.rfl

end convex_cone

section definitions

/-- A proper cone is a convex cone `K` that is nonempty and closed. -/
structure proper_cone (E : Type*) [normed_add_comm_group E] [inner_product_space ℝ E] [complete_space E]
  extends convex_cone ℝ E :=
(nonempty'  : (carrier : set E).nonempty)
(is_closed' : is_closed (carrier : set E))

end definitions

namespace proper_cone

section complete_space

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] [complete_space E]
variables {F : Type*} [normed_add_comm_group F] [inner_product_space ℝ F] [complete_space F]


instance : has_coe (proper_cone E) (convex_cone ℝ E) := ⟨λ K, K.1⟩
instance : has_mem E (proper_cone E) := ⟨λ e K, e ∈ (K : convex_cone ℝ E) ⟩
noncomputable instance : has_zero (proper_cone E) := ⟨ ⟨0, ⟨0, rfl⟩, is_closed_singleton⟩ ⟩
noncomputable instance : inhabited (proper_cone E) := ⟨0⟩

@[simp] lemma mem_coe {x : E} {K : proper_cone E} : x ∈ K ↔ x ∈ (K : convex_cone ℝ E) := iff.rfl

lemma nonempty (K : proper_cone E) : (K : set E).nonempty := K.nonempty'

lemma is_closed (K : proper_cone E) : is_closed (K : set E) := K.is_closed'

lemma pointed (K : proper_cone E) : (K : convex_cone ℝ E).pointed :=
(K : convex_cone ℝ E).pointed_of_nonempty_of_is_closed K.nonempty K.is_closed

@[ext] lemma ext {S T : proper_cone E} (h : (S : convex_cone ℝ E) = T) : S = T :=
by cases S; cases T; congr'

instance : has_star (proper_cone E) := ⟨ λ K,
⟨ (K : set E).inner_dual_cone, ⟨0, pointed_inner_dual_cone _⟩, is_closed_inner_dual_cone _ ⟩ ⟩

instance : has_involutive_star (proper_cone E) :=
{ star := has_star.star,
  star_involutive := λ K, proper_cone.ext $
    (K : convex_cone ℝ E).inner_dual_cone_of_inner_dual_cone_eq_self K.nonempty K.is_closed }

@[simp] lemma coe_star (K : proper_cone E) : ↑(star K) = (K : set E).inner_dual_cone := rfl

@[simp] lemma mem_star {K : proper_cone E} {y : E} : y ∈ star K ↔ ∀ x ∈ (K : set E), 0 ≤ ⟪x, y⟫_ℝ
:= by { rw [mem_coe, coe_star], exact mem_inner_dual_cone _ _ }

/-- The closure of image of a proper cone under a continuous `ℝ`-linear map is a proper cone. -/
noncomputable def map (f : E →L[ℝ] F) (K : proper_cone E) : proper_cone F :=
⟨ convex_cone.closure (convex_cone.map (f : E →ₗ[ℝ] F) ↑K),
  begin
    use 0,
    apply subset_closure,
    rw [set_like.mem_coe, convex_cone.mem_map],
    use ⟨0, K.pointed, map_zero _⟩
  end,
  is_closed_closure ⟩

@[simp] lemma coe_map (f : E →L[ℝ] F) (K : proper_cone E) :
  ↑(K.map f) = (convex_cone.map (f : E →ₗ[ℝ] F) ↑K).closure := rfl

@[simp] lemma mem_map {f : E →L[ℝ] F} {K : proper_cone E} {y : F} :
  y ∈ K.map f ↔
  ∃ (y' : ℕ → F), (∀ (n : ℕ), ∃ (x : E) (h : x ∈ K), f x = y' n) ∧ tendsto y' at_top (nhds y)
:=
by simp_rw [mem_coe, coe_map, convex_cone.mem_closure_iff_seq_limit, convex_cone.mem_map,
  continuous_linear_map.coe_coe]

theorem farkas_lemma (K : proper_cone E) {f : E →L[ℝ] F} {b : F} :
  b ∈ K.map f ↔ ∀ y : F, (adjoint f y) ∈ star K → 0 ≤ ⟪y, b⟫_ℝ := iff.intro
begin
  -- suppose `b ∈ K.map f`
  simp_rw [proper_cone.mem_map, proper_cone.mem_star, adjoint_inner_right, proper_cone.mem_coe,
    exists_prop],

  -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
  rintro ⟨seq, hmem, htends⟩ y hinner,

  suffices h : ∀ n, 0 ≤ ⟪y, seq n⟫_ℝ, from ge_of_tendsto' (continuous.seq_continuous
    (continuous.inner (@continuous_const _ _ _ _ y) continuous_id) htends) h,

  intro n,
  obtain ⟨x, hx, hseq⟩ := hmem n,
  rw [← hseq, real_inner_comm],
  exact hinner x hx,
end
begin
  -- proof by contradiction
  intro h,

  -- suppose `h : b ∉ K.map f`
  contrapose! h,

  -- as `b ∉ K.map f`, there is a hyperplane `y` separating `b` from `K.map f`
  obtain ⟨y, hxy, hyb⟩ := convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem _
    (K.map f).nonempty (K.map f).is_closed h,
  use y,

  -- the rest of the proof is a straightforward algebraic manipulation
  refine and.intro _ hyb,
  simp_rw [proper_cone.mem_star, adjoint_inner_right],
  intros x hxK,
  apply hxy (f x), clear hxy,
  change f x ∈ ↑(proper_cone.map f K),
  rw proper_cone.coe_map,
  apply subset_closure,
  rw [set_like.mem_coe, convex_cone.mem_map],
  use ⟨x, hxK, rfl⟩,
end

end complete_space

end proper_cone
