/-
Copyright (c) 2020 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.inner_product_space.adjoint

/-!
## References

* https://ti.inf.ethz.ch/ew/lehre/ApproxSDP09/notes/conelp.pdf

-/

open continuous_linear_map filter

namespace convex_cone

variables {E : Type*} [inner_product_space ℝ E]

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
def closure (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure ↑K,
  smul_mem' := by {
    rw ← sequential_space.seq_closure_eq_closure,
    exact λ c hc x ⟨seq, mem, tends⟩,
      ⟨λ n, c • seq n, ⟨λ n, K.smul_mem hc (mem n), tendsto.const_smul tends c⟩ ⟩ },
  add_mem' := by {
    rw ← sequential_space.seq_closure_eq_closure,
    exact λ x ⟨xseq, xmem, xtends⟩ y ⟨yseq, ymem, ytends⟩,
      ⟨λ n, xseq n + yseq n, ⟨λ n, K.add_mem (xmem n) (ymem n), tendsto.add xtends ytends⟩ ⟩ } }

@[simp] lemma coe_closure {K : convex_cone ℝ E} : (K.closure : set E) = _root_.closure ↑K := rfl

lemma mem_closure_iff_seq_limit {K : convex_cone ℝ E} {a : E} :
  a ∈ K.closure ↔ ∃ x : ℕ → E, (∀ n : ℕ, x n ∈ K) ∧ tendsto x at_top (nhds a) :=
by simp_rw [← set_like.mem_coe, coe_closure, mem_closure_iff_seq_limit]

end convex_cone

section definitions

/-- A proper cone is a convex cone `K` that is nonempty and closed. -/
structure proper_cone (E : Type*) [inner_product_space ℝ E] [complete_space E]
extends convex_cone ℝ E :=
(nonempty'  : (carrier : set E).nonempty)
(is_closed' : is_closed (carrier : set E))

end definitions

section complete_space
variables {E : Type*} [inner_product_space ℝ E] [complete_space E]
variables {F : Type*} [inner_product_space ℝ F] [complete_space F]

namespace proper_cone

instance : has_coe (proper_cone E) (convex_cone ℝ E) := ⟨λ K, K.1⟩
instance : has_mem E (proper_cone E) := ⟨λ e K, e ∈ (K : convex_cone ℝ E)⟩

@[simp] lemma mem_coe {x : E} {K : proper_cone E} : x ∈ K ↔ x ∈ (K : convex_cone ℝ E) := iff.rfl

lemma nonempty (K : proper_cone E) : (K : set E).nonempty := K.nonempty'

lemma is_closed (K : proper_cone E) : is_closed (K : set E) := K.is_closed'

lemma pointed (K : proper_cone E) : (K : convex_cone ℝ E).pointed :=
pointed_of_nonempty_closed_convex_cone K.nonempty K.is_closed

@[ext] lemma ext {S T : proper_cone E} (h : (S : convex_cone ℝ E) = T) : S = T :=
by cases S; cases T; congr'

instance : has_star (proper_cone E) := ⟨ λ K,
⟨ (K : set E).inner_dual_cone, ⟨0, pointed_inner_dual_cone _⟩, is_closed_inner_dual_cone _ ⟩ ⟩

instance : has_involutive_star (proper_cone E) :=
{ star := has_star.star,
  star_involutive := λ K, proper_cone.ext $
    inner_dual_cone_of_inner_dual_cone_eq_self K.nonempty K.is_closed }

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
  ∃ (x : ℕ → F), (∀ (n : ℕ), ∃ (x_1 : E) (h : x_1 ∈ K), f x_1 = x n) ∧ tendsto x at_top (nhds y)
:=
by simp_rw [mem_coe, coe_map, convex_cone.mem_closure_iff_seq_limit, convex_cone.mem_map,
  continuous_linear_map.coe_coe]

end proper_cone

theorem farkas_lemma {K : proper_cone E} {f : E →L[ℝ] F} {b : F} :
b ∈ K.map f ↔ ∀ y : F, (adjoint f y) ∈ star K → 0 ≤ ⟪y, b⟫_ℝ := iff.intro
begin
  sorry,
end
begin
  -- proof by contradiction
  intro h,

  -- `h : b ∉ K.map f`
  contrapose! h,

  -- as `b ∉ K.map f`, there is a hyperplane `y` separating `b` from `K.map f`
  obtain ⟨y, hxy, hyb⟩ := hyperplane_separation_point_nonempty_closed_convex_cone
    (K.map f).nonempty (K.map f).is_closed h,
  use y,

  -- the rest of the proof is a straightforward algebraic manipulation
  refine and.intro _ hyb,
  simp_rw [proper_cone.mem_star, adjoint_inner_right],
  intros x hxK,
  apply hxy (f x), clear hxy,
  suffices : f x ∈ ↑(proper_cone.map f K), from this,
  rw proper_cone.coe_map,
  apply subset_closure,
  rw [set_like.mem_coe, convex_cone.mem_map],
  use ⟨x, hxK, rfl⟩,
end

end complete_space
