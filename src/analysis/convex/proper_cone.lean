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

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
def closure {E : Type*} [inner_product_space ℝ E] (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure (K : set E),
  smul_mem' := by {
    rw ← sequential_space.seq_closure_eq_closure,
    exact λ c hc x ⟨seq, mem, tends⟩,
      ⟨λ n, c • seq n, ⟨λ n, K.smul_mem hc (mem n), tendsto.const_smul tends c⟩ ⟩ },
  add_mem' := by {
    rw ← sequential_space.seq_closure_eq_closure,
    exact λ x ⟨xseq, xmem, xtends⟩ y ⟨yseq, ymem, ytends⟩,
      ⟨λ n, xseq n + yseq n, ⟨λ n, K.add_mem (xmem n) (ymem n), tendsto.add xtends ytends⟩ ⟩ } }

end convex_cone

section definitions

/-- A proper cone is a convex cone `K` that is nonempty and closed. -/
structure proper_cone (E : Type*) [inner_product_space ℝ E] [complete_space E] :=
(carrier    : convex_cone ℝ E)
(nonempty'  : (carrier : set E).nonempty)
(is_closed' : is_closed (carrier : set E))

end definitions

section complete_space
variables {E : Type*} [inner_product_space ℝ E] [complete_space E]
variables {F : Type*} [inner_product_space ℝ F] [complete_space F]

namespace proper_cone

instance : has_coe (proper_cone E) (convex_cone ℝ E) := ⟨proper_cone.carrier⟩

instance : has_mem E (proper_cone E) := ⟨λ e K, e ∈ (K : convex_cone ℝ E)⟩

@[simp] lemma coe_mem {x : E} {K : proper_cone E} : x ∈ K ↔ x ∈ (K : convex_cone ℝ E) := iff.rfl

lemma nonempty (K : proper_cone E) : (K : set E).nonempty := K.nonempty'

lemma is_closed (K : proper_cone E) : is_closed (K : set E) := K.is_closed'

lemma pointed (K : proper_cone E) : (K : convex_cone ℝ E).pointed :=
pointed_of_nonempty_closed K.nonempty K.is_closed

@[ext] lemma ext {S T : proper_cone E} (h : (S : convex_cone ℝ E) = T) : S = T :=
by cases S; cases T; congr'

instance : has_star (proper_cone E) := ⟨ λ K,
{ carrier    := (K : set E).inner_dual_cone,
  nonempty'  := ⟨0, pointed_inner_dual_cone _⟩,
  is_closed' := is_closed_inner_dual_cone _ } ⟩

instance : has_involutive_star (proper_cone E) :=
{ star := has_star.star,
  star_involutive := λ K, proper_cone.ext $
    inner_dual_cone_of_inner_dual_cone_eq_self K.nonempty K.is_closed }

/-- The closure of image of a proper cone under a continuous `ℝ`-linear map is a proper cone. -/
noncomputable def map (f : E →L[ℝ] F) (K : proper_cone E) : proper_cone F :=
{ carrier := convex_cone.closure ((K : convex_cone ℝ E).map f),
  nonempty' :=
  begin
    use 0,
    apply subset_closure,
    rw [set_like.mem_coe, convex_cone.mem_map],
    use ⟨0, K.pointed, map_zero _⟩
  end,
  is_closed' := is_closed_closure }

/-- The preimage of a proper cone under a continuous `ℝ`-linear map is a proper cone. -/
noncomputable def comap (f : E →L[ℝ] F) (K' : proper_cone F) : proper_cone E :=
{ carrier := (K' : convex_cone ℝ F).comap f,
  nonempty' :=
  begin
    rw convex_cone.coe_comap,
    use 0,
    rw [set.mem_preimage, map_zero, set_like.mem_coe],
    exact K'.pointed,
  end,
  is_closed' :=
  begin
    rw [convex_cone.coe_comap, continuous_linear_map.coe_coe],
    exact is_closed.preimage f.continuous K'.is_closed,
  end }

end proper_cone

theorem farkas_lemma (K : proper_cone E) (f : E →L[ℝ] F) (b : F) :
b ∈ K.map f ↔ ∀ y : F, (adjoint f b) ∈ star K → 0 ≤ ⟪y, b⟫_ℝ := iff.intro
begin
  sorry,
end
begin
  sorry,
end

end complete_space
