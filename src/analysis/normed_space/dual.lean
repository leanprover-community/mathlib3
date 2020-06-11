/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.hahn_banach

/-!
# The topological dual of a normed space

In this file we define the topological dual of a normed space, and the bounded linear map from
a normed space into its double dual.

We also prove that, for base field the real numbers, this map is an isometry.  (TODO:  the same for
the complex numbers.)
-/

noncomputable theory

section general
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables (E : Type*) [normed_group E] [normed_space 𝕜 E]

/-- The topological dual of a normed space `E`. -/
@[derive [normed_group, normed_space 𝕜]] def dual := E →L[𝕜] 𝕜

instance : has_coe_to_fun (dual 𝕜 E) := ⟨_, λ f, f.to_fun⟩

instance : inhabited (dual 𝕜 E) := ⟨0⟩

/-- The inclusion of a normed space in its double (topological) dual. -/
def inclusion_in_double_dual (x : E) : (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ f, f x,
    add    := by simp,
    smul   := by simp }
  ∥x∥
  (λ f, by { rw mul_comm, exact f.le_op_norm x } )

@[simp] lemma dual_def (x : E) (f : dual 𝕜 E) :
  ((inclusion_in_double_dual 𝕜 E) x) f = f x := rfl

lemma double_dual_bound (x : E) : ∥(inclusion_in_double_dual 𝕜 E) x∥ ≤ ∥x∥ :=
begin
  apply continuous_linear_map.op_norm_le_bound, 
  { simp },
  { intros f, rw mul_comm, exact f.le_op_norm x, }
end

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual_map : E →L[𝕜] (dual 𝕜 (dual 𝕜 E)) :=
linear_map.mk_continuous
  { to_fun := λ (x : E), (inclusion_in_double_dual 𝕜 E) x,
    add    := λ x y, by { ext, simp },
    smul   := λ (c : 𝕜) x, by { ext, simp } }
  1
  (λ x, by { simp, apply double_dual_bound } )

end general

section real
variables (E : Type*) [normed_group E] [normed_space ℝ E]

/-- The inclusion of a real normed space in its double dual is an isometry onto its image.-/
lemma inclusion_in_double_dual_isometry (x : E) (h : vector_space.dim ℝ E > 0) :
  ∥inclusion_in_double_dual_map ℝ E x∥ = ∥x∥ :=
begin
  refine le_antisymm_iff.mpr ⟨double_dual_bound ℝ E x, _⟩,
  rw continuous_linear_map.norm_def,
  apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
  intros c, simp, intros h₁ h₂,
  cases exists_dual_vector' h x with f hf,
  calc ∥x∥ = f x : hf.2.symm
  ... ≤ ∥f x∥ : le_max_left (f x) (-f x)
  ... ≤ c * ∥f∥ : h₂ f
  ... = c : by rw [ hf.1, mul_one ],
end

-- TODO: This is also true over ℂ.

end real
