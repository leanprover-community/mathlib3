/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/

import algebra.pointwise
import analysis.normed_space.basic
import topology.algebra.module
import topology.metric_space.premetric_space

/-!
# Seminorms and local convexity
-/

local attribute [instance] set.scale_set set.scale_set_action
open set


-- subset properties : absorbent and balanced sets in a vector space
-- over a nondiscrete normed field
section

variables
(𝕜 : Type*) [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [vector_space 𝕜 E]

/-- a set `A` absorbs another set `B` if `B` is contained in scaling
`A` by elements of sufficiently large norms. -/
def absorbs (A B : set E) := ∃ r > 0, ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := ∀ x, ∃ r > 0, ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm no greater than one. -/
def balanced (A : set E) := ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variables {𝕜} {A : set E}

/-- a balanced set absorbs itself. -/
lemma absorbs_self_of_balanced (hA : balanced 𝕜 A) : absorbs 𝕜 A A :=
begin
  use [1, zero_lt_one], intros a ha x hx, rw mem_scale_set_iff_inv_smul_mem, 
  show a ≠ 0, from λ h, by rw [h, norm_zero] at ha; linarith,
  have : a⁻¹ • A ⊆ A, from hA _ (by rw normed_field.norm_inv; exact inv_le_one ha),
  exact this (smul_mem_scale_set _ hx),
end

-- balanced and absorbing sets in a t.v.s:
variables [topological_space E] [topological_vector_space 𝕜 E]

/-- every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A ∈ nhds (0 : E)) : absorbent 𝕜 A :=
λ x, let ⟨w, hw₁, hw₂, hw₃⟩ := mem_nhds_sets_iff.mp hA in
have hc : continuous (λ t : 𝕜, t • x), from
  continuous.smul continuous_id continuous_const,
let ⟨r, hr₁, hr₂⟩ :=
  metric.is_open_iff.mp (hc _ hw₂) 0
  (by rwa [mem_preimage, zero_smul]) in
have hr₃ : (r/2)⁻¹ > 0, from inv_pos (half_pos hr₁),
begin
  use [(r/2)⁻¹, hr₃], intros a ha₁,
  have ha₂ : 0 < ∥a∥, from calc 0 < _ : hr₃ ... ≤ _ : ha₁,
  have ha₃ : a⁻¹ • x ∈ w, from hr₂ (by {
    rw [metric.mem_ball, dist_eq_norm, sub_zero,
        normed_field.norm_inv],
    calc _ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).1 ha₁
       ... < r : half_lt_self hr₁ }),
  rw [mem_scale_set_iff_inv_smul_mem ((norm_pos_iff _).1 ha₂)],
  exact hw₁ ha₃,
end

 /-- the union of {0} with the interior of a balanced set
is balanced. -/

-- TODO: extract as lemmas the statements a • int A = int (a • A) and
-- a • cl A = cl (a • A) ? unless there's some sleek one-liner that
-- gives the result via `homeomorph` somehow.
lemma balanced_zero_union_interior (hA : balanced 𝕜 A) :
  balanced 𝕜 ({(0 : E)} ∪ interior A) :=
λ a ha, or.elim (classical.em (a = 0))
  (λ heq, begin
    rw [heq, zero_scale_set],
    apply subset_union_left {(0 : E)},
    exact ne_empty_of_mem (mem_union_left _ (mem_singleton _)),
  end)
  (λ hne, begin
    have h : (λ x, a • x) '' interior A ⊆ _, from
      (subset_interior_iff_subset_of_open
        (is_open_map_smul_of_ne_zero hne _ (is_open_interior))).2
          (image_subset _ interior_subset),
    rw [scale_set_eq_image, image_union, image_singleton, smul_zero],
    apply union_subset_union (subset.refl _),
    calc _ ⊆ interior (a • A) : by rwa [scale_set_eq_image]
    ...    ⊆ _                : interior_mono (hA _ ha)
  end)

/-- the interior of a balanced set is balanced if it contains the origin. -/
lemma balanced_interior (hA : balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
  balanced 𝕜 (interior A) :=
begin
  rw ←singleton_subset_iff at h,
  rw [←union_eq_self_of_subset_left h],
  exact balanced_zero_union_interior hA,
end

/-- the closure of a balanced set is balanced. -/
lemma balanced_closure (hA : balanced 𝕜 A) : balanced 𝕜 (closure A) :=
begin
  intros a ha,
  have : a • (closure A) ⊆ closure (a • A),
    by rw [scale_set_eq_image, scale_set_eq_image]; exact
    image_closure_subset_closure_image
      (continuous.smul continuous_const continuous_id),
  exact subset.trans this (closure_mono (hA _ ha)),
end

end


/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/

-- TODO: this code compiles if it asks only for much weaker instances
-- [has_norm 𝕜] [has_scalar 𝕜 E] [has_add E], but that feels weird,
-- especially since this is not a class that extends something else
-- which contains additional hypotheses that make the maths sensible.
structure seminorm (𝕜 : Type*) (E : Type*)
  [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E] :=
(to_fun   : E → ℝ)
(nonneg   : ∀ x : E, 0 ≤ to_fun x)
(smul     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

variables
{𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [vector_space 𝕜 E]

-- TODO: this section contains lemmas all named like `seminorm_lemma`,
-- mimicking e.g. `norm_sub_rev`. Immediately after there is a
-- namespace `seminorm`, which contains the definition `seminorm.ball`
-- and related lemmas named `seminorm.property_ball`, mimicking
-- `metric.ball` and `metric.bounded_ball`. What is the
-- convention/rationale?

-- also, it feels like I should somehow be reusing results from
-- `metric_space.premetric_space`, but I was afraid to construct class
-- instances just for the sake of passing through them and invoking
-- lemmas.

section seminorm

instance : has_coe_to_fun (seminorm 𝕜 E) := ⟨_, λ p, p.to_fun⟩

 variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

lemma seminorm_smul : p (c • x) = ∥c∥ * p x := p.smul _ _

lemma seminorm_triangle : p (x + y) ≤ p x + p y := p.triangle _ _

@[simp]
lemma seminorm_zero : p 0 = 0 :=
calc _ = p (0 • 0) : congr_arg _ (zero_smul _ _).symm
...    = ∥0∥ * p 0 : p.smul _ _
...    = 0 : by rw [norm_zero, zero_mul]

@[simp]
lemma seminorm_neg : p (-x) = p x :=
calc _ = p ((-1 : 𝕜) • x) : by rw neg_one_smul
...    = _ : by rw [seminorm_smul p (-1 : 𝕜) x, norm_neg,
                    normed_field.norm_one, one_mul]

@[simp]
lemma seminorm_sub_rev : p (x - y) = p (y - x) :=
by rw [←neg_sub, seminorm_neg]

end seminorm

namespace seminorm

/-- the ball of radius r at x with respect to seminorm p: the set of
elements `y` with `p (y - x) < `r`. -/
def ball (p : seminorm 𝕜 E) (x : E) (r : ℝ) := { y : E | p (y - x) < r }

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
iff.rfl

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r :=
by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
ext $ λ x, by rw mem_ball_zero; exact iff.rfl

/-- seminorm-balls at zero are balanced. -/
lemma balanced_ball_zero : balanced 𝕜 (ball p 0 r) :=
begin
  rintros a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero] at hy,
  rw [mem_ball_zero, hx, seminorm_smul],
  calc _ ≤ p y : mul_le_of_le_one_left (p.nonneg _) ha ... < _ : hy
end

variables {V : Type*} [add_comm_group V] [vector_space ℝ V]

-- TODO: convexity and absorbent/balanced sets in vector spaces over ℝ

end seminorm

-- TODO: the minkowski functional, topology induced by family of
-- seminorms, local convexity.
