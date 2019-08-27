/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous linear maps between normed spaces, and prove
its basic properties. In particular, show that this space is itself a normed space.
-/

import topology.metric_space.lipschitz
import analysis.asymptotics
noncomputable theory
local attribute [instance] classical.prop_decidable

set_option class.instance_max_depth 70

variables {𝕂 : Type*} {E : Type*} {F : Type*} {G : Type*}
[nondiscrete_normed_field 𝕂]
[normed_group E] [normed_space 𝕂 E]
[normed_group F] [normed_space 𝕂 F]
[normed_group G] [normed_space 𝕂 G]
(c : 𝕂) (f g : E →L[𝕂] F) (h : F →L[𝕂] G) (x y z : E)
include 𝕂

open metric continuous_linear_map

lemma exists_pos_bound_of_bound {f : E → F} (M : ℝ) (h : ∀x, ∥f x∥ ≤ M * ∥x∥) :
  ∃ N > 0, ∀x, ∥f x∥ ≤ N * ∥x∥ :=
⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), λx, calc
  ∥f x∥ ≤ M * ∥x∥ : h x
  ... ≤ max M 1 * ∥x∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _) ⟩

lemma linear_map.continuous_of_bound (f : E →ₗ[𝕂] F) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
begin
  have : ∀ (x y : E), dist (f x) (f y) ≤ C * dist x y := λx y, calc
    dist (f x) (f y) = ∥f x - f y∥ : by rw dist_eq_norm
    ... = ∥f (x - y)∥ : by simp
    ... ≤ C * ∥x - y∥ : h _
    ... = C * dist x y : by rw dist_eq_norm,
  exact continuous_of_lipschitz this
end

def linear_map.with_bound (f : E →ₗ[𝕂] F) (h : ∃C : ℝ, ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕂] F :=
⟨f, let ⟨C, hC⟩ := h in linear_map.continuous_of_bound f C hC⟩

@[simp, elim_cast] lemma linear_map_with_bound_coe (f : E →ₗ[𝕂] F) (h : ∃C : ℝ, ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.with_bound h) : E →ₗ[𝕂] F) = f := rfl

@[simp] lemma linear_map_with_bound_apply (f : E →ₗ[𝕂] F) (h : ∃C : ℝ, ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.with_bound h x = f x := rfl

namespace continuous_linear_map

/-- A continuous linear map between normed spaces is bounded when the field is nondiscrete.
The continuity ensures boundedness on a ball of some radius δ. The nondiscreteness is then
used to rescale any element into an element of norm in [δ/C, δ], whose image has a controlled norm.
The norm control for the original element follows by rescaling. -/
theorem bound : ∃ C > 0, ∀ x : E, ∥f x∥ ≤ C * ∥x∥ :=
begin
  have : continuous_at f 0 := continuous_iff_continuous_at.1 f.2 _,
  rcases metric.tendsto_nhds_nhds.1 this 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos ε_pos,
  have H : ∀{a}, ∥a∥ ≤ δ → ∥f a∥ ≤ 1,
  { assume a ha,
    have : dist (f a) (f 0) ≤ 1,
    { apply le_of_lt (hε _),
      rw [dist_eq_norm, sub_zero],
      exact lt_of_le_of_lt ha (half_lt_self ε_pos) },
    simpa using this },
  rcases exists_one_lt_norm 𝕂 with ⟨c, hc⟩,
  refine ⟨δ⁻¹ * ∥c∥, mul_pos (inv_pos δ_pos) (lt_trans zero_lt_one hc), (λx, _)⟩,
  by_cases h : x = 0,
  { simp only [h, norm_zero, mul_zero, continuous_linear_map.map_zero], },
  { rcases rescale_to_shell hc δ_pos h with ⟨d, hd, dxle, ledx, dinv⟩,
    calc ∥f x∥
      = ∥f ((d⁻¹ * d) • x)∥ : by rwa [inv_mul_cancel, one_smul]
      ... = ∥d∥⁻¹ * ∥f (d • x)∥ :
        by rw [mul_smul, map_smul, norm_smul, norm_inv]
      ... ≤ ∥d∥⁻¹ * 1 :
        mul_le_mul_of_nonneg_left (H dxle) (by { rw ← norm_inv, exact norm_nonneg _ })
      ... ≤ δ⁻¹ * ∥c∥ * ∥x∥ : by { rw mul_one, exact dinv } }
end

section
open asymptotics filter

theorem is_O_id (l : filter E) : is_O f (λ x, x) l :=
let ⟨M, hMp, hM⟩ := f.bound in
⟨M, hMp, mem_sets_of_superset univ_mem_sets (λ x _, hM x)⟩

theorem is_O_comp (g : F →L[𝕂] G) (f : E → F) (l : filter E) :
  is_O (λ x', g (f x')) f l :=
((g.is_O_id ⊤).comp _).mono (map_le_iff_le_comap.mp lattice.le_top)

theorem is_O_sub (f : E →L[𝕂] F) (l : filter E) (x : E) :
  is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
is_O_comp f _ l

end

section op_norm
open set real

set_option class.instance_max_depth 100

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm := Inf { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ }
instance has_op_norm : has_norm (E →L[𝕂] F) := ⟨op_norm⟩

-- So that invocations of real.Inf_le ma𝕂e sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : E →L[𝕂] F} :
  ∃ c, c ∈ { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : E →L[𝕂] F} :
  bdd_below { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: ∥f x∥ ≤ ∥f∥ * ∥x∥. -/
theorem le_op_norm : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
classical.by_cases
  (λ heq : x = 0, by { rw heq, simp })
  (λ hne, have hlt : 0 < ∥x∥, from (norm_pos_iff _).2 hne,
    le_mul_of_div_le hlt ((le_Inf _ bounds_nonempty bounds_bdd_below).2
    (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (by { rw mul_comm, apply hc }))))

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
(or.elim (lt_or_eq_of_le (norm_nonneg _))
  (λ hlt, div_le_of_le_mul hlt (by { rw mul_comm, apply le_op_norm }))
  (λ heq, by { rw [←heq, div_zero], apply op_norm_nonneg }))

/-- The image of the unit ball under a continuous linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
λ hx, begin
  rw [←(mul_one ∥f∥)],
  calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
  ...    ≤ _ : mul_le_mul_of_nonneg_left hx (op_norm_nonneg _)
end

/-- If one controls the norm of every A x, then one controls the norm of A. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_triangle : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by { rw add_mul,
    calc _ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ...    ≤ _             : add_le_add (le_op_norm _ _) (le_op_norm _ _) }⟩

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, continuous_linear_map.ext (λ x, (norm_le_zero_iff _).1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul, hf], exact norm_zero })⟩)
    (op_norm_nonneg _))

@[simp] lemma norm_zero : ∥(0 : E →L[𝕂] F)∥ = 0 :=
by rw op_norm_zero_iff

/-- The norm of the identity is at most 1. It is in fact 1, except when the space is trivial where
it is 0. It means that one can not do better than an inequality in general. -/
lemma norm_id : ∥(id : E →L[𝕂] E)∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- The operator norm is homogeneous. -/
lemma op_norm_smul : ∥c • f∥ = ∥c∥ * ∥f∥ :=
le_antisymm
  (Inf_le _ bounds_bdd_below
    ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _), λ _,
    begin
      erw [norm_smul, mul_assoc],
      exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
    end⟩)
  (lb_le_Inf _ bounds_nonempty (λ _ ⟨hn, hc⟩,
    (or.elim (lt_or_eq_of_le (norm_nonneg c))
      (λ hlt,
        begin
          rw mul_comm,
          exact mul_le_of_le_div hlt (Inf_le _ bounds_bdd_below
          ⟨div_nonneg hn hlt, λ _,
          (by { rw div_mul_eq_mul_div, exact le_div_of_mul_le hlt
          (by { rw [ mul_comm, ←norm_smul ], exact hc _ }) })⟩)
        end)
      (λ heq, by { rw [←heq, zero_mul], exact hn }))))

lemma op_norm_neg : ∥-f∥ = ∥f∥ := calc
  ∥-f∥ = ∥(-1:𝕂) • f∥ : by rw neg_one_smul
  ... = ∥(-1:𝕂)∥ * ∥f∥ : by rw op_norm_smul
  ... = ∥f∥ : by simp

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : normed_group (E →L[𝕂] F) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_triangle, op_norm_neg⟩

/- The next instance should be found automatically, but it is not.
TODO: fix me -/
instance to_normed_group_prod : normed_group (E →L[𝕂] (F × G)) :=
continuous_linear_map.to_normed_group

instance to_normed_space : normed_space 𝕂 (E →L[𝕂] F) :=
⟨op_norm_smul⟩

/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le : ∥comp h f∥ ≤ ∥h∥ * ∥f∥ :=
(Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x,
  begin
    rw mul_assoc,
    calc _ ≤ ∥h∥ * ∥f x∥: le_op_norm _ _
    ... ≤ _ : mul_le_mul_of_nonneg_left
              (le_op_norm _ _) (op_norm_nonneg _)
  end⟩)

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ∥f∥ f :=
⟨op_norm_nonneg _, λ x y,
  by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }⟩

end op_norm

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp] lemma scalar_prod_space_iso_norm {c : E →L[𝕂] 𝕂} {f : F} :
  ∥scalar_prod_space_iso c f∥ = ∥c∥ * ∥f∥ :=
begin
  refine le_antisymm _ _,
  { apply op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (λx, _),
    calc
     ∥(c x) • f∥ = ∥c x∥ * ∥f∥ : norm_smul _ _
     ... ≤ (∥c∥ * ∥x∥) * ∥f∥ :
       mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)
     ... = ∥c∥ * ∥f∥ * ∥x∥ : by ring },
  { by_cases h : ∥f∥ = 0,
    { rw h, simp [norm_nonneg] },
    { have : 0 < ∥f∥ := lt_of_le_of_ne (norm_nonneg _) (ne.symm h),
      rw ← le_div_iff this,
      apply op_norm_le_bound _ (div_nonneg (norm_nonneg _) this) (λx, _),
      rw [div_mul_eq_mul_div, le_div_iff this],
      calc ∥c x∥ * ∥f∥ = ∥c x • f∥ : (norm_smul _ _).symm
      ... = ∥((scalar_prod_space_iso c f) : E → F) x∥ : rfl
      ... ≤ ∥scalar_prod_space_iso c f∥ * ∥x∥ : le_op_norm _ _ } },
end

end continuous_linear_map
