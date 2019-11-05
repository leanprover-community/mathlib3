/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import topology.uniform_space.uniform_embedding
import topology.algebra.module
import analysis.normed_space.operator_norm

/-!
# Extension of uniform continuous functions

Extension of a uniform continuous function preserves its properties.

## Main statements

Let `β` be a dense subset of `α`, with `e : β → α` as the inclusion map. Let `f : β → γ` be a
uniform continuous function on `β`. Then there is a uniform continuous function `ψ : α → γ` on `α`,
such that `ψ` is an extension of `f`, i.e. `ψ ∘ e = f`.

This theorem is proved in `topology.uniform_space.uniform_embedding.lean`. See the lemma
`uniform_continuous_uniformly_extend`.

In this file we show that

* If `f` is an `add_monoid_hom`, then `ψ` is an `add_monoid_hom`
* If `f` is a `continuous_linear_map`, them `ψ` is a `continuous_linear_map`
* If `∥f∥ ≤ M`, then `∥ψ∥ ≤ M`

## Implementation notes

`e` is generalized to be `uniform_inducing`.

## Tags

uniform continuous, extend, extension, operator norm, op_norm

-/

noncomputable theory

open set filter lattice function

open_locale classical

variables {α : Type*} {β : Type*} {γ : Type*}

section uniformly_extend_zero

variables [uniform_space α] [has_zero α]
variables [uniform_space β] [has_zero β]
variables [uniform_space γ] [has_zero γ] [separated γ]
variables (e : β → α) (e_zero : e 0 = 0) (h_e : uniform_inducing e) (h_dense : dense_range e)
variables {f : β → γ} (h_f : uniform_continuous f)

include e_zero h_f

local notation `ψ` := (h_e.dense_inducing h_dense).extend f

lemma uniformly_extend_zero (h : f 0 = 0) : ψ 0 = 0 :=
by { rw ← e_zero, rwa uniformly_extend_of_ind h_e h_dense h_f }

end uniformly_extend_zero

section uniformly_extend_add

variables [uniform_space α] [add_monoid α] [topological_add_monoid α]
variables [uniform_space β] [add_monoid β]
variables [uniform_space γ] [add_monoid γ] [topological_add_monoid γ] [separated γ]
          [complete_space γ]
variables (e : β → α) (e_add : ∀b₁ b₂, e (b₁ + b₂) = e b₁ + e b₂) (h_e : uniform_inducing e)
          (h_dense : dense_range e)
variables {f : β → γ} (h_f : uniform_continuous f)

include e_add h_f

local notation `ψ` := (h_e.dense_inducing h_dense).extend f

lemma uniformly_extend_add (h : ∀ b₁ b₂, f (b₁ + b₂) = f b₁ + f b₂) :
  ∀ a₁ a₂, ψ (a₁ + a₂) = ψ a₁ + ψ a₂ :=
have h₁ : continuous ψ,
begin
  apply uniform_continuous.continuous,
  apply uniform_continuous_uniformly_extend,
  exact h_f
end,
have h₂ : ∀ b₁ b₂, ψ (e b₁ + e b₂) = ψ (e b₁) + ψ (e b₂),
begin
  assume b₁ b₂, rw ← e_add,
  simp only [uniformly_extend_of_ind h_e h_dense h_f],
  apply h
end,
is_closed_property2 (h_e.dense_inducing h_dense)
  (is_closed_eq (h₁.comp (continuous_add continuous_fst continuous_snd))
          (continuous_add (h₁.comp continuous_fst) (h₁.comp continuous_snd)))
  h₂

end uniformly_extend_add

namespace add_monoid_hom

variables [uniform_space α] [add_monoid α] [topological_add_monoid α]
variables [uniform_space β] [add_monoid β]
variables [uniform_space γ] [add_monoid γ] [topological_add_monoid γ] [separated γ]
          [complete_space γ]
variables (e : add_monoid_hom β α) (h_e : uniform_inducing e)
          (h_dense : dense_range e)
variables {f : add_monoid_hom β γ} (h_f : uniform_continuous f)

include h_f

/-- Extension of a uniform continuous `add_monoid_hom` -/
def extend : add_monoid_hom α γ :=
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  map_zero' := uniformly_extend_zero e e.map_zero h_e h_dense h_f f.map_zero ,
  map_add' := uniformly_extend_add e e.map_add h_e h_dense h_f f.map_add }

local notation `ψ` := extend e h_e h_dense h_f

lemma uniform_continuous_extend : uniform_continuous ψ :=
uniform_continuous_uniformly_extend h_e h_dense h_f

end add_monoid_hom

section uniformly_extend_smul

variables {K : Type*} [semiring K] [topological_space K]
variables [uniform_space α] [add_comm_group α] [semimodule K α]
          [topological_semimodule K α]
variables [uniform_space β] [add_comm_group β] [semimodule K β]
variables [uniform_space γ] [add_comm_group γ] [semimodule K γ]
          [topological_semimodule K γ] [separated γ] [complete_space γ]
variables (e : β → α) (e_smul : ∀(k:K) b, e (k • b) = k • (e b)) (h_e : uniform_inducing e)
          (h_dense : dense_range e)
variables {f : β → γ} (h_f : uniform_continuous f)

include e_smul h_f

local notation `ψ` := (h_e.dense_inducing h_dense).extend f

lemma uniformly_extend_smul (h : ∀ (k:K) b, f (k • b) = k • (f b)) :
  ∀ (k:K) a, ψ (k • a) = k • (ψ a) :=
have h₁ : continuous ψ,
begin
  apply uniform_continuous.continuous,
  apply uniform_continuous_uniformly_extend,
  exact h_f
end,
have h₂ : ∀ (k:K) b, ψ (k • e b) = k • ψ (e b),
begin
  assume k b, rw ← e_smul,
  simp only [uniformly_extend_of_ind h_e h_dense h_f],
  apply h
end,
λk, is_closed_property (h_e.dense_inducing h_dense).closure_range
  (is_closed_eq (h₁.comp (continuous_smul (continuous_const) continuous_id))
                (continuous.comp (continuous_smul (continuous_const) continuous_id) h₁))
  (h₂ k)

end uniformly_extend_smul

namespace continuous_linear_map

section extend_continuous_linear_map

variables {K : Type*} [ring K] [topological_space K]
variables [uniform_space α] [add_comm_group α] [module K α] [topological_add_group α]
          [topological_semimodule K α]
variables [uniform_space β] [add_comm_group β] [module K β]
variables [uniform_space γ] [add_comm_group γ] [module K γ] [topological_add_group γ]
          [topological_semimodule K γ] [separated γ] [complete_space γ]
variables (e : β →L[K] α) (h_e : uniform_inducing e) (h_dense : dense_range e)
variables (f : β →L[K] γ) (h_f : uniform_continuous f)

include h_f

/-- Extension of a uniform continuous `continuous_linear_map`. -/
def extend : α →L[K] γ :=
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  add := uniformly_extend_add e e.map_add h_e h_dense h_f f.map_add,
  smul := uniformly_extend_smul e (λk, map_smul k e) h_e h_dense h_f $ λ k b, map_smul _ _ _,
  cont := uniform_continuous.continuous $ uniform_continuous_uniformly_extend _ _ h_f }

local notation `ψ` := extend e h_e h_dense f h_f

lemma uniform_continuous_extend : uniform_continuous ψ :=
uniform_continuous_uniformly_extend h_e h_dense h_f

end extend_continuous_linear_map

section operator_norm

set_option class.instance_max_depth 70

variables {K : Type*} [nondiscrete_normed_field K]
variables [normed_group α] [normed_space K α]
variables [normed_group β] [normed_space K β]
variables [normed_group γ] [normed_space K γ] [complete_space γ]
variables (e : β →L[K] α) (h_e : uniform_inducing e) (h_dense : dense_range e)
variables (f : β →L[K] γ) (h_f : uniform_continuous f)

local notation `ψ` := extend e h_e h_dense f h_f

lemma norm_uniformly_extend_le' {M N : ℝ} (N0 : 0 ≤ N) (he : ∀b, ∥b∥ ≤ N * ∥e b∥) (hf : ∥f∥ ≤ M) :
  ∥ψ∥ ≤ M * N :=
have M0 : 0 ≤ M := le_trans (norm_nonneg _) hf,
have MN0 : 0 ≤ M * N := mul_nonneg M0 N0,
have h₁ : continuous ψ,
begin
  apply uniform_continuous.continuous,
  apply uniform_continuous_uniformly_extend,
  exact h_e, exact h_dense, exact h_f
end,
have h₂ : ∀b, ∥ψ (e b)∥ ≤ M * N * ∥e b∥,
begin
  assume b,
  have h : ∥f b∥ ≤ M * ∥b∥ :=
    calc ∥f b∥ ≤ ∥f∥ * ∥b∥ : le_op_norm f b
      ... ≤ M * ∥b∥ : mul_le_mul hf (le_refl _) (norm_nonneg _) M0,
  have : ψ (e b) = f b := uniformly_extend_of_ind h_e h_dense h_f b,
  rw [this, mul_assoc],
  exact le_trans h (mul_le_mul (le_refl _) (he b) (norm_nonneg _) M0)
end,
op_norm_le_bound _ MN0
  $ @is_closed_property β α _ e (λa, ∥ψ a∥ ≤ M * N * ∥a∥) (h_e.dense_inducing h_dense).closure_range
      (is_closed_le (continuous_norm.comp h₁) (continuous_mul continuous_const continuous_norm))
      h₂

/-- Special case when the map `e` is the inclusion of `β` into `α`. -/
lemma norm_uniformly_extend_le {M : ℝ} (he : ∀b, ∥b∥ = ∥e b∥) (hf : ∥f∥ ≤ M) :
  ∥ψ∥ ≤ M :=
begin
  have := norm_uniformly_extend_le' e h_e h_dense f h_f zero_le_one
    (λb, by { rw one_mul, exact le_of_eq (he b) }) hf,
  rwa mul_one at this,
end

end operator_norm

end continuous_linear_map
