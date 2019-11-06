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

* If `f` is an `add_monoid_hom`, then `ψ` is also an `add_monoid_hom`.
* If `f` is a `continuous_linear_map`, them `ψ` is also a `continuous_linear_map`.
* If `∥f∥ ≤ M`, then `∥ψ∥ ≤ M`.

## Main definitions

* For `f : β →+ γ`, `f.extend _ _ _ _ : α →+ γ` is the extension of `f`.
* Fof `f : α →L[K] γ`, `f.extend _ _ _ _ : α →L[K] γ` is the extension of `f`.

## Implementation notes

`e` is generalized to be `uniform_inducing`.

## Tags

uniform continuous, extend, extension, operator norm, op_norm

-/

noncomputable theory

open set filter lattice function

open_locale classical

variables {α : Type*} {β : Type*} {γ : Type*}

section uniformly_extend_add

variables [topological_space α] [add_monoid α] [topological_add_monoid α]
variables [topological_space β] [has_add β]
variables [topological_space γ] [add_monoid γ] [topological_add_monoid γ] [t2_space γ]
variables (e : β → α) (e_add : ∀b₁ b₂, e (b₁ + b₂) = e b₁ + e b₂) (h_e : dense_inducing e)
variables {f : β → γ} (f_add : ∀ b₁ b₂, f (b₁ + b₂) = f b₁ + f b₂)
variables {ψ : α → γ} (ψ_cont : continuous ψ) (h_psi : ∀b, ψ (e b) = f b)

include e_add f_add h_psi

lemma uniformly_extend_add : ∀ a₁ a₂, ψ (a₁ + a₂) = ψ a₁ + ψ a₂ :=
have h : ∀ b₁ b₂, ψ (e b₁ + e b₂) = ψ (e b₁) + ψ (e b₂),
begin
  assume b₁ b₂, rw ← e_add,
  simp only [h_psi],
  apply f_add
end,
is_closed_property2 h_e
  (is_closed_eq (ψ_cont.comp (continuous_add continuous_fst continuous_snd))
          (continuous_add (ψ_cont.comp continuous_fst) (ψ_cont.comp continuous_snd)))
  h

end uniformly_extend_add

namespace add_monoid_hom

variables [uniform_space α] [add_monoid α] [topological_add_monoid α]
variables [uniform_space β] [add_monoid β]
variables [uniform_space γ] [add_monoid γ] [topological_add_monoid γ] [separated γ]
          [complete_space γ]
variables (f : β →+ γ) (h_f : uniform_continuous f)
variables (e : β →+ α) (h_e : uniform_inducing e) (h_dense : dense_range e)

include h_f

/-- If `f : β →+ γ` is a uniform continuous `add_monoid_hom` defined on a dense subset of `α`,
    then `f.extend : α →+ γ` is a uniform continuous extension of `f` that is also an
    `add_monoid_hom`. -/
protected def extend : add_monoid_hom α γ :=
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  map_zero' := by simp only [e.map_zero.symm, uniformly_extend_of_ind h_e h_dense h_f, f.map_zero],
  map_add' := uniformly_extend_add e
    e.map_add
    (h_e.dense_inducing h_dense)
    f.map_add
    (uniform_continuous_uniformly_extend h_e h_dense h_f).continuous
    (uniformly_extend_of_ind h_e h_dense h_f) }

local notation `ψ` := f.extend h_f e h_e h_dense

lemma uniform_continuous_extend : uniform_continuous ψ :=
uniform_continuous_uniformly_extend h_e h_dense h_f

end add_monoid_hom

section uniformly_extend_smul

variables {K : Type*} [semiring K] [topological_space K]
variables [topological_space α] [add_comm_group α] [semimodule K α]
          [topological_semimodule K α]
variables [topological_space β] [add_comm_group β] [semimodule K β]
variables [topological_space γ] [add_comm_group γ] [semimodule K γ]
          [topological_semimodule K γ] [t2_space γ]
variables (e : β → α) (e_smul : ∀(k:K) b, e (k • b) = k • (e b)) (h_e : dense_inducing e)
variables {f : β → γ} (f_smul : ∀ (k:K) b, f (k • b) = k • (f b))
variables {ψ : α → γ} (ψ_cont : continuous ψ) (h_psi : ∀b, ψ (e b) = f b)

include e_smul f_smul h_psi

lemma uniformly_extend_smul  :
  ∀ (k:K) a, ψ (k • a) = k • (ψ a) :=
have h : ∀ (k:K) b, ψ (k • e b) = k • ψ (e b),
begin
  assume k b,
  rw [← e_smul, h_psi, h_psi],
  apply f_smul
end,
λk, is_closed_property h_e.closure_range
  (is_closed_eq (ψ_cont.comp (continuous_smul (continuous_const) continuous_id))
                (continuous.comp (continuous_smul (continuous_const) continuous_id) ψ_cont))
  (h k)

end uniformly_extend_smul

section uniformly_extend_norm

set_option class.instance_max_depth 70

variables {K : Type*} [nondiscrete_normed_field K]
variables [normed_group α] [normed_space K α]
variables [normed_group β] [normed_space K β]
variables [normed_group γ] [normed_space K γ]
variables {e : β →L[K] α} (h_e : dense_inducing e)
variables {f : β →L[K] γ}
variables {ψ : α →L[K] γ} (h_psi : ∀b, ψ (e b) = f b)

include h_e h_psi

lemma uniformly_extend_norm' {M N : ℝ} (N0 : 0 ≤ N) (he : ∀b, ∥b∥ ≤ N * ∥e b∥) (hf : ∥f∥ ≤ M) :
  ∥ψ∥ ≤ M * N :=
have M0 : 0 ≤ M := le_trans (norm_nonneg _) hf,
have MN0 : 0 ≤ M * N := mul_nonneg M0 N0,
have h : ∀b, ∥ψ (e b)∥ ≤ M * N * ∥e b∥,
begin
  assume b,
  have h : ∥f b∥ ≤ M * ∥b∥ :=
    calc ∥f b∥ ≤ ∥f∥ * ∥b∥ : f.le_op_norm b
      ... ≤ M * ∥b∥ : mul_le_mul hf (le_refl _) (norm_nonneg _) M0,
  rw [h_psi, mul_assoc],
  exact le_trans h (mul_le_mul (le_refl _) (he b) (norm_nonneg _) M0)
end,
ψ.op_norm_le_bound MN0
  $ @is_closed_property β α _ e (λa, ∥ψ a∥ ≤ M * N * ∥a∥) h_e.closure_range
    (is_closed_le (continuous_norm.comp ψ.cont) (continuous_mul continuous_const continuous_norm))
    h

lemma uniformly_extend_norm {M : ℝ} (he : ∀b, ∥b∥ = ∥e b∥) (hf : ∥f∥ ≤ M) :
  ∥ψ∥ ≤ M :=
begin
  have := uniformly_extend_norm' h_e h_psi zero_le_one
    (λb, by { rw one_mul, exact le_of_eq (he b) }) hf,
  rwa mul_one at this,
end

end uniformly_extend_norm

namespace continuous_linear_map

section extend_continuous_linear_map

variables {K : Type*} [ring K] [topological_space K]
variables [uniform_space α] [add_comm_group α] [module K α] [topological_add_group α]
          [topological_semimodule K α]
variables [uniform_space β] [add_comm_group β] [module K β]
variables [uniform_space γ] [add_comm_group γ] [module K γ] [topological_add_group γ]
          [topological_semimodule K γ] [separated γ] [complete_space γ]
variables (f : β →L[K] γ) (h_f : uniform_continuous f)
variables (e : β →L[K] α) (h_e : uniform_inducing e) (h_dense : dense_range e)

include h_f

/-- If `f : β →L[K] γ` is a uniform continuous `continuous_linear_map` defined on a dense subset of
    `α`, then `f.extend : α →L[K] γ` is a uniform continuous extension of `f` that is also a
    `continuous_linear_map`. -/
def extend : α →L[K] γ :=
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  add := uniformly_extend_add e
    e.map_add
    (h_e.dense_inducing h_dense)
    f.map_add
    (uniform_continuous_uniformly_extend h_e h_dense h_f).continuous
    (uniformly_extend_of_ind h_e h_dense h_f),
  smul := uniformly_extend_smul e
    (λk b, map_smul _ _ _)
    (h_e.dense_inducing h_dense)
    (λk b, map_smul _ _ _)
    (uniform_continuous_uniformly_extend h_e h_dense h_f).continuous
    (uniformly_extend_of_ind h_e h_dense h_f)  ,
  cont := uniform_continuous.continuous $ uniform_continuous_uniformly_extend _ _ h_f }

local notation `ψ` := f.extend h_f e h_e h_dense

lemma uniform_continuous_extend : uniform_continuous ψ :=
uniform_continuous_uniformly_extend h_e h_dense h_f

end extend_continuous_linear_map

section operator_norm

set_option class.instance_max_depth 70

variables {K : Type*} [nondiscrete_normed_field K]
variables [normed_group α] [normed_space K α]
variables [normed_group β] [normed_space K β]
variables [normed_group γ] [normed_space K γ] [complete_space γ]
variables (f : β →L[K] γ) (h_f : uniform_continuous f)
variables (e : β →L[K] α) (h_e : uniform_inducing e) (h_dense : dense_range e)

local notation `ψ` := f.extend h_f e h_e h_dense

lemma norm_uniformly_extend_le' {M N : ℝ} (N0 : 0 ≤ N) (he : ∀b, ∥b∥ ≤ N * ∥e b∥) (hf : ∥f∥ ≤ M) :
  ∥ψ∥ ≤ M * N :=
uniformly_extend_norm' (h_e.dense_inducing h_dense) (uniformly_extend_of_ind h_e h_dense h_f)
  N0 he hf

lemma norm_uniformly_extend_le {M : ℝ} (he : ∀b, ∥b∥ = ∥e b∥) (hf : ∥f∥ ≤ M) : ∥ψ∥ ≤ M :=
uniformly_extend_norm (h_e.dense_inducing h_dense) (uniformly_extend_of_ind h_e h_dense h_f) he hf

end operator_norm

end continuous_linear_map
