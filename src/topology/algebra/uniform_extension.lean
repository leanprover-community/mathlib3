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

Extension of a uniform continuous function `f : β → γ` on a uniform space `β` to its completion
preserves many of `f`'s properties.

## Main statements

Let `α` and `β` be uniform spaces and let `β` be a dense subset of `α`, with `e : β → α` as the
inclusion map. Let `f : β → γ` be a uniform continuous function from `β` to a complete Hausdorff
space `γ`. Then there is a uniform continuous function `ψ : α → γ` on `α`, such that `ψ` is an
extension of `f`, i.e. `ψ ∘ e = f`.

In this file we show that

* If `f` is an `add_monoid_hom`, then `ψ` is also an `add_monoid_hom`.
* If `f` is a `continuous_linear_map`, then `ψ` is also a `continuous_linear_map`.
* If `∥f∥ ≤ M`, then `∥ψ∥ ≤ M`.

## Main definitions

* For `f : β →+ γ`, `f.extend _ _ _ _ : α →+ γ` is the extension of `f`.
* Fof `f : α →L[K] γ`, `f.extend _ _ _ _ : α →L[K] γ` is the extension of `f`.

## Implementation notes

Mainly used in `measure_theory.bochner_integration` to extend integrals on integrable simple
functions to integrals on all integrable functions.

One can find similar results in `topology.algebra.group_completion` and
`topology.algebra.uniform_ring`, where an explicit construction of completions is given, and thus
`f : β → γ` is extended to `ψ : completion β → γ`. This approach is not suitable for extending
integrals, since integrable functions are usually defined independently of simple functions.

For results about functions without extra structures attached to them, see
`topology.uniform_space.abstract_completion`.

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
variables (e : β → α) (e_add : ∀b₁ b₂, e (b₁ + b₂) = e b₁ + e b₂) (h_e : dense_range e)
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
λk, is_closed_property h_e.dense
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
  $ @is_closed_property β α _ e (λa, ∥ψ a∥ ≤ M * N * ∥a∥) h_e.dense
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

section

variables {K : Type*} [ring K]
variables [uniform_space β] [add_comm_group β] [module K β] [uniform_add_group β]
variables [uniform_space γ] [add_comm_group γ] [module K γ] [uniform_add_group γ]
variables (f : β →L[K] γ)

protected lemma uniform_continuous : uniform_continuous f :=
uniform_continuous_of_continuous f.continuous

end

variables {K : Type*} [ring K] [topological_space K]
variables [uniform_space α] [add_comm_group α] [module K α]
          [topological_semimodule K α] [uniform_add_group α]
variables [uniform_space β] [add_comm_group β] [module K β] [uniform_add_group β]
variables [uniform_space γ] [add_comm_group γ] [module K γ] [uniform_add_group γ]
          [topological_semimodule K γ] [separated γ] [complete_space γ]
variables (f : β →L[K] γ)
variables (e : β →L[K] α) (h_e : uniform_inducing e) (h_dense : dense_range e)

/-- If `f : β →L[K] γ` is a uniform continuous `continuous_linear_map` defined on a dense subset of
    `α`, then `f.extend : α →L[K] γ` is a uniform continuous extension of `f` that is also a
    `continuous_linear_map`. -/
def extend : α →L[K] γ :=
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  add := uniformly_extend_add e
    e.map_add
    h_dense
    f.map_add
    (uniform_continuous_uniformly_extend h_e h_dense f.uniform_continuous).continuous
    (uniformly_extend_of_ind h_e h_dense f.uniform_continuous),
  smul := uniformly_extend_smul e
    (λk b, map_smul _ _ _)
    (h_e.dense_inducing h_dense)
    (λk b, map_smul _ _ _)
    (uniform_continuous_uniformly_extend h_e h_dense f.uniform_continuous).continuous
    (uniformly_extend_of_ind h_e h_dense f.uniform_continuous),
  cont := uniform_continuous.continuous $ uniform_continuous_uniformly_extend _ _ f.uniform_continuous }

local notation `ψ` := f.extend e h_e h_dense

lemma uniform_continuous_extend : uniform_continuous ψ :=
uniform_continuous_uniformly_extend h_e h_dense f.uniform_continuous

end extend_continuous_linear_map

section operator_norm

set_option class.instance_max_depth 70

variables {K : Type*} [nondiscrete_normed_field K]
variables [normed_group α] [normed_space K α]
variables [normed_group β] [normed_space K β]
variables [normed_group γ] [normed_space K γ] [complete_space γ]
variables {f : β →L[K] γ} {e : β →L[K] α}

lemma uniform_embedding_of_norm_le {N : ℝ} (he : ∀b, ∥b∥ ≤ N * ∥e b∥) : uniform_embedding e :=
begin
  refine metric.uniform_embedding_iff.2 ⟨_, e.uniform_continuous, _⟩,
  { assume x y hxy,
    have : ∥e (x - y)∥ = 0 := by simp [hxy],
    have : ∥x - y∥ = 0 := le_antisymm
      (calc ∥x - y∥ ≤ N * ∥e (x - y)∥ : he _
         ... = 0 : by { rw [this, mul_zero] } )
      (norm_nonneg _),
    rwa [norm_eq_zero, sub_eq_zero] at this },
  { assume δ δ0,
    by_cases hN : 0 < N,
    { use (1/N) * δ,
      refine ⟨mul_pos (one_div_pos_of_pos hN) δ0, λa b h, _⟩,
      calc dist a b = ∥a - b∥ : by rw [dist_eq_norm]
        ... ≤ N * ∥e (a - b)∥ : he _
        ... = N * dist (e a) (e b) : by rw [map_sub, dist_eq_norm]
        ... < N * ((1 / N) * δ) : by { rw mul_lt_mul_left hN, exact h }
        ... = δ : by { rw [← mul_assoc, mul_one_div_cancel, one_mul], exact ne_of_gt hN } },
     { use δ, use δ0,
       assume a b h,
       calc dist a b = ∥a - b∥ : by rw dist_eq_norm
         ... ≤ N * ∥e (a - b)∥ : he _
         ... ≤ 0 : mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _)
         ... < δ : δ0 } }
end

lemma uniform_embedding_of_norm_eq (he : ∀b, ∥b∥ = ∥e b∥) : uniform_embedding e :=
have he : ∀b, ∥b∥ ≤ 1 * ∥e b∥ := λb, by { rw one_mul, exact le_of_eq (he b) },
uniform_embedding_of_norm_le he

section

variables {M N : ℝ} (N0 : 0 ≤ N) (h_dense : dense_range e) (h_e : ∀b, ∥b∥ ≤ N * ∥e b∥) (h_f : ∥f∥ ≤ M)

local notation `ψ` := f.extend e (uniform_embedding_of_norm_le h_e).to_uniform_inducing h_dense

lemma norm_uniformly_extend_le' : ∥ψ∥ ≤ M * N :=
have he : uniform_inducing e := (uniform_embedding_of_norm_le h_e).to_uniform_inducing,
uniformly_extend_norm' (he.dense_inducing h_dense)
  (uniformly_extend_of_ind he h_dense f.uniform_continuous)
  N0 h_e h_f

end

section

variables {M : ℝ} (h_dense : dense_range e) (h_e : ∀b, ∥b∥ = ∥e b∥) (h_f : ∥f∥ ≤ M)

local notation `ψ` := f.extend e (uniform_embedding_of_norm_eq h_e).to_uniform_inducing h_dense

lemma norm_uniformly_extend_le {M : ℝ}  (hf : ∥f∥ ≤ M) : ∥ψ∥ ≤ M :=
have he : uniform_inducing e := (uniform_embedding_of_norm_eq h_e).to_uniform_inducing,
uniformly_extend_norm (he.dense_inducing h_dense)
  (uniformly_extend_of_ind he h_dense f.uniform_continuous) h_e hf

end

end operator_norm

end continuous_linear_map












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
    h_dense
    f.map_add
    (uniform_continuous_uniformly_extend h_e h_dense h_f).continuous
    (uniformly_extend_of_ind h_e h_dense h_f) }

local notation `ψ` := f.extend h_f e h_e h_dense

lemma uniform_continuous_extend : uniform_continuous ψ :=
uniform_continuous_uniformly_extend h_e h_dense h_f

end add_monoid_hom
