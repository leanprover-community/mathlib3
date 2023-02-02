/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import analysis.inner_product_space.basic
import analysis.normed_space.completion

/-!
# Inner product space structure of the the Hausdorff completion of an inner product space

## Main results

## Tags

inner product space, Hilbert space, norm, Hausdorff completion

-/

noncomputable theory
open is_R_or_C uniform_space function
variables {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]

namespace uniform_space.completion

instance {𝕜' E' : Type*} [topological_space 𝕜'] [uniform_space E'] [has_inner 𝕜' E'] :
  has_inner 𝕜' (completion E') :=
{ inner := curry $ (dense_inducing_coe.prod dense_inducing_coe).extend (uncurry inner) }

@[simp] lemma inner_coe (a b : E) :
  inner (a : completion E) (b : completion E) = (inner a b : 𝕜) :=
(dense_inducing_coe.prod dense_inducing_coe).extend_eq
  (continuous_inner : continuous (uncurry inner : E × E → 𝕜)) (a, b)

protected lemma continuous_inner :
  continuous (uncurry inner : completion E × completion E → 𝕜) :=
begin
  let inner' : E →+ E →+ 𝕜 :=
  { to_fun := λ x, (innerₛₗ x).to_add_monoid_hom,
    map_zero' := by ext x; exact inner_zero_left,
    map_add' := λ x y, by ext z; exact inner_add_left },
  have : continuous (λ p : E × E, inner' p.1 p.2) := continuous_inner,
  rw [completion.has_inner, uncurry_curry _],
  change continuous (((dense_inducing_to_compl E).prod (dense_inducing_to_compl E)).extend
    (λ p : E × E, inner' p.1 p.2)),
  exact (dense_inducing_to_compl E).extend_Z_bilin (dense_inducing_to_compl E) this,
end

protected lemma continuous.inner {α : Type*} [topological_space α]
  {f g : α → completion E} (hf : continuous f) (hg : continuous g) :
  continuous (λ x : α, inner (f x) (g x) : α → 𝕜) :=
uniform_space.completion.continuous_inner.comp (hf.prod_mk hg : _)

instance : inner_product_space 𝕜 (completion E) :=
{ to_normed_add_comm_group := infer_instance,
  norm_sq_eq_inner := λ x, completion.induction_on x
    (is_closed_eq
      (continuous_norm.pow 2)
      (continuous_re.comp (continuous.inner continuous_id' continuous_id')))
    (λ a, by simp only [norm_coe, inner_coe, inner_self_eq_norm_sq]),
  conj_sym := λ x y, completion.induction_on₂ x y
    (is_closed_eq
      (continuous_conj.comp (continuous.inner continuous_snd continuous_fst))
      (continuous.inner continuous_fst continuous_snd))
    (λ a b, by simp only [inner_coe, inner_conj_sym]),
  add_left := λ x y z, completion.induction_on₃ x y z
    (is_closed_eq
      (continuous.inner (continuous_fst.add (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
      ((continuous.inner continuous_fst (continuous_snd.comp continuous_snd)).add
        (continuous.inner (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd))))
    (λ a b c, by simp only [← coe_add, inner_coe, inner_add_left]),
  smul_left := λ x y c, completion.induction_on₂ x y
    (is_closed_eq
      (continuous.inner (continuous_fst.const_smul c) continuous_snd)
      ((continuous_mul_left _).comp (continuous.inner continuous_fst continuous_snd)))
    (λ a b, by simp only [← coe_smul c a, inner_coe, inner_smul_left]) }

end uniform_space.completion
