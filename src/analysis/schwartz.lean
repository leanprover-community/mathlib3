/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.cont_diff
import analysis.inner_product_space.basic
import analysis.normed_space.basic
import analysis.normed_space.operator_norm
import analysis.asymptotics.superpolynomial_decay
import algebra.big_operators.fin
import analysis.seminorm
import analysis.normed_space.multilinear

/-!
# Schwartz

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open filter
open_locale big_operators ennreal nnreal

variables {R 𝕜 E F ι : Type*}

section iterated_fderiv

variables [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group E] [normed_space 𝕜 E]
variables [normed_add_comm_group F] [normed_space 𝕜 F]

lemma cont_diff.differentiable_at_iterated_fderiv {n k : ℕ} {f : E → F} (hf : cont_diff 𝕜 n f)
  (h : k < n):
  differentiable 𝕜 (iterated_fderiv 𝕜 k f) :=
begin
  rw [←differentiable_on_univ, ←iterated_fderiv_within_univ],
  refine hf.cont_diff_on.differentiable_on_iterated_fderiv_within _ unique_diff_on_univ,
  simp only [h, with_top.coe_lt_coe],
end

-- iterated_fderiv_add
lemma iterated_fderiv_add {n : ℕ} {f g : E → F} (hf : cont_diff 𝕜 n f)
  (hg : cont_diff 𝕜 n g):
  iterated_fderiv 𝕜 n (λ x, f x + g x) = iterated_fderiv 𝕜 n f + iterated_fderiv 𝕜 n g :=
begin
  induction n with k hk,
  { ext, simp },
  specialize hk (hf.of_le $ with_top.coe_le_coe.mpr $ k.le_succ),
  specialize hk (hg.of_le $ with_top.coe_le_coe.mpr $ k.le_succ),
  ext x m,
  rw [pi.add_apply, continuous_multilinear_map.add_apply],
  simp_rw iterated_fderiv_succ_apply_left m,
  rw [←continuous_multilinear_map.add_apply],
  congr,
  rw ←continuous_linear_map.add_apply,
  congr,
  have hf' : differentiable_at 𝕜 (iterated_fderiv 𝕜 k f) x :=
  (cont_diff.differentiable_at_iterated_fderiv hf (lt_add_one k)).differentiable_at,
  have hg' : differentiable_at 𝕜 (iterated_fderiv 𝕜 k g) x :=
  (cont_diff.differentiable_at_iterated_fderiv hg (lt_add_one k)).differentiable_at,
  rw ←fderiv_add hf' hg',
  congr,
  ext,
  rw hk,
  rw pi.add_apply,
end

-- iterated_fderiv_add
lemma iterated_fderiv_add_apply {n : ℕ} {f g : E → F} {x : E} (hf : cont_diff 𝕜 n f)
  (hg : cont_diff 𝕜 n g):
  iterated_fderiv 𝕜 n (λ x, f x + g x) x = iterated_fderiv 𝕜 n f x + iterated_fderiv 𝕜 n g x :=
begin
  refine (congr_fun (iterated_fderiv_add hf hg) x).trans _,
  rw [pi.add_apply],
end

variables [semiring R] [module R F] [smul_comm_class 𝕜 R F] [has_continuous_const_smul R F]
-- iterated_fderiv_const_smul
lemma iterated_fderiv_const_smul {n : ℕ} {f : E → F} (hf : cont_diff 𝕜 n f) (c : R) :
  iterated_fderiv 𝕜 n (λ y, c • f y) = c • iterated_fderiv 𝕜 n f :=
begin
  induction n with k hk,
  { ext, simp },
  specialize hk (hf.of_le $ with_top.coe_le_coe.mpr $ k.le_succ),
  ext x m,
  rw [pi.smul_apply, continuous_multilinear_map.smul_apply],
  simp_rw iterated_fderiv_succ_apply_left m,
  rw [←continuous_multilinear_map.add_apply],
  congr,
  sorry,
end

end iterated_fderiv

variables [normed_add_comm_group E] [normed_space ℝ E]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables (E F)

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of ∥x∥. -/
structure schwartz :=
  (to_fun : E → F)
  (smooth' : cont_diff ℝ ⊤ to_fun)
  (decay' : ∀ (k n : ℕ), ∃ (C : ℝ) (hC : 0 < C), ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n to_fun x∥ ≤ C)

variables {E F}

namespace schwartz

-- General nonsense for `fun_like` structures

instance fun_like : fun_like (schwartz E F) E (λ _, F) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (schwartz E F) (λ _, E → F) := ⟨λ p, p.to_fun⟩

def decay (f : schwartz E F) (k n : ℕ) : ∃ (C : ℝ) (hC : 0 < C),
  ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ C :=
f.decay' k n

def smooth (f : schwartz E F) : cont_diff ℝ ⊤ f := f.smooth'

@[ext] lemma ext {f g : schwartz E F} (h : ∀ x, (f : E → F) x = g x) : f = g := fun_like.ext f g h

section aux

lemma seminorm_add_le_aux (k n : ℕ) (f g : schwartz E F) (x : E) :
  ∥x∥^k * ∥iterated_fderiv ℝ n (f+g) x∥ ≤
  ∥x∥^k * ∥iterated_fderiv ℝ n f x∥
  + ∥x∥^k * ∥iterated_fderiv ℝ n g x∥ :=
begin
  rw ←mul_add,
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  convert norm_add_le _ _,
  refine iterated_fderiv_add_apply _ _,
  { exact f.smooth.of_le (le_of_lt $ with_top.coe_lt_top _) },
  { exact g.smooth.of_le (le_of_lt $ with_top.coe_lt_top _) },
end

end aux

section seminorms

variables (e : basis ι ℝ E) (i : ι) (x : E) (n : ℕ) (a : fin n → ι)
variables (f : E → F) (f': E → ℂ )

#check iterated_fderiv ℝ n f x (e ∘ a)
#check finset.univ.prod (λ i, ∥e (a i)∥)


variables [has_smul ℝ F]

@[protected]
noncomputable
def seminorm (k n : ℕ) (f : schwartz E F) : ℝ :=
Inf {c | 0 ≤ c ∧ ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ c}

lemma bounds_nonempty (k n : ℕ) (f : schwartz E F) :
  ∃ (c : ℝ), c ∈ {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ c} :=
let ⟨M, hMp, hMb⟩ := f.decay k n in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below (k n : ℕ) (f : schwartz E F) :
  bdd_below { c | 0 ≤ c ∧ ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ c } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma seminorm_le_bound (k n : ℕ) (f : schwartz E F) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ M) :
  f.seminorm k n ≤ M :=
cInf_le (bounds_bdd_below k n f) ⟨hMp, hM⟩

lemma op_norm_nonneg (k n : ℕ) (f : schwartz E F) : 0 ≤ f.seminorm k n :=
le_cInf (bounds_nonempty k n f) (λ _ ⟨hx, _⟩, hx)

end seminorms

section smul

variables [semiring R] [module R ℝ] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R ℝ F]
--[distrib_mul_action R 𝕜] [smul_comm_class 𝕜 R F] [has_continuous_const_smul R F]

variables (r : R)
#check ∥r • (1 : ℝ)∥

instance : has_smul R (schwartz E F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := sorry,
  decay' := λ k n, begin
    rcases f.decay k n with ⟨C, hC, hf⟩,
    refine ⟨C * (∥c • (1 : ℝ)∥+1), by positivity, _⟩,
    intros x,
    specialize hf x,
    have hc : 0 ≤ ∥c • (1 : ℝ)∥ := by positivity,
    refine le_trans _ ((mul_le_mul_of_nonneg_right hf hc).trans _),
    {
      rw mul_assoc,
      refine mul_le_mul_of_nonneg_left _ (by positivity),
      sorry,
    },
    sorry,
  end}⟩
-- need iterated_fderiv_const_smul


end smul


instance : has_zero (schwartz E F) :=
⟨{ to_fun := λ _, 0,
  smooth' := cont_diff_const,
  decay' := λ k n, ⟨1, zero_lt_one, λ _, by simp [iterated_fderiv_within_zero_fun]⟩ }⟩
-- todo: `iterated_fderiv_within_zero_fun` should be `simp`
-- (and be called `iterated_fderiv_zero_fun`)

@[simp] lemma zero_apply {x : E} : (0 : schwartz E F) x = 0 := rfl

instance : has_add (schwartz E F) :=
⟨λ f g, ⟨f + g, f.smooth.add g.smooth,
  begin
    intros k n,
    rcases f.decay k n with ⟨Cf, hCf, hf⟩,
    rcases g.decay k n with ⟨Cg, hCg, hg⟩,
    refine ⟨Cf + Cg, by positivity, λ x, _⟩,
    specialize hf x,
    specialize hg x,
    refine le_trans _ (add_le_add hf hg),
    exact seminorm_add_le_aux k n f g x,
  end⟩ ⟩

@[simp] lemma add_apply {f g : schwartz E F} {x : E} : (f + g) x = f x + g x := rfl
/-
instance : add_zero_class (schwartz E F) :=
{ zero := has_zero.zero,
  add := has_add.add,
  zero_add := λ _, by { ext, rw [add_apply, zero_apply, zero_add] },
  add_zero := λ _, by { ext, rw [add_apply, zero_apply, add_zero] } }-/


instance : add_comm_monoid (schwartz E F) :=
fun_like.coe_injective.add_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)


variables (f g : schwartz E F) (x : E)

#check f + g

end schwartz
