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

variables {R E F ι : Type*}
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
  refine mul_le_mul rfl.le _ (by positivity) (by positivity),
  convert norm_add_le _ _,
  -- need lemma iterated_fderiv_add
  sorry,
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
variables [has_continuous_const_smul R F] [has_coe R ℝ]
--[distrib_mul_action R 𝕜] [smul_comm_class 𝕜 R F] [has_continuous_const_smul R F]

variables (r : R)
#check ∥(r : ℝ)∥

instance : has_smul R (schwartz E F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := sorry,
  decay' := λ k n, begin
    rcases f.decay k n with ⟨C, hC, hf⟩,
    refine ⟨C, by positivity, _⟩,
    intros x,
    specialize hf x,
    refine has_le.le.trans _ hf,
    refine mul_le_mul_of_nonneg_left _ (by positivity),
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

instance : add_zero_class (schwartz E F) :=
{ zero := has_zero.zero,
  add := has_add.add,
  zero_add := λ _, by { ext, rw [add_apply, zero_apply, zero_add] },
  add_zero := λ _, by { ext, rw [add_apply, zero_apply, add_zero] } }


instance : add_comm_monoid (schwartz E F) :=
fun_like.coe_injective.add_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)


variables (f g : schwartz E F) (x : E)

#check f + g

end schwartz
