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
import data.real.ennreal
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
variables [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
variables [normed_add_comm_group F] [normed_space 𝕜 F]

variables (𝕜 E F)

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of ∥x∥. -/
structure schwartz :=
  (to_fun : E → F)
  (smooth' : cont_diff 𝕜 ⊤ to_fun)
  (decay' : ∀ (k n : ℕ), ∃ (C : ℝ) (hC : 0 < C), ∀ x, ∥x∥^k * ∥iterated_fderiv 𝕜 n to_fun x∥ ≤ C)

variables {𝕜 E F}

namespace schwartz

instance fun_like : fun_like (schwartz 𝕜 E F) E (λ _, F) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun (schwartz 𝕜 E F) (λ _, E → F) := ⟨λ p, p.to_fun⟩

def decay (f : schwartz 𝕜 E F) (k n : ℕ) : ∃ (C : ℝ) (hC : 0 < C),
  ∀ x, ∥x∥^k * ∥iterated_fderiv 𝕜 n f x∥ ≤ C :=
f.decay' k n

def smooth (f : schwartz 𝕜 E F) : cont_diff 𝕜 ⊤ f := f.smooth'

@[ext] lemma ext {f g : schwartz 𝕜 E F} (h : ∀ x, (f : E → F) x = g x) : f = g := fun_like.ext f g h

section seminorms

variables (e : basis ι 𝕜 E) (i : ι) (x : E) (n : ℕ) (a : fin n → ι)
variables (f : E → F) (f': E → ℂ )

#check iterated_fderiv 𝕜 n f x (e ∘ a)
#check finset.univ.prod (λ i, ∥e (a i)∥)


variables [has_smul ℝ F]

noncomputable
def schwartz_seminorm (e : basis ι 𝕜 E) (n k : ℕ) (a : fin k → ι) (f : E → F) : ℝ≥0∞ :=
⨆ x : E, ∥x∥₊^n * ∥iterated_fderiv 𝕜 k f x (e ∘ a)∥₊

lemma mul_lt_left₀ {α : Type*} {a b : α} [linear_ordered_comm_group_with_zero α]
  (c : α) (h : a < b) (hc : 0 < c) :
  c * a < c * b := sorry

lemma seminorm_finite (e : basis ι 𝕜 E) (n k : ℕ) (a : fin k → ι) (f : schwartz 𝕜 E F) :
  schwartz_seminorm e n k a f < ∞ :=
begin
  have hf := f.decay n k,
  rcases hf with ⟨C, hC, hf⟩,
  dunfold schwartz_seminorm,
  rw supr_lt_iff,
  let C' : ℝ≥0 := ⟨C * finset.univ.prod (λ i, ∥e (a i)∥), sorry⟩, -- easy
  refine ⟨C', ennreal.coe_lt_top, _⟩,
  intros x,
  norm_cast,
  specialize hf x,
  rw ←nnreal.coe_le_coe,
  rw nnreal.coe_mul,
  rw nnreal.coe_pow,
  rw coe_nnnorm,
  rw coe_nnnorm,
  simp only [subtype.coe_mk],
  by_cases ha : e ∘ a = 0,
  {
    simp [ha],
    -- need lemma: ⇑(iterated_fderiv 𝕜 k ⇑f x) 0 = 0
    sorry,
  },
  rw ←ne.def at ha,
  rw ←norm_pos_iff at ha,
  have : 0 ≤ finset.univ.prod (λ i, ∥e (a i)∥) := sorry, --easy
  refine has_le.le.trans _ (mul_le_mul_of_nonneg_right hf this),
  have xn_ne : 0 < ∥x∥ ^ n := sorry, -- split cases earlier
  rw mul_assoc,
  rw mul_le_mul_left xn_ne,
  exact continuous_multilinear_map.le_op_norm _ _,
end

#check add_mul

#exit


end seminorms

section smul

variables [semiring R] [module R ℝ] [module R F] [smul_comm_class 𝕜 R F]
variables [has_continuous_const_smul R F]
--[distrib_mul_action R 𝕜] [smul_comm_class 𝕜 R F] [has_continuous_const_smul R F]

instance : has_smul R (schwartz 𝕜 E F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := sorry,
  decay' := λ k n, begin
    rcases f.decay k n with ⟨C, hC, hf⟩,
    refine ⟨C, by positivity, _⟩,
    intros x,
    specialize hf x,
    refine lt_of_le_of_lt _ hf,
    refine mul_le_mul rfl.le _ (by positivity) (by positivity), -- Heather you are the best
    sorry,
  end}⟩
-- need iterated_fderiv_const_smul


end smul


instance : has_zero (schwartz 𝕜 E F) :=
⟨{ to_fun := λ _, 0,
  smooth' := cont_diff_const,
  decay' := λ k n, ⟨1, zero_lt_one, λ _, by simp [iterated_fderiv_within_zero_fun]⟩ }⟩
-- todo: `iterated_fderiv_within_zero_fun` should be `simp`
-- (and be called `iterated_fderiv_zero_fun`)

@[simp] lemma zero_apply {x : E} : (0 : schwartz 𝕜 E F) x = 0 := rfl

instance : has_add (schwartz 𝕜 E F) :=
⟨λ f g, ⟨f + g, f.smooth.add g.smooth,
  begin
    intros k n,
    rcases f.decay k n with ⟨Cf, hCf, hf⟩,
    rcases g.decay k n with ⟨Cg, hCg, hg⟩,
    refine ⟨Cf + Cg, by positivity, λ x, _⟩, -- Thank you Heather
    specialize hf x,
    specialize hg x,
    refine lt_of_le_of_lt _ (add_lt_add hf hg),
    rw ←mul_add,
    refine mul_le_mul rfl.le _ (by positivity) (by positivity), -- Heather you are the best
    convert norm_add_le _ _,
    -- need lemma iterated_fderiv_add
    sorry,
  end⟩ ⟩

@[simp] lemma add_apply {f g : schwartz 𝕜 E F} {x : E} : (f + g) x = f x + g x := rfl

instance : add_zero_class (schwartz 𝕜 E F) :=
{ zero := has_zero.zero,
  add := has_add.add,
  zero_add := λ _, by { ext, rw [add_apply, zero_apply, zero_add] },
  add_zero := λ _, by { ext, rw [add_apply, zero_apply, add_zero] } }


instance : add_comm_monoid (schwartz 𝕜 E F) :=
fun_like.coe_injective.add_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)


variables (f g : schwartz 𝕜 E F) (x : E)

#check f + g

/-
instance : has_coe (schwartz_space 𝕜 E) (E → 𝕜) := ⟨subtype.val⟩

instance : can_lift (E → 𝕜) (schwartz_space 𝕜 E) := subtype.can_lift _

protected lemma eq {f g : schwartz_space 𝕜 E} : (f : E → 𝕜) = (g : E → 𝕜) → f = g := subtype.eq

lemma mem_schwartz_space {f : E → 𝕜} : f ∈ schwartz_space 𝕜 E ↔ is_schwartz f := iff.rfl
-/
end schwartz
