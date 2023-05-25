/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.cont_diff
import analysis.calculus.iterated_deriv
import analysis.locally_convex.with_seminorms
import topology.algebra.uniform_filter_basis
import topology.continuous_function.bounded
import tactic.positivity
import analysis.special_functions.pow.real

/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖^k * ‖iterated_fderiv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates. The abstract theory of topological vector spaces developed in
`seminorm_family.module_filter_basis` and `with_seminorms.to_locally_convex_space` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `schwartz_map`: The Schwartz space is the space of smooth functions such that all derivatives
decay faster than any power of `‖x‖`.
* `schwartz_map.seminorm`: The family of seminorms as described above
* `schwartz_map.fderiv_clm`: The differential as a continuous linear map
`𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`
* `schwartz_map.deriv_clm`: The one-dimensional derivative as a continuous linear map
`𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`

## Main statements

* `schwartz_map.uniform_add_group` and `schwartz_map.locally_convex`: The Schwartz space is a
locally convex topological vector space.
* `schwartz_map.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
on `(1 + ‖x‖) ^ k * ‖iterated_fderiv ℝ n f x‖`.

## Implementation details

The implementation of the seminorms is taken almost literally from `continuous_linear_map.op_norm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `schwartz_map E F` localized in `schwartz_space`

## Tags

Schwartz space, tempered distributions
-/

noncomputable theory

open_locale big_operators nat

variables {𝕜 𝕜' D E F G : Type*}

variables [normed_add_comm_group E] [normed_space ℝ E]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables (E F)

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
structure schwartz_map :=
  (to_fun : E → F)
  (smooth' : cont_diff ℝ ⊤ to_fun)
  (decay' : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n to_fun x‖ ≤ C)

localized "notation `𝓢(` E `, ` F `)` := schwartz_map E F" in schwartz_space

variables {E F}

namespace schwartz_map

instance : has_coe 𝓢(E, F) (E → F) := ⟨to_fun⟩

instance fun_like : fun_like 𝓢(E, F) E (λ _, F) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun 𝓢(E, F) (λ _, E → F) := ⟨λ p, p.to_fun⟩

/-- All derivatives of a Schwartz function are rapidly decaying. -/
lemma decay (f : 𝓢(E, F)) (k n : ℕ) : ∃ (C : ℝ) (hC : 0 < C),
  ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ C :=
begin
  rcases f.decay' k n with ⟨C, hC⟩,
  exact ⟨max C 1, by positivity, λ x, (hC x).trans (le_max_left _ _)⟩,
end

/-- Every Schwartz function is smooth. -/
lemma smooth (f : 𝓢(E, F)) (n : ℕ∞) : cont_diff ℝ n f := f.smooth'.of_le le_top

/-- Every Schwartz function is continuous. -/
@[continuity, protected] lemma continuous (f : 𝓢(E, F)) : continuous f := (f.smooth 0).continuous

/-- Every Schwartz function is differentiable. -/
@[protected] lemma differentiable (f : 𝓢(E, F)) : differentiable ℝ f :=
(f.smooth 1).differentiable rfl.le

/-- Every Schwartz function is differentiable at any point. -/
@[protected] lemma differentiable_at (f : 𝓢(E, F)) {x : E} : differentiable_at ℝ f x :=
f.differentiable.differentiable_at

@[ext] lemma ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g := fun_like.ext f g h

section is_O

variables (f : 𝓢(E, F))

/-- Auxiliary lemma, used in proving the more general result `is_O_cocompact_zpow`. -/
lemma is_O_cocompact_zpow_neg_nat (k : ℕ) :
  asymptotics.is_O (filter.cocompact E) f (λ x, ‖x‖ ^ (-k : ℤ)) :=
begin
  obtain ⟨d, hd, hd'⟩ := f.decay k 0,
  simp_rw norm_iterated_fderiv_zero at hd',
  simp_rw [asymptotics.is_O, asymptotics.is_O_with],
  refine ⟨d, filter.eventually.filter_mono filter.cocompact_le_cofinite _⟩,
  refine (filter.eventually_cofinite_ne 0).mp (filter.eventually_of_forall (λ x hx, _)),
  rwa [real.norm_of_nonneg (zpow_nonneg (norm_nonneg _) _), zpow_neg, ←div_eq_mul_inv, le_div_iff'],
  exacts [hd' x, zpow_pos_of_pos (norm_pos_iff.mpr hx) _],
end

lemma is_O_cocompact_rpow [proper_space E] (s : ℝ) :
  asymptotics.is_O (filter.cocompact E) f (λ x, ‖x‖ ^ s) :=
begin
  let k := ⌈-s⌉₊,
  have hk : -(k : ℝ) ≤ s, from neg_le.mp (nat.le_ceil (-s)),
  refine (is_O_cocompact_zpow_neg_nat f k).trans _,
  refine (_ : asymptotics.is_O filter.at_top
    (λ x:ℝ, x ^ (-k : ℤ)) (λ x:ℝ, x ^ s)).comp_tendsto tendsto_norm_cocompact_at_top,
  simp_rw [asymptotics.is_O, asymptotics.is_O_with],
  refine ⟨1, filter.eventually_of_mem (filter.eventually_ge_at_top 1) (λ x hx, _)⟩,
  rw [one_mul, real.norm_of_nonneg (real.rpow_nonneg_of_nonneg (zero_le_one.trans hx) _),
    real.norm_of_nonneg (zpow_nonneg (zero_le_one.trans hx) _), ←real.rpow_int_cast, int.cast_neg,
    int.cast_coe_nat],
  exact real.rpow_le_rpow_of_exponent_le hx hk,
end

lemma is_O_cocompact_zpow [proper_space E] (k : ℤ) :
  asymptotics.is_O (filter.cocompact E) f (λ x, ‖x‖ ^ k) :=
by simpa only [real.rpow_int_cast] using is_O_cocompact_rpow f k

end is_O

section aux

lemma bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
  ∃ (c : ℝ), c ∈ {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ c} :=
let ⟨M, hMp, hMb⟩ := f.decay k n in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below (k n : ℕ) (f : 𝓢(E, F)) :
  bdd_below {c | 0 ≤ c ∧ ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ c} :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
  ‖x‖^k * ‖iterated_fderiv ℝ n (f+g) x‖ ≤
  ‖x‖^k * ‖iterated_fderiv ℝ n f x‖
  + ‖x‖^k * ‖iterated_fderiv ℝ n g x‖ :=
begin
  rw ←mul_add,
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  convert norm_add_le _ _,
  exact iterated_fderiv_add_apply (f.smooth _) (g.smooth _),
end

lemma decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n (-f) x‖ = ‖x‖ ^ k * ‖iterated_fderiv ℝ n f x‖ :=
begin
  nth_rewrite 3 ←norm_neg,
  congr,
  exact iterated_fderiv_neg_apply,
end

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

lemma decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n (c • f) x‖ =
  ‖c‖ * ‖x‖ ^ k * ‖iterated_fderiv ℝ n f x‖ :=
by rw [mul_comm (‖c‖), mul_assoc, iterated_fderiv_const_smul_apply (f.smooth _), norm_smul]

end aux

section seminorm_aux

/-- Helper definition for the seminorms of the Schwartz space. -/
@[protected]
def seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
Inf {c | 0 ≤ c ∧ ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ c}

lemma seminorm_aux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminorm_aux k n :=
le_cInf (bounds_nonempty k n f) (λ _ ⟨hx, _⟩, hx)

lemma le_seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n ⇑f x‖ ≤ f.seminorm_aux k n :=
le_cInf (bounds_nonempty k n f) (λ y ⟨_, h⟩, h x)

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma seminorm_aux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ M) :
  f.seminorm_aux k n ≤ M :=
cInf_le (bounds_bdd_below k n f) ⟨hMp, hM⟩

end seminorm_aux

/-! ### Algebraic properties -/

section smul

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
  [normed_field 𝕜'] [normed_space 𝕜' F] [smul_comm_class ℝ 𝕜' F]

instance : has_smul 𝕜 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := (f.smooth _).const_smul c,
  decay' := λ k n, begin
    refine ⟨f.seminorm_aux k n * (‖c‖+1), λ x, _⟩,
    have hc : 0 ≤ ‖c‖ := by positivity,
    refine le_trans _ ((mul_le_mul_of_nonneg_right (f.le_seminorm_aux k n x) hc).trans _),
    { apply eq.le,
      rw [mul_comm _ (‖c‖), ← mul_assoc],
      exact decay_smul_aux k n f c x },
    { apply mul_le_mul_of_nonneg_left _ (f.seminorm_aux_nonneg k n),
      linarith }
  end}⟩

@[simp] lemma smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • (f x) := rfl

instance
[has_smul 𝕜 𝕜'] [is_scalar_tower 𝕜 𝕜' F] : is_scalar_tower 𝕜 𝕜' 𝓢(E, F) :=
⟨λ a b f, ext $ λ x, smul_assoc a b (f x)⟩

instance [smul_comm_class 𝕜 𝕜' F] : smul_comm_class 𝕜 𝕜' 𝓢(E, F) :=
⟨λ a b f, ext $ λ x, smul_comm a b (f x)⟩

lemma seminorm_aux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) :
  (c • f).seminorm_aux k n ≤ ‖c‖ * f.seminorm_aux k n :=
begin
  refine (c • f).seminorm_aux_le_bound k n (mul_nonneg (norm_nonneg _) (seminorm_aux_nonneg _ _ _))
    (λ x, (decay_smul_aux k n f c x).le.trans _),
  rw mul_assoc,
  exact mul_le_mul_of_nonneg_left (f.le_seminorm_aux k n x) (norm_nonneg _),
end

instance has_nsmul : has_smul ℕ 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := (f.smooth _).const_smul c,
  decay' := begin
    have : c • (f : E → F) = (c : ℝ) • f,
    { ext x, simp only [pi.smul_apply, ← nsmul_eq_smul_cast] },
    simp only [this],
    exact ((c : ℝ) • f).decay',
  end}⟩

instance has_zsmul : has_smul ℤ 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := (f.smooth _).const_smul c,
  decay' := begin
    have : c • (f : E → F) = (c : ℝ) • f,
    { ext x, simp only [pi.smul_apply, ← zsmul_eq_smul_cast] },
    simp only [this],
    exact ((c : ℝ) • f).decay',
  end}⟩

end smul

section zero

instance : has_zero 𝓢(E, F) :=
⟨{ to_fun := λ _, 0,
  smooth' := cont_diff_const,
  decay' := λ _ _, ⟨1, λ _, by simp⟩ }⟩

instance : inhabited 𝓢(E, F) := ⟨0⟩

lemma coe_zero : ↑(0 : 𝓢(E, F)) = (0 : E → F) := rfl

@[simp] lemma coe_fn_zero : coe_fn (0 : 𝓢(E, F)) = (0 : E → F) := rfl

@[simp] lemma zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 := rfl

lemma seminorm_aux_zero (k n : ℕ) :
  (0 : 𝓢(E, F)).seminorm_aux k n = 0 :=
le_antisymm (seminorm_aux_le_bound k n _ rfl.le (λ _, by simp [pi.zero_def]))
  (seminorm_aux_nonneg _ _ _)

end zero

section neg

instance : has_neg 𝓢(E, F) :=
⟨λ f, ⟨-f, (f.smooth _).neg, λ k n,
  ⟨f.seminorm_aux k n, λ x, (decay_neg_aux k n f x).le.trans (f.le_seminorm_aux k n x)⟩⟩⟩

end neg

section add

instance : has_add 𝓢(E, F) :=
⟨λ f g, ⟨f + g, (f.smooth _).add (g.smooth _), λ k n,
  ⟨f.seminorm_aux k n + g.seminorm_aux k n, λ x, (decay_add_le_aux k n f g x).trans
    (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x))⟩⟩⟩

@[simp] lemma add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x := rfl

lemma seminorm_aux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
  (f + g).seminorm_aux k n ≤ f.seminorm_aux k n + g.seminorm_aux k n :=
(f + g).seminorm_aux_le_bound k n
  (add_nonneg (seminorm_aux_nonneg _ _ _) (seminorm_aux_nonneg _ _ _)) $
  λ x, (decay_add_le_aux k n f g x).trans $
  add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x)

end add

section sub

instance : has_sub 𝓢(E, F) :=
⟨λ f g, ⟨f - g, (f.smooth _).sub (g.smooth _),
  begin
    intros k n,
    refine ⟨f.seminorm_aux k n + g.seminorm_aux k n, λ x, _⟩,
    refine le_trans _ (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x)),
    rw sub_eq_add_neg,
    rw ←decay_neg_aux k n g x,
    convert decay_add_le_aux k n f (-g) x,
    -- exact fails with deterministic timeout
  end⟩ ⟩

@[simp] lemma sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x := rfl

end sub

section add_comm_group

instance : add_comm_group 𝓢(E, F) :=
fun_like.coe_injective.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl)

variables (E F)

/-- Coercion as an additive homomorphism. -/
def coe_hom : 𝓢(E, F) →+ (E → F) :=
{ to_fun := λ f, f, map_zero' := coe_zero, map_add' := λ _ _, rfl }

variables {E F}

lemma coe_coe_hom : (coe_hom E F : 𝓢(E, F) → (E → F)) = coe_fn := rfl

lemma coe_hom_injective : function.injective (coe_hom E F) :=
by { rw coe_coe_hom, exact fun_like.coe_injective }

end add_comm_group

section module

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

instance : module 𝕜 𝓢(E, F) :=
coe_hom_injective.module 𝕜 (coe_hom E F) (λ _ _, rfl)

end module

section seminorms

/-! ### Seminorms on Schwartz space-/

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
@[protected]
def seminorm (k n : ℕ) : seminorm 𝕜 𝓢(E, F) := seminorm.of_smul_le (seminorm_aux k n)
  (seminorm_aux_zero k n) (seminorm_aux_add_le k n) (seminorm_aux_smul_le k n)

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
lemma seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ M) : seminorm 𝕜 k n f ≤ M :=
f.seminorm_aux_le_bound k n hMp hM

/-- If one controls the seminorm for every `x`, then one controls the seminorm.

Variant for functions `𝓢(ℝ, F)`. -/
lemma seminorm_le_bound' (k n : ℕ) (f : 𝓢(ℝ, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, |x|^k * ‖iterated_deriv n f x‖ ≤ M) : seminorm 𝕜 k n f ≤ M :=
begin
  refine seminorm_le_bound 𝕜 k n f hMp _,
  simpa only [real.norm_eq_abs, norm_iterated_fderiv_eq_norm_iterated_deriv],
end

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
lemma le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n f x‖ ≤ seminorm 𝕜 k n f :=
f.le_seminorm_aux k n x

/-- The seminorm controls the Schwartz estimate for any fixed `x`.

Variant for functions `𝓢(ℝ, F)`. -/
lemma le_seminorm' (k n : ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
  |x| ^ k * ‖iterated_deriv n f x‖ ≤ seminorm 𝕜 k n f :=
begin
  have := le_seminorm 𝕜 k n f x,
  rwa [← real.norm_eq_abs, ← norm_iterated_fderiv_eq_norm_iterated_deriv],
end

lemma norm_iterated_fderiv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
  ‖iterated_fderiv ℝ n f x₀‖ ≤ (schwartz_map.seminorm 𝕜 0 n) f :=
begin
  have := schwartz_map.le_seminorm 𝕜 0 n f x₀,
  rwa [pow_zero, one_mul] at this,
end

lemma norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) :
  ‖x₀‖^k * ‖f x₀‖ ≤ (schwartz_map.seminorm 𝕜 k 0) f :=
begin
  have := schwartz_map.le_seminorm 𝕜 k 0 f x₀,
  rwa norm_iterated_fderiv_zero at this,
end

lemma norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) :
  ‖f x₀‖ ≤ (schwartz_map.seminorm 𝕜 0 0) f :=
begin
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀,
  rwa [pow_zero, one_mul] at this,
end

variables (𝕜 E F)

/-- The family of Schwartz seminorms. -/
def _root_.schwartz_seminorm_family : seminorm_family 𝕜 𝓢(E, F) (ℕ × ℕ) :=
λ m, seminorm 𝕜 m.1 m.2

@[simp] lemma schwartz_seminorm_family_apply (n k : ℕ) :
  schwartz_seminorm_family 𝕜 E F (n,k) = schwartz_map.seminorm 𝕜 n k := rfl

@[simp] lemma schwartz_seminorm_family_apply_zero :
  schwartz_seminorm_family 𝕜 E F 0 = schwartz_map.seminorm 𝕜 0 0 := rfl

variables {𝕜 E F}

/-- A more convenient version of `le_sup_seminorm_apply`.

The set `finset.Iic m` is the set of all pairs `(k', n')` with `k' ≤ m.1` and `n' ≤ m.2`.
Note that the constant is far from optimal. -/
lemma one_add_le_sup_seminorm_apply {m : ℕ × ℕ} {k n : ℕ} (hk : k ≤ m.1) (hn : n ≤ m.2)
  (f : 𝓢(E, F)) (x : E) :
  (1 + ‖x‖) ^ k * ‖iterated_fderiv ℝ n f x‖
    ≤ 2^m.1 * (finset.Iic m).sup (λ m, seminorm 𝕜 m.1 m.2) f :=
begin
  rw [add_comm, add_pow],
  simp only [one_pow, mul_one, finset.sum_congr, finset.sum_mul],
  norm_cast,
  rw ← nat.sum_range_choose m.1,
  push_cast,
  rw [finset.sum_mul],
  have hk' : finset.range (k + 1) ⊆ finset.range (m.1 + 1) :=
  by rwa [finset.range_subset, add_le_add_iff_right],
  refine le_trans (finset.sum_le_sum_of_subset_of_nonneg hk' (λ _ _ _, by positivity)) _,
  refine finset.sum_le_sum (λ i hi, _),
  rw [mul_comm (‖x‖^i), mul_assoc],
  refine mul_le_mul _ _ (by positivity) (by positivity),
  { norm_cast,
    exact i.choose_le_choose hk },
  exact (le_seminorm 𝕜 i n f x).trans (seminorm.le_def.1 (finset.le_sup_of_le
    (finset.mem_Iic.2 $ prod.mk_le_mk.2 ⟨finset.mem_range_succ_iff.mp hi, hn⟩) le_rfl) _),
end

end seminorms

section topology

/-! ### The topology on the Schwartz space-/

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
variables (𝕜 E F)

instance : topological_space 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).module_filter_basis.topology'

lemma _root_.schwartz_with_seminorms : with_seminorms (schwartz_seminorm_family 𝕜 E F) :=
begin
  have A : with_seminorms (schwartz_seminorm_family ℝ E F) := ⟨rfl⟩,
  rw seminorm_family.with_seminorms_iff_nhds_eq_infi at ⊢ A,
  rw A,
  refl
end

variables {𝕜 E F}

instance : has_continuous_smul 𝕜 𝓢(E, F) :=
begin
  rw (schwartz_with_seminorms 𝕜 E F).with_seminorms_eq,
  exact (schwartz_seminorm_family 𝕜 E F).module_filter_basis.has_continuous_smul,
end

instance : topological_add_group 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).add_group_filter_basis.is_topological_add_group

instance : uniform_space 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).add_group_filter_basis.uniform_space

instance : uniform_add_group 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).add_group_filter_basis.uniform_add_group

instance : locally_convex_space ℝ 𝓢(E, F) :=
(schwartz_with_seminorms ℝ E F).to_locally_convex_space

instance : topological_space.first_countable_topology (𝓢(E, F)) :=
(schwartz_with_seminorms ℝ E F).first_countable

end topology

section clm

/-! ### Construction of continuous linear maps between Schwartz spaces -/

variables [normed_field 𝕜] [normed_field 𝕜']
variables [normed_add_comm_group D] [normed_space ℝ D]
variables [normed_space 𝕜 E] [smul_comm_class ℝ 𝕜 E]
variables [normed_add_comm_group G] [normed_space ℝ G] [normed_space 𝕜' G] [smul_comm_class ℝ 𝕜' G]
variables {σ : 𝕜 →+* 𝕜'}

/-- Create a semilinear map between Schwartz spaces.

Note: This is a helper definition for `mk_clm`. -/
def mk_lm (A : (D → E) → (F → G))
  (hadd : ∀ (f g : 𝓢(D, E)) x, A (f + g) x = A f x + A g x)
  (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) x, A (a • f) x = σ a • A f x)
  (hsmooth : ∀ (f : 𝓢(D, E)), cont_diff ℝ ⊤ (A f))
  (hbound : ∀ (n : ℕ × ℕ), ∃ (s : finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C), ∀ (f : 𝓢(D, E)) (x : F),
  ‖x‖ ^ n.fst * ‖iterated_fderiv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartz_seminorm_family 𝕜 D E) f) :
  𝓢(D, E) →ₛₗ[σ] 𝓢(F, G) :=
{ to_fun := λ f,
  { to_fun := A f,
    smooth' := hsmooth f,
    decay' :=
    begin
      intros k n,
      rcases hbound ⟨k, n⟩ with ⟨s, C, hC, h⟩,
      exact ⟨C * (s.sup (schwartz_seminorm_family 𝕜 D E)) f, h f⟩,
    end, },
  map_add' := λ f g, ext (hadd f g),
  map_smul' := λ a f, ext (hsmul a f), }

/-- Create a continuous semilinear map between Schwartz spaces.

For an example of using this definition, see `fderiv_clm`. -/
def mk_clm [ring_hom_isometric σ] (A : (D → E) → (F → G))
  (hadd : ∀ (f g : 𝓢(D, E)) x, A (f + g) x = A f x + A g x)
  (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) x, A (a • f) x = σ a • A f x)
  (hsmooth : ∀ (f : 𝓢(D, E)), cont_diff ℝ ⊤ (A f))
  (hbound : ∀ (n : ℕ × ℕ), ∃ (s : finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C), ∀ (f : 𝓢(D, E)) (x : F),
  ‖x‖ ^ n.fst * ‖iterated_fderiv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartz_seminorm_family 𝕜 D E) f) :
  𝓢(D, E) →SL[σ] 𝓢(F, G) :=
{ cont :=
  begin
    change continuous (mk_lm A hadd hsmul hsmooth hbound : 𝓢(D, E) →ₛₗ[σ] 𝓢(F, G)),
    refine seminorm.continuous_from_bounded (schwartz_with_seminorms 𝕜 D E)
      (schwartz_with_seminorms 𝕜' F G) _ (λ n, _),
    rcases hbound n with ⟨s, C, hC, h⟩,
    refine ⟨s, ⟨C, hC⟩, (λ f, _)⟩,
    simp only [seminorm.comp_apply, seminorm.smul_apply, nnreal.smul_def, algebra.id.smul_eq_mul,
      subtype.coe_mk],
    exact (mk_lm A hadd hsmul hsmooth hbound f).seminorm_le_bound 𝕜' n.1 n.2 (by positivity) (h f),
  end,
  to_linear_map := mk_lm A hadd hsmul hsmooth hbound }

end clm

section multiplication

variables [normed_add_comm_group D] [normed_space ℝ D]
variables [normed_add_comm_group G] [normed_space ℝ G]

/-- Provided one can estimate each `iterated_fderiv ℝ n` by `C * (1 + ‖x‖)^k`,
then one can find `C` and `k` independent of `n` such that the same estimate holds. -/
lemma norm_iterated_fderiv_le_uniform_aux {g : D → F}
  (hg_growth : ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ (x : D), ‖iterated_fderiv ℝ n g x‖ ≤ C * (1 + ‖x‖)^k) :
  ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ) (hC : 0 ≤ C), ∀ (N : ℕ) (hN : N ≤ n) (x : D) ,
    ‖iterated_fderiv ℝ N g x‖ ≤ C * (1 + ‖x‖)^k :=
begin
  intro n,
  choose k C f using hg_growth,
  use (finset.range (n+1)).sup k,
  let C' := max (0 : ℝ) ((finset.range (n+1)).sup' (by simp) C),
  have hC' : 0 ≤ C' := by simp only [le_refl, finset.le_sup'_iff, true_or, le_max_iff],
  use [C', hC'],
  intros N hN x,
  rw ← finset.mem_range_succ_iff at hN,
  refine le_trans (f N x) (mul_le_mul _ _ (by positivity) hC'),
  { simp only [finset.le_sup'_iff, le_max_iff],
    right,
    exact ⟨N, hN, rfl.le⟩ },
  refine pow_le_pow (by simp only [le_add_iff_nonneg_right, norm_nonneg]) _,
  exact finset.le_sup hN,
end

/-- The multiplication with a smooth function of temperate growth is a continuous linear map on
Schwartz space. -/
def mul_clm (B : E →L[ℝ] F →L[ℝ] G) {g : D → F} (hg_smooth : cont_diff ℝ ⊤ g)
  (hg_growth : ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ (x : D), ‖iterated_fderiv ℝ n g x‖ ≤ C * (1 + ‖x‖)^k) :
  𝓢(D, E) →L[ℝ] 𝓢(D, G) :=
mk_clm (λ f x, B (f x) (g x))
  (λ _ _ _, by simp only [map_add, add_left_inj, pi.add_apply, eq_self_iff_true,
    continuous_linear_map.add_apply])
  (λ _ _ _, by simp only [pi.smul_apply, continuous_linear_map.coe_smul',
    continuous_linear_map.map_smul, ring_hom.id_apply])
  (λ f, B.is_bounded_bilinear_map.cont_diff.comp (f.smooth'.prod hg_smooth))
  (begin
    -- Porting note: rewrite this proof with `rel_congr`
    rintro ⟨k, n⟩,
    rcases norm_iterated_fderiv_le_uniform_aux hg_growth n with ⟨l, C, hC, hgrowth'⟩,
    use [finset.Iic (l+k,n), ‖B‖ * (n + 1) * n.choose (n / 2) * (C * 2^(l + k)), by positivity],
    intros f x,
    have hxk : 0 ≤ ‖x‖^k := by positivity,
    have hnorm_mul :=
    continuous_linear_map.norm_iterated_fderiv_le_of_bilinear B f.smooth' hg_smooth x le_top,
    refine le_trans (mul_le_mul_of_nonneg_left hnorm_mul hxk) _,
    rw [← mul_assoc (‖x‖^k), mul_comm (‖x‖^k)],
    simp_rw [mul_assoc (‖B‖)],
    refine mul_le_mul_of_nonneg_left _ (by positivity),
    rw [finset.mul_sum],
    have : ∑ (x_1 : ℕ) in finset.range (n + 1), (1 : ℝ) = n + 1 := by simp,
    repeat { rw [mul_assoc ((n : ℝ) + 1)] },
    rw [← this, finset.sum_mul],
    refine finset.sum_le_sum (λ i hi, _),
    simp only [one_mul],
    rw [← mul_assoc, mul_comm (‖x‖^k), mul_assoc, mul_assoc, mul_assoc],
    refine mul_le_mul _ _ (by positivity) (by positivity),
    { norm_cast,
      exact i.choose_le_middle n },
    specialize hgrowth' (n - i) (by simp only [tsub_le_self]) x,
    rw [← mul_assoc],
    refine le_trans (mul_le_mul_of_nonneg_left hgrowth' (by positivity)) _,
    rw [mul_comm _ (C * _), mul_assoc, mul_assoc C],
    refine mul_le_mul_of_nonneg_left _ hC,
    nth_rewrite 1 mul_comm,
    rw [← mul_assoc],
    rw finset.mem_range_succ_iff at hi,
    change i ≤ (l + k, n).snd at hi,
    refine le_trans _ (one_add_le_sup_seminorm_apply le_rfl hi f x ),
    refine mul_le_mul_of_nonneg_right _ (norm_nonneg _),
    rw [pow_add],
    refine mul_le_mul_of_nonneg_left _ (by positivity),
    refine pow_le_pow_of_le_left (norm_nonneg _) _ _,
    simp only [zero_le_one, le_add_iff_nonneg_left],
  end)

end multiplication

section comp

variables [normed_add_comm_group D] [normed_space ℝ D]
variables [normed_add_comm_group G] [normed_space ℝ G]

/-- Composition with a smooth function of temperate growth on the right is a continuous linear
map on Schwartz space. -/
def comp_clm {g : D → E} (hg_smooth : cont_diff ℝ ⊤ g)
  (hg_growth : ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖iterated_fderiv ℝ n g x‖ ≤ C * (1 + ‖x‖)^k)
  (hg_upper : ∃ (k : ℕ) (C : ℝ) (hC : 1 ≤ C), ∀ x, 1 + ‖x‖ ≤ C * (1 + ‖g x‖)^k ) :
  𝓢(E, F) →L[ℝ] 𝓢(D, F) :=
mk_clm (λ f x, (f (g x)))
  (λ f f' x, by simp only [add_left_inj, pi.add_apply, eq_self_iff_true])
  (λ a f x, by simp only [pi.smul_apply, ring_hom.id_apply])
  (λ f, f.smooth'.comp hg_smooth)
  (begin
    rintros ⟨k, n⟩,
    rcases norm_iterated_fderiv_le_uniform_aux hg_growth n with ⟨l, C, hC, hgrowth'⟩,
    rcases hg_upper with ⟨kg, Cg, hCg, hg_upper'⟩,
    let k' := kg * (k + l * n),
    use [finset.Iic (k',n), Cg ^ (k + l * n) * ((C + 1) ^ n * n! * 2 ^ k'), by positivity],
    intros f x,
    let seminorm_f := ((finset.Iic (k',n)).sup (schwartz_seminorm_family ℝ _ _)) f,
    have hg_upper'' : (1 + ‖x‖)^(k + l * n) ≤ Cg^(k + l*n) * (1 + ‖g x‖)^k' :=
    begin
      rw [pow_mul, ← mul_pow],
      exact pow_le_pow_of_le_left (by positivity) (hg_upper' x) _,
    end,
    have hbound : ∀ i, i ≤ n → ‖iterated_fderiv ℝ i f (g x)‖ ≤
      2 ^ k' * seminorm_f / ((1 + ‖g x‖) ^ k'):=
    begin
      intros i hi,
      have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity,
      rw le_div_iff' hpos,
      change i ≤ (k', n).snd at hi,
      exact one_add_le_sup_seminorm_apply le_rfl hi _ _,
    end,
    have hgrowth'' : ∀ (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n),
      ‖iterated_fderiv ℝ N g x‖ ≤ ((C + 1) * (1 + ‖x‖)^l)^N :=
    begin
      intros N hN₁ hN₂,
      refine (hgrowth' N hN₂ x).trans _,
      rw [mul_pow],
      have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne.symm,
      refine mul_le_mul _ _ (by positivity) (by positivity),
      { exact le_trans (by simp [hC]) (le_self_pow (by simp [hC]) hN₁'), },
      { refine le_self_pow (one_le_pow_of_one_le _ l) hN₁',
      simp only [le_add_iff_nonneg_right, norm_nonneg] },
    end,
    have := norm_iterated_fderiv_comp_le f.smooth' hg_smooth le_top x hbound hgrowth'',
    have hxk : ‖x‖^k ≤ (1 + ‖x‖)^k :=
    pow_le_pow_of_le_left (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _,
    refine le_trans (mul_le_mul hxk this (by positivity) (by positivity)) _,
    have rearrange :
      (1 + ‖x‖) ^ k * (n! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
      ((1 + ‖x‖)^(k + l * n) / (1 + ‖g x‖) ^ k') * ((C + 1)^n * n! * 2^k' * seminorm_f) :=
    begin
      rw [mul_pow, pow_add, ← pow_mul],
      ring,
    end,
    rw rearrange,
    have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity,
    rw ← div_le_iff hgxk' at hg_upper'',
    have hpos : 0 ≤ (C + 1) ^ n * n! * 2 ^ k' * seminorm_f :=
    begin
      have : 0 ≤ seminorm_f := map_nonneg _ _,
      positivity,
    end,
    refine le_trans (mul_le_mul_of_nonneg_right hg_upper'' hpos) _,
    rw [← mul_assoc],
  end)

end comp

section derivatives

/-! ### Derivatives of Schwartz functions -/

variables (𝕜)
variables [is_R_or_C 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

/-- The Fréchet derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def fderiv_clm : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F) :=
mk_clm (fderiv ℝ)
  (λ f g _, fderiv_add f.differentiable_at g.differentiable_at)
  (λ a f _, fderiv_const_smul f.differentiable_at a)
  (λ f, (cont_diff_top_iff_fderiv.mp f.smooth').2)
  (λ ⟨k, n⟩, ⟨{⟨k, n+1⟩}, 1, zero_le_one, λ f x, by simpa only [schwartz_seminorm_family_apply,
    seminorm.comp_apply, finset.sup_singleton, one_smul, norm_iterated_fderiv_fderiv, one_mul]
      using f.le_seminorm 𝕜 k (n+1) x⟩)

@[simp] lemma fderiv_clm_apply (f : 𝓢(E, F)) (x : E) : fderiv_clm 𝕜 f x = fderiv ℝ f x :=
rfl

/-- The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map. -/
def deriv_clm : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F) :=
mk_clm (λ f, deriv f)
  (λ f g _, deriv_add f.differentiable_at g.differentiable_at)
  (λ a f _, deriv_const_smul a f.differentiable_at)
  (λ f, (cont_diff_top_iff_deriv.mp f.smooth').2)
  (λ ⟨k, n⟩, ⟨{⟨k, n+1⟩}, 1, zero_le_one, λ f x, by simpa only [real.norm_eq_abs,
    finset.sup_singleton, schwartz_seminorm_family_apply, one_mul,
    norm_iterated_fderiv_eq_norm_iterated_deriv, ← iterated_deriv_succ']
    using f.le_seminorm' 𝕜 k (n + 1) x⟩)

@[simp] lemma deriv_clm_apply (f : 𝓢(ℝ, F)) (x : ℝ) : deriv_clm 𝕜 f x = deriv f x := rfl

end derivatives

section bounded_continuous_function

/-! ### Inclusion into the space of bounded continuous functions -/

open_locale bounded_continuous_function

/-- Schwartz functions as bounded continuous functions -/
def to_bounded_continuous_function (f : 𝓢(E, F)) : E →ᵇ F :=
bounded_continuous_function.of_normed_add_comm_group f (schwartz_map.continuous f)
  (schwartz_map.seminorm ℝ 0 0 f) (norm_le_seminorm ℝ f)

@[simp] lemma to_bounded_continuous_function_apply (f : 𝓢(E, F)) (x : E) :
  f.to_bounded_continuous_function x = f x := rfl

/-- Schwartz functions as continuous functions -/
def to_continuous_map (f : 𝓢(E, F)) : C(E, F) :=
f.to_bounded_continuous_function.to_continuous_map

variables (𝕜 E F)
variables [is_R_or_C 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to bounded continuous functions as a linear map. -/
def to_bounded_continuous_function_lm : 𝓢(E, F) →ₗ[𝕜] E →ᵇ F :=
{ to_fun := λ f, f.to_bounded_continuous_function,
  map_add' := λ f g, by { ext, exact add_apply },
  map_smul' := λ a f, by { ext, exact smul_apply } }

@[simp] lemma to_bounded_continuous_function_lm_apply (f : 𝓢(E, F)) (x : E) :
  to_bounded_continuous_function_lm 𝕜 E F f x = f x := rfl

/-- The inclusion map from Schwartz functions to bounded continuous functions as a continuous linear
map. -/
def to_bounded_continuous_function_clm : 𝓢(E, F) →L[𝕜] E →ᵇ F :=
{ cont :=
  begin
    change continuous (to_bounded_continuous_function_lm 𝕜 E F),
    refine seminorm.continuous_from_bounded (schwartz_with_seminorms 𝕜 E F)
      (norm_with_seminorms 𝕜 (E →ᵇ F)) _ (λ i, ⟨{0}, 1, λ f, _⟩),
    rw [finset.sup_singleton, one_smul , seminorm.comp_apply, coe_norm_seminorm,
        schwartz_seminorm_family_apply_zero, bounded_continuous_function.norm_le (map_nonneg _ _)],
    intros x,
    exact norm_le_seminorm 𝕜 _ _,
  end,
  .. to_bounded_continuous_function_lm 𝕜 E F}

@[simp] lemma to_bounded_continuous_function_clm_apply (f : 𝓢(E, F)) (x : E) :
  to_bounded_continuous_function_clm 𝕜 E F f x = f x := rfl

variables {E}

/-- The Dirac delta distribution -/
def delta (x : E) : 𝓢(E, F) →L[𝕜] F :=
(bounded_continuous_function.eval_clm 𝕜 x).comp (to_bounded_continuous_function_clm 𝕜 E F)

@[simp] lemma delta_apply (x₀ : E) (f : 𝓢(E, F)) : delta 𝕜 F x₀ f = f x₀ := rfl

end bounded_continuous_function

end schwartz_map
