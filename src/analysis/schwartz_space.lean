/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.cont_diff
import analysis.normed_space.basic
import analysis.locally_convex.with_seminorms
import analysis.normed_space.multilinear
import topology.algebra.uniform_filter_basis
import analysis.inner_product_space.basic
import tactic.positivity
import algebra.order.pointwise

/-!
# Schwartz space

This file defines the Schwartz space and the space of tempered distributions.

## Main definitions

* `schwartz`: The Schwartz space

## Main statements

* `schwartz.uniform_add_group` and `schwartz.locally_convex`: The Schwartz space is a locally
convex topological vector space.

## Notation

* `𝓢(E, F)`: The Schwartz space `schwartz E F`

## Tags

Schwartz space, tempered distributions
-/

open filter
open_locale big_operators ennreal nnreal topological_space

noncomputable theory

variables {R R' 𝕜 E F : Type*}

variables [normed_add_comm_group E] [normed_space ℝ E]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables (E F)

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of ∥x∥. -/
structure schwartz_map :=
  (to_fun : E → F)
  (smooth' : cont_diff ℝ ⊤ to_fun)
  (decay' : ∀ (k n : ℕ), ∃ (C : ℝ) (hC : 0 < C), ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n to_fun x∥ ≤ C)

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
  ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ C :=
f.decay' k n

/-- Every Schwartz function is smooth. -/
lemma smooth (f : 𝓢(E, F)) : cont_diff ℝ ⊤ f := f.smooth'

@[ext] lemma ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g := fun_like.ext f g h

section aux

lemma bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
  ∃ (c : ℝ), c ∈ {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ c} :=
let ⟨M, hMp, hMb⟩ := f.decay k n in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below (k n : ℕ) (f : 𝓢(E, F)) :
  bdd_below { c | 0 ≤ c ∧ ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ c } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
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

variables [is_R_or_C 𝕜] [normed_space 𝕜 F]
variables [semiring R] [module R 𝕜] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R 𝕜 F]

lemma decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : R) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n (c • f) x∥ =
  ∥c • (1 : 𝕜)∥ * ∥x∥ ^ k * ∥iterated_fderiv ℝ n f x∥ :=
begin
  nth_rewrite 2 mul_comm,
  rw mul_assoc,
  congr,
  rw iterated_fderiv_const_smul_apply ,
  { rw ←smul_one_smul 𝕜 c,
    rw norm_smul,
    apply_instance },
  { exact f.smooth.of_le (le_of_lt $ with_top.coe_lt_top _) },
end

lemma decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n (-f) x∥ = ∥x∥ ^ k * ∥iterated_fderiv ℝ n f x∥ :=
begin
  nth_rewrite 3 ←norm_neg,
  congr,
  exact iterated_fderiv_neg_apply,
end

variables [normed_space ℂ F]

lemma decay_smul_aux' (k n : ℕ) (f : 𝓢(E, F)) (c : ℂ) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n (c • f) x∥ =
  ∥c∥ * ∥x∥ ^ k * ∥iterated_fderiv ℝ n f x∥ :=
begin
  nth_rewrite 2 mul_comm,
  rw mul_assoc,
  congr,
  rw iterated_fderiv_const_smul_apply ,
  { rw norm_smul },
  { exact f.smooth.of_le (le_of_lt $ with_top.coe_lt_top _) },
end

end aux

/-! ### Algebraic properties -/

section smul

variables [normed_space ℂ F]
variables [semiring R] [module R ℂ] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R ℂ F]
variables [semiring R'] [module R' ℂ] [module R' F] [smul_comm_class ℝ R' F]
variables [has_continuous_const_smul R' F] [is_scalar_tower R' ℂ F]

-- Note that we define the scalar multiplication only in the case that `F` is a vector space
-- over `ℂ`. The reason for this is that the type-system cannot infer instances if we were to
-- replace `ℂ` by `[is_R_or_C 𝕜]`. This is mathematically no problem, because the usual Schwartz
-- space is `𝓢(E, ℂ)` and the space `𝓢(E, ℝ)` is never used in mathematics.
instance : has_smul R 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := f.smooth.const_smul c,
  decay' := λ k n, begin
    rcases f.decay k n with ⟨C, hC, hf⟩,
    refine ⟨C * (∥c • (1 : ℂ)∥+1), by positivity, _⟩,
    intros x,
    specialize hf x,
    have hc : 0 ≤ ∥c • (1 : ℂ)∥ := by positivity,
    refine le_trans _ ((mul_le_mul_of_nonneg_right hf hc).trans _),
    { refine eq.le _,
      nth_rewrite 1 mul_comm,
      rw ←mul_assoc,
      refine decay_smul_aux k n f c x },
    rw [mul_le_mul_left hC, le_add_iff_nonneg_right],
    exact zero_le_one,
  end}⟩

@[simp] lemma smul_apply {f : 𝓢(E, F)} {c : R} {x : E} : (c • f) x = c • (f x) := rfl

instance [has_smul R R'] [is_scalar_tower R R' F] : is_scalar_tower R R' 𝓢(E, F) :=
⟨λ a b f, ext $ λ x, smul_assoc a b (f x)⟩

instance [smul_comm_class R R' F] : smul_comm_class R R' 𝓢(E, F) :=
⟨λ a b f, ext $ λ x, smul_comm a b (f x)⟩

end smul

section zero

instance : has_zero 𝓢(E, F) :=
⟨{ to_fun := λ _, 0,
  smooth' := cont_diff_const,
  decay' := λ _ _, ⟨1, zero_lt_one, λ _, by simp⟩ }⟩

instance : inhabited 𝓢(E, F) := ⟨0⟩

lemma coe_zero : ↑(0 : 𝓢(E, F)) = (0 : E → F) := rfl

@[simp] lemma coe_fn_zero : coe_fn (0 : 𝓢(E, F)) = (0 : E → F) := rfl

@[simp] lemma zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 := rfl

end zero

section neg

instance : has_neg 𝓢(E, F) :=
⟨λ f, ⟨-f, f.smooth.neg,
  begin
    intros k n,
    rcases f.decay k n with ⟨C, hC, hf⟩,
    exact ⟨C, hC, λ x, (decay_neg_aux k n f x).le.trans (hf x)⟩,
  end⟩ ⟩

end neg

section add

instance : has_add 𝓢(E, F) :=
⟨λ f g, ⟨f + g, f.smooth.add g.smooth,
  begin
    intros k n,
    rcases f.decay k n with ⟨Cf, hCf, hf⟩,
    rcases g.decay k n with ⟨Cg, hCg, hg⟩,
    refine ⟨Cf + Cg, by positivity, λ x, _⟩,
    exact (decay_add_le_aux k n f g x).trans (add_le_add (hf x) (hg x)),
  end⟩ ⟩

@[simp] lemma add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x := rfl

end add

section sub

instance : has_sub 𝓢(E, F) :=
⟨λ f g, ⟨f - g, f.smooth.sub g.smooth,
  begin
    intros k n,
    rcases f.decay k n with ⟨Cf, hCf, hf⟩,
    rcases g.decay k n with ⟨Cg, hCg, hg⟩,
    refine ⟨Cf + Cg, by positivity, λ x, _⟩,
    refine le_trans _ (add_le_add (hf x) (hg x)),
    rw sub_eq_add_neg,
    rw ←decay_neg_aux k n g x,
    convert decay_add_le_aux k n f (-g) x,
    -- exact fails with deterministic timeout
  end⟩ ⟩

@[simp] lemma sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x := rfl

end sub

section add_comm_group

variables [normed_space ℂ F]

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

variables [normed_space ℂ F]
variables [semiring R] [module R ℂ] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R ℂ F]

instance : module R 𝓢(E, F) :=
coe_hom_injective.module R (coe_hom E F) (λ _ _, rfl)

end module

section seminorms

/-! ### Seminorms on Schwartz space-/

/-- Helper definition for the seminorms of the Schwartz space. -/
@[protected]
def seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
Inf {c | 0 ≤ c ∧ ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ c}

lemma seminorm_aux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminorm_aux k n :=
le_cInf (bounds_nonempty k n f) (λ _ ⟨hx, _⟩, hx)

lemma le_seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n ⇑f x∥ ≤ f.seminorm_aux k n :=
le_cInf (bounds_nonempty k n f) (λ y ⟨_, h⟩, h x)

section

open tactic tactic.positivity

/-- Extension for the `positivity` tactic: seminorms are nonnegative. -/
@[positivity]
meta def _root_.tactic.positivity_schwartz_seminorm_aux : expr → tactic strictness
| `(schwartz_map.seminorm_aux %%a %%b %%c) := nonnegative <$> mk_app ``seminorm_aux_nonneg [a, b, c]
| _ := failed

end

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma seminorm_aux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ M) :
  f.seminorm_aux k n ≤ M :=
cInf_le (bounds_bdd_below k n f) ⟨hMp, hM⟩

lemma seminorm_aux_zero (k n : ℕ) :
  (0 : 𝓢(E, F)).seminorm_aux k n = 0 :=
le_antisymm (seminorm_aux_le_bound k n _ rfl.le (λ _, by simp [pi.zero_def])) (by positivity)

lemma seminorm_aux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
  (f + g).seminorm_aux k n ≤ f.seminorm_aux k n + g.seminorm_aux k n :=
(f + g).seminorm_aux_le_bound k n (by positivity) $ λ x, (decay_add_le_aux k n f g x).trans $
  add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x)

variables [normed_space ℂ F]

lemma seminorm_aux_smul_le (k n : ℕ) (r : ℂ) (f : 𝓢(E, F)) :
  (r • f).seminorm_aux k n ≤ ∥r∥ * f.seminorm_aux k n :=
begin
  refine (r • f).seminorm_aux_le_bound k n (by positivity) (λ x, _),
  refine (decay_smul_aux' k n f r x).le.trans _,
  rw mul_assoc,
  exact mul_le_mul_of_nonneg_left (f.le_seminorm_aux k n x) (norm_nonneg _),
end

/-- The seminorms of the Schwartz space -/
@[protected]
def seminorm (k n : ℕ) : seminorm ℂ 𝓢(E, F) := seminorm.of_smul_le (seminorm_aux k n)
  (seminorm_aux_zero k n) (seminorm_aux_add_le k n) (seminorm_aux_smul_le k n)

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ∥x∥^k * ∥iterated_fderiv ℝ n f x∥ ≤ M) :
  seminorm k n f ≤ M := f.seminorm_aux_le_bound k n hMp hM

lemma le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n ⇑f x∥ ≤ seminorm k n f := f.le_seminorm_aux k n x

end seminorms

section topology

/-! ### The topology on the Schwartz space-/

variables (E F)
variables [normed_space ℂ F]


/-- The family of Schwartz seminorms. -/
def _root_.schwartz_seminorm_family : seminorm_family ℂ 𝓢(E, F) (ℕ × ℕ) :=
λ n, seminorm n.1 n.2

variables {E F}

instance : topological_space 𝓢(E, F) := (schwartz_seminorm_family E F).module_filter_basis.topology'

instance : has_continuous_smul ℂ 𝓢(E, F) :=
(schwartz_seminorm_family E F).module_filter_basis.has_continuous_smul

instance : topological_add_group 𝓢(E, F) :=
(schwartz_seminorm_family E F).module_filter_basis.to_add_group_filter_basis
  .is_topological_add_group

instance : uniform_space 𝓢(E, F) :=
(schwartz_seminorm_family E F).module_filter_basis.to_add_group_filter_basis.uniform_space

instance : uniform_add_group 𝓢(E, F) :=
(schwartz_seminorm_family E F).module_filter_basis.to_add_group_filter_basis.uniform_add_group

variables (E F)

lemma _root_.schwartz_with_seminorms : with_seminorms (schwartz_seminorm_family E F) := ⟨rfl⟩

variables {E F}

instance : locally_convex_space ℝ 𝓢(E, F) :=
seminorm_family.to_locally_convex_space (schwartz_with_seminorms E F)

end topology

end schwartz_map
