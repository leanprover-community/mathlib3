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

/-!
# Schwartz space

## Main definitions

* `schwartz`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

-- Todo: Fix complex scalar multiplication

open filter
open_locale big_operators ennreal nnreal topological_space

noncomputable theory

variables {R 𝕜 E F ι : Type*}

section iterated_fderiv

variables [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group E] [normed_space 𝕜 E]
variables [normed_add_comm_group F] [normed_space 𝕜 F]

lemma cont_diff.differentiable_at_iterated_fderiv {n k : ℕ} {f : E → F} (hf : cont_diff 𝕜 n f)
  (h : k < n):
  differentiable 𝕜 (iterated_fderiv 𝕜 k f) :=
(cont_diff_iff_continuous_differentiable.mp hf).2 k (by simp only [h, with_top.coe_lt_coe])

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

-- iterated_fderiv_add
lemma iterated_fderiv_neg {n : ℕ} {f : E → F} :
  iterated_fderiv 𝕜 n (-f) = -iterated_fderiv 𝕜 n f :=
begin
  induction n with k hk,
  { ext, simp },
  ext x m,
  rw [pi.neg_apply, continuous_multilinear_map.neg_apply],
  simp_rw iterated_fderiv_succ_apply_left m,
  rw [←continuous_multilinear_map.neg_apply],
  congr,
  rw ←continuous_linear_map.neg_apply,
  congr,
  rw ←fderiv_neg,
  congr,
  ext,
  rw hk,
  rw pi.neg_apply,
end

lemma iterated_fderiv_neg_apply {n : ℕ} {f : E → F} {x : E}  :
  iterated_fderiv 𝕜 n (-f) x = -iterated_fderiv 𝕜 n f x :=
congr_fun iterated_fderiv_neg x

variables [semiring R] [module R F] [smul_comm_class 𝕜 R F] [has_continuous_const_smul R F]

lemma smul_continuous_multilinear_map {k : ℕ} {c : R}
  (m : continuous_multilinear_map 𝕜 (λ (i : fin k), E) F):
  (c • continuous_linear_map.id 𝕜 F).comp_continuous_multilinear_map m = c • m :=
by { ext x, simp }

instance {k : ℕ}: has_continuous_const_smul R (continuous_multilinear_map 𝕜 (λ (i : fin k), E) F) :=
⟨λ c, begin
  simp_rw ←smul_continuous_multilinear_map,
  refine (continuous_linear_map.comp_continuous_multilinear_mapL 𝕜 _ F F (c • continuous_linear_map.id 𝕜 F)).2,
end⟩

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
  rw [←continuous_multilinear_map.smul_apply],
  congr,
  rw ←continuous_linear_map.smul_apply,
  congr,
  have hf' : differentiable_at 𝕜 (iterated_fderiv 𝕜 k f) x :=
  (cont_diff.differentiable_at_iterated_fderiv hf (lt_add_one k)).differentiable_at,
  rw ←fderiv_const_smul hf',
  congr,
  exact hk,
end

lemma iterated_fderiv_const_smul_apply {n : ℕ} {f : E → F} {x : E} (hf : cont_diff 𝕜 n f) (c : R) :
  iterated_fderiv 𝕜 n (λ y, c • f y) x = c • iterated_fderiv 𝕜 n f x :=
(congr_fun (iterated_fderiv_const_smul hf c) x)

variables {n : with_top ℕ} (c : R)

/- The scalar multiplication is smooth. -/
lemma cont_diff_const_smul {c : R} : cont_diff 𝕜 n (λ p : F, c • p) :=
(c • continuous_linear_map.id 𝕜 F).cont_diff

lemma cont_diff_within_at.const_smul {n : with_top ℕ} {f : E → F} {s : set E} {x : E} (c : R)
  (hf : cont_diff_within_at 𝕜 n f s x) : cont_diff_within_at 𝕜 n (λ y, c • f y) s x :=
cont_diff_const_smul.cont_diff_within_at.comp x hf set.subset_preimage_univ

lemma cont_diff.const_smul {n : with_top ℕ} {f : E → F} (c : R)
  (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ y, c • f y) :=
begin
  rw cont_diff_iff_cont_diff_at at hf ⊢,
  intro x,
  specialize hf x,
  rw ←cont_diff_within_at_univ at hf ⊢,
  exact hf.const_smul _,
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

instance : has_coe (schwartz E F) (E → F) := ⟨to_fun⟩

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

variables [is_R_or_C 𝕜] [normed_space 𝕜 F]
variables [semiring R] [module R 𝕜] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R 𝕜 F]

lemma seminorm_smul_aux (k n : ℕ) (f : schwartz E F) (c : R) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n (λ y, c • f y) x∥ =
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

lemma seminorm_neg_aux (k n : ℕ) (f : schwartz E F) (x : E) :
  ∥x∥ ^ k * ∥iterated_fderiv ℝ n (-f) x∥ = ∥x∥ ^ k * ∥iterated_fderiv ℝ n f x∥ :=
begin
  nth_rewrite 3 ←norm_neg,
  congr,
  exact iterated_fderiv_neg_apply,
end

end aux

section smul

#check ℂ

variables [normed_space ℂ F]
variables [semiring R] [module R ℂ] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R ℂ F]

--variables [semiring R] [module R ℝ] [module R F] [smul_comm_class ℝ R F]
--variables [has_continuous_const_smul R F] [is_scalar_tower R ℝ F]

--variables [semiring R] [module R F] [has_continuous_const_smul R F] [is_scalar_tower R ℝ F]

--instance (𝕜 : Type*) [is_R_or_C 𝕜] [normed_space 𝕜 F] [module R 𝕜] [is_scalar_tower R 𝕜 F]:
instance :
  has_smul R (schwartz E F) :=
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
      refine seminorm_smul_aux k n f c x,
    },
    rw [mul_le_mul_left hC, le_add_iff_nonneg_right],
    exact zero_le_one,
  end}⟩

@[simp] lemma smul_apply {f : schwartz E F} {c : R} {x : E} : (c • f) x = c • (f x) := rfl

end smul

section zero

instance : has_zero (schwartz E F) :=
⟨{ to_fun := λ _, 0,
  smooth' := cont_diff_const,
  decay' := λ k n, ⟨1, zero_lt_one, λ _, by simp [iterated_fderiv_within_zero_fun]⟩ }⟩
-- todo: `iterated_fderiv_within_zero_fun` should be `simp`
-- (and be called `iterated_fderiv_zero_fun`)

lemma coe_zero : ↑(0 : schwartz E F) = (0 : E → F) := rfl

@[simp] lemma zero_apply {x : E} : (0 : schwartz E F) x = 0 := rfl

end zero

section neg

instance : has_neg (schwartz E F) :=
⟨λ f, ⟨-f, f.smooth.neg,
  begin
    intros k n,
    rcases f.decay k n with ⟨C, hC, hf⟩,
    use [C, hC],
    intro x,
    refine le_trans (eq.le _) (hf x),
    exact seminorm_neg_aux k n f x,
  end⟩ ⟩

end neg

section add

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

lemma coe_add (f g : schwartz E F) : (f : E → F) + g = f + g := rfl

@[simp] lemma add_apply {f g : schwartz E F} {x : E} : (f + g) x = f x + g x := rfl

end add

instance : has_sub (schwartz E F) :=
⟨λ f g, ⟨f - g, f.smooth.sub g.smooth,
  begin
    intros k n,
    rcases f.decay k n with ⟨Cf, hCf, hf⟩,
    rcases g.decay k n with ⟨Cg, hCg, hg⟩,
    refine ⟨Cf + Cg, by positivity, λ x, _⟩,
    specialize hf x,
    specialize hg x,
    refine le_trans _ (add_le_add hf hg),
    rw sub_eq_add_neg,
    rw ←seminorm_neg_aux k n g x,
    convert seminorm_add_le_aux k n f (-g) x, -- for some reason exact fails with timeout
  end⟩ ⟩

@[simp] lemma sub_apply {f g : schwartz E F} {x : E} : (f - g) x = f x - g x := rfl

variables [normed_space ℂ F]

instance : add_comm_group (schwartz E F) :=
fun_like.coe_injective.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl)
/-begin
  haveI : has_smul ℕ (schwartz E F) := schwartz.has_smul ℝ,
  haveI : has_smul ℤ (schwartz E F) := schwartz.has_smul ℝ,
  exact fun_like.coe_injective.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)
    (λ x n, begin
      ext,
      exact smul_apply,
      sorry,
    end) (λ x z, begin
      sorry,
    end)
end-/

variables (E F)

/-- Coercion as an additive homomorphism. -/
def coe_hom : (schwartz E F) →+ (E → F) :=
{ to_fun := λ f, f, map_zero' := coe_zero, map_add' := coe_add }

variables {E F}

lemma coe_coe_hom : (coe_hom E F : (schwartz E F) → (E → F)) = coe_fn := rfl

lemma coe_hom_injective : function.injective (coe_hom E F) :=
by { rw coe_coe_hom, exact fun_like.coe_injective }

section module

variables [normed_space ℂ F]
variables [semiring R] [module R ℂ] [module R F] [smul_comm_class ℝ R F]
variables [has_continuous_const_smul R F] [is_scalar_tower R ℂ F]

--variables [semiring R] [module R ℝ] [module R F] [smul_comm_class ℝ R F]
--variables [has_continuous_const_smul R F] [is_scalar_tower R ℝ F]

instance : module R (schwartz E F) :=
coe_hom_injective.module R (coe_hom E F) (λ _ _, rfl)

end module

section seminorms

variables [has_smul ℝ F]

@[protected]
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

def seminorm' (k n : ℕ) : seminorm ℝ (schwartz E F) := seminorm.of (schwartz.seminorm k n)
  (λ x y, begin
    sorry,
  end)
  (λ r x, begin
    sorry,
  end)

end seminorms

variables (E F)

def seminorm_family : seminorm_family ℝ (schwartz E F) (ℕ × ℕ) := λ n, schwartz.seminorm' n.1 n.2

variables {E F}

instance : topological_space (schwartz E F) := (seminorm_family E F).module_filter_basis.topology'

instance : has_continuous_smul ℝ (schwartz E F) :=
  (seminorm_family E F).module_filter_basis.has_continuous_smul

instance : topological_add_group (schwartz E F) :=
  (seminorm_family E F).module_filter_basis.to_add_group_filter_basis.is_topological_add_group

instance : uniform_space (schwartz E F) :=
  (seminorm_family E F).module_filter_basis.to_add_group_filter_basis.uniform_space

instance : uniform_add_group (schwartz E F) :=
  (seminorm_family E F).module_filter_basis.to_add_group_filter_basis.uniform_add_group

variables (f g : schwartz E F) (x : E) (c : ℂ)
variables (fi : ℕ → schwartz E F) (T : schwartz E F →L[ℝ] schwartz E F)

#check c • f

end schwartz
