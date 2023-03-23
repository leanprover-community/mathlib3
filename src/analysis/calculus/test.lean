/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.cont_diff

/-!
# Higher differentiability of usual operations

We prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions. We also expand the API aound `C^n` functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable theory
open_locale classical big_operators nnreal

local notation `∞` := (⊤ : ℕ∞)

universes u v w uD uE uF uG

local attribute [instance, priority 1001]
normed_add_comm_group.to_add_comm_group normed_space.to_module' add_comm_group.to_add_comm_monoid

open set fin filter function
open_locale topology

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{D : Type uD} [normed_add_comm_group D] [normed_space 𝕜 D]
{E : Type uE} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type uF} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type uG} [normed_add_comm_group G] [normed_space 𝕜 G]
{X : Type*} [normed_add_comm_group X] [normed_space 𝕜 X]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F}
{b : E × F → G} {m n : ℕ∞} {p : E → formal_multilinear_series 𝕜 E F}

open_locale nat

lemma norm_iterated_fderiv_within_comp_le_aux
  {Eu Fu Gu : Type u}
  [normed_add_comm_group Eu] [normed_space 𝕜 Eu]
  [normed_add_comm_group Fu] [normed_space 𝕜 Fu]
  [normed_add_comm_group Gu] [normed_space 𝕜 Gu]
  {g : Fu → Gu} {f : Eu → Fu} {n : ℕ} {s : set Eu} {t : set Fu} {x : Eu}
  (hg : cont_diff_on 𝕜 n g t) (hf : cont_diff_on 𝕜 n f s)
  (ht : unique_diff_on 𝕜 t) (hs : unique_diff_on 𝕜 s)
  (hst : maps_to f s t) (hx : x ∈ s)
  {C : ℝ} {D : ℝ} (hC : ∀ i, i ≤ n → ‖iterated_fderiv_within 𝕜 i g t (f x)‖ ≤ C)
  (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iterated_fderiv_within 𝕜 i f s x‖ ≤ D^i) :
  ‖iterated_fderiv_within 𝕜 n (g ∘ f) s x‖ ≤ n! * C * D^n :=
begin
  unfreezingI { induction n using nat.case_strong_induction_on with n IH generalizing Gu },
  { simpa only [norm_iterated_fderiv_within_zero, nat.factorial_zero, algebra_map.coe_one,
      one_mul, pow_zero, mul_one] using hC 0 le_rfl },
  have L : (1 : with_top ℕ) ≤ n.succ,
    by simpa only [enat.coe_one, nat.one_le_cast] using nat.succ_pos n,
  have M : (n : with_top ℕ) < n.succ := nat.cast_lt.2 (nat.lt_succ_self n),
  have Cnonneg : 0 ≤ C := (norm_nonneg _).trans (hC 0 bot_le),
  have Dnonneg : 0 ≤ D,
  { have : 1 ≤ n+1, by simp only [le_add_iff_nonneg_left, zero_le'],
    simpa only [pow_one] using (norm_nonneg _).trans (hD 1 le_rfl this) },
  have I : ∀ i ∈ finset.range (n+1),
    ‖iterated_fderiv_within 𝕜 i ((fderiv_within 𝕜 g t) ∘ f) s x‖ ≤ i! * C * D^i,
  sorry { assume i hi,
    simp only [finset.mem_range, nat.lt_succ_iff] at hi,
    apply IH i hi,
    apply hf.of_le (nat.cast_le.2 (hi.trans (nat.le_succ n))),
    { assume j hj h'j,
      exact hD j hj (h'j.trans (hi.trans (nat.le_succ n))) },
    { apply hg.fderiv_within ht,
      simp only [nat.cast_succ],
      exact add_le_add_right (nat.cast_le.2 hi) _ },
    { assume j hj,
      have : ‖iterated_fderiv_within 𝕜 j (fderiv_within 𝕜 g t) t (f x)‖
        = ‖iterated_fderiv_within 𝕜 (j+1) g t (f x)‖,
      by rw [iterated_fderiv_within_succ_eq_comp_right ht (hst hx), linear_isometry_equiv.norm_map],
      rw this,
      exact hC (j+1) (add_le_add (hj.trans hi) le_rfl) } },
  calc
  ‖iterated_fderiv_within 𝕜 (n+1) (g ∘ f) s x‖ =
        ‖iterated_fderiv_within 𝕜 n (λ (y : Eu), fderiv_within 𝕜 (g ∘ f) s y) s x‖ :
    sorry -- by rw [iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map]
  ... = ‖iterated_fderiv_within 𝕜 n (λ (y : Eu), continuous_linear_map.compL 𝕜 Eu Fu Gu
        (fderiv_within 𝕜 g t (f y)) (fderiv_within 𝕜 f s y)) s x‖ :
  sorry /-begin
    congr' 1,
    apply iterated_fderiv_within_congr hs (λ y hy, _) hx,
    apply fderiv_within.comp _ _ _ hst (hs y hy),
    { exact hg.differentiable_on L _ (hst hy) },
    { exact hf.differentiable_on L _ hy }
  end-/
  ... ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ) *
          ‖iterated_fderiv_within 𝕜 i ((fderiv_within 𝕜 g t) ∘ f) s x‖
            * ‖iterated_fderiv_within 𝕜 (n-i) (fderiv_within 𝕜 f s) s x‖ :
  sorry /-begin
    have A : cont_diff_on 𝕜 n ((fderiv_within 𝕜 g t) ∘ f) s,
    { apply cont_diff_on.comp _ (hf.of_le M.le) hst,
      apply hg.fderiv_within ht,
      simp only [nat.cast_succ, le_refl] },
    have B : cont_diff_on 𝕜 n (fderiv_within 𝕜 f s) s,
    { apply hf.fderiv_within hs,
      simp only [nat.cast_succ, le_refl] },
    exact (continuous_linear_map.compL 𝕜 Eu Fu Gu).norm_iterated_fderiv_within_le_of_bilinear_of_le_one A B hs hx
       le_rfl (continuous_linear_map.norm_compL_le 𝕜 Eu Fu Gu),
  end-/
  ... ≤ ∑ i in finset.range (n+1), (n.choose i : ℝ) * (i! * C * D^i) * (D^(n-i+1)) :
  begin
    apply finset.sum_le_sum (λ i hi, _),
    simp only [mul_assoc (n.choose i : ℝ)],
    refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
    apply mul_le_mul (I i hi),

  end
  ... ≤ _ : sorry
end


#exit

fderiv_within 𝕜 (g ∘ f) s x = (fderiv_within 𝕜 g t (f x)).comp (fderiv_within 𝕜 f s x)
