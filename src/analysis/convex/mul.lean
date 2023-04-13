/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.monovary
import analysis.convex.function

/-!
# Product of convex functions

## TODO

Introduce `has_distrib_smul`?
-/

variables {𝕜 E F : Type*} [linear_ordered_comm_ring 𝕜] [linear_ordered_comm_ring E]
  [linear_ordered_add_comm_group F] [module 𝕜 E] [module 𝕜 F] [module E F] [is_scalar_tower 𝕜 E F]
  [smul_comm_class 𝕜 E F] [ordered_smul 𝕜 E] [ordered_smul 𝕜 F] [ordered_smul E F] {s : set 𝕜}

lemma convex_on.smul' {f : 𝕜 → E} {g : 𝕜 → F} (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : monovary_on f g s) :
  convex_on 𝕜 s (f • g) :=
begin
  refine ⟨hf.1, λ x hx y hy a b ha hb hab, _⟩,
  dsimp,
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (hg₀ $ hf.1 hx hy ha hb hab) $
    add_nonneg (smul_nonneg ha $ hf₀ hx) $ smul_nonneg hb $ hf₀ hy).trans _,
  calc
      _ = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x)
        : _
    ... ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y)
        : add_le_add_left (smul_le_smul_of_nonneg (hfg.smul_add_smul_le_smul_add_smul hx hy) $
            mul_nonneg ha hb) _
    ... = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y)
        : by simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    ... = _ : by simp_rw [hab, mul_one],
  { simp only [mul_add, add_smul, smul_add],
    rw [←smul_smul_smul_comm a, ←smul_smul_smul_comm b, ←smul_smul_smul_comm a b,
      ←smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b,
      add_comm _ ((b * b) • f y • g y), add_add_add_comm, add_comm ((a * b) • f y • g x)],
    all_goals { apply_instance } }
end

lemma concave_on.smul' {f : 𝕜 → E} {g : 𝕜 → F} (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : antivary_on f g s) :
  concave_on 𝕜 s (f • g) :=
begin
  refine ⟨hf.1, λ x hx y hy a b ha hb hab, _⟩,
  dsimp,
  refine (smul_le_smul (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab) (add_nonneg
    (smul_nonneg ha $ hg₀ hx) $ smul_nonneg hb $ hg₀ hy) $ hf₀ $ hf.1 hx hy ha hb hab).trans' _,
  calc a • f x • g x + b • f y • g y
        = (a * (a + b)) • (f x • g x) + (b * (a + b)) • (f y • g y)
        : by simp_rw [hab, mul_one]
    ... = (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g x + f y • g y)
        : by simp only [mul_add, add_smul, smul_add, mul_comm _ a]; abel
    ... ≤ (a * a) • (f x • g x) + (b * b) • (f y • g y) + (a * b) • (f x • g y + f y • g x)
        : add_le_add_left (smul_le_smul_of_nonneg (hfg.smul_add_smul_le_smul_add_smul hx hy) $
            mul_nonneg ha hb) _
    ... = _ : _,
  { simp only [mul_add, add_smul, smul_add],
    rw [←smul_smul_smul_comm a, ←smul_smul_smul_comm b, ←smul_smul_smul_comm a b,
      ←smul_smul_smul_comm b b, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_comm b a,
      add_comm ((a * b) • f x • g y), add_comm ((a * b) • f x • g y), add_add_add_comm],
    all_goals { apply_instance } }
end

lemma convex_on.smul'' {f : 𝕜 → E} {g : 𝕜 → F} (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : antivary_on f g s) :
  concave_on 𝕜 s (f • g) :=
begin
  letI : module (𝕜 → E) (𝕜 → F) := pi.module',
  rw ←neg_smul_neg,
  exact hf.neg.smul' hg.neg (λ x hx, neg_nonneg.2 $ hf₀ hx) (λ x hx, neg_nonneg.2 $ hg₀ hx) hfg.neg,
end

lemma concave_on.smul'' {f : 𝕜 → E} {g : 𝕜 → F} (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : monovary_on f g s) :
  convex_on 𝕜 s (f • g) :=
begin
  letI : module (𝕜 → E) (𝕜 → F) := pi.module',
  rw ←neg_smul_neg,
  exact hf.neg.smul' hg.neg (λ x hx, neg_nonneg.2 $ hf₀ hx) (λ x hx, neg_nonneg.2 $ hg₀ hx) hfg.neg,
end

lemma convex_on.smul_concave_on {f : 𝕜 → E} {g : 𝕜 → F} (hf : convex_on 𝕜 s f)
  (hg : concave_on 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0)
  (hfg : antivary_on f g s) : concave_on 𝕜 s (f • g) :=
begin
  rw [←neg_convex_on_iff, ←smul_neg],
  exact hf.smul' hg.neg hf₀ (λ x hx, neg_nonneg.2 $ hg₀ hx) hfg.neg_right,
end

lemma concave_on.smul_convex_on {f : 𝕜 → E} {g : 𝕜 → F} (hf : concave_on 𝕜 s f)
  (hg : convex_on 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0)
  (hfg : monovary_on f g s) : convex_on 𝕜 s (f • g) :=
begin
  rw [←neg_concave_on_iff, ←smul_neg],
  exact hf.smul' hg.neg hf₀ (λ x hx, neg_nonneg.2 $ hg₀ hx) hfg.neg_right,
end

lemma convex_on.smul_concave_on' {f : 𝕜 → E} {g : 𝕜 → F} (hf : convex_on 𝕜 s f)
  (hg : concave_on 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x)
  (hfg : monovary_on f g s) : convex_on 𝕜 s (f • g) :=
begin
  rw [←neg_concave_on_iff, ←smul_neg],
  exact hf.smul'' hg.neg hf₀ (λ x hx, neg_nonpos.2 $ hg₀ hx) hfg.neg_right,
end

lemma concave_on.smul_convex_on' {f : 𝕜 → E} {g : 𝕜 → F} (hf : concave_on 𝕜 s f)
  (hg : convex_on 𝕜 s g) (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x)
  (hfg : antivary_on f g s) : concave_on 𝕜 s (f • g) :=
begin
  rw [←neg_convex_on_iff, ←smul_neg],
  exact hf.smul'' hg.neg hf₀ (λ x hx, neg_nonpos.2 $ hg₀ hx) hfg.neg_right,
end

variables [is_scalar_tower 𝕜 E E] [smul_comm_class 𝕜 E E]

lemma convex_on.mul {f g : 𝕜 → E} (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : monovary_on f g s) :
  convex_on 𝕜 s (f * g) :=
hf.smul' hg hf₀ hg₀ hfg

lemma concave_on.mul {f g : 𝕜 → E} (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : antivary_on f g s) :
  concave_on 𝕜 s (f * g) :=
hf.smul' hg hf₀ hg₀ hfg

lemma convex_on.mul' {f g : 𝕜 → E} (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : antivary_on f g s) :
  concave_on 𝕜 s (f * g) :=
hf.smul'' hg hf₀ hg₀ hfg

lemma concave_on.mul' {f g : 𝕜 → E} (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : monovary_on f g s) :
  convex_on 𝕜 s (f * g) :=
hf.smul'' hg hf₀ hg₀ hfg

lemma convex_on.mul_concave_on {f g : 𝕜 → E} (hf : convex_on 𝕜 s f) (hg : concave_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : antivary_on f g s) :
  concave_on 𝕜 s (f * g) :=
hf.smul_concave_on hg hf₀ hg₀ hfg

lemma concave_on.mul_convex_on {f g : 𝕜 → E} (hf : concave_on 𝕜 s f) (hg : convex_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ f x) (hg₀ : ∀ ⦃x⦄, x ∈ s → g x ≤ 0) (hfg : monovary_on f g s) :
  convex_on 𝕜 s (f * g) :=
hf.smul_convex_on hg hf₀ hg₀ hfg

lemma convex_on.mul_concave_on' {f g : 𝕜 → E} (hf : convex_on 𝕜 s f) (hg : concave_on 𝕜 s g)
  (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : monovary_on f g s) :
  convex_on 𝕜 s (f * g) :=
hf.smul_concave_on' hg hf₀ hg₀ hfg

lemma concave_on.mul_convex_on' {f g : 𝕜 → E} (hf : concave_on 𝕜 s f) (hg : convex_on 𝕜 s g)
 (hf₀ : ∀ ⦃x⦄, x ∈ s → f x ≤ 0) (hg₀ : ∀ ⦃x⦄, x ∈ s → 0 ≤ g x) (hfg : antivary_on f g s) :
  concave_on 𝕜 s (f • g) :=
hf.smul_convex_on' hg hf₀ hg₀ hfg
