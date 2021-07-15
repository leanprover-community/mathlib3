/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.metric_space.lipschitz
import analysis.special_functions.pow

/-!
# Holder continuous functions

In this file we define `f : X → Y` to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
`r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. We also prove some basic
facts about this definition.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `nnreal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotonically increasing in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

 -/

variables {X Y Z : Type*}

open filter
open_locale nnreal ennreal topological_space

section emetric

variables [pseudo_emetric_space X] [pseudo_emetric_space Y] [pseudo_emetric_space Z]

/-- A function `f : X → Y` between two `pseudo_emeteric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
def holder_with (C r : ℝ≥0) (f : X → Y) : Prop :=
∀ x y, edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ)

@[simp] lemma holder_with_one {C : ℝ≥0} {f : X → Y} :
  holder_with C 1 f ↔ lipschitz_with C f :=
by simp only [holder_with, lipschitz_with, nnreal.coe_one, ennreal.rpow_one]

lemma holder_with_id : holder_with 1 1 (id : X → X) :=
holder_with_one.mpr lipschitz_with.id

namespace holder_with

variables {C r : ℝ≥0} {f : X → Y}

lemma edist_le (h : holder_with C r f) (x y : X) :
  edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ) :=
h x y

lemma edist_le_of_le (h : holder_with C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
  edist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
(h _ _).trans (ennreal.mul_left_mono (ennreal.rpow_le_rpow hd r.coe_nonneg))

lemma comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : holder_with Cg rg g)
  {Cf rf : ℝ≥0} {f : X → Y} (hf : holder_with Cf rf f) :
  holder_with (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
begin
  intros x y,
  rw [ennreal.coe_mul, mul_comm rg, nnreal.coe_mul, ennreal.rpow_mul, mul_assoc,
    ← ennreal.coe_rpow_of_nonneg _ rg.coe_nonneg, ← ennreal.mul_rpow_of_nonneg _ _ rg.coe_nonneg],
  exact hg.edist_le_of_le (hf _ _)
end

/-- A Hölder continuous function is uniformly continuous -/
protected lemma uniform_continuous (hf : holder_with C r f) (h0 : 0 < r) : uniform_continuous f :=
begin
  refine emetric.uniform_continuous_iff.2 (λε εpos, _),
  have : tendsto (λ d : ℝ≥0∞, (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0),
  { convert ennreal.tendsto.const_mul (ennreal.continuous_rpow_const.tendsto 0) _,
    { simp [h0] },
    { exact or.inr ennreal.coe_ne_top } },
  rcases ennreal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩,
  exact ⟨δ, δ0, λ x y h, (hf x y).trans_lt (H h)⟩,
end

protected lemma continuous (hf : holder_with C r f) (h0 : 0 < r) : continuous f :=
(hf.uniform_continuous h0).continuous

lemma ediam_image_le (hf : holder_with C r f) (s : set X) :
  emetric.diam (f '' s) ≤ C * emetric.diam s ^ (r : ℝ) :=
emetric.diam_image_le_iff.2 $ λ x hx y hy, hf.edist_le_of_le $ emetric.edist_le_diam_of_mem hx hy

end holder_with

end emetric

section metric

variables [pseudo_metric_space X] [pseudo_metric_space Y] {C r : ℝ≥0} {f : X → Y}

namespace holder_with

lemma nndist_le_of_le (hf : holder_with C r f) {x y : X} {d : ℝ≥0} (hd : nndist x y ≤ d) :
  nndist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
begin
  rw [← ennreal.coe_le_coe, ← edist_nndist, ennreal.coe_mul,
    ← ennreal.coe_rpow_of_nonneg _ r.coe_nonneg],
  apply hf.edist_le_of_le,
  rwa [edist_nndist, ennreal.coe_le_coe],
end

lemma nndist_le (hf : holder_with C r f) (x y : X) :
  nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
hf.nndist_le_of_le le_rfl

lemma dist_le_of_le (hf : holder_with C r f) {x y : X} {d : ℝ} (hd : dist x y ≤ d) :
  dist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
begin
  lift d to ℝ≥0 using dist_nonneg.trans hd,
  rw dist_nndist at hd ⊢,
  norm_cast at hd ⊢,
  exact hf.nndist_le_of_le hd
end

lemma dist_le (hf : holder_with C r f) (x y : X) :
  dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
hf.dist_le_of_le le_rfl

end holder_with

end metric
