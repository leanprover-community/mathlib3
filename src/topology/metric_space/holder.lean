/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.metric_space.lipschitz
import analysis.special_functions.pow

/-!
# Hölder continuous functions

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `holder_on_with`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `holder_with`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `nnreal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotonically increasing in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

 -/

variables {X Y Z : Type*}

open filter set
open_locale nnreal ennreal topological_space

section emetric

variables [pseudo_emetric_space X] [pseudo_emetric_space Y] [pseudo_emetric_space Z]

/-- A function `f : X → Y` between two `pseudo_emetric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
def holder_with (C r : ℝ≥0) (f : X → Y) : Prop :=
∀ x y, edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ)

/-- A function `f : X → Y` between two `pseudo_emeteric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0` on a set `s : set X`, if `edist (f x) (f y) ≤ C * edist x y ^ r`
for all `x y ∈ s`. -/
def holder_on_with (C r : ℝ≥0) (f : X → Y) (s : set X) : Prop :=
∀ (x ∈ s) (y ∈ s), edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ)

@[simp] lemma holder_on_with_empty (C r : ℝ≥0) (f : X → Y) : holder_on_with C r f ∅ :=
λ x hx, hx.elim

@[simp] lemma holder_on_with_singleton (C r : ℝ≥0) (f : X → Y) (x : X) : holder_on_with C r f {x} :=
by { rintro a (rfl : a = x) b (rfl : b = a), rw edist_self, exact zero_le _ }

lemma set.subsingleton.holder_on_with {s : set X} (hs : s.subsingleton) (C r : ℝ≥0) (f : X → Y) :
  holder_on_with C r f s :=
hs.induction_on (holder_on_with_empty C r f) (holder_on_with_singleton C r f)

lemma holder_on_with_univ {C r : ℝ≥0} {f : X → Y} :
  holder_on_with C r f univ ↔ holder_with C r f :=
by simp only [holder_on_with, holder_with, mem_univ, true_implies_iff]

@[simp] lemma holder_on_with_one {C : ℝ≥0} {f : X → Y} {s : set X} :
  holder_on_with C 1 f s ↔ lipschitz_on_with C f s :=
by simp only [holder_on_with, lipschitz_on_with, nnreal.coe_one, ennreal.rpow_one]

alias holder_on_with_one ↔ _ lipschitz_on_with.holder_on_with

@[simp] lemma holder_with_one {C : ℝ≥0} {f : X → Y} :
  holder_with C 1 f ↔ lipschitz_with C f :=
holder_on_with_univ.symm.trans $ holder_on_with_one.trans lipschitz_on_univ

alias holder_with_one ↔ _ lipschitz_with.holder_with

lemma holder_with_id : holder_with 1 1 (id : X → X) :=
lipschitz_with.id.holder_with

protected lemma holder_with.holder_on_with {C r : ℝ≥0} {f : X → Y} (h : holder_with C r f)
  (s : set X) :
  holder_on_with C r f s :=
λ x _ y _, h x y

namespace holder_on_with

variables {C r : ℝ≥0} {f : X → Y} {s t : set X}

lemma edist_le (h : holder_on_with C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
  edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ) :=
h x hx y hy

lemma edist_le_of_le (h : holder_on_with C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s)
  {d : ℝ≥0∞} (hd : edist x y ≤ d) :
  edist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
(h.edist_le hx hy).trans (mul_le_mul_left' (ennreal.rpow_le_rpow hd r.coe_nonneg) _)

lemma comp {Cg rg : ℝ≥0} {g : Y → Z} {t : set Y} (hg : holder_on_with Cg rg g t)
  {Cf rf : ℝ≥0} {f : X → Y} (hf : holder_on_with Cf rf f s) (hst : maps_to f s t) :
  holder_on_with (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
begin
  intros x hx y hy,
  rw [ennreal.coe_mul, mul_comm rg, nnreal.coe_mul, ennreal.rpow_mul, mul_assoc,
    ← ennreal.coe_rpow_of_nonneg _ rg.coe_nonneg, ← ennreal.mul_rpow_of_nonneg _ _ rg.coe_nonneg],
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)
end

lemma comp_holder_with {Cg rg : ℝ≥0} {g : Y → Z} {t : set Y} (hg : holder_on_with Cg rg g t)
  {Cf rf : ℝ≥0} {f : X → Y} (hf : holder_with Cf rf f) (ht : ∀ x, f x ∈ t) :
  holder_with (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
holder_on_with_univ.mp $ hg.comp (hf.holder_on_with univ) (λ x _, ht x)

/-- A Hölder continuous function is uniformly continuous -/
protected lemma uniform_continuous_on (hf : holder_on_with C r f s) (h0 : 0 < r) :
  uniform_continuous_on f s :=
begin
  refine emetric.uniform_continuous_on_iff.2 (λε εpos, _),
  have : tendsto (λ d : ℝ≥0∞, (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0),
    from ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ennreal.coe_ne_top h0,
  rcases ennreal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩,
  exact ⟨δ, δ0, λ x y hx hy h, (hf.edist_le hx hy).trans_lt (H h)⟩,
end

protected lemma continuous_on (hf : holder_on_with C r f s) (h0 : 0 < r) : continuous_on f s :=
(hf.uniform_continuous_on h0).continuous_on

protected lemma mono (hf : holder_on_with C r f s) (ht : t ⊆ s) : holder_on_with C r f t :=
λ x hx y hy, hf.edist_le (ht hx) (ht hy)

lemma ediam_image_le_of_le (hf : holder_on_with C r f s) {d : ℝ≥0∞} (hd : emetric.diam s ≤ d) :
  emetric.diam (f '' s) ≤ C * d ^ (r : ℝ) :=
emetric.diam_image_le_iff.2 $ λ x hx y hy, hf.edist_le_of_le hx hy $
  (emetric.edist_le_diam_of_mem hx hy).trans hd

lemma ediam_image_le (hf : holder_on_with C r f s) :
  emetric.diam (f '' s) ≤ C * emetric.diam s ^ (r : ℝ) :=
hf.ediam_image_le_of_le le_rfl

lemma ediam_image_le_of_subset (hf : holder_on_with C r f s) (ht : t ⊆ s) :
  emetric.diam (f '' t) ≤ C * emetric.diam t ^ (r : ℝ) :=
(hf.mono ht).ediam_image_le

lemma ediam_image_le_of_subset_of_le (hf : holder_on_with C r f s) (ht : t ⊆ s) {d : ℝ≥0∞}
  (hd : emetric.diam t ≤ d) :
  emetric.diam (f '' t) ≤ C * d ^ (r : ℝ) :=
(hf.mono ht).ediam_image_le_of_le hd

lemma ediam_image_inter_le_of_le (hf : holder_on_with C r f s) {d : ℝ≥0∞}
  (hd : emetric.diam t ≤ d) :
  emetric.diam (f '' (t ∩ s)) ≤ C * d ^ (r : ℝ) :=
hf.ediam_image_le_of_subset_of_le (inter_subset_right _ _) $
  (emetric.diam_mono $ inter_subset_left _ _).trans hd

lemma ediam_image_inter_le (hf : holder_on_with C r f s) (t : set X) :
  emetric.diam (f '' (t ∩ s)) ≤ C * emetric.diam t ^ (r : ℝ) :=
hf.ediam_image_inter_le_of_le le_rfl

end holder_on_with

namespace holder_with

variables {C r : ℝ≥0} {f : X → Y}

lemma edist_le (h : holder_with C r f) (x y : X) :
  edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ) :=
h x y

lemma edist_le_of_le (h : holder_with C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
  edist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
(h.holder_on_with univ).edist_le_of_le trivial trivial hd

lemma comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : holder_with Cg rg g)
  {Cf rf : ℝ≥0} {f : X → Y} (hf : holder_with Cf rf f) :
  holder_with (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
(hg.holder_on_with univ).comp_holder_with hf (λ _, trivial)

lemma comp_holder_on_with {Cg rg : ℝ≥0} {g : Y → Z} (hg : holder_with Cg rg g)
  {Cf rf : ℝ≥0} {f : X → Y} {s : set X} (hf : holder_on_with Cf rf f s) :
  holder_on_with (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
(hg.holder_on_with univ).comp hf (λ _ _, trivial)

/-- A Hölder continuous function is uniformly continuous -/
protected lemma uniform_continuous (hf : holder_with C r f) (h0 : 0 < r) : uniform_continuous f :=
uniform_continuous_on_univ.mp $ (hf.holder_on_with univ).uniform_continuous_on h0

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
