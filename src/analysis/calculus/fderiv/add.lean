/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.linear
import analysis.calculus.fderiv.comp

/-!
# Additive operations on derivatives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

section const_smul

variables {R : Type*} [semiring R] [module R F] [smul_comm_class 𝕜 R F]
  [has_continuous_const_smul R F]

/-! ### Derivative of a function multiplied by a constant -/
theorem has_strict_fderiv_at.const_smul (h : has_strict_fderiv_at f f' x) (c : R) :
  has_strict_fderiv_at (λ x, c • f x) (c • f') x :=
(c • (1 : F →L[𝕜] F)).has_strict_fderiv_at.comp x h

theorem has_fderiv_at_filter.const_smul (h : has_fderiv_at_filter f f' x L) (c : R) :
  has_fderiv_at_filter (λ x, c • f x) (c • f') x L :=
(c • (1 : F →L[𝕜] F)).has_fderiv_at_filter.comp x h tendsto_map

theorem has_fderiv_within_at.const_smul (h : has_fderiv_within_at f f' s x) (c : R) :
  has_fderiv_within_at (λ x, c • f x) (c • f') s x :=
h.const_smul c

theorem has_fderiv_at.const_smul (h : has_fderiv_at f f' x) (c : R) :
  has_fderiv_at (λ x, c • f x) (c • f') x :=
h.const_smul c

lemma differentiable_within_at.const_smul (h : differentiable_within_at 𝕜 f s x) (c : R) :
  differentiable_within_at 𝕜 (λy, c • f y) s x :=
(h.has_fderiv_within_at.const_smul c).differentiable_within_at

lemma differentiable_at.const_smul (h : differentiable_at 𝕜 f x) (c : R) :
  differentiable_at 𝕜 (λy, c • f y) x :=
(h.has_fderiv_at.const_smul c).differentiable_at

lemma differentiable_on.const_smul (h : differentiable_on 𝕜 f s) (c : R) :
  differentiable_on 𝕜 (λy, c • f y) s :=
λx hx, (h x hx).const_smul c

lemma differentiable.const_smul (h : differentiable 𝕜 f) (c : R) :
  differentiable 𝕜 (λy, c • f y) :=
λx, (h x).const_smul c

lemma fderiv_within_const_smul (hxs : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f s x) (c : R) :
  fderiv_within 𝕜 (λy, c • f y) s x = c • fderiv_within 𝕜 f s x :=
(h.has_fderiv_within_at.const_smul c).fderiv_within hxs

lemma fderiv_const_smul (h : differentiable_at 𝕜 f x) (c : R) :
  fderiv 𝕜 (λy, c • f y) x = c • fderiv 𝕜 f x :=
(h.has_fderiv_at.const_smul c).fderiv

end const_smul

section add

/-! ### Derivative of the sum of two functions -/

theorem has_strict_fderiv_at.add (hf : has_strict_fderiv_at f f' x)
  (hg : has_strict_fderiv_at g g' x) :
  has_strict_fderiv_at (λ y, f y + g y) (f' + g') x :=
(hf.add hg).congr_left $ λ y,
  by { simp only [linear_map.sub_apply, linear_map.add_apply, map_sub, map_add, add_apply], abel }

theorem has_fderiv_at_filter.add
  (hf : has_fderiv_at_filter f f' x L) (hg : has_fderiv_at_filter g g' x L) :
  has_fderiv_at_filter (λ y, f y + g y) (f' + g') x L :=
(hf.add hg).congr_left $ λ _,
  by { simp only [linear_map.sub_apply, linear_map.add_apply, map_sub, map_add, add_apply], abel }

theorem has_fderiv_within_at.add
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ y, f y + g y) (f' + g') s x :=
hf.add hg

theorem has_fderiv_at.add
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x + g x) (f' + g') x :=
hf.add hg

lemma differentiable_within_at.add
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  differentiable_within_at 𝕜 (λ y, f y + g y) s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  differentiable_at 𝕜 (λ y, f y + g y) x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).differentiable_at

lemma differentiable_on.add
  (hf : differentiable_on 𝕜 f s) (hg : differentiable_on 𝕜 g s) :
  differentiable_on 𝕜 (λy, f y + g y) s :=
λx hx, (hf x hx).add (hg x hx)

@[simp] lemma differentiable.add
  (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
  differentiable 𝕜 (λy, f y + g y) :=
λx, (hf x).add (hg x)

lemma fderiv_within_add (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  fderiv_within 𝕜 (λy, f y + g y) s x = fderiv_within 𝕜 f s x + fderiv_within 𝕜 g s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λy, f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.add_const (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ y, f y + c) f' x :=
add_zero f' ▸ hf.add (has_strict_fderiv_at_const _ _)

theorem has_fderiv_at_filter.add_const
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ y, f y + c) f' x L :=
add_zero f' ▸ hf.add (has_fderiv_at_filter_const _ _ _)

theorem has_fderiv_within_at.add_const
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ y, f y + c) f' s x :=
hf.add_const c

theorem has_fderiv_at.add_const (hf : has_fderiv_at f f' x) (c : F):
  has_fderiv_at (λ x, f x + c) f' x :=
hf.add_const c

lemma differentiable_within_at.add_const
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, f y + c) s x :=
(hf.has_fderiv_within_at.add_const c).differentiable_within_at

@[simp] lemma differentiable_within_at_add_const_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, f y + c) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma differentiable_at.add_const
  (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, f y + c) x :=
(hf.has_fderiv_at.add_const c).differentiable_at

@[simp] lemma differentiable_at_add_const_iff (c : F) :
  differentiable_at 𝕜 (λ y, f y + c) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma differentiable_on.add_const
  (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, f y + c) s :=
λx hx, (hf x hx).add_const c

@[simp] lemma differentiable_on_add_const_iff (c : F) :
  differentiable_on 𝕜 (λ y, f y + c) s ↔ differentiable_on 𝕜 f s :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma differentiable.add_const
  (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, f y + c) :=
λx, (hf x).add_const c

@[simp] lemma differentiable_add_const_iff (c : F) :
  differentiable 𝕜 (λ y, f y + c) ↔ differentiable 𝕜 f :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma fderiv_within_add_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, f y + c) s x = fderiv_within 𝕜 f s x :=
if hf : differentiable_within_at 𝕜 f s x
then (hf.has_fderiv_within_at.add_const c).fderiv_within hxs
else by { rw [fderiv_within_zero_of_not_differentiable_within_at hf,
  fderiv_within_zero_of_not_differentiable_within_at], simpa }

lemma fderiv_add_const (c : F) : fderiv 𝕜 (λy, f y + c) x = fderiv 𝕜 f x :=
by simp only [← fderiv_within_univ, fderiv_within_add_const unique_diff_within_at_univ]

theorem has_strict_fderiv_at.const_add (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ y, c + f y) f' x :=
zero_add f' ▸ (has_strict_fderiv_at_const _ _).add hf

theorem has_fderiv_at_filter.const_add
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ y, c + f y) f' x L :=
zero_add f' ▸ (has_fderiv_at_filter_const _ _ _).add hf

theorem has_fderiv_within_at.const_add
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ y, c + f y) f' s x :=
hf.const_add c

theorem has_fderiv_at.const_add
  (hf : has_fderiv_at f f' x) (c : F):
  has_fderiv_at (λ x, c + f x) f' x :=
hf.const_add c

lemma differentiable_within_at.const_add
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, c + f y) s x :=
(hf.has_fderiv_within_at.const_add c).differentiable_within_at

@[simp] lemma differentiable_within_at_const_add_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, c + f y) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma differentiable_at.const_add
  (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, c + f y) x :=
(hf.has_fderiv_at.const_add c).differentiable_at

@[simp] lemma differentiable_at_const_add_iff (c : F) :
  differentiable_at 𝕜 (λ y, c + f y) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma differentiable_on.const_add (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, c + f y) s :=
λx hx, (hf x hx).const_add c

@[simp] lemma differentiable_on_const_add_iff (c : F) :
  differentiable_on 𝕜 (λ y, c + f y) s ↔ differentiable_on 𝕜 f s :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma differentiable.const_add (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, c + f y) :=
λx, (hf x).const_add c

@[simp] lemma differentiable_const_add_iff (c : F) :
  differentiable 𝕜 (λ y, c + f y) ↔ differentiable 𝕜 f :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma fderiv_within_const_add (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, c + f y) s x = fderiv_within 𝕜 f s x :=
by simpa only [add_comm] using fderiv_within_add_const hxs c

lemma fderiv_const_add (c : F) : fderiv 𝕜 (λy, c + f y) x = fderiv 𝕜 f x :=
by simp only [add_comm c, fderiv_add_const]

end add

section sum
/-! ### Derivative of a finite sum of functions -/

open_locale big_operators

variables {ι : Type*} {u : finset ι} {A : ι → (E → F)} {A' : ι → (E →L[𝕜] F)}

theorem has_strict_fderiv_at.sum (h : ∀ i ∈ u, has_strict_fderiv_at (A i) (A' i) x) :
  has_strict_fderiv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
begin
  dsimp [has_strict_fderiv_at] at *,
  convert is_o.sum h,
  simp [finset.sum_sub_distrib, continuous_linear_map.sum_apply]
end

theorem has_fderiv_at_filter.sum (h : ∀ i ∈ u, has_fderiv_at_filter (A i) (A' i) x L) :
  has_fderiv_at_filter (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x L :=
begin
  dsimp [has_fderiv_at_filter] at *,
  convert is_o.sum h,
  simp [continuous_linear_map.sum_apply]
end

theorem has_fderiv_within_at.sum (h : ∀ i ∈ u, has_fderiv_within_at (A i) (A' i) s x) :
  has_fderiv_within_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) s x :=
has_fderiv_at_filter.sum h

theorem has_fderiv_at.sum (h : ∀ i ∈ u, has_fderiv_at (A i) (A' i) x) :
  has_fderiv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
has_fderiv_at_filter.sum h

theorem differentiable_within_at.sum (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  differentiable_within_at 𝕜 (λ y, ∑ i in u, A i y) s x :=
has_fderiv_within_at.differentiable_within_at $ has_fderiv_within_at.sum $
λ i hi, (h i hi).has_fderiv_within_at

@[simp] theorem differentiable_at.sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  differentiable_at 𝕜 (λ y, ∑ i in u, A i y) x :=
has_fderiv_at.differentiable_at $ has_fderiv_at.sum $ λ i hi, (h i hi).has_fderiv_at

theorem differentiable_on.sum (h : ∀ i ∈ u, differentiable_on 𝕜 (A i) s) :
  differentiable_on 𝕜 (λ y, ∑ i in u, A i y) s :=
λ x hx, differentiable_within_at.sum $ λ i hi, h i hi x hx

@[simp] theorem differentiable.sum (h : ∀ i ∈ u, differentiable 𝕜 (A i)) :
  differentiable 𝕜 (λ y, ∑ i in u, A i y) :=
λ x, differentiable_at.sum $ λ i hi, h i hi x

theorem fderiv_within_sum (hxs : unique_diff_within_at 𝕜 s x)
  (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  fderiv_within 𝕜 (λ y, ∑ i in u, A i y) s x = (∑ i in u, fderiv_within 𝕜 (A i) s x) :=
(has_fderiv_within_at.sum (λ i hi, (h i hi).has_fderiv_within_at)).fderiv_within hxs

theorem fderiv_sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  fderiv 𝕜 (λ y, ∑ i in u, A i y) x = (∑ i in u, fderiv 𝕜 (A i) x) :=
(has_fderiv_at.sum (λ i hi, (h i hi).has_fderiv_at)).fderiv

end sum

section neg
/-! ### Derivative of the negative of a function -/

theorem has_strict_fderiv_at.neg (h : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, -f x) (-f') x :=
(-1 : F →L[𝕜] F).has_strict_fderiv_at.comp x h

theorem has_fderiv_at_filter.neg (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (λ x, -f x) (-f') x L :=
(-1 : F →L[𝕜] F).has_fderiv_at_filter.comp x h tendsto_map

theorem has_fderiv_within_at.neg (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_fderiv_at.neg (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, -f x) (-f') x :=
h.neg

lemma differentiable_within_at.neg (h : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λy, -f y) s x :=
h.has_fderiv_within_at.neg.differentiable_within_at

@[simp] lemma differentiable_within_at_neg_iff :
  differentiable_within_at 𝕜 (λy, -f y) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma differentiable_at.neg (h : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λy, -f y) x :=
h.has_fderiv_at.neg.differentiable_at

@[simp] lemma differentiable_at_neg_iff :
  differentiable_at 𝕜 (λy, -f y) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma differentiable_on.neg (h : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λy, -f y) s :=
λx hx, (h x hx).neg

@[simp] lemma differentiable_on_neg_iff :
  differentiable_on 𝕜 (λy, -f y) s ↔ differentiable_on 𝕜 f s :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma differentiable.neg (h : differentiable 𝕜 f) :
  differentiable 𝕜 (λy, -f y) :=
λx, (h x).neg

@[simp] lemma differentiable_neg_iff : differentiable 𝕜 (λy, -f y) ↔ differentiable 𝕜 f :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma fderiv_within_neg (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λy, -f y) s x = - fderiv_within 𝕜 f s x :=
if h : differentiable_within_at 𝕜 f s x
then h.has_fderiv_within_at.neg.fderiv_within hxs
else by { rw [fderiv_within_zero_of_not_differentiable_within_at h,
  fderiv_within_zero_of_not_differentiable_within_at, neg_zero], simpa }

@[simp] lemma fderiv_neg : fderiv 𝕜 (λy, -f y) x = - fderiv 𝕜 f x :=
by simp only [← fderiv_within_univ, fderiv_within_neg unique_diff_within_at_univ]

end neg

section sub
/-! ### Derivative of the difference of two functions -/

theorem has_strict_fderiv_at.sub
  (hf : has_strict_fderiv_at f f' x) (hg : has_strict_fderiv_at g g' x) :
  has_strict_fderiv_at (λ x, f x - g x) (f' - g') x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_fderiv_at_filter.sub
  (hf : has_fderiv_at_filter f f' x L) (hg : has_fderiv_at_filter g g' x L) :
  has_fderiv_at_filter (λ x, f x - g x) (f' - g') x L :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_fderiv_within_at.sub
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_fderiv_at.sub
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

lemma differentiable_within_at.sub
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  differentiable_within_at 𝕜 (λ y, f y - g y) s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  differentiable_at 𝕜 (λ y, f y - g y) x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).differentiable_at

lemma differentiable_on.sub
  (hf : differentiable_on 𝕜 f s) (hg : differentiable_on 𝕜 g s) :
  differentiable_on 𝕜 (λy, f y - g y) s :=
λx hx, (hf x hx).sub (hg x hx)

@[simp] lemma differentiable.sub
  (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
  differentiable 𝕜 (λy, f y - g y) :=
λx, (hf x).sub (hg x)

lemma fderiv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  fderiv_within 𝕜 (λy, f y - g y) s x = fderiv_within 𝕜 f s x - fderiv_within 𝕜 g s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λy, f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.sub_const
  (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ x, f x - c) f' x :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_fderiv_at_filter.sub_const
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ x, f x - c) f' x L :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_fderiv_within_at.sub_const
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ x, f x - c) f' s x :=
hf.sub_const c

theorem has_fderiv_at.sub_const
  (hf : has_fderiv_at f f' x) (c : F) :
  has_fderiv_at (λ x, f x - c) f' x :=
hf.sub_const c

lemma differentiable_within_at.sub_const
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, f y - c) s x :=
(hf.has_fderiv_within_at.sub_const c).differentiable_within_at

@[simp] lemma differentiable_within_at_sub_const_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, f y - c) s x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [sub_eq_add_neg, differentiable_within_at_add_const_iff]

lemma differentiable_at.sub_const (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, f y - c) x :=
(hf.has_fderiv_at.sub_const c).differentiable_at

@[simp] lemma differentiable_at_sub_const_iff (c : F) :
  differentiable_at 𝕜 (λ y, f y - c) x ↔ differentiable_at 𝕜 f x :=
by simp only [sub_eq_add_neg, differentiable_at_add_const_iff]

lemma differentiable_on.sub_const (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, f y - c) s :=
λx hx, (hf x hx).sub_const c

@[simp] lemma differentiable_on_sub_const_iff (c : F) :
  differentiable_on 𝕜 (λ y, f y - c) s ↔ differentiable_on 𝕜 f s :=
by simp only [sub_eq_add_neg, differentiable_on_add_const_iff]

lemma differentiable.sub_const (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, f y - c) :=
λx, (hf x).sub_const c

@[simp] lemma differentiable_sub_const_iff (c : F) :
  differentiable 𝕜 (λ y, f y - c) ↔ differentiable 𝕜 f :=
by simp only [sub_eq_add_neg, differentiable_add_const_iff]

lemma fderiv_within_sub_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, f y - c) s x = fderiv_within 𝕜 f s x :=
by simp only [sub_eq_add_neg, fderiv_within_add_const hxs]

lemma fderiv_sub_const (c : F) : fderiv 𝕜 (λy, f y - c) x = fderiv 𝕜 f x :=
by simp only [sub_eq_add_neg, fderiv_add_const]

theorem has_strict_fderiv_at.const_sub
  (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ x, c - f x) (-f') x :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_fderiv_at_filter.const_sub
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ x, c - f x) (-f') x L :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_fderiv_within_at.const_sub
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ x, c - f x) (-f') s x :=
hf.const_sub c

theorem has_fderiv_at.const_sub
  (hf : has_fderiv_at f f' x) (c : F) :
  has_fderiv_at (λ x, c - f x) (-f') x :=
hf.const_sub c

lemma differentiable_within_at.const_sub
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, c - f y) s x :=
(hf.has_fderiv_within_at.const_sub c).differentiable_within_at

@[simp] lemma differentiable_within_at_const_sub_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, c - f y) s x ↔ differentiable_within_at 𝕜 f s x :=
by simp [sub_eq_add_neg]

lemma differentiable_at.const_sub
  (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, c - f y) x :=
(hf.has_fderiv_at.const_sub c).differentiable_at

@[simp] lemma differentiable_at_const_sub_iff (c : F) :
  differentiable_at 𝕜 (λ y, c - f y) x ↔ differentiable_at 𝕜 f x :=
by simp [sub_eq_add_neg]

lemma differentiable_on.const_sub (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, c - f y) s :=
λx hx, (hf x hx).const_sub c

@[simp] lemma differentiable_on_const_sub_iff (c : F) :
  differentiable_on 𝕜 (λ y, c - f y) s ↔ differentiable_on 𝕜 f s :=
by simp [sub_eq_add_neg]

lemma differentiable.const_sub (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, c - f y) :=
λx, (hf x).const_sub c

@[simp] lemma differentiable_const_sub_iff (c : F) :
  differentiable 𝕜 (λ y, c - f y) ↔ differentiable 𝕜 f :=
by simp [sub_eq_add_neg]

lemma fderiv_within_const_sub (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, c - f y) s x = -fderiv_within 𝕜 f s x :=
by simp only [sub_eq_add_neg, fderiv_within_const_add, fderiv_within_neg, hxs]

lemma fderiv_const_sub (c : F) : fderiv 𝕜 (λy, c - f y) x = -fderiv 𝕜 f x :=
by simp only [← fderiv_within_univ, fderiv_within_const_sub unique_diff_within_at_univ]

end sub

end
