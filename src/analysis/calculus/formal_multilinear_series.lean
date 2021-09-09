/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.multilinear

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `times_cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

noncomputable theory

open set fin
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[derive add_comm_group]
def formal_multilinear_series
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E]
  (F : Type*) [normed_group F] [normed_space 𝕜 F] :=
Π (n : ℕ), (E [×n]→L[𝕜] F)

instance : inhabited (formal_multilinear_series 𝕜 E F) := ⟨0⟩

section module
/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/
local attribute [reducible] formal_multilinear_series

instance : module 𝕜 (formal_multilinear_series 𝕜 E F) :=
begin
  letI : ∀ n, module 𝕜 (continuous_multilinear_map 𝕜 (λ (i : fin n), E) F) :=
    λ n, by apply_instance,
  apply_instance
end

end module

namespace formal_multilinear_series

variables (p : formal_multilinear_series 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift : formal_multilinear_series 𝕜 E (E →L[𝕜] F) :=
λn, (p n.succ).curry_right

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift (q : formal_multilinear_series 𝕜 E (E →L[𝕜] F)) (z : F) :
  formal_multilinear_series 𝕜 E F
| 0       := (continuous_multilinear_curry_fin0 𝕜 E F).symm z
| (n + 1) := continuous_multilinear_curry_right_equiv' 𝕜 n E F (q n)

/-- Killing the zeroth coefficient in a formal multilinear series -/
def remove_zero (p : formal_multilinear_series 𝕜 E F) : formal_multilinear_series 𝕜 E F
| 0       := 0
| (n + 1) := p (n + 1)

@[simp] lemma remove_zero_coeff_zero : p.remove_zero 0 = 0 := rfl

@[simp] lemma remove_zero_coeff_succ (n : ℕ) : p.remove_zero (n+1) = p (n+1) := rfl

lemma remove_zero_of_pos {n : ℕ} (h : 0 < n) : p.remove_zero n = p n :=
by { rw ← nat.succ_pred_eq_of_pos h, refl }

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
lemma congr (p : formal_multilinear_series 𝕜 E F) {m n : ℕ} {v : fin m → E} {w : fin n → E}
  (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
  p m v = p n w :=
by { cases h1, congr' with ⟨i, hi⟩, exact h2 i hi hi }

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def comp_continuous_linear_map (p : formal_multilinear_series 𝕜 F G) (u : E →L[𝕜] F) :
  formal_multilinear_series 𝕜 E G :=
λ n, (p n).comp_continuous_linear_map (λ (i : fin n), u)

@[simp] lemma comp_continuous_linear_map_apply
  (p : formal_multilinear_series 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ) (v : fin n → E) :
  (p.comp_continuous_linear_map u) n v = p n (u ∘ v) := rfl

variables (𝕜) {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E]
variables [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series, where `𝕜'` is a
normed algebra over `𝕜`. -/
@[simp] protected def restrict_scalars (p : formal_multilinear_series 𝕜' E F) :
  formal_multilinear_series 𝕜 E F :=
λ n, (p n).restrict_scalars 𝕜

end formal_multilinear_series
