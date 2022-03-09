/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
import measure_theory.measure.measure_space
import data.set.pi

/-!
# Joint and marginal distributions

This file defines joint and marginal distributions on random variables.

Given an event space `α`, an arbitrary (not necessarily countable) index type `ι`, 
an index of types `β : ι → Type*` each with their own measurable space, an index
of random variables `f : Π (i : ι), α → (β i)` and a measure `μ : measure α`,
we define the joint distribution `joint μ f` as the distribution on `Π (i : ι), β i`
induced by `f` via `μ`.

For a set of "marginalizing variable" indices `mv : set ι`, we define the
marginal distribution `marginal μ f mv` as the distribution on `Π (i : mv), β i` induced by
the restriction of `f` to `mv` via `μ`.

We also define a generic marginalization on a measure `μ : measure (Π (i : ι), β i)` to
an index subset `mv` (yielding a `measure (Π (i : mv), β i)`) as `marginalize μ mv`.

## Notations

Because we expect to frequently use `set.pi_restrict` in this context, we define special notation
for it. For a `S : set ι`,
* the notation `<[S]` stands for `set.image (set.pi_restrict S)`,
  i.e. the restrictor of `set (Π (i : ι), β i)` to `set (Π (i : S), β i)`, and
* the notation `>[S]` stands for `set.image (set.pi_restrict S)`,
  i.e. the extender of `set (Π (i : S), β i)` to `set (Π (i : ι), β i)`.
In both cases `S` can be omitted from the brackets to be inferred.

## Main statements

* `marginal_eq_marginalize_joint`: the marginal distribution is the marginalized joint distribution.
* `marginal_apply`: the marginal distribution's measure of a set `s : Π (i : mv), β i`
is the joint distribution's measure of that same set, extended to allow the unmarginalized variables
to take any value.

## Tags

random variable, joint, marginal, marginalization
-/
open measure_theory measure_theory.measure measurable_space

noncomputable theory

namespace probability_theory

localized "notation  `<[`S`]` := set.image (set.pi_restrict S)" in probability_theory
localized "notation  `>[`S`]` := set.preimage (set.pi_restrict S)" in probability_theory

localized "notation  `<[]` := set.image (set.pi_restrict _)" in probability_theory
localized "notation  `>[]` := set.preimage (set.pi_restrict _)" in probability_theory

variables {α : Type*} {m : measurable_space α} (μ : measure α) {ι : Type*}
  {β : ι → Type*} (f : Π i : ι, α → (β i)) [Π i : ι, measurable_space (β i)]

section definitions

/-- The joint distribution induced by an indexed family of random variables `f`. -/
def joint : measure (Π i : ι, β i) := map (λ a i, f i a) μ

/-- The marginal distribution induced by an indexed family of random variables `f`
restricted to a subset of "marginalizing variable" indices `mv` (represented as
an index subtype). -/
def marginal (mv : set ι) : measure $ Π i : mv, β i := joint μ $ mv.pi_restrict f

/-- Generic marginalization of the joint measure `μ` on the given subset of variables `mv`. -/
def marginalize (μ : measure (Π i : ι, β i)) (mv : set ι) :
  measure (Π i : mv, β i) := map mv.pi_restrict μ

end definitions

section marginal

/-- The marginal distribution is the marginalized joint distribution. -/
lemma marginal_eq_marginalize_joint (hm : ∀ i : ι, measurable (f i)) (mv : set ι) :
  marginal μ f mv = marginalize (joint μ f) mv :=
by { rw [marginalize, joint, map_map, function.comp], refl,
  apply measurable_pi_restrict, exact measurable_pi_iff.mpr hm }

lemma marginalize_apply (μ : measure (Π i : ι, β i)) (mv : set ι)
  {s : set (Π i : mv, β i)} (hms : measurable_set s) :
  marginalize μ mv s = μ (>[] s) :=
by { rw [marginalize, map_apply _ hms], apply measurable_pi_restrict }

/-- The marginalization principle: the marginal probability of a particular "marginal assignment" 
measurable set `s` is equal to the joint probability of that same set, extended to allow
the unmarginalized variables to take any value. -/
lemma marginal_apply (hm : ∀ i : ι, measurable (f i)) (mv : set ι)
  {s : set (Π i : mv, β i)} (hms : measurable_set s) :
  marginal μ f mv s = joint μ f (>[] s) :=
by rw [marginal_eq_marginalize_joint _ _ hm, marginalize_apply _ _ hms] 

end marginal

end probability_theory
