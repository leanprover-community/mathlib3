/-
Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
Authors: Martin Zinkevich, Hunter Monroe
 -/

import measure_theory.measure_space

/-! This file defines the basic concepts in probability theory.
    There are four fundamental principles:
    1. Make theorems as readable as possible. Use Pr[A ∧ B], not μ (A ∩ B). Other examples:
       Pr[(X >ᵣ 3) ∨ (Y =ᵣ 7)]. While events are technically sets, in probability theory,
       they are better written as propositions that may or may not hold.
    2. Avoid absurd statements where possible. Don't allow Pr[A] if A is not an event,
       or Pr[X ∈ᵣ S] if S is not measurable, or Pr[∀ᵣ a in S, E a] if S is not countable.
       It is always possible to write Pr[⟨S, ...proof S is an event...⟩].
    3. Embed measurability into the objects and operations themselves. An event is measurable by
       definition. When we take the and, or, not, for all, exists, measurability should be
       automatic.
    4. Don't expect the reader to know measure theory, but at times it may be required by the
       author.

    Several concepts are defined in this module:
      probability_space: a measure_space where the measure has a value of 1.
      measurable_setB: a subtype of a set that is measurable (defined based upon the measurable
      space).
      event: a measurable_setB on a probability space (defined based upon the probability).
      Pr[E]: the probability of an event (note: expectations are defined in real_random_variable).
      measurable_fun: a subtype of a function that is measurable (denoted (M₁ →ₘ M₂)).
      random_variable: a measurable_fun whose domain is a probability space (denoted (P →ᵣ M)).

     Some symbols are defined as well:
     * (∀ᵣ i, E i): for all E
     * (∃ᵣ i, F i): exists i, such that F.
     * X ∈ᵣ S: the event that the random variable X is in the measurable set S.
     * and more!

     Also, various independence and identical definitions are specified. Some choices:
     * A and B are independent if A has zero probability.
     * an infinite family of events/random variables is independent if every finite subset
       is independent.
     * Two random variables are identical if they have equal probability on every measurable
       set. The probability spaces on which they are defined need not be equal.
      -/

class probability_space (α: Type*) extends measure_theory.measure_space α :=
  (univ_one:volume.measure_of (set.univ) = 1)

instance probability_space.to_measurable_space (α:Type*) [probability_space α]:measurable_space α:=
  measure_theory.measure_space.to_measurable_space

@[simp]
lemma probability_space.univ_one' {α:Type*} (Pα:probability_space α):
  (@measure_theory.measure_space.volume α Pα.to_measure_space) (@set.univ α) = 1 := begin
  rw ← measure_theory.coe_to_outer_measure,
  rw ← measure_theory.outer_measure.measure_of_eq_coe,
  rw probability_space.univ_one
end
