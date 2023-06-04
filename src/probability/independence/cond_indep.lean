/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.independence.indep_kernel
import probability.kernel.condexp

/-!
# Conditional Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `indep_sets.indep`: variant with two π-systems.

## Implementation notes

The definitions of independence in this file are a particular case of independence with respect to a
kernel and a measure, as defined in the file `indep_kernel.lean`.

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set Ω)`.
Three other independence notions are related to `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space Ω`,
* `Indep_set`: independence of a family of sets `s : ι → set Ω`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). See
`probability_theory.Indep_setsₖ`. An alternative and equivalent way of defining independence would
have been to use countable sets.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {Ω} {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space Ω]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory measurable_space
open_locale big_operators measure_theory ennreal

namespace probability_theory

variables {Ω ι : Type*} [nonempty Ω] [topological_space Ω] [polish_space Ω]
  {m₀ : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω]

section definitions

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def cond_Indep_sets (π : ι → set (set Ω)) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] :
  Prop :=
Indep_setsₖ π (condexp_kernel μ m₀) (μ.trim hm₀)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def cond_indep_sets (s1 s2 : set (set Ω)) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] :
  Prop :=
indep_setsₖ s1 s2 (condexp_kernel μ m₀) (μ.trim hm₀)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def cond_Indep (m : ι → measurable_space Ω) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] :
  Prop :=
Indepₖ m (condexp_kernel μ m₀) (μ.trim hm₀)

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def cond_indep {Ω : Type*} [nonempty Ω] [topological_space Ω] [polish_space Ω]
  (m₁ m₂ : measurable_space Ω) {m₀ : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω]
  (hm₀ : m₀ ≤ mΩ) (μ : measure Ω . volume_tac) [is_finite_measure μ] :
  Prop :=
indepₖ m₁ m₂ (condexp_kernel μ m₀) (μ.trim hm₀)

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def cond_Indep_set (s : ι → set Ω) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] : Prop :=
Indep_setₖ s (condexp_kernel μ m₀) (μ.trim hm₀)

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def cond_indep_set (s t : set Ω) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] : Prop :=
indep_setₖ s t (condexp_kernel μ m₀) (μ.trim hm₀)

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def cond_Indep_fun {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), Ω → β x) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] : Prop :=
Indep_funₖ m f (condexp_kernel μ m₀) (μ.trim hm₀)

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def cond_indep_fun {β γ} [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) (hm₀ : m₀ ≤ mΩ)
  (μ : measure Ω . volume_tac) [is_finite_measure μ] : Prop :=
indep_funₖ f g (condexp_kernel μ m₀) (μ.trim hm₀)

end definitions

section definition_lemmas

variables {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]

/-
lemma cond_Indep_sets_def (π : ι → set (set Ω)) :
  cond_Indep_sets π hm₀ μ ↔ ∀ (s : finset ι) {f : ι → set Ω} (H : ∀ i, i ∈ s → f i ∈ π i),
    μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i) :=
by simp only [cond_Indep_sets, Indep_setsₖ, ae_dirac_eq, filter.eventually_pure, kernel.const_apply]

lemma cond_indep_sets_def (s1 s2 : set (set Ω)) :
  cond_indep_sets s1 s2 hm₀ μ ↔ ∀ t1 t2 : set Ω, t1 ∈ s1 → t2 ∈ s2 → (μ (t1 ∩ t2) = μ t1 * μ t2) :=
by simp only [cond_indep_sets, indep_setsₖ, ae_dirac_eq, filter.eventually_pure, kernel.const_apply]
-/

lemma cond_Indep_iff_cond_Indep_sets (m : ι → measurable_space Ω) :
  cond_Indep m hm₀ μ ↔ cond_Indep_sets (λ x, {s | measurable_set[m x] s}) hm₀ μ :=
by rw [cond_Indep, cond_Indep_sets, Indepₖ]

lemma cond_indep_iff_cond_indep_sets (m₁ m₂ : measurable_space Ω) [mΩ : measurable_space Ω]
  [borel_space Ω] {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ] :
  cond_indep m₁ m₂ hm₀ μ
    ↔ cond_indep_sets {s | measurable_set[m₁] s} {s | measurable_set[m₂] s} hm₀ μ :=
by rw [cond_indep, cond_indep_sets, indepₖ]

/-
lemma cond_indep_iff (m₁ m₂ : measurable_space Ω) [mΩ : measurable_space Ω]
  [borel_space Ω] {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ] :
  cond_indep m₁ m₂ hm₀ μ
    ↔ ∀ t1 t2, measurable_set[m₁] t1 → measurable_set[m₂] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 :=
by { rw [cond_indep_iff_cond_indep_sets, cond_indep_sets_def], refl, }
-/

lemma cond_Indep_set_iff_cond_Indep (s : ι → set Ω) :
  cond_Indep_set s hm₀ μ ↔ cond_Indep (λ i, generate_from {s i}) hm₀ μ :=
by rw [cond_Indep_set, cond_Indep, Indep_setₖ]

lemma cond_indep_set_iff_cond_indep (s t : set Ω) :
  cond_indep_set s t hm₀ μ ↔ cond_indep (generate_from {s}) (generate_from {t}) hm₀ μ :=
by rw [cond_indep_set, cond_indep, indep_setₖ]

lemma cond_Indep_fun_iff_cond_Indep {β : ι → Type*}
  (m : Π (x : ι), measurable_space (β x)) (f : Π (x : ι), Ω → β x) :
  cond_Indep_fun m f hm₀ μ ↔ cond_Indep (λ x, measurable_space.comap (f x) (m x)) hm₀ μ :=
by rw [cond_Indep_fun, cond_Indep, Indep_funₖ]

lemma cond_indep_fun_iff_cond_indep {β γ} [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) :
  cond_indep_fun f g hm₀ μ
    ↔ cond_indep (measurable_space.comap f mβ) (measurable_space.comap g mγ) hm₀ μ :=
by rw [cond_indep_fun, cond_indep, indep_funₖ]

/-
lemma cond_indep_fun_iff {β γ} [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) :
  cond_indep_fun f g hm₀ μ ↔ ∀ t1 t2, measurable_set[measurable_space.comap f mβ] t1
    → measurable_set[measurable_space.comap g mγ] t2 → μ (t1 ∩ t2) = μ t1 * μ t2 :=
by rw [cond_indep_fun_iff_cond_indep, cond_indep_iff]
-/

end definition_lemmas

section indep

variables {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]

@[symm] lemma cond_indep_sets.symm {s₁ s₂ : set (set Ω)} (h : cond_indep_sets s₁ s₂ hm₀ μ) :
  cond_indep_sets s₂ s₁ hm₀ μ :=
h.symm

@[symm] lemma cond_indep.symm {m₁ m₂ : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]
  (h : cond_indep m₁ m₂ hm₀ μ) :
  cond_indep m₂ m₁ hm₀ μ :=
cond_indep_sets.symm h

lemma cond_indep_bot_right (m' : measurable_space Ω) {m : measurable_space Ω}
  [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_probability_measure μ] :
  cond_indep m' ⊥ hm₀ μ :=
indepₖ_bot_right m'

lemma cond_indep_bot_left (m' : measurable_space Ω) {m : measurable_space Ω}
  [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_probability_measure μ] :
  cond_indep ⊥ m' hm₀ μ :=
indepₖ_bot_left m'

lemma cond_indep_set_empty_right {m : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  cond_indep_set s ∅ hm₀ μ :=
indep_setₖ_empty_right s

lemma cond_indep_set_empty_left {m : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  cond_indep_set ∅ s hm₀ μ :=
indep_setₖ_empty_left s

lemma cond_indep_sets_of_cond_indep_sets_of_le_left {s₁ s₂ s₃: set (set Ω)}
  (h_indep : cond_indep_sets s₁ s₂ hm₀ μ) (h31 : s₃ ⊆ s₁) :
  cond_indep_sets s₃ s₂ hm₀ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma cond_indep_sets_of_cond_indep_sets_of_le_right {s₁ s₂ s₃: set (set Ω)}
  (h_indep : cond_indep_sets s₁ s₂ hm₀ μ) (h32 : s₃ ⊆ s₂) :
  cond_indep_sets s₁ s₃ hm₀ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma cond_indep_of_cond_indep_of_le_left {m₁ m₂ m₃ : measurable_space Ω}
  [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]
  (h_indep : cond_indep m₁ m₂ hm₀ μ) (h31 : m₃ ≤ m₁) :
  cond_indep m₃ m₂ hm₀ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma cond_indep_of_cond_indep_of_le_right {m₁ m₂ m₃ : measurable_space Ω}
  [mΩ : measurable_space Ω] [borel_space Ω]
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]
  (h_indep : cond_indep m₁ m₂ hm₀ μ) (h32 : m₃ ≤ m₂) :
  cond_indep m₁ m₃ hm₀ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma cond_indep_sets.union {s₁ s₂ s' : set (set Ω)}
  (h₁ : cond_indep_sets s₁ s' hm₀ μ) (h₂ : cond_indep_sets s₂ s' hm₀ μ) :
  cond_indep_sets (s₁ ∪ s₂) s' hm₀ μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

@[simp] lemma cond_indep_sets.union_iff {s₁ s₂ s' : set (set Ω)} :
  cond_indep_sets (s₁ ∪ s₂) s' hm₀ μ ↔ cond_indep_sets s₁ s' hm₀ μ ∧ cond_indep_sets s₂ s' hm₀ μ :=
⟨λ h, ⟨cond_indep_sets_of_cond_indep_sets_of_le_left h (set.subset_union_left s₁ s₂),
    cond_indep_sets_of_cond_indep_sets_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, cond_indep_sets.union h.left h.right⟩

lemma cond_indep_sets.Union {s : ι → set (set Ω)} {s' : set (set Ω)}
  (hyp : ∀ n, cond_indep_sets (s n) s' hm₀ μ) :
  cond_indep_sets (⋃ n, s n) s' hm₀ μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma cond_indep_sets.bUnion {s : ι → set (set Ω)} {s' : set (set Ω)} {u : set ι}
  (hyp : ∀ n ∈ u, cond_indep_sets (s n) s' hm₀ μ) :
  cond_indep_sets (⋃ n ∈ u, s n) s' hm₀ μ :=
begin
  intros t1 t2 ht1 ht2,
  simp_rw set.mem_Union at ht1,
  rcases ht1 with ⟨n, hpn, ht1⟩,
  exact hyp n hpn t1 t2 ht1 ht2,
end

lemma cond_indep_sets.inter {s₁ s' : set (set Ω)} (s₂ : set (set Ω))
  (h₁ : cond_indep_sets s₁ s' hm₀ μ) :
  cond_indep_sets (s₁ ∩ s₂) s' hm₀ μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma cond_indep_sets.Inter {s : ι → set (set Ω)} {s' : set (set Ω)}
  (h : ∃ n, cond_indep_sets (s n) s' hm₀ μ) :
  cond_indep_sets (⋂ n, s n) s' hm₀ μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

lemma cond_indep_sets.bInter {s : ι → set (set Ω)} {s' : set (set Ω)}
  {u : set ι} (h : ∃ n ∈ u, cond_indep_sets (s n) s' hm₀ μ) :
  cond_indep_sets (⋂ n ∈ u, s n) s' hm₀ μ :=
begin
  intros t1 t2 ht1 ht2,
  rcases h with ⟨n, hn, h⟩,
  exact h t1 t2 (set.bInter_subset_of_mem hn ht1) ht2,
end

/-
lemma cond_indep_sets_singleton_iff {s t : set Ω} :
  cond_indep_sets {s} {t} hm₀ μ ↔ μ (s ∩ t) = μ s * μ t :=
begin
  rw [cond_indep_sets, indep_setsₖ_singleton_iff],
  simp only [ae_dirac_eq, filter.eventually_pure, kernel.const_apply],
end
-/

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

variables {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]

lemma cond_Indep_sets.cond_indep_sets {s : ι → set (set Ω)}
  (h_indep : cond_Indep_sets s hm₀ μ) {i j : ι} (hij : i ≠ j) :
  cond_indep_sets (s i) (s j) hm₀ μ :=
Indep_setsₖ.indep_setsₖ h_indep hij

lemma cond_Indep.cond_indep {m : ι → measurable_space Ω}
  (h_indep : cond_Indep m hm₀ μ) {i j : ι} (hij : i ≠ j) :
  cond_indep (m i) (m j) hm₀ μ :=
begin
  change cond_indep_sets ((λ x, measurable_set[m x]) i) ((λ x, measurable_set[m x]) j) hm₀ μ,
  exact cond_Indep_sets.cond_indep_sets h_indep hij,
end

lemma cond_Indep_fun.cond_indep_fun {β : ι → Type*}
  {m : Π x, measurable_space (β x)} {f : Π i, Ω → β i} (hf_Indep : cond_Indep_fun m f hm₀ μ)
  {i j : ι} (hij : i ≠ j) :
  cond_indep_fun (f i) (f j) hm₀ μ :=
Indep_funₖ.indep_funₖ hf_Indep hij

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

variables {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]

lemma cond_Indep.cond_Indep_sets {m : ι → measurable_space Ω}
  {s : ι → set (set Ω)} (hms : ∀ n, m n = generate_from (s n))
  (h_indep : cond_Indep m hm₀ μ) :
  cond_Indep_sets s hm₀ μ :=
λ S f hfs, h_indep S $ λ x hxS,
  ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

lemma cond_indep.cond_indep_sets {s1 s2 : set (set Ω)}
  (h_indep : cond_indep (generate_from s1) (generate_from s2) hm₀ μ) :
  cond_indep_sets s1 s2 hm₀ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

lemma cond_indep_sets.cond_indep {m1 m2 : measurable_space Ω} [mΩ : measurable_space Ω]
  [borel_space Ω] {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_probability_measure μ]
  {p1 p2 : set (set Ω)} (h1 : m1 ≤ mΩ) (h2 : m2 ≤ mΩ)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : cond_indep_sets p1 p2 hm₀ μ) :
  cond_indep m1 m2 hm₀ μ :=
indep_setsₖ.indepₖ h1 h2 hp1 hp2 hpm1 hpm2 hyp

lemma cond_indep_sets.cond_indep' [mΩ : measurable_space Ω]
  [borel_space Ω] {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)}
  (hp1m : ∀ s ∈ p1, measurable_set s) (hp2m : ∀ s ∈ p2, measurable_set s)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hyp : cond_indep_sets p1 p2 hm₀ μ) :
  cond_indep (generate_from p1) (generate_from p2) hm₀ μ :=
hyp.cond_indep (generate_from_le hp1m) (generate_from_le hp2m) hp1 hp2 rfl rfl

variables {hm₀ : m₀ ≤ mΩ} {μ : measure Ω}

lemma cond_indep_sets_pi_Union_Inter_of_disjoint [is_probability_measure μ]
  {s : ι → set (set Ω)} {S T : set ι}
  (h_indep : cond_Indep_sets s hm₀ μ) (hST : disjoint S T) :
  cond_indep_sets (pi_Union_Inter s S) (pi_Union_Inter s T) hm₀ μ :=
indep_setsₖ_pi_Union_Inter_of_disjoint h_indep hST

lemma cond_Indep_set.cond_indep_generate_from_of_disjoint [is_probability_measure μ] {s : ι → set Ω}
  (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set s hm₀ μ) (S T : set ι) (hST : disjoint S T) :
  cond_indep (generate_from {t | ∃ n ∈ S, s n = t}) (generate_from {t | ∃ k ∈ T, s k = t}) hm₀ μ :=
Indep_setₖ.indepₖ_generate_from_of_disjoint hsm hs S T hST

lemma cond_indep_supr_of_disjoint [is_probability_measure μ] {m : ι → measurable_space Ω}
  (h_le : ∀ i, m i ≤ mΩ) (h_indep : cond_Indep m hm₀ μ) {S T : set ι} (hST : disjoint S T) :
  cond_indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) hm₀ μ :=
indepₖ_supr_of_disjoint h_le h_indep hST

lemma cond_indep_supr_of_directed_le {m : ι → measurable_space Ω}
  {m' : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω] {hm₀ : m₀ ≤ mΩ}
  {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, cond_indep (m i) m' hm₀ μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
  (hm : directed (≤) m) :
  cond_indep (⨆ i, m i) m' hm₀ μ :=
indepₖ_supr_of_directed_le h_indep h_le h_le' hm

lemma cond_Indep_set.cond_indep_generate_from_lt [preorder ι] [is_probability_measure μ]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set s hm₀ μ) (i : ι) :
  cond_indep (generate_from {s i}) (generate_from {t | ∃ j < i, s j = t}) hm₀ μ :=
Indep_setₖ.indepₖ_generate_from_lt hsm hs i

lemma cond_Indep_set.cond_indep_generate_from_le [linear_order ι] [is_probability_measure μ]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set s hm₀ μ)
  (i : ι) {k : ι} (hk : i < k) :
  cond_indep (generate_from {s k}) (generate_from {t | ∃ j ≤ i, s j = t}) hm₀ μ :=
Indep_setₖ.indepₖ_generate_from_le hsm hs i hk

lemma cond_Indep_set.cond_indep_generate_from_le_nat [is_probability_measure μ]
  {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : cond_Indep_set s hm₀ μ) (n : ℕ):
  cond_indep (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) hm₀ μ :=
hs.cond_indep_generate_from_le hsm _ n.lt_succ_self

lemma cond_indep_supr_of_monotone [semilattice_sup ι] {m : ι → measurable_space Ω}
  {m' : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω] {hm₀ : m₀ ≤ mΩ}
  {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, cond_indep (m i) m' hm₀ μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ) (hm : monotone m) :
  cond_indep (⨆ i, m i) m' hm₀ μ :=
cond_indep_supr_of_directed_le h_indep h_le h_le' (monotone.directed_le hm)

lemma cond_indep_supr_of_antitone [semilattice_inf ι] {m : ι → measurable_space Ω}
  {m' : measurable_space Ω} [mΩ : measurable_space Ω] [borel_space Ω] {hm₀ : m₀ ≤ mΩ}
  {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, cond_indep (m i) m' hm₀ μ) (h_le : ∀ i, m i ≤ mΩ) (h_le' : m' ≤ mΩ)
  (hm : antitone m) :
  cond_indep (⨆ i, m i) m' hm₀ μ :=
cond_indep_supr_of_directed_le h_indep h_le h_le' (directed_of_inf hm)

lemma cond_Indep_sets.pi_Union_Inter_of_not_mem {π : ι → set (set Ω)} {a : ι} {S : finset ι}
  [is_finite_measure μ] (hp_ind : cond_Indep_sets π hm₀ μ) (haS : a ∉ S) :
  cond_indep_sets (pi_Union_Inter π S) (π a) hm₀ μ :=
Indep_setsₖ.pi_Union_Inter_of_not_mem hp_ind haS

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem cond_Indep_sets.cond_Indep [is_probability_measure μ] (m : ι → measurable_space Ω)
  (h_le : ∀ i, m i ≤ mΩ) (π : ι → set (set Ω)) (h_pi : ∀ n, is_pi_system (π n))
  (h_generate : ∀ i, m i = generate_from (π i)) (h_ind : cond_Indep_sets π hm₀ μ) :
  cond_Indep m hm₀ μ :=
Indep_setsₖ.Indepₖ m h_le π h_pi h_generate h_ind

end from_pi_systems_to_measurable_spaces

section indep_set
/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/

variables {s t : set Ω} (S T : set (set Ω)) {hm₀ : m₀ ≤ mΩ} {μ : measure Ω}

lemma cond_indep_set_iff_cond_indep_sets_singleton
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  cond_indep_set s t hm₀ μ ↔ cond_indep_sets {s} {t} hm₀ μ :=
indep_setₖ_iff_indep_setsₖ_singleton hs_meas ht_meas

/-
lemma cond_indep_set_iff_measure_inter_eq_mul
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  cond_indep_set s t hm₀ μ ↔ μ (s ∩ t) = μ s * μ t :=
(cond_indep_set_iff_cond_indep_sets_singleton hs_meas ht_meas μ).trans cond_indep_sets_singleton_iff
-/

lemma cond_indep_sets.cond_indep_set_of_mem (hs : s ∈ S) (ht : t ∈ T)
  (hs_meas : measurable_set s) (ht_meas : measurable_set t) (μ : measure Ω . volume_tac)
  [is_probability_measure μ] (h_indep : cond_indep_sets S T hm₀ μ) :
  cond_indep_set s t hm₀ μ :=
indep_setsₖ.indep_setₖ_of_mem S T hs ht hs_meas ht_meas h_indep

lemma cond_indep.cond_indep_set_of_measurable_set {m₁ m₂ : measurable_space Ω}
  [mΩ : measurable_space Ω] [borel_space Ω] {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]
  (h_indep : cond_indep m₁ m₂ hm₀ μ) {s t : set Ω} (hs : measurable_set[m₁] s)
  (ht : measurable_set[m₂] t) :
  cond_indep_set s t hm₀ μ :=
indepₖ.indep_setₖ_of_measurable_set h_indep hs ht

lemma cond_indep_iff_forall_cond_indep_set (m₁ m₂ : measurable_space Ω)
  [mΩ : measurable_space Ω] [borel_space Ω] {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ] :
  cond_indep m₁ m₂ hm₀ μ
    ↔ ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → cond_indep_set s t hm₀ μ :=
indepₖ_iff_forall_indep_setₖ m₁ m₂

end indep_set

section indep_fun

/-! ### Independence of random variables

-/

variables {β β' γ γ' : Type*} {f : Ω → β} {g : Ω → β'}
  {hm₀ : m₀ ≤ mΩ} {μ : measure Ω} [is_finite_measure μ]

/-
lemma cond_indep_fun_iff_measure_inter_preimage_eq_mul
  {mβ : measurable_space β} {mβ' : measurable_space β'} :
  cond_indep_fun f g hm₀ μ
    ↔ ∀ s t, measurable_set s → measurable_set t
      → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) :=
begin
  rw [cond_indep_fun, indep_funₖ_iff_measure_inter_preimage_eq_mul],
  simp only [ae_dirac_eq, filter.eventually_pure, kernel.const_apply],
end

lemma cond_Indep_fun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
  (m : Π x, measurable_space (β x)) (f : Π i, Ω → β i) :
  cond_Indep_fun m f hm₀ μ
    ↔ ∀ (S : finset ι) {sets : Π i : ι, set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
      μ (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i in S, μ ((f i) ⁻¹' (sets i)) :=
begin
  rw [cond_Indep_fun, Indep_funₖ_iff_measure_inter_preimage_eq_mul],
  simp only [ae_dirac_eq, filter.eventually_pure, kernel.const_apply],
end

lemma cond_indep_fun_iff_cond_indep_set_preimage {mβ : measurable_space β} {mβ' : measurable_space β'}
  [is_probability_measure μ] (hf : measurable f) (hg : measurable g) :
  cond_indep_fun f g hm₀ μ
    ↔ ∀ s t, measurable_set s → measurable_set t → cond_indep_set (f ⁻¹' s) (g ⁻¹' t) hm₀ μ :=
begin
  refine cond_indep_fun_iff_measure_inter_preimage_eq_mul.trans _,
  split; intros h s t hs ht; specialize h s t hs ht,
  { rwa cond_indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ, },
  { rwa ← cond_indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ, },
end
-/

@[symm] lemma cond_indep_fun.symm {mβ : measurable_space β} {f g : Ω → β}
  (hfg : cond_indep_fun f g hm₀ μ) :
  cond_indep_fun g f hm₀ μ :=
hfg.symm

/-
lemma cond_indep_fun.ae_eq {mβ : measurable_space β} {f g f' g' : Ω → β}
  (hfg : cond_indep_fun f g hm₀ μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
  cond_indep_fun f' g' hm₀ μ :=
begin
  refine indep_funₖ.ae_eq hfg _ _,
  simp only [ae_dirac_eq, filter.eventually_pure],
  exacts [hf, hg],
end
-/

lemma cond_indep_fun.comp {mβ : measurable_space β} {mβ' : measurable_space β'}
  {mγ : measurable_space γ} {mγ' : measurable_space γ'} {φ : β → γ} {ψ : β' → γ'}
  (hfg : cond_indep_fun f g hm₀ μ) (hφ : measurable φ) (hψ : measurable ψ) :
  cond_indep_fun (φ ∘ f) (ψ ∘ g) hm₀ μ :=
indep_funₖ.comp hfg hφ hψ

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma cond_Indep_fun.cond_indep_fun_finset [is_probability_measure μ]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (S T : finset ι) (hST : disjoint S T) (hf_Indep : cond_Indep_fun m f hm₀ μ)
  (hf_meas : ∀ i, measurable (f i)) :
  cond_indep_fun (λ a (i : S), f i a) (λ a (i : T), f i a) hm₀ μ :=
Indep_funₖ.indep_funₖ_finset S T hST hf_Indep hf_meas

lemma cond_Indep_fun.cond_indep_fun_prod [is_probability_measure μ]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (hf_Indep : cond_Indep_fun m f hm₀ μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  cond_indep_fun (λ a, (f i a, f j a)) (f k) hm₀ μ :=
Indep_funₖ.indep_funₖ_prod hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma cond_Indep_fun.mul [is_probability_measure μ]
  {ι : Type*} {β : Type*} {m : measurable_space β} [has_mul β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : cond_Indep_fun (λ _, m) f hm₀ μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  cond_indep_fun (f i * f j) (f k) hm₀ μ :=
Indep_funₖ.mul hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma cond_Indep_fun.cond_indep_fun_finset_prod_of_not_mem [is_probability_measure μ]
  {ι : Type*} {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : cond_Indep_fun (λ _, m) f hm₀ μ) (hf_meas : ∀ i, measurable (f i))
  {s : finset ι} {i : ι} (hi : i ∉ s) :
  cond_indep_fun (∏ j in s, f j) (f i) hm₀ μ :=
Indep_funₖ.indep_funₖ_finset_prod_of_not_mem hf_Indep hf_meas hi

@[to_additive]
lemma cond_Indep_fun.cond_indep_fun_prod_range_succ [is_probability_measure μ]
  {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ℕ → Ω → β} (hf_Indep : cond_Indep_fun (λ _, m) f hm₀ μ) (hf_meas : ∀ i, measurable (f i))
  (n : ℕ) :
  cond_indep_fun (∏ j in finset.range n, f j) (f n) hm₀ μ :=
hf_Indep.cond_indep_fun_finset_prod_of_not_mem hf_meas finset.not_mem_range_self

lemma cond_Indep_set.cond_Indep_fun_indicator [has_zero β] [has_one β] {m : measurable_space β}
  {s : ι → set Ω} (hs : cond_Indep_set s hm₀ μ) :
  cond_Indep_fun (λ n, m) (λ n, (s n).indicator (λ ω, 1)) hm₀ μ :=
Indep_setₖ.Indep_funₖ_indicator hs

end indep_fun

end probability_theory
