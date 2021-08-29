/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.continuous_on
import algebra.indicator_function
import topology.algebra.group
import topology.algebra.ordered.liminf_limsup
import topology.instances.ennreal

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is lower semicontinuous at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it can not jump down.

Upper semicontinuous functions are defined similarly.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 definitions related to lower semicontinuity:
* `lower_semicontinuous_within_at f s x`
* `lower_semicontinuous_at f x`
* `lower_semicontinuous_on f s`
* `lower_semicontinuous f`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are lower semicontinuous;
* `indicator s (λ _, y)` is lower semicontinuous when `s` is open and `0 ≤ y`, or when `s` is closed
  and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `order_dual`.

-/

open_locale topological_space big_operators ennreal
open set

variables {α : Type*} [topological_space α] {β : Type*} [preorder β]
{f g : α → β} {x : α} {s t : set α} {y z : β}

/-! ### Main definitions -/

/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def lower_semicontinuous_within_at (f : α → β) (s : set α) (x : α) :=
∀ y < f x, ∀ᶠ x' in 𝓝[s] x, y < f x'

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`.-/
def lower_semicontinuous_on (f : α → β) (s : set α) :=
∀ x ∈ s, lower_semicontinuous_within_at f s x

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def lower_semicontinuous_at (f : α → β) (x : α) :=
∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def lower_semicontinuous (f : α → β) :=
∀ x, lower_semicontinuous_at f x

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def upper_semicontinuous_within_at (f : α → β) (s : set α) (x : α) :=
∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def upper_semicontinuous_on (f : α → β) (s : set α) :=
∀ x ∈ s, upper_semicontinuous_within_at f s x

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
def upper_semicontinuous_at (f : α → β) (x : α) :=
∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def upper_semicontinuous (f : α → β) :=
∀ x, upper_semicontinuous_at f x

/-!
### Lower semicontinuous functions
-/

/-! #### Basic dot notation interface for lower semicontinuity -/

lemma lower_semicontinuous_within_at.mono (h : lower_semicontinuous_within_at f s x)
  (hst : t ⊆ s) : lower_semicontinuous_within_at f t x :=
λ y hy, filter.eventually.filter_mono (nhds_within_mono _ hst) (h y hy)

lemma lower_semicontinuous_within_at_univ_iff :
  lower_semicontinuous_within_at f univ x ↔ lower_semicontinuous_at f x :=
by simp [lower_semicontinuous_within_at, lower_semicontinuous_at, nhds_within_univ]

lemma lower_semicontinuous_at.lower_semicontinuous_within_at
  (s : set α) (h : lower_semicontinuous_at f x) : lower_semicontinuous_within_at f s x :=
λ y hy, filter.eventually.filter_mono nhds_within_le_nhds (h y hy)

lemma lower_semicontinuous_on.lower_semicontinuous_within_at
  (h : lower_semicontinuous_on f s) (hx : x ∈ s) :
  lower_semicontinuous_within_at f s x :=
h x hx

lemma lower_semicontinuous_on.mono (h : lower_semicontinuous_on f s) (hst : t ⊆ s) :
  lower_semicontinuous_on f t :=
λ x hx, (h x (hst hx)).mono hst

lemma lower_semicontinuous_on_univ_iff :
  lower_semicontinuous_on f univ ↔ lower_semicontinuous f :=
by simp [lower_semicontinuous_on, lower_semicontinuous, lower_semicontinuous_within_at_univ_iff]

lemma lower_semicontinuous.lower_semicontinuous_at
  (h : lower_semicontinuous f) (x : α) : lower_semicontinuous_at f x :=
h x

lemma lower_semicontinuous.lower_semicontinuous_within_at
  (h : lower_semicontinuous f) (s : set α) (x : α) : lower_semicontinuous_within_at f s x :=
(h x).lower_semicontinuous_within_at s

lemma lower_semicontinuous.lower_semicontinuous_on
  (h : lower_semicontinuous f) (s : set α) : lower_semicontinuous_on f s :=
λ x hx, h.lower_semicontinuous_within_at s x

/-! #### Constants -/

lemma lower_semicontinuous_within_at_const :
  lower_semicontinuous_within_at (λ x, z) s x :=
λ y hy, filter.eventually_of_forall (λ x, hy)

lemma lower_semicontinuous_at_const :
  lower_semicontinuous_at (λ x, z) x :=
λ y hy, filter.eventually_of_forall (λ x, hy)

lemma lower_semicontinuous_on_const :
  lower_semicontinuous_on (λ x, z) s :=
λ x hx, lower_semicontinuous_within_at_const

lemma lower_semicontinuous_const :
  lower_semicontinuous (λ (x : α), z) :=
λ x, lower_semicontinuous_at_const

/-! #### Indicators -/

section
variables [has_zero β]

lemma is_open.lower_semicontinuous_indicator (hs : is_open s) (hy : 0 ≤ y) :
  lower_semicontinuous (indicator s (λ x, y)) :=
begin
  assume x z hz,
  by_cases h : x ∈ s; simp [h] at hz,
  { filter_upwards [hs.mem_nhds h],
    simp [hz] { contextual := tt} },
  { apply filter.eventually_of_forall (λ x', _),
    by_cases h' : x' ∈ s;
    simp [h', hz.trans_le hy, hz] }
end

lemma is_open.lower_semicontinuous_on_indicator (hs : is_open s) (hy : 0 ≤ y) :
  lower_semicontinuous_on (indicator s (λ x, y)) t :=
(hs.lower_semicontinuous_indicator hy).lower_semicontinuous_on t

lemma is_open.lower_semicontinuous_at_indicator (hs : is_open s) (hy : 0 ≤ y) :
  lower_semicontinuous_at (indicator s (λ x, y)) x :=
(hs.lower_semicontinuous_indicator hy).lower_semicontinuous_at x

lemma is_open.lower_semicontinuous_within_at_indicator (hs : is_open s) (hy : 0 ≤ y) :
  lower_semicontinuous_within_at (indicator s (λ x, y)) t x :=
(hs.lower_semicontinuous_indicator hy).lower_semicontinuous_within_at t x

lemma is_closed.lower_semicontinuous_indicator (hs : is_closed s) (hy : y ≤ 0) :
  lower_semicontinuous (indicator s (λ x, y)) :=
begin
  assume x z hz,
  by_cases h : x ∈ s; simp [h] at hz,
  { apply filter.eventually_of_forall (λ x', _),
    by_cases h' : x' ∈ s;
    simp [h', hz, hz.trans_le hy], },
  { filter_upwards [hs.is_open_compl.mem_nhds h],
    simp [hz] { contextual := tt } }
end

lemma is_closed.lower_semicontinuous_on_indicator (hs : is_closed s) (hy : y ≤ 0) :
  lower_semicontinuous_on (indicator s (λ x, y)) t :=
(hs.lower_semicontinuous_indicator hy).lower_semicontinuous_on t

lemma is_closed.lower_semicontinuous_at_indicator (hs : is_closed s) (hy : y ≤ 0) :
  lower_semicontinuous_at (indicator s (λ x, y)) x :=
(hs.lower_semicontinuous_indicator hy).lower_semicontinuous_at x

lemma is_closed.lower_semicontinuous_within_at_indicator (hs : is_closed s) (hy : y ≤ 0) :
  lower_semicontinuous_within_at (indicator s (λ x, y)) t x :=
(hs.lower_semicontinuous_indicator hy).lower_semicontinuous_within_at t x

end

/-! #### Relationship with continuity -/

theorem lower_semicontinuous_iff_is_open :
  lower_semicontinuous f ↔ ∀ y, is_open (f ⁻¹' (Ioi y)) :=
⟨λ H y, is_open_iff_mem_nhds.2 (λ x hx, H x y hx), λ H x y y_lt, is_open.mem_nhds (H y) y_lt⟩

lemma lower_semicontinuous.is_open_preimage (hf : lower_semicontinuous f) (y : β) :
  is_open (f ⁻¹' (Ioi y)) :=
lower_semicontinuous_iff_is_open.1 hf y

section
variables {γ : Type*} [linear_order γ] [topological_space γ] [order_topology γ]

lemma continuous_within_at.lower_semicontinuous_within_at {f : α → γ}
  (h : continuous_within_at f s x) : lower_semicontinuous_within_at f s x :=
λ y hy, h (Ioi_mem_nhds hy)

lemma continuous_at.lower_semicontinuous_at {f : α → γ}
  (h : continuous_at f x) : lower_semicontinuous_at f x :=
λ y hy, h (Ioi_mem_nhds hy)

lemma continuous_on.lower_semicontinuous_on {f : α → γ}
  (h : continuous_on f s) : lower_semicontinuous_on f s :=
λ x hx, (h x hx).lower_semicontinuous_within_at

lemma continuous.lower_semicontinuous {f : α → γ}
  (h : continuous f) : lower_semicontinuous f :=
λ x, h.continuous_at.lower_semicontinuous_at

end

/-! ### Composition -/

section
variables {γ : Type*} [linear_order γ] [topological_space γ] [order_topology γ]
variables {δ : Type*} [linear_order δ] [topological_space δ] [order_topology δ]

lemma continuous_at.comp_lower_semicontinuous_within_at
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : lower_semicontinuous_within_at f s x)
  (gmon : monotone g) : lower_semicontinuous_within_at (g ∘ f) s x :=
begin
  assume y hy,
  by_cases h : ∃ l, l < f x,
  { obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' (Ioi y) :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h,
    filter_upwards [hf z zlt],
    assume a ha,
    calc y < g (min (f x) (f a)) : hz (by simp [zlt, ha, le_refl])
    ... ≤ g (f a) : gmon (min_le_right _ _) },
  { simp only [not_exists, not_lt] at h,
    exact filter.eventually_of_forall (λ a, hy.trans_le (gmon (h (f a)))) }
end

lemma continuous_at.comp_lower_semicontinuous_at
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : lower_semicontinuous_at f x)
  (gmon : monotone g) : lower_semicontinuous_at (g ∘ f) x :=
begin
  simp only [← lower_semicontinuous_within_at_univ_iff] at hf ⊢,
  exact hg.comp_lower_semicontinuous_within_at hf gmon
end

lemma continuous.comp_lower_semicontinuous_on
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : lower_semicontinuous_on f s)
  (gmon : monotone g) : lower_semicontinuous_on (g ∘ f) s :=
λ x hx, (hg.continuous_at).comp_lower_semicontinuous_within_at (hf x hx) gmon

lemma continuous.comp_lower_semicontinuous
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : lower_semicontinuous f)
  (gmon : monotone g) : lower_semicontinuous (g ∘ f) :=
λ x, (hg.continuous_at).comp_lower_semicontinuous_at (hf x) gmon

lemma continuous_at.comp_lower_semicontinuous_within_at_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : lower_semicontinuous_within_at f s x)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : upper_semicontinuous_within_at (g ∘ f) s x :=
@continuous_at.comp_lower_semicontinuous_within_at α _ x s γ _ _ _ (order_dual δ) _ _ _
  g f hg hf gmon

lemma continuous_at.comp_lower_semicontinuous_at_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : lower_semicontinuous_at f x)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : upper_semicontinuous_at (g ∘ f) x :=
@continuous_at.comp_lower_semicontinuous_at α _ x γ _ _ _ (order_dual δ) _ _ _ g f hg hf gmon

lemma continuous.comp_lower_semicontinuous_on_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : lower_semicontinuous_on f s)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : upper_semicontinuous_on (g ∘ f) s :=
λ x hx, (hg.continuous_at).comp_lower_semicontinuous_within_at_antimono (hf x hx) gmon

lemma continuous.comp_lower_semicontinuous_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : lower_semicontinuous f)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : upper_semicontinuous (g ∘ f) :=
λ x, (hg.continuous_at).comp_lower_semicontinuous_at_antimono (hf x) gmon

end

/-! #### Addition -/

section
variables {ι : Type*} {γ : Type*} [linear_ordered_add_comm_monoid γ]
[topological_space γ] [order_topology γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma lower_semicontinuous_within_at.add' {f g : α → γ}
  (hf : lower_semicontinuous_within_at f s x) (hg : lower_semicontinuous_within_at g s x)
  (hcont : continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  lower_semicontinuous_within_at (λ z, f z + g z) s x :=
begin
  assume y hy,
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ : ∃ (u v : set γ), is_open u ∧ f x ∈ u ∧ is_open v ∧
    g x ∈ v ∧ u.prod v ⊆ {p : γ × γ | y < p.fst + p.snd} :=
  mem_nhds_prod_iff'.1 (hcont (is_open_Ioi.mem_nhds hy)),
  by_cases hx₁ : ∃ l, l < f x,
  { obtain ⟨z₁, z₁lt, h₁⟩ : ∃ z₁ < f x, Ioc z₁ (f x) ⊆ u :=
      exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁,
    by_cases hx₂ : ∃ l, l < g x,
    { obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂,
      filter_upwards [hf z₁ z₁lt, hg z₂ z₂lt],
      assume z h₁z h₂z,
      have A1 : min (f z) (f x) ∈ u,
      { by_cases H : f z ≤ f x,
        { simp [H], exact h₁ ⟨h₁z, H⟩ },
        { simp [le_of_not_le H], exact h₁ ⟨z₁lt, le_refl _⟩, } },
      have A2 : min (g z) (g x) ∈ v,
      { by_cases H : g z ≤ g x,
        { simp [H], exact h₂ ⟨h₂z, H⟩ },
        { simp [le_of_not_le H], exact h₂ ⟨z₂lt, le_refl _⟩, } },
      have : (min (f z) (f x), min (g z) (g x)) ∈ u.prod v := ⟨A1, A2⟩,
      calc y < min (f z) (f x) + min (g z) (g x) : h this
      ... ≤ f z + g z : add_le_add (min_le_left _ _) (min_le_left _ _) },
    { simp only [not_exists, not_lt] at hx₂,
      filter_upwards [hf z₁ z₁lt],
      assume z h₁z,
      have A1 : min (f z) (f x) ∈ u,
      { by_cases H : f z ≤ f x,
        { simp [H], exact h₁ ⟨h₁z, H⟩ },
        { simp [le_of_not_le H], exact h₁ ⟨z₁lt, le_refl _⟩, } },
      have : (min (f z) (f x), g x) ∈ u.prod v := ⟨A1, xv⟩,
      calc y < min (f z) (f x) + g x : h this
      ... ≤ f z + g z : add_le_add (min_le_left _ _) (hx₂ (g z)) } },
  { simp only [not_exists, not_lt] at hx₁,
    by_cases hx₂ : ∃ l, l < g x,
    { obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂,
      filter_upwards [hg z₂ z₂lt],
      assume z h₂z,
      have A2 : min (g z) (g x) ∈ v,
      { by_cases H : g z ≤ g x,
        { simp [H], exact h₂ ⟨h₂z, H⟩ },
        { simp [le_of_not_le H], exact h₂ ⟨z₂lt, le_refl _⟩, } },
      have : (f x, min (g z) (g x)) ∈ u.prod v := ⟨xu, A2⟩,
      calc y < f x + min (g z) (g x) : h this
      ... ≤ f z + g z : add_le_add (hx₁ (f z)) (min_le_left _ _) },
    { simp only [not_exists, not_lt] at hx₁ hx₂,
      apply filter.eventually_of_forall,
      assume z,
      have : (f x, g x) ∈ u.prod v := ⟨xu, xv⟩,
      calc y < f x + g x : h this
      ... ≤ f z + g z : add_le_add (hx₁ (f z)) (hx₂ (g z)) } },
end

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma lower_semicontinuous_at.add' {f g : α → γ}
  (hf : lower_semicontinuous_at f x) (hg : lower_semicontinuous_at g x)
  (hcont : continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  lower_semicontinuous_at (λ z, f z + g z) x :=
by { simp_rw [← lower_semicontinuous_within_at_univ_iff] at *, exact hf.add' hg hcont }

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma lower_semicontinuous_on.add' {f g : α → γ}
  (hf : lower_semicontinuous_on f s) (hg : lower_semicontinuous_on g s)
  (hcont : ∀ x ∈ s, continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  lower_semicontinuous_on (λ z, f z + g z) s :=
λ x hx, (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma lower_semicontinuous.add' {f g : α → γ}
  (hf : lower_semicontinuous f) (hg : lower_semicontinuous g)
  (hcont : ∀ x, continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  lower_semicontinuous (λ z, f z + g z) :=
λ x, (hf x).add' (hg x) (hcont x)

variable [has_continuous_add γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma lower_semicontinuous_within_at.add {f g : α → γ}
  (hf : lower_semicontinuous_within_at f s x) (hg : lower_semicontinuous_within_at g s x) :
  lower_semicontinuous_within_at (λ z, f z + g z) s x :=
hf.add' hg continuous_add.continuous_at

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma lower_semicontinuous_at.add {f g : α → γ}
  (hf : lower_semicontinuous_at f x) (hg : lower_semicontinuous_at g x) :
  lower_semicontinuous_at (λ z, f z + g z) x :=
hf.add' hg continuous_add.continuous_at

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma lower_semicontinuous_on.add {f g : α → γ}
  (hf : lower_semicontinuous_on f s) (hg : lower_semicontinuous_on g s) :
  lower_semicontinuous_on (λ z, f z + g z) s :=
hf.add' hg (λ x hx, continuous_add.continuous_at)

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma lower_semicontinuous.add {f g : α → γ}
  (hf : lower_semicontinuous f) (hg : lower_semicontinuous g) :
  lower_semicontinuous (λ z, f z + g z) :=
hf.add' hg (λ x, continuous_add.continuous_at)

lemma lower_semicontinuous_within_at_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, lower_semicontinuous_within_at (f i) s x) :
  lower_semicontinuous_within_at (λ z, (∑ i in a, f i z)) s x :=
begin
  classical,
  induction a using finset.induction_on with i a ia IH generalizing ha,
  { exact lower_semicontinuous_within_at_const },
  { simp only [ia, finset.sum_insert, not_false_iff],
    exact lower_semicontinuous_within_at.add (ha _ (finset.mem_insert_self i a))
      (IH (λ j ja, ha j (finset.mem_insert_of_mem ja))) }
end

lemma lower_semicontinuous_at_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, lower_semicontinuous_at (f i) x) :
  lower_semicontinuous_at (λ z, (∑ i in a, f i z)) x :=
begin
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *,
  exact lower_semicontinuous_within_at_sum ha
end

lemma lower_semicontinuous_on_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, lower_semicontinuous_on (f i) s) :
  lower_semicontinuous_on (λ z, (∑ i in a, f i z)) s :=
λ x hx, lower_semicontinuous_within_at_sum (λ i hi, ha i hi x hx)

lemma lower_semicontinuous_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, lower_semicontinuous (f i)) :
  lower_semicontinuous (λ z, (∑ i in a, f i z)) :=
λ x, lower_semicontinuous_at_sum (λ i hi, ha i hi x)

end

/-! #### Supremum -/

section
variables {ι : Sort*} {δ : Type*} [complete_linear_order δ]

lemma lower_semicontinuous_within_at_supr {f : ι → α → δ}
  (h : ∀ i, lower_semicontinuous_within_at (f i) s x) :
  lower_semicontinuous_within_at (λ x', ⨆ i, f i x') s x :=
begin
  assume y hy,
  rcases lt_supr_iff.1 hy with ⟨i, hi⟩,
  filter_upwards [h i y hi],
  assume x' hx',
  exact lt_supr_iff.2 ⟨i, hx'⟩,
end

lemma lower_semicontinuous_within_at_bsupr {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, lower_semicontinuous_within_at (f i hi) s x) :
  lower_semicontinuous_within_at (λ x', ⨆ i hi, f i hi x') s x :=
lower_semicontinuous_within_at_supr $ λ i, lower_semicontinuous_within_at_supr $ λ hi, h i hi

lemma lower_semicontinuous_at_supr {f : ι → α → δ}
  (h : ∀ i, lower_semicontinuous_at (f i) x) :
  lower_semicontinuous_at (λ x', ⨆ i, f i x') x :=
begin
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *,
  exact lower_semicontinuous_within_at_supr h
end

lemma lower_semicontinuous_at_bsupr {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, lower_semicontinuous_at (f i hi) x) :
  lower_semicontinuous_at (λ x', ⨆ i hi, f i hi x') x :=
lower_semicontinuous_at_supr $ λ i, lower_semicontinuous_at_supr $ λ hi, h i hi

lemma lower_semicontinuous_on_supr {f : ι → α → δ}
  (h : ∀ i, lower_semicontinuous_on (f i) s) :
  lower_semicontinuous_on (λ x', ⨆ i, f i x') s :=
λ x hx, lower_semicontinuous_within_at_supr (λ i, h i x hx)

lemma lower_semicontinuous_on_bsupr {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, lower_semicontinuous_on (f i hi) s) :
  lower_semicontinuous_on (λ x', ⨆ i hi, f i hi x') s :=
lower_semicontinuous_on_supr $ λ i, lower_semicontinuous_on_supr $ λ hi, h i hi

lemma lower_semicontinuous_supr {f : ι → α → δ}
  (h : ∀ i, lower_semicontinuous (f i)) :
  lower_semicontinuous (λ x', ⨆ i, f i x') :=
λ x, lower_semicontinuous_at_supr (λ i, h i x)

lemma lower_semicontinuous_bsupr {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, lower_semicontinuous (f i hi)) :
  lower_semicontinuous (λ x', ⨆ i hi, f i hi x') :=
lower_semicontinuous_supr $ λ i, lower_semicontinuous_supr $ λ hi, h i hi

end

/-! #### Infinite sums -/

section
variables {ι : Type*}

lemma lower_semicontinuous_within_at_tsum {f : ι → α → ℝ≥0∞}
  (h : ∀ i, lower_semicontinuous_within_at (f i) s x) :
  lower_semicontinuous_within_at (λ x', ∑' i, f i x') s x :=
begin
  simp_rw ennreal.tsum_eq_supr_sum,
  apply lower_semicontinuous_within_at_supr (λ b, _),
  exact lower_semicontinuous_within_at_sum (λ i hi, h i),
end

lemma lower_semicontinuous_at_tsum {f : ι → α → ℝ≥0∞}
  (h : ∀ i, lower_semicontinuous_at (f i) x) :
  lower_semicontinuous_at (λ x', ∑' i, f i x') x :=
begin
  simp_rw [← lower_semicontinuous_within_at_univ_iff] at *,
  exact lower_semicontinuous_within_at_tsum h
end

lemma lower_semicontinuous_on_tsum {f : ι → α → ℝ≥0∞}
  (h : ∀ i, lower_semicontinuous_on (f i) s) :
  lower_semicontinuous_on (λ x', ∑' i, f i x') s :=
λ x hx, lower_semicontinuous_within_at_tsum (λ i, h i x hx)

lemma lower_semicontinuous_tsum {f : ι → α → ℝ≥0∞}
  (h : ∀ i, lower_semicontinuous (f i)) :
  lower_semicontinuous (λ x', ∑' i, f i x') :=
λ x, lower_semicontinuous_at_tsum (λ i, h i x)

end

/-!
### Upper semicontinuous functions
-/

/-! #### Basic dot notation interface for upper semicontinuity -/

lemma upper_semicontinuous_within_at.mono (h : upper_semicontinuous_within_at f s x)
  (hst : t ⊆ s) : upper_semicontinuous_within_at f t x :=
λ y hy, filter.eventually.filter_mono (nhds_within_mono _ hst) (h y hy)

lemma upper_semicontinuous_within_at_univ_iff :
  upper_semicontinuous_within_at f univ x ↔ upper_semicontinuous_at f x :=
by simp [upper_semicontinuous_within_at, upper_semicontinuous_at, nhds_within_univ]

lemma upper_semicontinuous_at.upper_semicontinuous_within_at
  (s : set α) (h : upper_semicontinuous_at f x) : upper_semicontinuous_within_at f s x :=
λ y hy, filter.eventually.filter_mono nhds_within_le_nhds (h y hy)

lemma upper_semicontinuous_on.upper_semicontinuous_within_at
  (h : upper_semicontinuous_on f s) (hx : x ∈ s) :
  upper_semicontinuous_within_at f s x :=
h x hx

lemma upper_semicontinuous_on.mono (h : upper_semicontinuous_on f s) (hst : t ⊆ s) :
  upper_semicontinuous_on f t :=
λ x hx, (h x (hst hx)).mono hst

lemma upper_semicontinuous_on_univ_iff :
  upper_semicontinuous_on f univ ↔ upper_semicontinuous f :=
by simp [upper_semicontinuous_on, upper_semicontinuous, upper_semicontinuous_within_at_univ_iff]

lemma upper_semicontinuous.upper_semicontinuous_at
  (h : upper_semicontinuous f) (x : α) : upper_semicontinuous_at f x :=
h x

lemma upper_semicontinuous.upper_semicontinuous_within_at
  (h : upper_semicontinuous f) (s : set α) (x : α) : upper_semicontinuous_within_at f s x :=
(h x).upper_semicontinuous_within_at s

lemma upper_semicontinuous.upper_semicontinuous_on
  (h : upper_semicontinuous f) (s : set α) : upper_semicontinuous_on f s :=
λ x hx, h.upper_semicontinuous_within_at s x

/-! #### Constants -/

lemma upper_semicontinuous_within_at_const :
  upper_semicontinuous_within_at (λ x, z) s x :=
λ y hy, filter.eventually_of_forall (λ x, hy)

lemma upper_semicontinuous_at_const :
  upper_semicontinuous_at (λ x, z) x :=
λ y hy, filter.eventually_of_forall (λ x, hy)

lemma upper_semicontinuous_on_const :
  upper_semicontinuous_on (λ x, z) s :=
λ x hx, upper_semicontinuous_within_at_const

lemma upper_semicontinuous_const :
  upper_semicontinuous (λ (x : α), z) :=
λ x, upper_semicontinuous_at_const


/-! #### Indicators -/

section
variables [has_zero β]

lemma is_open.upper_semicontinuous_indicator (hs : is_open s) (hy : y ≤ 0) :
  upper_semicontinuous (indicator s (λ x, y)) :=
@is_open.lower_semicontinuous_indicator α _ (order_dual β) _ s y _ hs hy

lemma is_open.upper_semicontinuous_on_indicator (hs : is_open s) (hy : y ≤ 0) :
  upper_semicontinuous_on (indicator s (λ x, y)) t :=
(hs.upper_semicontinuous_indicator hy).upper_semicontinuous_on t

lemma is_open.upper_semicontinuous_at_indicator (hs : is_open s) (hy : y ≤ 0) :
  upper_semicontinuous_at (indicator s (λ x, y)) x :=
(hs.upper_semicontinuous_indicator hy).upper_semicontinuous_at x

lemma is_open.upper_semicontinuous_within_at_indicator (hs : is_open s) (hy : y ≤ 0) :
  upper_semicontinuous_within_at (indicator s (λ x, y)) t x :=
(hs.upper_semicontinuous_indicator hy).upper_semicontinuous_within_at t x

lemma is_closed.upper_semicontinuous_indicator (hs : is_closed s) (hy : 0 ≤ y) :
  upper_semicontinuous (indicator s (λ x, y)) :=
@is_closed.lower_semicontinuous_indicator α _ (order_dual β) _ s y _ hs hy

lemma is_closed.upper_semicontinuous_on_indicator (hs : is_closed s) (hy : 0 ≤ y) :
  upper_semicontinuous_on (indicator s (λ x, y)) t :=
(hs.upper_semicontinuous_indicator hy).upper_semicontinuous_on t

lemma is_closed.upper_semicontinuous_at_indicator (hs : is_closed s) (hy : 0 ≤ y) :
  upper_semicontinuous_at (indicator s (λ x, y)) x :=
(hs.upper_semicontinuous_indicator hy).upper_semicontinuous_at x

lemma is_closed.upper_semicontinuous_within_at_indicator (hs : is_closed s) (hy : 0 ≤ y) :
  upper_semicontinuous_within_at (indicator s (λ x, y)) t x :=
(hs.upper_semicontinuous_indicator hy).upper_semicontinuous_within_at t x

end

/-! #### Relationship with continuity -/

theorem upper_semicontinuous_iff_is_open :
  upper_semicontinuous f ↔ ∀ y, is_open (f ⁻¹' (Iio y)) :=
⟨λ H y, is_open_iff_mem_nhds.2 (λ x hx, H x y hx), λ H x y y_lt, is_open.mem_nhds (H y) y_lt⟩

lemma upper_semicontinuous.is_open_preimage (hf : upper_semicontinuous f) (y : β) :
  is_open (f ⁻¹' (Iio y)) :=
upper_semicontinuous_iff_is_open.1 hf y

section
variables {γ : Type*} [linear_order γ] [topological_space γ] [order_topology γ]

lemma continuous_within_at.upper_semicontinuous_within_at {f : α → γ}
  (h : continuous_within_at f s x) : upper_semicontinuous_within_at f s x :=
λ y hy, h (Iio_mem_nhds hy)

lemma continuous_at.upper_semicontinuous_at {f : α → γ}
  (h : continuous_at f x) : upper_semicontinuous_at f x :=
λ y hy, h (Iio_mem_nhds hy)

lemma continuous_on.upper_semicontinuous_on {f : α → γ}
  (h : continuous_on f s) : upper_semicontinuous_on f s :=
λ x hx, (h x hx).upper_semicontinuous_within_at

lemma continuous.upper_semicontinuous {f : α → γ}
  (h : continuous f) : upper_semicontinuous f :=
λ x, h.continuous_at.upper_semicontinuous_at

end

/-! ### Composition -/

section
variables {γ : Type*} [linear_order γ] [topological_space γ] [order_topology γ]
variables {δ : Type*} [linear_order δ] [topological_space δ] [order_topology δ]

lemma continuous_at.comp_upper_semicontinuous_within_at
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : upper_semicontinuous_within_at f s x)
  (gmon : monotone g) : upper_semicontinuous_within_at (g ∘ f) s x :=
@continuous_at.comp_lower_semicontinuous_within_at α _ x s (order_dual γ) _ _ _
  (order_dual δ) _ _ _ g f hg hf (λ x y hxy, gmon hxy)

lemma continuous_at.comp_upper_semicontinuous_at
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : upper_semicontinuous_at f x)
  (gmon : monotone g) : upper_semicontinuous_at (g ∘ f) x :=
@continuous_at.comp_lower_semicontinuous_at α _ x (order_dual γ) _ _ _
  (order_dual δ) _ _ _ g f hg hf (λ x y hxy, gmon hxy)

lemma continuous.comp_upper_semicontinuous_on
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : upper_semicontinuous_on f s)
  (gmon : monotone g) : upper_semicontinuous_on (g ∘ f) s :=
λ x hx, (hg.continuous_at).comp_upper_semicontinuous_within_at (hf x hx) gmon

lemma continuous.comp_upper_semicontinuous
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : upper_semicontinuous f)
  (gmon : monotone g) : upper_semicontinuous (g ∘ f) :=
λ x, (hg.continuous_at).comp_upper_semicontinuous_at (hf x) gmon

lemma continuous_at.comp_upper_semicontinuous_within_at_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : upper_semicontinuous_within_at f s x)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : lower_semicontinuous_within_at (g ∘ f) s x :=
@continuous_at.comp_upper_semicontinuous_within_at α _ x s γ _ _ _ (order_dual δ) _ _ _
  g f hg hf gmon

lemma continuous_at.comp_upper_semicontinuous_at_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous_at g (f x)) (hf : upper_semicontinuous_at f x)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : lower_semicontinuous_at (g ∘ f) x :=
@continuous_at.comp_upper_semicontinuous_at α _ x γ _ _ _ (order_dual δ) _ _ _ g f hg hf gmon

lemma continuous.comp_upper_semicontinuous_on_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : upper_semicontinuous_on f s)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : lower_semicontinuous_on (g ∘ f) s :=
λ x hx, (hg.continuous_at).comp_upper_semicontinuous_within_at_antimono (hf x hx) gmon

lemma continuous.comp_upper_semicontinuous_antimono
  {g : γ → δ} {f : α → γ} (hg : continuous g) (hf : upper_semicontinuous f)
  (gmon : ∀ x y, x ≤ y → g y ≤ g x) : lower_semicontinuous (g ∘ f) :=
λ x, (hg.continuous_at).comp_upper_semicontinuous_at_antimono (hf x) gmon

end

/-! #### Addition -/

section
variables {ι : Type*} {γ : Type*} [linear_ordered_add_comm_monoid γ]
[topological_space γ] [order_topology γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma upper_semicontinuous_within_at.add' {f g : α → γ}
  (hf : upper_semicontinuous_within_at f s x) (hg : upper_semicontinuous_within_at g s x)
  (hcont : continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  upper_semicontinuous_within_at (λ z, f z + g z) s x :=
@lower_semicontinuous_within_at.add' α _ x s (order_dual γ) _ _ _ _ _ hf hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma upper_semicontinuous_at.add' {f g : α → γ}
  (hf : upper_semicontinuous_at f x) (hg : upper_semicontinuous_at g x)
  (hcont : continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  upper_semicontinuous_at (λ z, f z + g z) x :=
by { simp_rw [← upper_semicontinuous_within_at_univ_iff] at *, exact hf.add' hg hcont }

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma upper_semicontinuous_on.add' {f g : α → γ}
  (hf : upper_semicontinuous_on f s) (hg : upper_semicontinuous_on g s)
  (hcont : ∀ x ∈ s, continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  upper_semicontinuous_on (λ z, f z + g z) s :=
λ x hx, (hf x hx).add' (hg x hx) (hcont x hx)

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
lemma upper_semicontinuous.add' {f g : α → γ}
  (hf : upper_semicontinuous f) (hg : upper_semicontinuous g)
  (hcont : ∀ x, continuous_at (λ (p : γ × γ), p.1 + p.2) (f x, g x)) :
  upper_semicontinuous (λ z, f z + g z) :=
λ x, (hf x).add' (hg x) (hcont x)

variable [has_continuous_add γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma upper_semicontinuous_within_at.add {f g : α → γ}
  (hf : upper_semicontinuous_within_at f s x) (hg : upper_semicontinuous_within_at g s x) :
  upper_semicontinuous_within_at (λ z, f z + g z) s x :=
hf.add' hg continuous_add.continuous_at

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma upper_semicontinuous_at.add {f g : α → γ}
  (hf : upper_semicontinuous_at f x) (hg : upper_semicontinuous_at g x) :
  upper_semicontinuous_at (λ z, f z + g z) x :=
hf.add' hg continuous_add.continuous_at

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma upper_semicontinuous_on.add {f g : α → γ}
  (hf : upper_semicontinuous_on f s) (hg : upper_semicontinuous_on g s) :
  upper_semicontinuous_on (λ z, f z + g z) s :=
hf.add' hg (λ x hx, continuous_add.continuous_at)

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
lemma upper_semicontinuous.add {f g : α → γ}
  (hf : upper_semicontinuous f) (hg : upper_semicontinuous g) :
  upper_semicontinuous (λ z, f z + g z) :=
hf.add' hg (λ x, continuous_add.continuous_at)

lemma upper_semicontinuous_within_at_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, upper_semicontinuous_within_at (f i) s x) :
  upper_semicontinuous_within_at (λ z, (∑ i in a, f i z)) s x :=
@lower_semicontinuous_within_at_sum α _ x s ι (order_dual γ) _ _ _ _ f a ha

lemma upper_semicontinuous_at_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, upper_semicontinuous_at (f i) x) :
  upper_semicontinuous_at (λ z, (∑ i in a, f i z)) x :=
begin
  simp_rw [← upper_semicontinuous_within_at_univ_iff] at *,
  exact upper_semicontinuous_within_at_sum ha
end

lemma upper_semicontinuous_on_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, upper_semicontinuous_on (f i) s) :
  upper_semicontinuous_on (λ z, (∑ i in a, f i z)) s :=
λ x hx, upper_semicontinuous_within_at_sum (λ i hi, ha i hi x hx)

lemma upper_semicontinuous_sum {f : ι → α → γ} {a : finset ι}
  (ha : ∀ i ∈ a, upper_semicontinuous (f i)) :
  upper_semicontinuous (λ z, (∑ i in a, f i z)) :=
λ x, upper_semicontinuous_at_sum (λ i hi, ha i hi x)

end

/-! #### Infimum -/

section
variables {ι : Sort*} {δ : Type*} [complete_linear_order δ]

lemma upper_semicontinuous_within_at_infi {f : ι → α → δ}
  (h : ∀ i, upper_semicontinuous_within_at (f i) s x) :
  upper_semicontinuous_within_at (λ x', ⨅ i, f i x') s x :=
@lower_semicontinuous_within_at_supr α _ x s ι (order_dual δ) _ f h

lemma upper_semicontinuous_within_at_binfi {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, upper_semicontinuous_within_at (f i hi) s x) :
  upper_semicontinuous_within_at (λ x', ⨅ i hi, f i hi x') s x :=
upper_semicontinuous_within_at_infi $ λ i, upper_semicontinuous_within_at_infi $ λ hi, h i hi

lemma upper_semicontinuous_at_infi {f : ι → α → δ}
  (h : ∀ i, upper_semicontinuous_at (f i) x) :
  upper_semicontinuous_at (λ x', ⨅ i, f i x') x :=
@lower_semicontinuous_at_supr α _ x ι (order_dual δ) _ f h

lemma upper_semicontinuous_at_binfi {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, upper_semicontinuous_at (f i hi) x) :
  upper_semicontinuous_at (λ x', ⨅ i hi, f i hi x') x :=
upper_semicontinuous_at_infi $ λ i, upper_semicontinuous_at_infi $ λ hi, h i hi

lemma upper_semicontinuous_on_infi {f : ι → α → δ}
  (h : ∀ i, upper_semicontinuous_on (f i) s) :
  upper_semicontinuous_on (λ x', ⨅ i, f i x') s :=
λ x hx, upper_semicontinuous_within_at_infi (λ i, h i x hx)

lemma upper_semicontinuous_on_binfi {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, upper_semicontinuous_on (f i hi) s) :
  upper_semicontinuous_on (λ x', ⨅ i hi, f i hi x') s :=
upper_semicontinuous_on_infi $ λ i, upper_semicontinuous_on_infi $ λ hi, h i hi

lemma upper_semicontinuous_infi {f : ι → α → δ}
  (h : ∀ i, upper_semicontinuous (f i)) :
  upper_semicontinuous (λ x', ⨅ i, f i x') :=
λ x, upper_semicontinuous_at_infi (λ i, h i x)

lemma upper_semicontinuous_binfi {p : ι → Prop} {f : Π i (h : p i), α → δ}
  (h : ∀ i hi, upper_semicontinuous (f i hi)) :
  upper_semicontinuous (λ x', ⨅ i hi, f i hi x') :=
upper_semicontinuous_infi $ λ i, upper_semicontinuous_infi $ λ hi, h i hi

end

section
variables {γ : Type*} [linear_order γ] [topological_space γ] [order_topology γ]

lemma continuous_within_at_iff_lower_upper_semicontinuous_within_at {f : α → γ} :
  continuous_within_at f s x ↔
    lower_semicontinuous_within_at f s x ∧ upper_semicontinuous_within_at f s x:=
begin
  refine ⟨λ h, ⟨h.lower_semicontinuous_within_at, h.upper_semicontinuous_within_at⟩, _⟩,
  rintros ⟨h₁, h₂⟩,
  assume v hv,
  simp only [filter.mem_map],
  by_cases Hl : ∃ l, l < f x,
  { rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩,
    by_cases Hu : ∃ u, f x < u,
    { rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩,
      filter_upwards [h₁ l lfx, h₂ u fxu],
      assume a lfa fau,
      cases le_or_gt (f a) (f x) with h h,
      { exact hl ⟨lfa, h⟩ },
      { exact hu ⟨le_of_lt h, fau⟩ } },
    { simp only [not_exists, not_lt] at Hu,
      filter_upwards [h₁ l lfx],
      assume a lfa,
      exact hl ⟨lfa, Hu (f a)⟩ } },
  { simp only [not_exists, not_lt] at Hl,
    by_cases Hu : ∃ u, f x < u,
    { rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩,
      filter_upwards [h₂ u fxu],
      assume a lfa,
      apply hu,
      exact ⟨Hl (f a), lfa⟩ },
    { simp only [not_exists, not_lt] at Hu,
      apply filter.eventually_of_forall,
      assume a,
      have : f a = f x := le_antisymm (Hu _) (Hl _),
      rw this,
      exact mem_of_mem_nhds hv } }
end

lemma continuous_at_iff_lower_upper_semicontinuous_at {f : α → γ} :
  continuous_at f x ↔ (lower_semicontinuous_at f x ∧ upper_semicontinuous_at f x) :=
by simp_rw [← continuous_within_at_univ, ← lower_semicontinuous_within_at_univ_iff,
  ← upper_semicontinuous_within_at_univ_iff,
  continuous_within_at_iff_lower_upper_semicontinuous_within_at]

lemma continuous_on_iff_lower_upper_semicontinuous_on {f : α → γ} :
  continuous_on f s ↔ (lower_semicontinuous_on f s ∧ upper_semicontinuous_on f s) :=
begin
  simp only [continuous_on, continuous_within_at_iff_lower_upper_semicontinuous_within_at],
  exact ⟨λ H, ⟨λ x hx, (H x hx).1, λ x hx, (H x hx).2⟩, λ H x hx, ⟨H.1 x hx, H.2 x hx⟩⟩
end

lemma continuous_iff_lower_upper_semicontinuous {f : α → γ} :
  continuous f ↔ (lower_semicontinuous f ∧ upper_semicontinuous f) :=
by simp_rw [continuous_iff_continuous_on_univ, continuous_on_iff_lower_upper_semicontinuous_on,
    lower_semicontinuous_on_univ_iff, upper_semicontinuous_on_univ_iff]

end
