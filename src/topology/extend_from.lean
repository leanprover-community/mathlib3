/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker
-/
import topology.separation

/-!
# Extending a function from a subset

The main definition of this file is `extend_from A f` where `f : X → Y`
and `A : set X`. This defines a new function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists.

This is analoguous to the way `dense_inducing.extend` "extends" a function
`f : X → Z` to a function `g : Y → Z` along a dense inducing `i : X → Y`.

The main theorem we prove about this definition is `continuous_on_extend_from`
which states that, for `extend_from A f` to be continuous on a set `B ⊆ closure A`,
it suffices that `f` converges within `A` at any point of `B`, provided that
`f` is a function to a regular space.

-/

noncomputable theory

open_locale topological_space
open filter set

variables {X Y : Type*} [topological_space X] [topological_space Y]

/-- Extend a function from a set `A`. The resulting function `g` is such that
at any `x₀`, if `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `g x₀` is defined to be one of these `y`. Else, `g x₀` could be anything. -/
def extend_from (A : set X) (f : X → Y) : X → Y :=
λ x, @@lim _ ⟨f x⟩ (𝓝[A] x) f

/-- If `f` converges to some `y` as `x` tends to `x₀` within `A`,
then `f` tends to `extend_from A f x` as `x` tends to `x₀`. -/
lemma tendsto_extend_from {A : set X} {f : X → Y} {x : X}
  (h : ∃ y, tendsto f (𝓝[A] x) (𝓝 y)) : tendsto f (𝓝[A] x) (𝓝 $ extend_from A f x) :=
tendsto_nhds_lim h

lemma extend_from_eq [t2_space Y] {A : set X} {f : X → Y} {x : X} {y : Y} (hx : x ∈ closure A)
  (hf : tendsto f (𝓝[A] x) (𝓝 y)) : extend_from A f x = y :=
begin
  haveI := mem_closure_iff_nhds_within_ne_bot.mp hx,
  exact tendsto_nhds_unique (tendsto_nhds_lim ⟨y, hf⟩) hf,
end

lemma extend_from_extends [t2_space Y] {f : X → Y} {A : set X} (hf : continuous_on f A) :
  ∀ x ∈ A, extend_from A f x = f x :=
λ x x_in, extend_from_eq (subset_closure x_in) (hf x x_in)

/-- If `f` is a function to a regular space `Y` which has a limit within `A` at any
point of a set `B ⊆ closure A`, then `extend_from A f` is continuous on `B`. -/
lemma continuous_on_extend_from [regular_space Y] {f : X → Y} {A B : set X} (hB : B ⊆ closure A)
  (hf : ∀ x ∈ B, ∃ y, tendsto f (𝓝[A] x) (𝓝 y)) : continuous_on (extend_from A f) B :=
begin
  set φ := extend_from A f,
  intros x x_in,
  suffices : ∀ V' ∈ 𝓝 (φ x), is_closed V' → φ ⁻¹' V' ∈ 𝓝[B] x,
    by simpa [continuous_within_at, (closed_nhds_basis _).tendsto_right_iff],
  intros V' V'_in V'_closed,
  obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, is_open V ∧ V ∩ A ⊆ f ⁻¹' V',
  { have := tendsto_extend_from (hf x x_in),
    rcases (nhds_within_basis_open x A).tendsto_left_iff.mp this V' V'_in with ⟨V, ⟨hxV, V_op⟩, hV⟩,
    use [V, is_open.mem_nhds V_op hxV, V_op, hV] },
  suffices : ∀ y ∈ V ∩ B, φ y ∈ V',
    from mem_of_superset (inter_mem_inf V_in $ mem_principal_self B) this,
  rintros y ⟨hyV, hyB⟩,
  haveI := mem_closure_iff_nhds_within_ne_bot.mp (hB hyB),
  have limy : tendsto f (𝓝[A] y) (𝓝 $ φ y) := tendsto_extend_from (hf y hyB),
  have hVy : V ∈ 𝓝 y := is_open.mem_nhds V_op hyV,
  have : V ∩ A ∈ (𝓝[A] y),
    by simpa [inter_comm] using inter_mem_nhds_within _ hVy,
  exact V'_closed.mem_of_tendsto limy (mem_of_superset this hV)
end

/-- If a function `f` to a regular space `Y` has a limit within a
dense set `A` for any `x`, then `extend_from A f` is continuous. -/
lemma continuous_extend_from [regular_space Y] {f : X → Y} {A : set X} (hA : dense A)
  (hf : ∀ x, ∃ y, tendsto f (𝓝[A] x) (𝓝 y)) : continuous (extend_from A f) :=
begin
  rw continuous_iff_continuous_on_univ,
  exact continuous_on_extend_from (λ x _, hA x) (by simpa using hf)
end
