/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.uniform_space.uniform_convergence_topology

/-!
# Equicontinuity of a family of functions

Let `X` be a topological space and `α` a `uniform_space`. A family of functions `F : ι → X → α`
is said to be *equicontinuous at a point `x₀ : X`* when, for any entourage `U` in `α`, there is a
neighborhood `V` of `x₀` such that, for all `x ∈ V`, and *for all `i`*, `F i x` is `U`-close to
`F i x₀`. In other words, one has `∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x, ∀ i, dist x₀ x < δ → dist (F i x₀) (F i x) < ε`.

`F` is said to be *equicontinuous* if it is equicontinuous at each point.

A closely related concept is that of ***uniform*** *equicontinuity* of a family of functions
`F : ι → β → α` between uniform spaces, which means that, for any entourage `U` in `α`, there is an
entourage `V` in `β` such that, if `x` and `y` are `V`-close, then *for all `i`*, `F i x` and
`F i y` are `U`-close. In other words, one has
`∀ U ∈ 𝓤 α, ∀ᶠ xy in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x y, ∀ i, dist x y < δ → dist (F i x₀) (F i x) < ε`.

## Main definitions

* `equicontinuous_at`: equicontinuity of a family of functions at a point
* `equicontinuous`: equicontinuity of a family of functions on the whole domain
* `uniform_equicontinuous`: uniform equicontinuity of a family of functions on the whole domain

## Main statements

* `equicontinuous_iff_continuous`: equicontinuity can be expressed as a simple continuity
  condition between well-chosen function spaces. This is really useful for building up the theory.
* `equicontinuous.closure`: if a set of functions is equicontinuous, its closure
  *for the topology of uniform convergence* is also equicontinuous.

## Notations

Throughout this file, we use :
- `ι`, `κ` for indexing types
- `X`, `Y`, `Z` for topological spaces
- `α`, `β`, `γ` for uniform spaces

## Implementation details

We choose to express equicontinuity as a properties of indexed families of functions rather
than sets of functions for the following reasons:
- it is really easy to express equicontinuity of `H : set (X → α)` using our setup: it is just
  equicontinuity of the family `coe : ↥H → (X → α)`. On the other hand, going the other way around
  would require working with the range of the family, which is always annoying because it
  introduces useless existentials.
- in most applications, one doesn't work with bare functions but with a more specific hom type
  `hom`. Equicontinuity of a set `H : set hom` would then have to be expressed as equicontinuity
  of `coe_fn '' H`, which is super annoying to work with. This is much simpler with families,
  because equicontinuity of a family `𝓕 : ι → hom` would simply be expressed as equicontinuity
  of `coe_fn ∘ 𝓕`, which doesn't introduce any nasty existentials.

To simplify statements, we do provide abbreviations `set.equicontinuous_at`, `set.equicontinuous`
and `set.uniform_equicontinuous` asserting the corresponding fact about the family
`coe : ↥H → (X → α)` where `H : set (X → α)`. Note however that these won't work for sets of hom
types, and in that case one should go back to the family definition rather than using `set.image`.

Since we have no use case for it yet, we don't introduce any relative version
(i.e no `equicontinuous_within_at` or `equicontinuous_on`), but this is more of a conservative
position than a design decision, so anyone needing relative versions should feel free to add them,
and that should hopefully be a straightforward task.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/

section

open uniform_space filter set
open_locale uniformity topological_space

variables {ι κ X Y Z α β γ 𝓕 : Type*} [topological_space X] [topological_space Y]
  [topological_space Z] [uniform_space α] [uniform_space β] [uniform_space γ]

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous at `x₀ : X`* if, for all entourage `U ∈ 𝓤 α`, there is a neighborhood `V` of `x₀`
such that, for all `x ∈ V` and for all `i : ι`, `F i x` is `U`-close to `F i x₉`. -/
def equicontinuous_at (F : ι → X → α) (x₀ : X) : Prop :=
∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U

/-- We say that a set of `H : set (X → α)` functions is equicontinuous at a point if the family
`coe : ↥H → (X → α)` is equicontinuous at that point. -/
protected abbreviation set.equicontinuous_at (H : set $ X → α) (x₀ : X) : Prop :=
equicontinuous_at (coe : H → X → α) x₀

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous* on all of `X` if it is equicontinuous at each point of `X`. -/
def equicontinuous (F : ι → X → α) : Prop :=
∀ x₀, equicontinuous_at F x₀

/-- We say that a set of `H : set (X → α)` functions is equicontinuous if the family
`coe : ↥H → (X → α)` is equicontinuous. -/
protected abbreviation set.equicontinuous (H : set $ X → α) : Prop :=
equicontinuous (coe : H → X → α)

/-- A family `F : ι → β → α` of functions between uniform spaces is *uniformly equicontinuous* if,
for all entourage `U ∈ 𝓤 α`, there is an entourage `V ∈ 𝓤 β` such that, whenever `x` and `y` are
`V`-close, we have that, *for all `i : ι`*, `F i x` is `U`-close to `F i x₉`. -/
def uniform_equicontinuous (F : ι → β → α) : Prop :=
∀ U ∈ 𝓤 α, ∀ᶠ (xy : β × β) in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U

/-- We say that a set of `H : set (X → α)` functions is uniformly equicontinuous if the family
`coe : ↥H → (X → α)` is uniformly equicontinuous. -/
protected abbreviation set.uniform_equicontinuous (H : set $ β → α) : Prop :=
uniform_equicontinuous (coe : H → β → α)

lemma equicontinuous_at_empty [h : is_empty ι] (F : ι → X → α) (x₀ : X) :
  equicontinuous_at F x₀ :=
λ U hU, eventually_of_forall (λ x i, h.elim i)

lemma equicontinuous_empty [h : is_empty ι] (F : ι → X → α) :
  equicontinuous F :=
equicontinuous_at_empty F

lemma uniform_equicontinuous_empty [h : is_empty ι] (F : ι → β → α) :
  uniform_equicontinuous F :=
λ U hU, eventually_of_forall (λ xy i, h.elim i)

/-- Reformulation of equicontinuity at `x₀` comparing two variables near `x₀` instead of comparing
only one with `x₀`. -/
lemma equicontinuous_at_iff_pair {F : ι → X → α} {x₀ : X} : equicontinuous_at F x₀ ↔
  ∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝 x₀, ∀ (x y ∈ V) i, (F i x, F i y) ∈ U :=
begin
  split; intros H U hU,
  { rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩,
    refine ⟨_, H V hV, λ x hx y hy i, hVU (prod_mk_mem_comp_rel _ (hy i))⟩,
    exact hVsymm.mk_mem_comm.mp (hx i) },
  { rcases H U hU with ⟨V, hV, hVU⟩,
    filter_upwards [hV] using λ x hx i, (hVU x₀ (mem_of_mem_nhds hV) x hx i) }
end

/-- Uniform equicontinuity implies equicontinuity. -/
lemma uniform_equicontinuous.equicontinuous {F : ι → β → α} (h : uniform_equicontinuous F) :
  equicontinuous F :=
λ x₀ U hU, mem_of_superset (ball_mem_nhds x₀ (h U hU)) (λ x hx i, hx i)

/-- Each function of a family equicontinuous at `x₀` is continuous at `x₀`. -/
lemma equicontinuous_at.continuous_at {F : ι → X → α} {x₀ : X} (h : equicontinuous_at F x₀)
  (i : ι) : continuous_at (F i) x₀ :=
begin
  intros U hU,
  rw uniform_space.mem_nhds_iff at hU,
  rcases hU with ⟨V, hV₁, hV₂⟩,
  exact mem_map.mpr (mem_of_superset (h V hV₁) (λ x hx, hV₂ (hx i)))
end

protected lemma set.equicontinuous_at.continuous_at_of_mem {H : set $ X → α} {x₀ : X}
  (h : H.equicontinuous_at x₀) {f : X → α} (hf : f ∈ H) : continuous_at f x₀ :=
h.continuous_at ⟨f, hf⟩

/-- Each function of an equicontinuous family is continuous. -/
lemma equicontinuous.continuous {F : ι → X → α} (h : equicontinuous F) (i : ι) :
  continuous (F i) :=
continuous_iff_continuous_at.mpr (λ x, (h x).continuous_at i)

protected lemma set.equicontinuous.continuous_of_mem {H : set $ X → α} (h : H.equicontinuous)
  {f : X → α} (hf : f ∈ H) : continuous f :=
h.continuous ⟨f, hf⟩

/-- Each function of a uniformly equicontinuous family is uniformly continuous. -/
lemma uniform_equicontinuous.uniform_continuous {F : ι → β → α} (h : uniform_equicontinuous F)
  (i : ι) : uniform_continuous (F i) :=
λ U hU, mem_map.mpr (mem_of_superset (h U hU) $ λ xy hxy, (hxy i))

protected lemma set.uniform_equicontinuous.uniform_continuous_of_mem {H : set $ β → α}
  (h : H.uniform_equicontinuous) {f : β → α} (hf : f ∈ H) : uniform_continuous f :=
h.uniform_continuous ⟨f, hf⟩

/-- Taking sub-families preserves equicontinuity at a point. -/
lemma equicontinuous_at.comp {F : ι → X → α} {x₀ : X} (h : equicontinuous_at F x₀) (u : κ → ι) :
  equicontinuous_at (F ∘ u) x₀ :=
λ U hU, (h U hU).mono (λ x H k, H (u k))

protected lemma set.equicontinuous_at.mono {H H' : set $ X → α} {x₀ : X}
  (h : H.equicontinuous_at x₀) (hH : H' ⊆ H) : H'.equicontinuous_at x₀ :=
h.comp (inclusion hH)

/-- Taking sub-families preserves equicontinuity. -/
lemma equicontinuous.comp {F : ι → X → α} (h : equicontinuous F) (u : κ → ι) :
  equicontinuous (F ∘ u) :=
λ x, (h x).comp u

protected lemma set.equicontinuous.mono {H H' : set $ X → α}
  (h : H.equicontinuous) (hH : H' ⊆ H) : H'.equicontinuous :=
h.comp (inclusion hH)

/-- Taking sub-families preserves uniform equicontinuity. -/
lemma uniform_equicontinuous.comp {F : ι → β → α} (h : uniform_equicontinuous F) (u : κ → ι) :
  uniform_equicontinuous (F ∘ u) :=
λ U hU, (h U hU).mono (λ x H k, H (u k))

protected lemma set.uniform_equicontinuous.mono {H H' : set $ β → α}
  (h : H.uniform_equicontinuous) (hH : H' ⊆ H) : H'.uniform_equicontinuous :=
h.comp (inclusion hH)

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff `range 𝓕` is equicontinuous at `x₀`,
i.e the family `coe : range F → X → α` is equicontinuous at `x₀`. -/
lemma equicontinuous_at_iff_range {F : ι → X → α} {x₀ : X} :
  equicontinuous_at F x₀ ↔ equicontinuous_at (coe : range F → X → α) x₀ :=
⟨λ h, by rw ← comp_range_splitting F; exact h.comp _, λ h, h.comp (range_factorization F)⟩

/-- A family `𝓕 : ι → X → α` is equicontinuous iff `range 𝓕` is equicontinuous,
i.e the family `coe : range F → X → α` is equicontinuous. -/
lemma equicontinuous_iff_range {F : ι → X → α} :
  equicontinuous F ↔ equicontinuous (coe : range F → X → α) :=
forall_congr (λ x₀, equicontinuous_at_iff_range)

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff `range 𝓕` is uniformly equicontinuous,
i.e the family `coe : range F → β → α` is uniformly equicontinuous. -/
lemma uniform_equicontinuous_at_iff_range {F : ι → β → α} :
  uniform_equicontinuous F ↔ uniform_equicontinuous (coe : range F → β → α) :=
⟨λ h, by rw ← comp_range_splitting F; exact h.comp _, λ h, h.comp (range_factorization F)⟩

section

local attribute [-instance] Pi.topological_space
local attribute [-instance] Pi.uniform_space
local attribute [instance] uniform_convergence.topological_space
local attribute [instance] uniform_convergence.uniform_space

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff the function `swap 𝓕 : X → ι → α` is
continuous at `x₀` *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developping the equicontinuity API, but it should not be used directly for other
purposes. -/
lemma equicontinuous_at_iff_continuous_at {F : ι → X → α} {x₀ : X} :
  equicontinuous_at F x₀ ↔ continuous_at (function.swap F) x₀ :=
by rw [continuous_at, (uniform_convergence.has_basis_nhds ι α _).tendsto_right_iff]; refl

/-- A family `𝓕 : ι → X → α` is equicontinuous iff the function `swap 𝓕 : X → ι → α` is
continuous *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developping the equicontinuity API, but it should not be used directly for other
purposes. -/
lemma equicontinuous_iff_continuous {F : ι → X → α} :
  equicontinuous F ↔ continuous (function.swap F) :=
by simp_rw [equicontinuous, continuous_iff_continuous_at, equicontinuous_at_iff_continuous_at]

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff the function `swap 𝓕 : β → ι → α` is
uniformly continuous *when `ι → α` is equipped with the uniform structure of uniform convergence*.
This is very useful for developping the equicontinuity API, but it should not be used directly
for other purposes. -/
lemma uniform_equicontinuous_iff_uniform_continuous {F : ι → β → α} :
  uniform_equicontinuous F ↔ uniform_continuous (function.swap F) :=
by rw [uniform_continuous, (uniform_convergence.has_basis_uniformity ι α).tendsto_right_iff]; refl

lemma equicontinuous_at_infi_rng {α' : Type*} [u : κ → uniform_space α'] {F : ι → X → α'}
  {x₀ : X} :
  @equicontinuous_at _ _ _ _ (⨅ k, u k) F x₀ ↔
  ∀ k, @equicontinuous_at _ _ _ _ (u k) F x₀ :=
begin
  simp_rw [equicontinuous_at_iff_continuous_at, continuous_at],
  rw [uniform_convergence.topological_space, uniform_convergence.infi_eq,
      to_topological_space_infi, nhds_infi, tendsto_infi]
end

lemma equicontinuous_infi_rng {α' : Type*} [u : κ → uniform_space α'] {F : ι → X → α'} :
  @equicontinuous _ _ _ _ (⨅ k, u k) F ↔ ∀ k, @equicontinuous _ _ _ _ (u k) F :=
begin
  simp_rw [equicontinuous_iff_continuous],
  rw [uniform_convergence.topological_space, uniform_convergence.infi_eq,
      to_topological_space_infi, continuous_infi_rng]
end

lemma uniform_equicontinuous_infi_rng {α' : Type*} [u : κ → uniform_space α'] {F : ι → β → α'} :
  @uniform_equicontinuous _ _ _ (⨅ k, u k) _ F ↔ ∀ k, @uniform_equicontinuous _ _ _ (u k) _ F :=
begin
  simp_rw [uniform_equicontinuous_iff_uniform_continuous],
  rw [uniform_convergence.infi_eq, uniform_continuous_infi_rng],
end

lemma equicontinuous_at_infi_dom {X' : Type*} [t : κ → topological_space X'] {F : ι → X' → α}
  {x₀ : X'} {k : κ} (hk : @equicontinuous_at _ _ _ (t k) _ F x₀) :
  @equicontinuous_at _ _ _ (⨅ k, t k) _ F x₀ :=
begin
  simp_rw [equicontinuous_at_iff_continuous_at, continuous_at] at ⊢ hk,
  rw [nhds_infi],
  exact tendsto_infi' k hk
end

lemma equicontinuous_infi_dom {X' : Type*} [t : κ → topological_space X'] {F : ι → X' → α}
  {k : κ} (hk : @equicontinuous _ _ _ (t k) _ F) :
  @equicontinuous _ _ _ (⨅ k, t k) _ F :=
begin
  simp_rw [equicontinuous_iff_continuous] at ⊢ hk,
  exact continuous_infi_dom hk
end

lemma uniform_equicontinuous_infi_dom {β' : Type*} [u : κ → uniform_space β'] {F : ι → β' → α}
  {k : κ} (hk : @uniform_equicontinuous _ _ _ _ (u k) F) :
  @uniform_equicontinuous _ _ _ _ (⨅ k, u k) F :=
begin
  simp_rw [uniform_equicontinuous_iff_uniform_continuous] at ⊢ hk,
  exact uniform_continuous_infi_dom hk
end

lemma filter.has_basis.equicontinuous_at_iff_left {κ : Type*} {p : κ → Prop} {s : κ → set X}
  {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).has_basis p s) : equicontinuous_at F x₀ ↔
  ∀ U ∈ 𝓤 α, ∃ k (_ : p k), ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U :=
begin
  rw [equicontinuous_at_iff_continuous_at, continuous_at,
      hX.tendsto_iff (uniform_convergence.has_basis_nhds ι α _)],
  refl
end

lemma filter.has_basis.equicontinuous_at_iff_right {κ : Type*} {p : κ → Prop} {s : κ → set (α × α)}
  {F : ι → X → α} {x₀ : X} (hα : (𝓤 α).has_basis p s) : equicontinuous_at F x₀ ↔
  ∀ k, p k → ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ s k :=
begin
  rw [equicontinuous_at_iff_continuous_at, continuous_at,
      (uniform_convergence.has_basis_nhds_of_basis ι α _ hα).tendsto_right_iff],
  refl
end

lemma filter.has_basis.equicontinuous_at_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop} {s₁ : κ₁ → set X}
  {p₂ : κ₂ → Prop} {s₂ : κ₂ → set (α × α)} {F : ι → X → α} {x₀ : X}
  (hX : (𝓝 x₀).has_basis p₁ s₁) (hα : (𝓤 α).has_basis p₂ s₂) : equicontinuous_at F x₀ ↔
  ∀ k₂, p₂ k₂ → ∃ k₁ (_ : p₁ k₁), ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ :=
begin
  rw [equicontinuous_at_iff_continuous_at, continuous_at,
      hX.tendsto_iff (uniform_convergence.has_basis_nhds_of_basis ι α _ hα)],
  refl
end

lemma filter.has_basis.uniform_equicontinuous_iff_left {κ : Type*} {p : κ → Prop}
  {s : κ → set (β × β)} {F : ι → β → α} (hβ : (𝓤 β).has_basis p s) : uniform_equicontinuous F ↔
  ∀ U ∈ 𝓤 α, ∃ k (_ : p k), ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      hβ.tendsto_iff (uniform_convergence.has_basis_uniformity ι α)],
  simp_rw [prod.forall],
  refl
end

lemma filter.has_basis.uniform_equicontinuous_iff_right {κ : Type*} {p : κ → Prop}
  {s : κ → set (α × α)} {F : ι → β → α} (hα : (𝓤 α).has_basis p s) : uniform_equicontinuous F ↔
  ∀ k, p k → ∀ᶠ (xy : β × β) in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ s k :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      (uniform_convergence.has_basis_uniformity_of_basis ι α hα).tendsto_right_iff],
  refl
end

lemma filter.has_basis.uniform_equicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
  {s₁ : κ₁ → set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → set (α × α)} {F : ι → β → α}
  (hβ : (𝓤 β).has_basis p₁ s₁) (hα : (𝓤 α).has_basis p₂ s₂) : uniform_equicontinuous F ↔
  ∀ k₂, p₂ k₂ → ∃ k₁ (_ : p₁ k₁), ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ :=
begin
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_continuous,
      hβ.tendsto_iff (uniform_convergence.has_basis_uniformity_of_basis ι α hα)],
  simp_rw [prod.forall],
  refl
end

/-- Given `u : α → β` a uniform inducing, a family `𝓕 : ι → X → α` is equicontinuous at a point
`x₀ : X` iff the family `𝓕'`, obtained by precomposing each function of `𝓕` by `u`, is
equicontinuous at `x₀`. -/
lemma uniform_inducing.equicontinuous_at_iff {F : ι → X → α} {x₀ : X} {u : α → β}
  (hu : uniform_inducing u) :
  equicontinuous_at F x₀ ↔ equicontinuous_at (((∘) u) ∘ F) x₀ :=
begin
  have := (uniform_convergence.postcomp_uniform_inducing hu).inducing,
  rw [equicontinuous_at_iff_continuous_at, equicontinuous_at_iff_continuous_at,
      this.continuous_at_iff]
end

/-- Given `u : α → β` a uniform inducing, a family `𝓕 : ι → X → α` is equicontinuous iff the
family `𝓕'`, obtained by precomposing each function of `𝓕` by `u`, is equicontinuous. -/
lemma uniform_inducing.equicontinuous_iff {F : ι → X → α} {u : α → β}
  (hu : uniform_inducing u) :
  equicontinuous F ↔ equicontinuous (((∘) u) ∘ F) :=
begin
  congrm (∀ x, (_ : Prop)),
  rw hu.equicontinuous_at_iff
end

/-- Given `u : α → γ` a uniform inducing, a family `𝓕 : ι → β → α` is uniformly equicontinuous iff
the family `𝓕'`, obtained by precomposing each function of `𝓕` by `u`, is uniformly
equicontinuous. -/
lemma uniform_inducing.uniform_equicontinuous_iff {F : ι → β → α} {u : α → γ}
  (hu : uniform_inducing u) :
  uniform_equicontinuous F ↔ uniform_equicontinuous (((∘) u) ∘ F) :=
begin
  have := uniform_convergence.postcomp_uniform_inducing hu,
  rw [uniform_equicontinuous_iff_uniform_continuous, uniform_equicontinuous_iff_uniform_continuous,
      this.uniform_continuous_iff]
end

/-- If a set of functions is equicontinuous, its closure *for the topology of uniform convergence*
is also equicontinuous. -/
lemma equicontinuous.closure {A : set $ X → α} (hA : A.equicontinuous) :
  (closure A).equicontinuous :=
begin
  intros x U hU,
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩,
  filter_upwards [hA x V hV],
  rintros y hy ⟨f, hf⟩,
  rcases uniform_space.mem_closure_iff_ball.mp hf
    ((uniform_convergence.has_basis_uniformity X α).mem_of_mem hV) with ⟨g, hgf, hg⟩,
  exact hVU (prod_mk_mem_comp_rel (prod_mk_mem_comp_rel (hgf x) (hy ⟨g, hg⟩)) $
    hVsymm.mk_mem_comm.mp (hgf y))
end

/-- A version of `equicontinuous.closure` applicable to subsets of types which embed continuously
into `X → α` *with the topology of uniform convergence*. It turns out we don't need any
other condition on the embedding than continuity, but in practice this will mostly be applied
to `fun_like` types where the coercion is injective. -/
lemma continuous.equicontinuous_closure {A : set Y} {u : Y → X → α}
  (hA : equicontinuous (u ∘ coe : A → X → α)) (hu : continuous u) :
  equicontinuous (u ∘ coe : (closure A) → X → α) :=
begin
  rw [equicontinuous_iff_range, range_comp, subtype.range_coe] at *,
  exact set.equicontinuous.mono hA.closure (image_closure_subset_closure_image hu)
end

end

end
