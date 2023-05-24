/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import order.filter.small_sets
import topology.subset_properties
import topology.nhds_set

/-!
# Uniform spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `uniform_embedding.lean`)
* totally bounded sets (in `cauchy.lean`)
* totally bounded complete sets are compact (in `cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (prod.mk x) (𝓤 X)`

where `prod.mk x : X → X × X := (λ y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `set (X × X)`, the composition `V ○ W : set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `set (X × X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (α β : Type*) := α → β → Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (α × α)`
instead of `rel α α` because we really need sets to use the filter library, and elements
of filters on `α × α` have type `set (α × α)`.

The structure `uniform_space X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

open set filter classical
open_locale classical topology filter

set_option eqn_compiler.zeta true

universes u

/-!
### Relations, seen as `set (α × α)`
-/
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Sort*}

/-- The identity relation, or the graph of the identity function -/
def id_rel {α : Type*} := {p : α × α | p.1 = p.2}

@[simp] theorem mem_id_rel {a b : α} : (a, b) ∈ @id_rel α ↔ a = b := iff.rfl

@[simp] theorem id_rel_subset {s : set (α × α)} : id_rel ⊆ s ↔ ∀ a, (a, a) ∈ s :=
by simp [subset_def]; exact forall_congr (λ a, by simp)

/-- The composition of relations -/
def comp_rel {α : Type u} (r₁ r₂ : set (α×α)) := {p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

localized "infix (name := uniformity.comp_rel) ` ○ `:55 := comp_rel" in uniformity

@[simp] theorem mem_comp_rel {r₁ r₂ : set (α×α)}
  {x y : α} : (x, y) ∈ r₁ ○ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ := iff.rfl

@[simp] theorem swap_id_rel : prod.swap '' id_rel = @id_rel α :=
set.ext $ assume ⟨a, b⟩, by simp [image_swap_eq_preimage_swap]; exact eq_comm

theorem monotone.comp_rel [preorder β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x) ○ (g x)) :=
assume a b h p ⟨z, h₁, h₂⟩, ⟨z, hf h h₁, hg h h₂⟩

@[mono]
lemma comp_rel_mono {f g h k: set (α×α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
λ ⟨x, y⟩ ⟨z, h, h'⟩, ⟨z, h₁ h, h₂ h'⟩

lemma prod_mk_mem_comp_rel {a b c : α} {s t : set (α×α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
  (a, b) ∈ s ○ t :=
⟨c, h₁, h₂⟩

@[simp] lemma id_comp_rel {r : set (α×α)} : id_rel ○ r = r :=
set.ext $ assume ⟨a, b⟩, by simp

lemma comp_rel_assoc {r s t : set (α×α)} :
  (r ○ s) ○ t = r ○ (s ○ t) :=
by ext p; cases p; simp only [mem_comp_rel]; tauto

lemma left_subset_comp_rel {s t : set (α × α)} (h : id_rel ⊆ t) : s ⊆ s ○ t :=
λ ⟨x, y⟩ xy_in, ⟨y, xy_in, h $ by exact rfl⟩

lemma right_subset_comp_rel {s t : set (α × α)} (h : id_rel ⊆ s) : t ⊆ s ○ t :=
λ ⟨x, y⟩ xy_in, ⟨x, h $ by exact rfl, xy_in⟩

lemma subset_comp_self {s : set (α × α)} (h : id_rel ⊆ s) : s ⊆ s ○ s :=
left_subset_comp_rel h

lemma subset_iterate_comp_rel {s t : set (α × α)} (h : id_rel ⊆ s) (n : ℕ) :
  t ⊆ (((○) s) ^[n] t) :=
begin
  induction n with n ihn generalizing t,
  exacts [subset.rfl, (right_subset_comp_rel h).trans ihn]
end

/-- The relation is invariant under swapping factors. -/
def symmetric_rel (V : set (α × α)) : Prop := prod.swap ⁻¹' V = V

/-- The maximal symmetric relation contained in a given relation. -/
def symmetrize_rel (V : set (α × α)) : set (α × α) := V ∩ prod.swap ⁻¹' V

lemma symmetric_symmetrize_rel (V : set (α × α)) : symmetric_rel (symmetrize_rel V) :=
by simp [symmetric_rel, symmetrize_rel, preimage_inter, inter_comm, ← preimage_comp]

lemma symmetrize_rel_subset_self (V : set (α × α)) : symmetrize_rel V ⊆ V :=
sep_subset _ _

@[mono]
lemma symmetrize_mono {V W: set (α × α)} (h : V ⊆ W) : symmetrize_rel V ⊆ symmetrize_rel W :=
inter_subset_inter h $ preimage_mono h

lemma symmetric_rel.mk_mem_comm {V : set (α × α)} (hV : symmetric_rel V) {x y : α} :
  (x, y) ∈ V ↔ (y, x) ∈ V :=
set.ext_iff.1 hV (y, x)

lemma symmetric_rel.eq {U : set (α × α)} (hU : symmetric_rel U) : prod.swap ⁻¹' U = U := hU

lemma symmetric_rel.inter {U V : set (α × α)} (hU : symmetric_rel U) (hV : symmetric_rel V) :
  symmetric_rel (U ∩ V) :=
by rw [symmetric_rel, preimage_inter, hU.eq, hV.eq]

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure uniform_space.core (α : Type u) :=
(uniformity : filter (α × α))
(refl       : 𝓟 id_rel ≤ uniformity)
(symm       : tendsto prod.swap uniformity uniformity)
(comp       : uniformity.lift' (λs, s ○ s) ≤ uniformity)

/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def uniform_space.core.mk' {α : Type u} (U : filter (α × α))
  (refl : ∀ (r ∈ U) x, (x, x) ∈ r)
  (symm : ∀ r ∈ U, prod.swap ⁻¹' r ∈ U)
  (comp : ∀ r ∈ U, ∃ t ∈ U, t ○ t ⊆ r) : uniform_space.core α :=
⟨U, λ r ru, id_rel_subset.2 (refl _ ru), symm,
  λ r ru, let ⟨s, hs, hsr⟩ := comp _ ru in mem_of_superset (mem_lift' hs) hsr⟩

/-- Defining an `uniform_space.core` from a filter basis satisfying some uniformity-like axioms. -/
def uniform_space.core.mk_of_basis {α : Type u} (B : filter_basis (α × α))
  (refl : ∀ (r ∈ B) x, (x, x) ∈ r)
  (symm : ∀ r ∈ B, ∃ t ∈ B, t ⊆ prod.swap ⁻¹' r)
  (comp : ∀ r ∈ B, ∃ t ∈ B, t ○ t ⊆ r) : uniform_space.core α :=
{ uniformity := B.filter,
  refl := B.has_basis.ge_iff.mpr (λ r ru, id_rel_subset.2 $ refl _ ru),
  symm := (B.has_basis.tendsto_iff B.has_basis).mpr symm,
  comp := (has_basis.le_basis_iff (B.has_basis.lift' (monotone_id.comp_rel monotone_id))
    B.has_basis).mpr comp }

/-- A uniform space generates a topological space -/
def uniform_space.core.to_topological_space {α : Type u} (u : uniform_space.core α) :
  topological_space α :=
{ is_open        := λs, ∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ u.uniformity,
  is_open_univ   := by simp; intro; exact univ_mem,
  is_open_inter  :=
    assume s t hs ht x ⟨xs, xt⟩, by filter_upwards [hs x xs, ht x xt]; simp {contextual := tt},
  is_open_sUnion :=
    assume s hs x ⟨t, ts, xt⟩, by filter_upwards [hs t ts x xt] with p ph h using ⟨t, ts, ph h⟩ }

lemma uniform_space.core_eq :
  ∀{u₁ u₂ : uniform_space.core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
| ⟨u₁, _, _, _⟩  ⟨u₂, _, _, _⟩ rfl := by congr

-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].

/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class uniform_space (α : Type u) extends topological_space α, uniform_space.core α :=
(is_open_uniformity : ∀s, @_root_.is_open _ to_topological_space s ↔
  (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ uniformity))

/-- Alternative constructor for `uniform_space α` when a topology is already given. -/
@[pattern] def uniform_space.mk' {α} (t : topological_space α)
  (c : uniform_space.core α)
  (is_open_uniformity : ∀s:set α, is_open s ↔
    (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ c.uniformity)) :
  uniform_space α := ⟨c, is_open_uniformity⟩

/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def uniform_space.of_core {α : Type u} (u : uniform_space.core α) : uniform_space α :=
{ to_core := u,
  to_topological_space := u.to_topological_space,
  is_open_uniformity := assume a, iff.rfl }

/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def uniform_space.of_core_eq {α : Type u} (u : uniform_space.core α) (t : topological_space α)
  (h : t = u.to_topological_space) : uniform_space α :=
{ to_core := u,
  to_topological_space := t,
  is_open_uniformity := assume a, h.symm ▸ iff.rfl }

lemma uniform_space.to_core_to_topological_space (u : uniform_space α) :
  u.to_core.to_topological_space = u.to_topological_space :=
topological_space_eq $ funext $ λ s, by rw [uniform_space.is_open_uniformity, is_open_mk]

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity (α : Type u) [uniform_space α] : filter (α × α) :=
  (@uniform_space.to_core α _).uniformity

localized "notation (name := uniformity_of) `𝓤[` u `]` := @uniformity hole! u" in topology

@[ext]
lemma uniform_space_eq : ∀ {u₁ u₂ : uniform_space α}, 𝓤[u₁] = 𝓤[u₂] → u₁ = u₂
| (uniform_space.mk' t₁ u₁ o₁)  (uniform_space.mk' t₂ u₂ o₂) h :=
  have u₁ = u₂, from uniform_space.core_eq h,
  have t₁ = t₂, from topological_space_eq $ funext $ assume s, by rw [o₁, o₂]; simp [this],
  by simp [*]

lemma uniform_space.of_core_eq_to_core
  (u : uniform_space α) (t : topological_space α) (h : t = u.to_core.to_topological_space) :
  uniform_space.of_core_eq u.to_core t h = u :=
uniform_space_eq rfl

/-- Replace topology in a `uniform_space` instance with a propositionally (but possibly not
definitionally) equal one. -/
@[reducible] def uniform_space.replace_topology {α : Type*} [i : topological_space α]
  (u : uniform_space α) (h : i = u.to_topological_space) : uniform_space α :=
uniform_space.of_core_eq u.to_core i $ h.trans u.to_core_to_topological_space.symm

lemma uniform_space.replace_topology_eq {α : Type*} [i : topological_space α] (u : uniform_space α)
  (h : i = u.to_topological_space) : u.replace_topology h = u :=
u.of_core_eq_to_core _ _

/-- Define a `uniform_space` using a "distance" function. The function can be, e.g., the distance in
a (usual or extended) metric space or an absolute value on a ring. -/
def uniform_space.of_fun {α β : Type*} [ordered_add_comm_monoid β]
  (d : α → α → β) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
  (triangle : ∀ x y z, d x z ≤ d x y + d y z)
  (half : ∀ ε > (0 : β), ∃ δ > (0 : β), ∀ x < δ, ∀ y < δ, x + y < ε) :
  uniform_space α :=
uniform_space.of_core
  { uniformity := ⨅ r > 0, 𝓟 { x | d x.1 x.2 < r },
    refl := le_infi₂ $ λ r hr, principal_mono.2 $ id_rel_subset.2 $ λ x, by simpa [refl],
    symm := tendsto_infi_infi $ λ r, tendsto_infi_infi $ λ _, tendsto_principal_principal.2 $
      λ x hx, by rwa [mem_set_of, symm],
    comp := le_infi₂ $ λ r hr, let ⟨δ, h0, hδr⟩ := half r hr in le_principal_iff.2 $ mem_of_superset
      (mem_lift' $ mem_infi_of_mem δ $ mem_infi_of_mem h0 $ mem_principal_self _) $
      λ ⟨x, z⟩ ⟨y, h₁, h₂⟩, (triangle _ _ _).trans_lt (hδr _ h₁ _ h₂) }

lemma uniform_space.has_basis_of_fun {α β : Type*} [linear_ordered_add_comm_monoid β]
  (h₀ : ∃ x : β, 0 < x) (d : α → α → β) (refl : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
  (triangle : ∀ x y z, d x z ≤ d x y + d y z)
  (half : ∀ ε > (0 : β), ∃ δ > (0 : β), ∀ x < δ, ∀ y < δ, x + y < ε) :
  𝓤[uniform_space.of_fun d refl symm triangle half].has_basis ((<) (0 : β))
    (λ ε, { x | d x.1 x.2 < ε }) :=
has_basis_binfi_principal'
  (λ ε₁ h₁ ε₂ h₂, ⟨min ε₁ ε₂, lt_min h₁ h₂, λ _x hx, lt_of_lt_of_le hx (min_le_left _ _),
    λ _x hx, lt_of_lt_of_le hx (min_le_right _ _)⟩) h₀

section uniform_space
variables [uniform_space α]

localized "notation (name := uniformity) `𝓤` := uniformity" in uniformity

lemma is_open_uniformity {s : set α} :
  is_open s ↔ (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ 𝓤 α) :=
uniform_space.is_open_uniformity s

lemma refl_le_uniformity : 𝓟 id_rel ≤ 𝓤 α :=
(@uniform_space.to_core α _).refl

instance uniformity.ne_bot [nonempty α] : ne_bot (𝓤 α) :=
diagonal_nonempty.principal_ne_bot.mono refl_le_uniformity

lemma refl_mem_uniformity {x : α} {s : set (α × α)} (h : s ∈ 𝓤 α) :
  (x, x) ∈ s :=
refl_le_uniformity h rfl

lemma mem_uniformity_of_eq {x y : α} {s : set (α × α)} (h : s ∈ 𝓤 α) (hx : x = y) :
  (x, y) ∈ s :=
refl_le_uniformity h hx

lemma symm_le_uniformity : map (@prod.swap α α) (𝓤 _) ≤ (𝓤 _) :=
(@uniform_space.to_core α _).symm

lemma comp_le_uniformity : (𝓤 α).lift' (λs:set (α×α), s ○ s) ≤ 𝓤 α :=
(@uniform_space.to_core α _).comp

lemma tendsto_swap_uniformity : tendsto (@prod.swap α α) (𝓤 α) (𝓤 α) :=
symm_le_uniformity

lemma comp_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∃ t ∈ 𝓤 α, t ○ t ⊆ s :=
have s ∈ (𝓤 α).lift' (λt:set (α×α), t ○ t),
  from comp_le_uniformity hs,
(mem_lift'_sets $ monotone_id.comp_rel monotone_id).mp this

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions). -/
lemma eventually_uniformity_iterate_comp_subset {s : set (α × α)} (hs : s ∈ 𝓤 α) (n : ℕ) :
  ∀ᶠ t in (𝓤 α).small_sets, ((○) t) ^[n] t ⊆ s :=
begin
  suffices : ∀ᶠ t in (𝓤 α).small_sets, t ⊆ s ∧ (((○) t) ^[n] t ⊆ s),
    from (eventually_and.1 this).2,
  induction n with n ihn generalizing s, { simpa },
  rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩,
  refine (ihn htU).mono (λ U hU, _),
  rw [function.iterate_succ_apply'],
  exact ⟨hU.1.trans $ (subset_comp_self $ refl_le_uniformity htU).trans hts,
    (comp_rel_mono hU.1 hU.2).trans hts⟩
end

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
lemma eventually_uniformity_comp_subset {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∀ᶠ t in (𝓤 α).small_sets, t ○ t ⊆ s :=
eventually_uniformity_iterate_comp_subset hs 1

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is transitive. -/
lemma filter.tendsto.uniformity_trans {l : filter β} {f₁ f₂ f₃ : β → α}
  (h₁₂ : tendsto (λ x, (f₁ x, f₂ x)) l (𝓤 α)) (h₂₃ : tendsto (λ x, (f₂ x, f₃ x)) l (𝓤 α)) :
  tendsto (λ x, (f₁ x, f₃ x)) l (𝓤 α) :=
begin
  refine le_trans (le_lift'.2 $ λ s hs, mem_map.2 _) comp_le_uniformity,
  filter_upwards [h₁₂ hs, h₂₃ hs] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩,
end

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is symmetric -/
lemma filter.tendsto.uniformity_symm {l : filter β} {f : β → α × α}
  (h : tendsto f l (𝓤 α)) :
  tendsto (λ x, ((f x).2, (f x).1)) l (𝓤 α) :=
tendsto_swap_uniformity.comp h

/-- Relation `λ f g, tendsto (λ x, (f x, g x)) l (𝓤 α)` is reflexive. -/
lemma tendsto_diag_uniformity (f : β → α) (l : filter β) :
  tendsto (λ x, (f x, f x)) l (𝓤 α) :=
assume s hs, mem_map.2 $ univ_mem' $ λ x, refl_mem_uniformity hs

lemma tendsto_const_uniformity {a : α} {f : filter β} : tendsto (λ _, (a, a)) f (𝓤 α) :=
tendsto_diag_uniformity (λ _, a) f

lemma symm_of_uniformity {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∃ t ∈ 𝓤 α, (∀a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
have preimage prod.swap s ∈ 𝓤 α, from symm_le_uniformity hs,
⟨s ∩ preimage prod.swap s, inter_mem hs this, λ a b ⟨h₁, h₂⟩, ⟨h₂, h₁⟩, inter_subset_left _ _⟩

lemma comp_symm_of_uniformity {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∃ t ∈ 𝓤 α, (∀{a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ t ○ t ⊆ s :=
let ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs in
let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁ in
⟨t', ht', ht'₁, subset.trans (monotone_id.comp_rel monotone_id ht'₂) ht₂⟩

lemma uniformity_le_symm : 𝓤 α ≤ (@prod.swap α α) <$> 𝓤 α :=
by rw [map_swap_eq_comap_swap];
from map_le_iff_le_comap.1 tendsto_swap_uniformity

lemma uniformity_eq_symm : 𝓤 α = (@prod.swap α α) <$> 𝓤 α :=
le_antisymm uniformity_le_symm symm_le_uniformity

@[simp] lemma comap_swap_uniformity : comap (@prod.swap α α) (𝓤 α) = 𝓤 α :=
(congr_arg _ uniformity_eq_symm).trans $ comap_map prod.swap_injective

lemma symmetrize_mem_uniformity {V : set (α × α)} (h : V ∈ 𝓤 α) : symmetrize_rel V ∈ 𝓤 α :=
begin
  apply (𝓤 α).inter_sets h,
  rw [← image_swap_eq_preimage_swap, uniformity_eq_symm],
  exact image_mem_map h,
end

/-- Symmetric entourages form a basis of `𝓤 α` -/
lemma uniform_space.has_basis_symmetric :
  (𝓤 α).has_basis (λ s : set (α × α), s ∈ 𝓤 α ∧ symmetric_rel s) id :=
has_basis_self.2 $ λ t t_in, ⟨symmetrize_rel t, symmetrize_mem_uniformity t_in,
  symmetric_symmetrize_rel t, symmetrize_rel_subset_self t⟩

theorem uniformity_lift_le_swap {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : (𝓤 α).lift (λs, g (preimage prod.swap s)) ≤ f) : (𝓤 α).lift g ≤ f :=
calc (𝓤 α).lift g ≤ (filter.map (@prod.swap α α) $ 𝓤 α).lift g :
    lift_mono uniformity_le_symm le_rfl
  ... ≤ _ :
    by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

lemma uniformity_lift_le_comp {f : set (α×α) → filter β} (h : monotone f) :
  (𝓤 α).lift (λs, f (s ○ s)) ≤ (𝓤 α).lift f :=
calc (𝓤 α).lift (λs, f (s ○ s)) =
    ((𝓤 α).lift' (λs:set (α×α), s ○ s)).lift f :
  begin
    rw [lift_lift'_assoc],
    exact monotone_id.comp_rel monotone_id,
    exact h
  end
  ... ≤ (𝓤 α).lift f : lift_mono comp_le_uniformity le_rfl

lemma comp_le_uniformity3 :
  (𝓤 α).lift' (λs:set (α×α), s ○ (s ○ s)) ≤ (𝓤 α) :=
calc (𝓤 α).lift' (λd, d ○ (d ○ d)) =
  (𝓤 α).lift (λs, (𝓤 α).lift' (λt:set(α×α), s ○ (t ○ t))) :
  begin
    rw [lift_lift'_same_eq_lift'],
    exact (assume x, monotone_const.comp_rel $ monotone_id.comp_rel monotone_id),
    exact (assume x, monotone_id.comp_rel monotone_const),
  end
  ... ≤ (𝓤 α).lift (λs, (𝓤 α).lift' (λt:set(α×α), s ○ t)) :
    lift_mono' $ assume s hs, @uniformity_lift_le_comp α _ _ (𝓟 ∘ (○) s) $
      monotone_principal.comp (monotone_const.comp_rel monotone_id)
  ... = (𝓤 α).lift' (λs:set(α×α), s ○ s) :
    lift_lift'_same_eq_lift'
      (assume s, monotone_const.comp_rel monotone_id)
      (assume s, monotone_id.comp_rel monotone_const)
  ... ≤ (𝓤 α) : comp_le_uniformity

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
lemma comp_symm_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∃ t ∈ 𝓤 α, symmetric_rel t ∧ t ○ t ⊆ s :=
begin
  obtain ⟨w, w_in, w_sub⟩ : ∃ w ∈ 𝓤 α, w ○ w ⊆ s := comp_mem_uniformity_sets hs,
  use [symmetrize_rel w, symmetrize_mem_uniformity w_in, symmetric_symmetrize_rel w],
  have : symmetrize_rel w ⊆ w := symmetrize_rel_subset_self w,
  calc symmetrize_rel w ○ symmetrize_rel w ⊆ w ○ w : by mono
                                       ... ⊆ s     : w_sub,
end

lemma subset_comp_self_of_mem_uniformity {s : set (α × α)} (h : s ∈ 𝓤 α) : s ⊆ s ○ s :=
subset_comp_self (refl_le_uniformity h)

lemma comp_comp_symm_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∃ t ∈ 𝓤 α, symmetric_rel t ∧ t ○ t ○ t ⊆ s :=
begin
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, w_symm, w_sub⟩,
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩,
  use [t, t_in, t_symm],
  have : t ⊆ t ○ t :=  subset_comp_self_of_mem_uniformity t_in,
  calc
  t ○ t ○ t ⊆ w ○ t       : by mono
        ... ⊆ w ○ (t ○ t) : by mono
        ... ⊆ w ○ w       : by mono
        ... ⊆ s           : w_sub,
end

/-!
### Balls in uniform spaces
-/

/-- The ball around `(x : β)` with respect to `(V : set (β × β))`. Intended to be
used for `V ∈ 𝓤 β`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def uniform_space.ball (x : β) (V : set (β × β)) : set β := (prod.mk x) ⁻¹' V

open uniform_space (ball)

lemma uniform_space.mem_ball_self (x : α) {V : set (α × α)} (hV : V ∈ 𝓤 α) :
  x ∈ ball x V :=
refl_mem_uniformity hV

/-- The triangle inequality for `uniform_space.ball` -/
lemma mem_ball_comp {V W : set (β × β)} {x y z} (h : y ∈ ball x V) (h' : z ∈ ball y W) :
  z ∈ ball x (V ○ W) :=
prod_mk_mem_comp_rel h h'

lemma ball_subset_of_comp_subset {V W : set (β × β)} {x y} (h : x ∈ ball y W) (h' : W ○ W ⊆ V) :
  ball x W ⊆ ball y V :=
λ z z_in, h' (mem_ball_comp h z_in)

lemma ball_mono {V W : set (β × β)} (h : V ⊆ W) (x : β) : ball x V ⊆ ball x W :=
preimage_mono h

lemma ball_inter (x : β) (V W : set (β × β)) : ball x (V ∩ W) = ball x V ∩ ball x W :=
preimage_inter

lemma ball_inter_left (x : β) (V W : set (β × β)) : ball x (V ∩ W) ⊆ ball x V :=
ball_mono (inter_subset_left V W) x

lemma ball_inter_right (x : β) (V W : set (β × β)) : ball x (V ∩ W) ⊆ ball x W :=
ball_mono (inter_subset_right V W) x

lemma mem_ball_symmetry {V : set (β × β)} (hV : symmetric_rel V) {x y} :
  x ∈ ball y V ↔ y ∈ ball x V :=
show (x, y) ∈ prod.swap ⁻¹' V ↔ (x, y) ∈ V, by { unfold symmetric_rel at hV, rw hV }

lemma ball_eq_of_symmetry {V : set (β × β)} (hV : symmetric_rel V) {x} :
  ball x V = {y | (y, x) ∈ V} :=
by { ext y, rw mem_ball_symmetry hV, exact iff.rfl }

lemma mem_comp_of_mem_ball {V W : set (β × β)} {x y z : β} (hV : symmetric_rel V)
  (hx : x ∈ ball z V) (hy : y ∈ ball z W) : (x, y) ∈ V ○ W :=
begin
  rw mem_ball_symmetry hV at hx,
  exact ⟨z, hx, hy⟩
end

lemma uniform_space.is_open_ball (x : α) {V : set (α × α)} (hV : is_open V) :
  is_open (ball x V) :=
hV.preimage $ continuous_const.prod_mk continuous_id

lemma mem_comp_comp {V W M : set (β × β)} (hW' : symmetric_rel W) {p : β × β} :
  p ∈ V ○ M ○ W ↔ ((ball p.1 V ×ˢ ball p.2 W) ∩ M).nonempty :=
begin
  cases p with x y,
  split,
  { rintros ⟨z, ⟨w, hpw, hwz⟩, hzy⟩,
    exact ⟨(w, z), ⟨hpw, by rwa mem_ball_symmetry hW'⟩, hwz⟩, },
  { rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩,
    rwa mem_ball_symmetry hW' at z_in,
    use [z, w] ; tauto },
end

/-!
### Neighborhoods in uniform spaces
-/

lemma mem_nhds_uniformity_iff_right {x : α} {s : set α} :
  s ∈ 𝓝 x ↔ {p : α × α | p.1 = x → p.2 ∈ s} ∈ 𝓤 α :=
begin
  refine ⟨_, λ hs, _⟩,
  { simp only [mem_nhds_iff, is_open_uniformity, and_imp, exists_imp_distrib],
    intros t ts ht xt,
    filter_upwards [ht x xt] using λ y h eq, ts (h eq) },
  { refine mem_nhds_iff.mpr ⟨{x | {p : α × α | p.1 = x → p.2 ∈ s} ∈ 𝓤 α}, _, _, hs⟩,
    { exact λ y hy, refl_mem_uniformity hy rfl },
    { refine is_open_uniformity.mpr (λ y hy, _),
      rcases comp_mem_uniformity_sets hy with ⟨t, ht, tr⟩,
      filter_upwards [ht], rintro ⟨a, b⟩ hp' rfl,
      filter_upwards [ht], rintro ⟨a', b'⟩ hp'' rfl,
      exact @tr (a, b') ⟨a', hp', hp''⟩ rfl } }
end

lemma mem_nhds_uniformity_iff_left {x : α} {s : set α} :
  s ∈ 𝓝 x ↔ {p : α × α | p.2 = x → p.1 ∈ s} ∈ 𝓤 α :=
by { rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right], refl }

lemma nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (prod.mk x) :=
by { ext s, rw [mem_nhds_uniformity_iff_right, mem_comap_prod_mk] }

/-- See also `is_open_iff_open_ball_subset`. -/
lemma is_open_iff_ball_subset {s : set α} : is_open s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, ball x V ⊆ s :=
begin
  simp_rw [is_open_iff_mem_nhds, nhds_eq_comap_uniformity],
  exact iff.rfl,
end

lemma nhds_basis_uniformity' {p : ι → Prop} {s : ι → set (α × α)} (h : (𝓤 α).has_basis p s)
  {x : α} :
  (𝓝 x).has_basis p (λ i, ball x (s i)) :=
by { rw [nhds_eq_comap_uniformity], exact h.comap (prod.mk x) }

lemma nhds_basis_uniformity {p : ι → Prop} {s : ι → set (α × α)} (h : (𝓤 α).has_basis p s) {x : α} :
  (𝓝 x).has_basis p (λ i, {y | (y, x) ∈ s i}) :=
begin
  replace h := h.comap prod.swap,
  rw [← map_swap_eq_comap_swap, ← uniformity_eq_symm] at h,
  exact nhds_basis_uniformity' h
end

lemma nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap (λ y, (y, x)) :=
(nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis $ (𝓤 α).basis_sets.comap _

lemma uniform_space.mem_nhds_iff {x : α} {s : set α} : s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, ball x V ⊆ s :=
begin
  rw [nhds_eq_comap_uniformity, mem_comap],
  exact iff.rfl,
end

lemma uniform_space.ball_mem_nhds (x : α) ⦃V : set (α × α)⦄ (V_in : V ∈ 𝓤 α) : ball x V ∈ 𝓝 x :=
begin
  rw uniform_space.mem_nhds_iff,
  exact ⟨V, V_in, subset.refl _⟩
end

lemma uniform_space.mem_nhds_iff_symm {x : α} {s : set α} :
  s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 α, symmetric_rel V ∧ ball x V ⊆ s :=
begin
  rw uniform_space.mem_nhds_iff,
  split,
  { rintros ⟨V, V_in, V_sub⟩,
    use [symmetrize_rel V, symmetrize_mem_uniformity V_in, symmetric_symmetrize_rel V],
    exact subset.trans (ball_mono (symmetrize_rel_subset_self V) x) V_sub },
  { rintros ⟨V, V_in, V_symm, V_sub⟩,
    exact ⟨V, V_in, V_sub⟩ }
end

lemma uniform_space.has_basis_nhds (x : α) :
  has_basis (𝓝 x) (λ s : set (α × α), s ∈ 𝓤 α ∧ symmetric_rel s) (λ s, ball x s) :=
⟨λ t, by simp [uniform_space.mem_nhds_iff_symm, and_assoc]⟩

open uniform_space

lemma uniform_space.mem_closure_iff_symm_ball {s : set α} {x} :
  x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → symmetric_rel V → (s ∩ ball x V).nonempty :=
by simp [mem_closure_iff_nhds_basis (has_basis_nhds x), set.nonempty]

lemma uniform_space.mem_closure_iff_ball {s : set α} {x} :
  x ∈ closure s ↔ ∀ {V}, V ∈ 𝓤 α → (ball x V ∩ s).nonempty :=
by simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

lemma uniform_space.has_basis_nhds_prod (x y : α) :
  has_basis (𝓝 (x, y)) (λ s, s ∈ 𝓤 α ∧ symmetric_rel s) $ λ s, ball x s ×ˢ ball y s :=
begin
  rw nhds_prod_eq,
  apply (has_basis_nhds x).prod_same_index (has_basis_nhds y),
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩,
  exact ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, U_symm.inter V_symm⟩,
         ball_inter_left x U V, ball_inter_right y U V⟩,
end

lemma nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
(nhds_basis_uniformity' (𝓤 α).basis_sets).eq_binfi

lemma nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' (λ s, {y | (y, x) ∈ s}) :=
(nhds_basis_uniformity (𝓤 α).basis_sets).eq_binfi

lemma mem_nhds_left (x : α) {s : set (α×α)} (h : s ∈ 𝓤 α) :
  {y : α | (x, y) ∈ s} ∈ 𝓝 x :=
ball_mem_nhds x h

lemma mem_nhds_right (y : α) {s : set (α×α)} (h : s ∈ 𝓤 α) :
  {x : α | (x, y) ∈ s} ∈ 𝓝 y :=
mem_nhds_left _ (symm_le_uniformity h)

lemma exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : set α} (h : U ∈ 𝓝 a) :
  ∃ (V ∈ 𝓝 a) (t ∈ 𝓤 α), ∀ a' ∈ V, uniform_space.ball a' t ⊆ U :=
let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h) in
⟨_, mem_nhds_left a ht, t, ht, λ a₁ h₁ a₂ h₂, @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩

lemma is_compact.nhds_set_basis_uniformity {p : ι → Prop} {s : ι → set (α × α)}
  (hU : (𝓤 α).has_basis p s) {K : set α} (hK : is_compact K) :
  (𝓝ˢ K).has_basis p (λ i, ⋃ x ∈ K, ball x (s i)) :=
begin
  refine ⟨λ U, _⟩,
  simp only [mem_nhds_set_iff_forall, (nhds_basis_uniformity' hU).mem_iff, Union₂_subset_iff],
  refine ⟨λ H, _, λ ⟨i, hpi, hi⟩ x hx, ⟨i, hpi, hi x hx⟩⟩,
  replace H : ∀ x ∈ K, ∃ i : {i // p i}, ball x (s i ○ s i) ⊆ U,
  { intros x hx,
    rcases H x hx with ⟨i, hpi, hi⟩,
    rcases comp_mem_uniformity_sets (hU.mem_of_mem hpi) with ⟨t, ht_mem, ht⟩,
    rcases hU.mem_iff.1 ht_mem with ⟨j, hpj, hj⟩,
    exact ⟨⟨j, hpj⟩, subset.trans (ball_mono ((comp_rel_mono hj hj).trans ht) _) hi⟩ },
  haveI : nonempty {a // p a}, from nonempty_subtype.2 hU.ex_mem,
  choose! I hI using H,
  rcases hK.elim_nhds_subcover (λ x, ball x $ s (I x))
    (λ x hx, ball_mem_nhds _ $ hU.mem_of_mem (I x).2) with ⟨t, htK, ht⟩,
  obtain ⟨i, hpi, hi⟩ : ∃ i (hpi : p i), s i ⊆ ⋂ x ∈ t, s (I x),
    from hU.mem_iff.1 ((bInter_finset_mem t).2 (λ x hx, hU.mem_of_mem (I x).2)),
  rw [subset_Inter₂_iff] at hi,
  refine ⟨i, hpi, λ x hx, _⟩,
  rcases mem_Union₂.1 (ht hx) with ⟨z, hzt : z ∈ t, hzx : x ∈ ball z (s (I z))⟩,
  calc ball x (s i) ⊆ ball z (s (I z) ○ s (I z)) : λ y hy, ⟨x, hzx, hi z hzt hy⟩
                ... ⊆ U                          : hI z (htK z hzt),
end

lemma disjoint.exists_uniform_thickening {A B : set α}
  (hA : is_compact A) (hB : is_closed B) (h : disjoint A B) :
  ∃ V ∈ 𝓤 α, disjoint (⋃ x ∈ A, ball x V) (⋃ x ∈ B, ball x V) :=
begin
  have : Bᶜ ∈ 𝓝ˢ A := hB.is_open_compl.mem_nhds_set.mpr h.le_compl_right,
  rw (hA.nhds_set_basis_uniformity (filter.basis_sets _)).mem_iff at this,
  rcases this with ⟨U, hU, hUAB⟩,
  rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩,
  refine ⟨V, hV, set.disjoint_left.mpr $ λ x, _⟩,
  simp only [mem_Union₂],
  rintro ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩,
  rw mem_ball_symmetry hVsymm at hxa hxb,
  exact hUAB (mem_Union₂_of_mem ha $ hVU $ mem_comp_of_mem_ball hVsymm hxa hxb) hb
end

lemma disjoint.exists_uniform_thickening_of_basis {p : ι → Prop} {s : ι → set (α × α)}
  (hU : (𝓤 α).has_basis p s) {A B : set α}
  (hA : is_compact A) (hB : is_closed B) (h : disjoint A B) :
  ∃ i, p i ∧ disjoint (⋃ x ∈ A, ball x (s i)) (⋃ x ∈ B, ball x (s i)) :=
begin
  rcases h.exists_uniform_thickening hA hB with ⟨V, hV, hVAB⟩,
  rcases hU.mem_iff.1 hV with ⟨i, hi, hiV⟩,
  exact ⟨i, hi, hVAB.mono
    (Union₂_mono $ λ a _, ball_mono hiV a) (Union₂_mono $ λ b _, ball_mono hiV b)⟩,
end

lemma tendsto_right_nhds_uniformity {a : α} : tendsto (λa', (a', a)) (𝓝 a) (𝓤 α) :=
assume s, mem_nhds_right a

lemma tendsto_left_nhds_uniformity {a : α} : tendsto (λa', (a, a')) (𝓝 a) (𝓤 α) :=
assume s, mem_nhds_left a

lemma lift_nhds_left {x : α} {g : set α → filter β} (hg : monotone g) :
  (𝓝 x).lift g = (𝓤 α).lift (λs:set (α×α), g (ball x s)) :=
by { rw [nhds_eq_comap_uniformity, comap_lift_eq2 hg], refl }

lemma lift_nhds_right {x : α} {g : set α → filter β} (hg : monotone g) :
  (𝓝 x).lift g = (𝓤 α).lift (λs:set (α×α), g {y | (y, x) ∈ s}) :=
by { rw [nhds_eq_comap_uniformity', comap_lift_eq2 hg], refl }

lemma nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
  𝓝 a ×ᶠ 𝓝 b =
  (𝓤 α).lift (λs:set (α×α), (𝓤 α).lift' (λt:set (α×α),
    {y : α | (y, a) ∈ s} ×ˢ {y : α | (b, y) ∈ t})) :=
begin
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift'],
  exacts [rfl, monotone_preimage, monotone_preimage]
end

lemma nhds_eq_uniformity_prod {a b : α} :
  𝓝 (a, b) =
  (𝓤 α).lift' (λs:set (α×α), {y : α | (y, a) ∈ s} ×ˢ {y : α | (b, y) ∈ s}) :=
begin
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift'],
  { intro s, exact monotone_const.set_prod monotone_preimage },
  { intro t, exact monotone_preimage.set_prod monotone_const }
end

lemma nhdset_of_mem_uniformity {d : set (α×α)} (s : set (α×α)) (hd : d ∈ 𝓤 α) :
  ∃(t : set (α×α)), is_open t ∧ s ⊆ t ∧ t ⊆ {p | ∃x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d} :=
let cl_d := {p:α×α | ∃x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d} in
have ∀p ∈ s, ∃t ⊆ cl_d, is_open t ∧ p ∈ t, from
  assume ⟨x, y⟩ hp, _root_.mem_nhds_iff.mp $
  show cl_d ∈ 𝓝 (x, y),
  begin
    rw [nhds_eq_uniformity_prod, mem_lift'_sets],
    exact ⟨d, hd, assume ⟨a, b⟩ ⟨ha, hb⟩, ⟨x, y, ha, hp, hb⟩⟩,
    exact monotone_preimage.set_prod monotone_preimage
  end,
have ∃t:(Π(p:α×α) (h:p ∈ s), set (α×α)),
    ∀p, ∀h:p ∈ s, t p h ⊆ cl_d ∧ is_open (t p h) ∧ p ∈ t p h,
  by simp [classical.skolem] at this; simp; assumption,
match this with
| ⟨t, ht⟩ :=
  ⟨(⋃ p:α×α, ⋃ h : p ∈ s, t p h : set (α×α)),
    is_open_Union $ assume (p:α×α), is_open_Union $ assume hp, (ht p hp).right.left,
    assume ⟨a, b⟩ hp, begin simp; exact ⟨a, b, hp, (ht (a,b) hp).right.right⟩ end,
    Union_subset $ assume p, Union_subset $ assume hp, (ht p hp).left⟩
end

/-- Entourages are neighborhoods of the diagonal. -/
lemma nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α :=
begin
  intros V V_in,
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩,
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x),
  { rw nhds_prod_eq,
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in) },
  apply mem_of_superset this,
  rintros ⟨u, v⟩ ⟨u_in, v_in⟩,
  exact w_sub (mem_comp_of_mem_ball w_symm u_in v_in)
end

/-- Entourages are neighborhoods of the diagonal. -/
lemma supr_nhds_le_uniformity : (⨆ x : α, 𝓝 (x, x)) ≤ 𝓤 α :=
supr_le nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
lemma nhds_set_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
(nhds_set_diagonal α).trans_le supr_nhds_le_uniformity

/-!
### Closure and interior in uniform spaces
-/

lemma closure_eq_uniformity (s : set $ α × α) :
  closure s = ⋂ V ∈ {V | V ∈ 𝓤 α ∧ symmetric_rel V}, V ○ s ○ V :=
begin
  ext ⟨x, y⟩,
  simp only [mem_closure_iff_nhds_basis (uniform_space.has_basis_nhds_prod x y), mem_Inter,
    mem_set_of_eq, and_imp, mem_comp_comp, exists_prop, ← mem_inter_iff, inter_comm, set.nonempty]
    { contextual := tt }
end

lemma uniformity_has_basis_closed : has_basis (𝓤 α) (λ V : set (α × α), V ∈ 𝓤 α ∧ is_closed V) id :=
begin
  refine filter.has_basis_self.2 (λ t h, _),
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩,
  refine ⟨closure w, mem_of_superset w_in subset_closure, is_closed_closure, _⟩,
  refine subset.trans _ r,
  rw closure_eq_uniformity,
  apply Inter_subset_of_subset,
  apply Inter_subset,
  exact ⟨w_in, w_symm⟩
end

lemma uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
eq.symm $ uniformity_has_basis_closed.lift'_closure_eq_self $ λ _, and.right

lemma filter.has_basis.uniformity_closure {p : ι → Prop} {U : ι → set (α × α)}
  (h : (𝓤 α).has_basis p U) : (𝓤 α).has_basis p (λ i, closure (U i)) :=
(@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

/-- Closed entourages form a basis of the uniformity filter. -/
lemma uniformity_has_basis_closure : has_basis (𝓤 α) (λ V : set (α × α), V ∈ 𝓤 α) closure :=
(𝓤 α).basis_sets.uniformity_closure

lemma closure_eq_inter_uniformity {t : set (α×α)} :
  closure t = (⋂ d ∈ 𝓤 α, d ○ (t ○ d)) :=
calc closure t = ⋂ V (hV : V ∈ 𝓤 α ∧ symmetric_rel V), V ○ t ○ V : closure_eq_uniformity t
... = ⋂ V ∈ 𝓤 α, V ○ t ○ V : eq.symm $ uniform_space.has_basis_symmetric.bInter_mem $
  λ V₁ V₂ hV, comp_rel_mono (comp_rel_mono hV subset.rfl) hV
... = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) : by simp only [comp_rel_assoc]

lemma uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
le_antisymm
  (le_infi $ assume d, le_infi $ assume hd,
    let ⟨s, hs, hs_comp⟩ := (mem_lift'_sets $
      monotone_id.comp_rel $ monotone_id.comp_rel monotone_id).mp
        (comp_le_uniformity3 hd) in
    let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs in
    have s ⊆ interior d, from
      calc s ⊆ t : hst
       ... ⊆ interior d : ht.subset_interior_iff.mpr $
        λ x (hx : x ∈ t), let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx in hs_comp ⟨x, h₁, y, h₂, h₃⟩,
    have interior d ∈ 𝓤 α, by filter_upwards [hs] using this,
    by simp [this])
  (assume s hs, ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset)

lemma interior_mem_uniformity {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  interior s ∈ 𝓤 α :=
by rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

lemma mem_uniformity_is_closed {s : set (α×α)} (h : s ∈ 𝓤 α) :
  ∃t ∈ 𝓤 α, is_closed t ∧ t ⊆ s :=
let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_has_basis_closed.mem_iff.1 h in
⟨t, ht_mem, htc, hts⟩

lemma is_open_iff_open_ball_subset {s : set α} :
  is_open s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, is_open V ∧ ball x V ⊆ s :=
begin
  rw is_open_iff_ball_subset,
  split; intros h x hx,
  { obtain ⟨V, hV, hV'⟩ := h x hx,
    exact ⟨interior V, interior_mem_uniformity hV, is_open_interior,
      (ball_mono interior_subset x).trans hV'⟩, },
  { obtain ⟨V, hV, -, hV'⟩ := h x hx,
    exact ⟨V, hV, hV'⟩, },
end

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
lemma dense.bUnion_uniformity_ball {s : set α} {U : set (α × α)} (hs : dense s) (hU : U ∈ 𝓤 α) :
  (⋃ x ∈ s, ball x U) = univ :=
begin
  refine Union₂_eq_univ_iff.2 (λ y, _),
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩,
  exact ⟨x, hxs, hxy⟩
end

/-!
### Uniformity bases
-/

/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
lemma uniformity_has_basis_open : has_basis (𝓤 α) (λ V : set (α × α), V ∈ 𝓤 α ∧ is_open V) id :=
has_basis_self.2 $ λ s hs,
  ⟨interior s, interior_mem_uniformity hs, is_open_interior, interior_subset⟩

lemma filter.has_basis.mem_uniformity_iff {p : β → Prop} {s : β → set (α×α)}
  (h : (𝓤 α).has_basis p s) {t : set (α × α)} :
  t ∈ 𝓤 α ↔ ∃ i (hi : p i), ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
h.mem_iff.trans $ by simp only [prod.forall, subset_def]

/-- Open elements `s : set (α × α)` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
lemma uniformity_has_basis_open_symmetric :
  has_basis (𝓤 α) (λ V : set (α × α), V ∈ 𝓤 α ∧ is_open V ∧ symmetric_rel V) id :=
begin
  simp only [← and_assoc],
  refine uniformity_has_basis_open.restrict (λ s hs, ⟨symmetrize_rel s, _⟩),
  exact ⟨⟨symmetrize_mem_uniformity hs.1, is_open.inter hs.2 (hs.2.preimage continuous_swap)⟩,
    symmetric_symmetrize_rel s, symmetrize_rel_subset_self s⟩
end

lemma comp_open_symm_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ 𝓤 α) :
  ∃ t ∈ 𝓤 α, is_open t ∧ symmetric_rel t ∧ t ○ t ⊆ s :=
begin
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs,
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_has_basis_open_symmetric.mem_iff.mp ht₁,
  exact ⟨u, hu₁, hu₂, hu₃, (comp_rel_mono hu₄ hu₄).trans ht₂⟩,
end

section

variable (α)

lemma uniform_space.has_seq_basis [is_countably_generated $ 𝓤 α] :
  ∃ V : ℕ → set (α × α), has_antitone_basis (𝓤 α) V ∧ ∀ n, symmetric_rel (V n) :=
let ⟨U, hsym, hbasis⟩ :=  uniform_space.has_basis_symmetric.exists_antitone_subbasis
in ⟨U, hbasis, λ n, (hsym n).2⟩

end

lemma filter.has_basis.bInter_bUnion_ball {p : ι → Prop} {U : ι → set (α × α)}
  (h : has_basis (𝓤 α) p U) (s : set α) :
  (⋂ i (hi : p i), ⋃ x ∈ s, ball x (U i)) = closure s :=
begin
  ext x,
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]
end

/-! ### Uniform continuity -/

/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
def uniform_continuous [uniform_space β] (f : α → β) :=
tendsto (λx:α×α, (f x.1, f x.2)) (𝓤 α) (𝓤 β)

/-- A function `f : α → β` is *uniformly continuous* on `s : set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def uniform_continuous_on [uniform_space β] (f : α → β) (s : set α) : Prop :=
tendsto (λ x : α × α, (f x.1, f x.2)) (𝓤 α ⊓ principal (s ×ˢ s)) (𝓤 β)

theorem uniform_continuous_def [uniform_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ r ∈ 𝓤 β, { x : α × α | (f x.1, f x.2) ∈ r} ∈ 𝓤 α :=
iff.rfl

theorem uniform_continuous_iff_eventually [uniform_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r :=
iff.rfl

theorem uniform_continuous_on_univ [uniform_space β] {f : α → β} :
  uniform_continuous_on f univ ↔ uniform_continuous f :=
by rw [uniform_continuous_on, uniform_continuous, univ_prod_univ, principal_univ, inf_top_eq]

lemma uniform_continuous_of_const [uniform_space β] {c : α → β} (h : ∀a b, c a = c b) :
  uniform_continuous c :=
have (λ (x : α × α), (c (x.fst), c (x.snd))) ⁻¹' id_rel = univ, from
  eq_univ_iff_forall.2 $ assume ⟨a, b⟩, h a b,
le_trans (map_le_iff_le_comap.2 $ by simp [comap_principal, this, univ_mem]) refl_le_uniformity

lemma uniform_continuous_id : uniform_continuous (@id α) :=
by simp [uniform_continuous]; exact tendsto_id

lemma uniform_continuous_const [uniform_space β] {b : β} : uniform_continuous (λa:α, b) :=
uniform_continuous_of_const $ λ _ _, rfl

lemma uniform_continuous.comp [uniform_space β] [uniform_space γ] {g : β → γ} {f : α → β}
  (hg : uniform_continuous g) (hf : uniform_continuous f) : uniform_continuous (g ∘ f) :=
hg.comp hf

lemma filter.has_basis.uniform_continuous_iff {ι'} [uniform_space β] {p : ι → Prop}
  {s : ι → set (α×α)} (ha : (𝓤 α).has_basis p s) {q : ι' → Prop} {t : ι' → set (β×β)}
  (hb : (𝓤 β).has_basis q t) {f : α → β} :
  uniform_continuous f ↔ ∀ i (hi : q i), ∃ j (hj : p j), ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ t i :=
(ha.tendsto_iff hb).trans $ by simp only [prod.forall]

lemma filter.has_basis.uniform_continuous_on_iff {ι'} [uniform_space β] {p : ι → Prop}
  {s : ι → set (α×α)} (ha : (𝓤 α).has_basis p s) {q : ι' → Prop} {t : ι' → set (β×β)}
  (hb : (𝓤 β).has_basis q t) {f : α → β} {S : set α} :
  uniform_continuous_on f S ↔
    ∀ i (hi : q i), ∃ j (hj : p j), ∀ x y ∈ S, (x, y) ∈ s j → (f x, f y) ∈ t i :=
((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans $
by simp_rw [prod.forall, set.inter_comm (s _), ball_mem_comm, mem_inter_iff, mem_prod, and_imp]

end uniform_space

open_locale uniformity

section constructions

instance : partial_order (uniform_space α) :=
{ le          := λt s, t.uniformity ≤ s.uniformity,
  le_antisymm := assume t s h₁ h₂, uniform_space_eq $ le_antisymm h₁ h₂,
  le_refl     := assume t, le_rfl,
  le_trans    := assume a b c h₁ h₂, le_trans h₁ h₂ }

instance : has_Inf (uniform_space α) :=
⟨assume s, uniform_space.of_core
{ uniformity := (⨅u∈s, 𝓤[u]),
  refl       := le_infi $ assume u, le_infi $ assume hu, u.refl,
  symm       := le_infi $ assume u, le_infi $ assume hu,
    le_trans (map_mono $ infi_le_of_le _ $ infi_le _ hu) u.symm,
  comp       := le_infi $ assume u, le_infi $ assume hu,
    le_trans (lift'_mono (infi_le_of_le _ $ infi_le _ hu) $ le_rfl) u.comp }⟩

private lemma Inf_le {tt : set (uniform_space α)} {t : uniform_space α} (h : t ∈ tt) :
  Inf tt ≤ t :=
show (⨅ u ∈ tt, 𝓤[u]) ≤ 𝓤[t], from infi₂_le t h

private lemma le_Inf {tt : set (uniform_space α)} {t : uniform_space α} (h : ∀t'∈tt, t ≤ t') :
  t ≤ Inf tt :=
show 𝓤[t] ≤ (⨅ u ∈ tt, 𝓤[u]), from le_infi₂ h

instance : has_top (uniform_space α) :=
⟨uniform_space.of_core { uniformity := ⊤, refl := le_top, symm := le_top, comp := le_top }⟩

instance : has_bot (uniform_space α) :=
⟨{ to_topological_space := ⊥,
  uniformity  := 𝓟 id_rel,
  refl        := le_rfl,
  symm        := by simp [tendsto],
  comp        := lift'_le (mem_principal_self _) $ principal_mono.2 id_comp_rel.subset,
  is_open_uniformity :=
    assume s, by simp [is_open_fold, subset_def, id_rel] {contextual := tt } } ⟩

instance : has_inf (uniform_space α) :=
⟨λ u₁ u₂,
  @uniform_space.replace_topology _
    (u₁.to_topological_space ⊓ u₂.to_topological_space) (uniform_space.of_core
    { uniformity  := u₁.uniformity ⊓ u₂.uniformity,
      refl        := le_inf u₁.refl u₂.refl,
      symm        := u₁.symm.inf u₂.symm,
      comp        := (lift'_inf_le _ _ _).trans $ inf_le_inf u₁.comp u₂.comp }) $
    eq_of_nhds_eq_nhds $ λ a,
      by simpa only [nhds_inf, nhds_eq_comap_uniformity] using comap_inf.symm⟩

instance : complete_lattice (uniform_space α) :=
{ sup           := λa b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left   := λ a b, le_Inf (λ _ ⟨h, _⟩, h),
  le_sup_right  := λ a b, le_Inf (λ _ ⟨_, h⟩, h),
  sup_le        := λ a b c h₁ h₂, Inf_le ⟨h₁, h₂⟩,
  inf           := (⊓),
  le_inf        := λ a b c h₁ h₂, show a.uniformity ≤ _, from le_inf h₁ h₂,
  inf_le_left   := λ a b, show _ ≤ a.uniformity, from inf_le_left,
  inf_le_right  := λ a b, show _ ≤ b.uniformity, from inf_le_right,
  top           := ⊤,
  le_top        := λ a, show a.uniformity ≤ ⊤, from le_top,
  bot           := ⊥,
  bot_le        := λ u, u.refl,
  Sup           := λ tt, Inf {t | ∀ t' ∈ tt, t' ≤ t},
  le_Sup        := λ s u h, le_Inf (λ u' h', h' u h),
  Sup_le        := λ s u h, Inf_le h,
  Inf           := Inf,
  le_Inf        := λ s a hs, le_Inf hs,
  Inf_le        := λ s a ha, Inf_le ha,
  ..uniform_space.partial_order }

lemma infi_uniformity {ι : Sort*} {u : ι → uniform_space α} : 𝓤[infi u] = (⨅i, 𝓤[u i]) :=
infi_range

lemma inf_uniformity {u v : uniform_space α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] := rfl

instance inhabited_uniform_space : inhabited (uniform_space α) := ⟨⊥⟩
instance inhabited_uniform_space_core : inhabited (uniform_space.core α) :=
⟨@uniform_space.to_core _ default⟩

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`. -/
def uniform_space.comap (f : α → β) (u : uniform_space β) : uniform_space α :=
{ uniformity := 𝓤[u].comap (λp:α×α, (f p.1, f p.2)),
  to_topological_space := u.to_topological_space.induced f,
  refl := le_trans (by simp; exact assume ⟨a, b⟩ (h : a = b), h ▸ rfl) (comap_mono u.refl),
  symm := by simp [tendsto_comap_iff, prod.swap, (∘)];
            exact tendsto_swap_uniformity.comp tendsto_comap,
  comp := le_trans
    begin
      rw [comap_lift'_eq, comap_lift'_eq2],
      exact (lift'_mono' $ assume s hs ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩, ⟨f x, h₁, h₂⟩),
      exact monotone_id.comp_rel monotone_id
    end
    (comap_mono u.comp),
  is_open_uniformity := λ s, by simp only [is_open_fold, is_open_induced, is_open_iff_mem_nhds,
    nhds_induced, nhds_eq_comap_uniformity, comap_comap, ← mem_comap_prod_mk, ← uniformity] }

lemma uniformity_comap [uniform_space β] (f : α → β) :
  𝓤[uniform_space.comap f ‹_›] = comap (prod.map f f) (𝓤 β) :=
rfl

@[simp] lemma uniform_space_comap_id {α : Type*} : uniform_space.comap (id : α → α) = id :=
by { ext : 2, rw [uniformity_comap, prod.map_id, comap_id] }

lemma uniform_space.comap_comap {α β γ} [uγ : uniform_space γ] {f : α → β} {g : β → γ} :
  uniform_space.comap (g ∘ f) uγ = uniform_space.comap f (uniform_space.comap g uγ) :=
by { ext1, simp only [uniformity_comap, comap_comap, prod.map_comp_map] }

lemma uniform_space.comap_inf {α γ} {u₁ u₂ : uniform_space γ} {f : α → γ} :
  (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
uniform_space_eq comap_inf

lemma uniform_space.comap_infi {ι α γ} {u : ι → uniform_space γ} {f : α → γ} :
  (⨅ i, u i).comap f = ⨅ i, (u i).comap f :=
begin
  ext : 1,
  simp [uniformity_comap, infi_uniformity]
end

lemma uniform_space.comap_mono {α γ} {f : α → γ} :
  monotone (λ u : uniform_space γ, u.comap f) :=
begin
  intros u₁ u₂ hu,
  change (𝓤 _) ≤ (𝓤 _),
  rw uniformity_comap,
  exact comap_mono hu
end

lemma uniform_continuous_iff {α β} {uα : uniform_space α} {uβ : uniform_space β} {f : α → β} :
  uniform_continuous f ↔ uα ≤ uβ.comap f :=
filter.map_le_iff_le_comap

lemma le_iff_uniform_continuous_id {u v : uniform_space α} :
  u ≤ v ↔ @uniform_continuous _ _ u v id :=
by rw [uniform_continuous_iff, uniform_space_comap_id, id]

lemma uniform_continuous_comap {f : α → β} [u : uniform_space β] :
  @uniform_continuous α β (uniform_space.comap f u) u f :=
tendsto_comap

theorem to_topological_space_comap {f : α → β} {u : uniform_space β} :
  @uniform_space.to_topological_space _ (uniform_space.comap f u) =
  topological_space.induced f (@uniform_space.to_topological_space β u) := rfl

lemma uniform_continuous_comap' {f : γ → β} {g : α → γ} [v : uniform_space β] [u : uniform_space α]
  (h : uniform_continuous (f ∘ g)) : @uniform_continuous α γ u (uniform_space.comap f v) g :=
tendsto_comap_iff.2 h

lemma to_nhds_mono {u₁ u₂ : uniform_space α} (h : u₁ ≤ u₂) (a : α) :
  @nhds _ (@uniform_space.to_topological_space _ u₁) a ≤
    @nhds _ (@uniform_space.to_topological_space _ u₂) a :=
by rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a]; exact (lift'_mono h le_rfl)

lemma to_topological_space_mono {u₁ u₂ : uniform_space α} (h : u₁ ≤ u₂) :
  @uniform_space.to_topological_space _ u₁ ≤ @uniform_space.to_topological_space _ u₂ :=
le_of_nhds_le_nhds $ to_nhds_mono h

lemma uniform_continuous.continuous [uniform_space α] [uniform_space β] {f : α → β}
  (hf : uniform_continuous f) : continuous f :=
continuous_iff_le_induced.mpr $ to_topological_space_mono $ uniform_continuous_iff.1 hf

lemma to_topological_space_bot : @uniform_space.to_topological_space α ⊥ = ⊥ := rfl

lemma to_topological_space_top : @uniform_space.to_topological_space α ⊤ = ⊤ :=
top_unique $ assume s hs, s.eq_empty_or_nonempty.elim
  (assume : s = ∅, this.symm ▸ @is_open_empty _ ⊤)
  (assume  ⟨x, hx⟩,
    have s = univ, from top_unique $ assume y hy, hs x hx (x, y) rfl,
    this.symm ▸ @is_open_univ _ ⊤)

lemma to_topological_space_infi {ι : Sort*} {u : ι → uniform_space α} :
  (infi u).to_topological_space = ⨅i, (u i).to_topological_space :=
begin
  refine (eq_of_nhds_eq_nhds $ assume a, _),
  simp only [nhds_infi, nhds_eq_uniformity, infi_uniformity],
  exact lift'_infi_of_map_univ (ball_inter _) preimage_univ
end

lemma to_topological_space_Inf {s : set (uniform_space α)} :
  (Inf s).to_topological_space = (⨅i∈s, @uniform_space.to_topological_space α i) :=
begin
  rw [Inf_eq_infi],
  simp only [← to_topological_space_infi],
end

lemma to_topological_space_inf {u v : uniform_space α} :
  (u ⊓ v).to_topological_space = u.to_topological_space ⊓ v.to_topological_space :=
rfl

/-- Uniform space structure on `ulift α`. -/
instance ulift.uniform_space [uniform_space α] : uniform_space (ulift α) :=
uniform_space.comap ulift.down ‹_›

section uniform_continuous_infi

lemma uniform_continuous_inf_rng {f : α → β} {u₁ : uniform_space α} {u₂ u₃ : uniform_space β}
  (h₁ : @@uniform_continuous u₁ u₂ f) (h₂ : @@uniform_continuous u₁ u₃ f) :
  @@uniform_continuous u₁ (u₂ ⊓ u₃) f :=
tendsto_inf.mpr ⟨h₁, h₂⟩

lemma uniform_continuous_inf_dom_left {f : α → β} {u₁ u₂ : uniform_space α} {u₃ : uniform_space β}
  (hf : @@uniform_continuous u₁ u₃ f) : @@uniform_continuous (u₁ ⊓ u₂) u₃ f :=
tendsto_inf_left hf

lemma uniform_continuous_inf_dom_right {f : α → β} {u₁ u₂ : uniform_space α} {u₃ : uniform_space β}
  (hf : @@uniform_continuous u₂ u₃ f) : @@uniform_continuous (u₁ ⊓ u₂) u₃ f :=
tendsto_inf_right hf

lemma uniform_continuous_Inf_dom {f : α → β} {u₁ : set (uniform_space α)} {u₂ : uniform_space β}
  {u : uniform_space α} (h₁ : u ∈ u₁) (hf : @@uniform_continuous u u₂ f) :
  @@uniform_continuous (Inf u₁) u₂ f :=
begin
  rw [uniform_continuous, Inf_eq_infi', infi_uniformity],
  exact tendsto_infi' ⟨u, h₁⟩ hf
end

lemma uniform_continuous_Inf_rng {f : α → β} {u₁ : uniform_space α} {u₂ : set (uniform_space β)}
  (h : ∀u∈u₂, @@uniform_continuous u₁ u f) : @@uniform_continuous u₁ (Inf u₂) f :=
begin
  rw [uniform_continuous, Inf_eq_infi', infi_uniformity],
  exact tendsto_infi.mpr (λ ⟨u, hu⟩, h u hu)
end

lemma uniform_continuous_infi_dom {f : α → β} {u₁ : ι → uniform_space α} {u₂ : uniform_space β}
  {i : ι} (hf : @@uniform_continuous (u₁ i) u₂ f) : @@uniform_continuous (infi u₁) u₂ f :=
begin
  rw [uniform_continuous, infi_uniformity],
  exact tendsto_infi' i hf
end

lemma uniform_continuous_infi_rng {f : α → β} {u₁ : uniform_space α} {u₂ : ι → uniform_space β}
  (h : ∀i, @@uniform_continuous u₁ (u₂ i) f) : @@uniform_continuous u₁ (infi u₂) f :=
by rwa [uniform_continuous, infi_uniformity, tendsto_infi]

end uniform_continuous_infi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
lemma discrete_topology_of_discrete_uniformity [hα : uniform_space α]
  (h : uniformity α = 𝓟 id_rel) :
  discrete_topology α :=
⟨(uniform_space_eq h.symm : ⊥ = hα) ▸ rfl⟩

instance : uniform_space empty := ⊥
instance : uniform_space punit := ⊥
instance : uniform_space bool := ⊥
instance : uniform_space ℕ := ⊥
instance : uniform_space ℤ := ⊥

section
variables [uniform_space α]

open additive multiplicative

instance : uniform_space (additive α) := ‹uniform_space α›
instance : uniform_space (multiplicative α) := ‹uniform_space α›

lemma uniform_continuous_of_mul : uniform_continuous (of_mul : α → additive α) :=
uniform_continuous_id
lemma uniform_continuous_to_mul : uniform_continuous (to_mul : additive α → α) :=
uniform_continuous_id
lemma uniform_continuous_of_add : uniform_continuous (of_add : α → multiplicative α) :=
uniform_continuous_id
lemma uniform_continuous_to_add : uniform_continuous (to_add : multiplicative α → α) :=
uniform_continuous_id

lemma uniformity_additive : 𝓤 (additive α) = (𝓤 α).map (prod.map of_mul of_mul) :=
by { convert map_id.symm, exact prod.map_id }

lemma uniformity_multiplicative : 𝓤 (multiplicative α) = (𝓤 α).map (prod.map of_add of_add) :=
by { convert map_id.symm, exact prod.map_id }

end

instance {p : α → Prop} [t : uniform_space α] : uniform_space (subtype p) :=
uniform_space.comap subtype.val t

lemma uniformity_subtype {p : α → Prop} [t : uniform_space α] :
  𝓤 (subtype p) = comap (λq:subtype p × subtype p, (q.1.1, q.2.1)) (𝓤 α) :=
rfl

lemma uniformity_set_coe {s : set α} [t : uniform_space α] :
  𝓤 s = comap (prod.map (coe : s → α) (coe : s → α)) (𝓤 α) :=
rfl

lemma uniform_continuous_subtype_val {p : α → Prop} [uniform_space α] :
  uniform_continuous (subtype.val : {a : α // p a} → α) :=
uniform_continuous_comap

lemma uniform_continuous_subtype_coe {p : α → Prop} [uniform_space α] :
  uniform_continuous (coe : {a : α // p a} → α) :=
uniform_continuous_subtype_val

lemma uniform_continuous.subtype_mk {p : α → Prop} [uniform_space α] [uniform_space β]
  {f : β → α} (hf : uniform_continuous f) (h : ∀x, p (f x)) :
  uniform_continuous (λx, ⟨f x, h x⟩ : β → subtype p) :=
uniform_continuous_comap' hf

lemma uniform_continuous_on_iff_restrict [uniform_space α] [uniform_space β] {f : α → β}
  {s : set α} :
  uniform_continuous_on f s ↔ uniform_continuous (s.restrict f) :=
begin
  unfold uniform_continuous_on set.restrict uniform_continuous tendsto,
  conv_rhs { rw [show (λ x : s × s, (f x.1, f x.2)) = prod.map f f ∘ prod.map coe coe, from rfl,
    uniformity_set_coe, ← map_map, map_comap, range_prod_map, subtype.range_coe] },
  refl
end

lemma tendsto_of_uniform_continuous_subtype
  [uniform_space α] [uniform_space β] {f : α → β} {s : set α} {a : α}
  (hf : uniform_continuous (λx:s, f x.val)) (ha : s ∈ 𝓝 a) :
  tendsto f (𝓝 a) (𝓝 (f a)) :=
by rw [(@map_nhds_subtype_coe_eq α _ s a (mem_of_mem_nhds ha) ha).symm]; exact
tendsto_map' (continuous_iff_continuous_at.mp hf.continuous _)

lemma uniform_continuous_on.continuous_on [uniform_space α] [uniform_space β] {f : α → β}
  {s : set α} (h : uniform_continuous_on f s) : continuous_on f s :=
begin
  rw uniform_continuous_on_iff_restrict at h,
  rw continuous_on_iff_continuous_restrict,
  exact h.continuous
end

@[to_additive]
instance [uniform_space α] : uniform_space (αᵐᵒᵖ) :=
uniform_space.comap mul_opposite.unop ‹_›

@[to_additive]
lemma uniformity_mul_opposite [uniform_space α] :
  𝓤 (αᵐᵒᵖ) = comap (λ q : αᵐᵒᵖ × αᵐᵒᵖ, (q.1.unop, q.2.unop)) (𝓤 α) :=
rfl

@[simp, to_additive] lemma comap_uniformity_mul_opposite [uniform_space α] :
  comap (λ p : α × α, (mul_opposite.op p.1, mul_opposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α :=
by simpa [uniformity_mul_opposite, comap_comap, (∘)] using comap_id

namespace mul_opposite

@[to_additive]
lemma uniform_continuous_unop [uniform_space α] : uniform_continuous (unop : αᵐᵒᵖ → α) :=
uniform_continuous_comap

@[to_additive]
lemma uniform_continuous_op [uniform_space α] : uniform_continuous (op : α → αᵐᵒᵖ) :=
uniform_continuous_comap' uniform_continuous_id

end mul_opposite

section prod

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance [u₁ : uniform_space α] [u₂ : uniform_space β] : uniform_space (α × β) :=
u₁.comap prod.fst ⊓ u₂.comap prod.snd

-- check the above produces no diamond
example [u₁ : uniform_space α] [u₂ : uniform_space β] :
  (prod.topological_space : topological_space (α × β)) = uniform_space.to_topological_space :=
rfl

theorem uniformity_prod [uniform_space α] [uniform_space β] : 𝓤 (α × β) =
  (𝓤 α).comap (λp:(α × β) × α × β, (p.1.1, p.2.1)) ⊓
  (𝓤 β).comap (λp:(α × β) × α × β, (p.1.2, p.2.2)) :=
rfl

lemma uniformity_prod_eq_comap_prod [uniform_space α] [uniform_space β] :
  𝓤 (α × β) = comap (λ p : (α × β) × (α × β), ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ᶠ 𝓤 β) :=
by rw [uniformity_prod, filter.prod, comap_inf, comap_comap, comap_comap]

lemma uniformity_prod_eq_prod [uniform_space α] [uniform_space β] :
  𝓤 (α × β) = map (λ p : (α × α) × (β × β), ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ᶠ 𝓤 β) :=
by rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]

lemma mem_uniformity_of_uniform_continuous_invariant [uniform_space α] [uniform_space β]
  {s : set (β × β)} {f : α → α → β} (hf : uniform_continuous (λ p : α × α, f p.1 p.2))
  (hs : s ∈ 𝓤 β) :
  ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff, (∘)] at hf,
  rcases mem_prod_iff.1 (mem_map.1 $ hf hs) with ⟨u, hu, v, hv, huvt⟩,
  exact ⟨u, hu, λ a b c hab, @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩
end

lemma mem_uniform_prod [t₁ : uniform_space α] [t₂ : uniform_space β] {a : set (α × α)}
  {b : set (β × β)} (ha : a ∈ 𝓤 α) (hb : b ∈ 𝓤 β) :
  {p:(α×β)×(α×β) | (p.1.1, p.2.1) ∈ a ∧ (p.1.2, p.2.2) ∈ b } ∈ 𝓤 (α × β) :=
by rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap ha) (preimage_mem_comap hb)

lemma tendsto_prod_uniformity_fst [uniform_space α] [uniform_space β] :
  tendsto (λp:(α×β)×(α×β), (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
le_trans (map_mono inf_le_left) map_comap_le

lemma tendsto_prod_uniformity_snd [uniform_space α] [uniform_space β] :
  tendsto (λp:(α×β)×(α×β), (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
le_trans (map_mono inf_le_right) map_comap_le

lemma uniform_continuous_fst [uniform_space α] [uniform_space β] :
  uniform_continuous (λp:α×β, p.1) :=
tendsto_prod_uniformity_fst

lemma uniform_continuous_snd [uniform_space α] [uniform_space β] :
  uniform_continuous (λp:α×β, p.2) :=
tendsto_prod_uniformity_snd

variables [uniform_space α] [uniform_space β] [uniform_space γ]
lemma uniform_continuous.prod_mk
  {f₁ : α → β} {f₂ : α → γ} (h₁ : uniform_continuous f₁) (h₂ : uniform_continuous f₂) :
  uniform_continuous (λa, (f₁ a, f₂ a)) :=
by rw [uniform_continuous, uniformity_prod]; exact
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma uniform_continuous.prod_mk_left {f : α × β → γ} (h : uniform_continuous f) (b) :
  uniform_continuous (λ a, f (a,b)) :=
h.comp (uniform_continuous_id.prod_mk uniform_continuous_const)

lemma uniform_continuous.prod_mk_right {f : α × β → γ} (h : uniform_continuous f) (a) :
  uniform_continuous (λ b, f (a,b)) :=
h.comp (uniform_continuous_const.prod_mk  uniform_continuous_id)

lemma uniform_continuous.prod_map [uniform_space δ] {f : α → γ} {g : β → δ}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (prod.map f g) :=
(hf.comp uniform_continuous_fst).prod_mk (hg.comp uniform_continuous_snd)

lemma to_topological_space_prod {α} {β} [u : uniform_space α] [v : uniform_space β] :
  @uniform_space.to_topological_space (α × β) prod.uniform_space =
    @prod.topological_space α β u.to_topological_space v.to_topological_space := rfl

/-- A version of `uniform_continuous_inf_dom_left` for binary functions -/
lemma uniform_continuous_inf_dom_left₂ {α β γ} {f : α → β → γ}
  {ua1 ua2 : uniform_space α} {ub1 ub2 : uniform_space β} {uc1 : uniform_space γ}
  (h : by haveI := ua1; haveI := ub1; exact uniform_continuous (λ p : α × β, f p.1 p.2)) :
  by haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2; exact uniform_continuous (λ p : α × β, f p.1 p.2) :=
begin
  -- proof essentially copied from ``continuous_inf_dom_left₂`
  have ha := @uniform_continuous_inf_dom_left _ _ id ua1 ua2 ua1 (@uniform_continuous_id _ (id _)),
  have hb := @uniform_continuous_inf_dom_left _ _ id ub1 ub2 ub1 (@uniform_continuous_id _ (id _)),
  have h_unif_cont_id := @uniform_continuous.prod_map _ _ _ _ (
    ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb,
  exact @uniform_continuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id,
end

/-- A version of `uniform_continuous_inf_dom_right` for binary functions -/
lemma uniform_continuous_inf_dom_right₂ {α β γ} {f : α → β → γ}
  {ua1 ua2 : uniform_space α} {ub1 ub2 : uniform_space β} {uc1 : uniform_space γ}
  (h : by haveI := ua2; haveI := ub2; exact uniform_continuous (λ p : α × β, f p.1 p.2)) :
  by haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2; exact uniform_continuous (λ p : α × β, f p.1 p.2) :=
begin
  -- proof essentially copied from ``continuous_inf_dom_right₂`
  have ha := @uniform_continuous_inf_dom_right _ _ id ua1 ua2 ua2 (@uniform_continuous_id _ (id _)),
  have hb := @uniform_continuous_inf_dom_right _ _ id ub1 ub2 ub2 (@uniform_continuous_id _ (id _)),
  have h_unif_cont_id := @uniform_continuous.prod_map _ _ _ _
    (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2  _ _ ha hb,
  exact @uniform_continuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id,
end

/-- A version of `uniform_continuous_Inf_dom` for binary functions -/
lemma uniform_continuous_Inf_dom₂ {α β γ} {f : α → β → γ}
  {uas : set (uniform_space α)} {ubs : set (uniform_space β)}
  {ua : uniform_space α} {ub : uniform_space β} {uc : uniform_space γ}
  (ha : ua ∈ uas) (hb : ub ∈ ubs)
  (hf : uniform_continuous (λ p : α × β, f p.1 p.2)):
  by haveI := Inf uas; haveI := Inf ubs;
    exact @uniform_continuous _ _ _ uc (λ p : α × β, f p.1 p.2) :=
begin
  -- proof essentially copied from ``continuous_Inf_dom`
  let t : uniform_space (α × β) := prod.uniform_space,
  have ha := uniform_continuous_Inf_dom ha uniform_continuous_id,
  have hb := uniform_continuous_Inf_dom hb uniform_continuous_id,
  have h_unif_cont_id := @uniform_continuous.prod_map _ _ _ _ (Inf uas) (Inf ubs) ua ub _ _ ha hb,
  exact @uniform_continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id,
end

end prod

section
open uniform_space function
variables {δ' : Type*} [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ]
  [uniform_space δ']

local notation f ` ∘₂ ` g := function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def uniform_continuous₂ (f : α → β → γ) := uniform_continuous (uncurry f)

lemma uniform_continuous₂_def (f : α → β → γ) :
  uniform_continuous₂ f ↔ uniform_continuous (uncurry f) := iff.rfl

lemma uniform_continuous₂.uniform_continuous {f : α → β → γ} (h : uniform_continuous₂ f) :
  uniform_continuous (uncurry f) := h

lemma uniform_continuous₂_curry (f : α × β → γ) :
  uniform_continuous₂ (function.curry f) ↔ uniform_continuous f :=
by rw [uniform_continuous₂, uncurry_curry]

lemma uniform_continuous₂.comp {f : α → β → γ} {g : γ → δ}
  (hg : uniform_continuous g) (hf : uniform_continuous₂ f) :
  uniform_continuous₂ (g ∘₂ f) :=
hg.comp hf

lemma uniform_continuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β}
  (hf : uniform_continuous₂ f) (hga : uniform_continuous ga) (hgb : uniform_continuous gb) :
  uniform_continuous₂ (bicompl f ga gb) :=
hf.uniform_continuous.comp (hga.prod_map hgb)

end

lemma to_topological_space_subtype [u : uniform_space α] {p : α → Prop} :
  @uniform_space.to_topological_space (subtype p) subtype.uniform_space =
    @subtype.topological_space α p u.to_topological_space := rfl

section sum
variables [uniform_space α] [uniform_space β]
open sum

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def uniform_space.core.sum : uniform_space.core (α ⊕ β) :=
uniform_space.core.mk'
  (map (λ p : α × α, (inl p.1, inl p.2)) (𝓤 α) ⊔ map (λ p : β × β, (inr p.1, inr p.2)) (𝓤 β))
  (λ r ⟨H₁, H₂⟩ x, by cases x; [apply refl_mem_uniformity H₁, apply refl_mem_uniformity H₂])
  (λ r ⟨H₁, H₂⟩, ⟨symm_le_uniformity H₁, symm_le_uniformity H₂⟩)
  (λ r ⟨Hrα, Hrβ⟩, begin
    rcases comp_mem_uniformity_sets Hrα with ⟨tα, htα, Htα⟩,
    rcases comp_mem_uniformity_sets Hrβ with ⟨tβ, htβ, Htβ⟩,
    refine ⟨_,
      ⟨mem_map_iff_exists_image.2 ⟨tα, htα, subset_union_left _ _⟩,
       mem_map_iff_exists_image.2 ⟨tβ, htβ, subset_union_right _ _⟩⟩, _⟩,
    rintros ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩,
                       ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩,
    { have A : (a, c) ∈ tα ○ tα := ⟨b, hab, hbc⟩,
      exact Htα A },
    { have A : (a, c) ∈ tβ ○ tβ := ⟨b, hab, hbc⟩,
      exact Htβ A }
  end)

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
lemma union_mem_uniformity_sum
  {a : set (α × α)} (ha : a ∈ 𝓤 α) {b : set (β × β)} (hb : b ∈ 𝓤 β) :
  ((λ p : (α × α), (inl p.1, inl p.2)) '' a ∪ (λ p : (β × β), (inr p.1, inr p.2)) '' b) ∈
    (@uniform_space.core.sum α β _ _).uniformity :=
⟨mem_map_iff_exists_image.2 ⟨_, ha, subset_union_left _ _⟩,
  mem_map_iff_exists_image.2 ⟨_, hb, subset_union_right _ _⟩⟩

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/
lemma uniformity_sum_of_open_aux {s : set (α ⊕ β)} (hs : is_open s) {x : α ⊕ β} (xs : x ∈ s) :
  { p : ((α ⊕ β) × (α ⊕ β)) | p.1 = x → p.2 ∈ s } ∈ (@uniform_space.core.sum α β _ _).uniformity :=
begin
  cases x,
  { refine mem_of_superset
      (union_mem_uniformity_sum (mem_nhds_uniformity_iff_right.1 (is_open.mem_nhds hs.1 xs))
        univ_mem)
      (union_subset _ _);
    rintro _ ⟨⟨_, b⟩, h, ⟨⟩⟩ ⟨⟩,
    exact h rfl },
  { refine mem_of_superset
      (union_mem_uniformity_sum univ_mem (mem_nhds_uniformity_iff_right.1
        (is_open.mem_nhds hs.2 xs)))
      (union_subset _ _);
    rintro _ ⟨⟨a, _⟩, h, ⟨⟩⟩ ⟨⟩,
    exact h rfl },
end

lemma open_of_uniformity_sum_aux {s : set (α ⊕ β)}
  (hs : ∀x ∈ s, { p : ((α ⊕ β) × (α ⊕ β)) | p.1 = x → p.2 ∈ s } ∈
    (@uniform_space.core.sum α β _ _).uniformity) :
  is_open s :=
begin
  split,
  { refine (@is_open_iff_mem_nhds α _ _).2 (λ a ha, mem_nhds_uniformity_iff_right.2 _),
    rcases mem_map_iff_exists_image.1 (hs _ ha).1 with ⟨t, ht, st⟩,
    refine mem_of_superset ht _,
    rintro p pt rfl, exact st ⟨_, pt, rfl⟩ rfl },
  { refine (@is_open_iff_mem_nhds β _ _).2 (λ b hb, mem_nhds_uniformity_iff_right.2 _),
    rcases mem_map_iff_exists_image.1 (hs _ hb).2 with ⟨t, ht, st⟩,
    refine mem_of_superset ht _,
    rintro p pt rfl, exact st ⟨_, pt, rfl⟩ rfl }
end

/- We can now define the uniform structure on the disjoint union -/
instance sum.uniform_space : uniform_space (α ⊕ β) :=
{ to_core := uniform_space.core.sum,
  is_open_uniformity := λ s, ⟨uniformity_sum_of_open_aux, open_of_uniformity_sum_aux⟩ }

lemma sum.uniformity : 𝓤 (α ⊕ β) =
    map (λ p : α × α, (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (λ p : β × β, (inr p.1, inr p.2)) (𝓤 β) := rfl

end sum

end constructions

/-- Let `c : ι → set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
lemma lebesgue_number_lemma {α : Type u} [uniform_space α] {s : set α} {ι} {c : ι → set α}
  (hs : is_compact s) (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ i, {y | (x, y) ∈ n} ⊆ c i :=
begin
  let u := λ n, {x | ∃ i (m ∈ 𝓤 α), {y | (x, y) ∈ m ○ n} ⊆ c i},
  have hu₁ : ∀ n ∈ 𝓤 α, is_open (u n),
  { refine λ n hn, is_open_uniformity.2 _,
    rintro x ⟨i, m, hm, h⟩,
    rcases comp_mem_uniformity_sets hm with ⟨m', hm', mm'⟩,
    apply (𝓤 α).sets_of_superset hm',
    rintros ⟨x, y⟩ hp rfl,
    refine ⟨i, m', hm', λ z hz, h (monotone_id.comp_rel monotone_const mm' _)⟩,
    dsimp [-mem_comp_rel] at hz ⊢, rw comp_rel_assoc,
    exact ⟨y, hp, hz⟩ },
  have hu₂ : s ⊆ ⋃ n ∈ 𝓤 α, u n,
  { intros x hx,
    rcases mem_Union.1 (hc₂ hx) with ⟨i, h⟩,
    rcases comp_mem_uniformity_sets (is_open_uniformity.1 (hc₁ i) x h) with ⟨m', hm', mm'⟩,
    exact mem_bUnion hm' ⟨i, _, hm', λ y hy, mm' hy rfl⟩ },
  rcases hs.elim_finite_subcover_image hu₁ hu₂ with ⟨b, bu, b_fin, b_cover⟩,
  refine ⟨_, (bInter_mem b_fin).2 bu, λ x hx, _⟩,
  rcases mem_Union₂.1 (b_cover hx) with ⟨n, bn, i, m, hm, h⟩,
  refine ⟨i, λ y hy, h _⟩,
  exact prod_mk_mem_comp_rel (refl_mem_uniformity hm) (bInter_subset_of_mem bn hy)
end

/-- Let `c : set (set α)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `t ∈ c`. -/
lemma lebesgue_number_lemma_sUnion {α : Type u} [uniform_space α] {s : set α} {c : set (set α)}
  (hs : is_compact s) (hc₁ : ∀ t ∈ c, is_open t) (hc₂ : s ⊆ ⋃₀ c) :
  ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ t ∈ c, ∀ y, (x, y) ∈ n → y ∈ t :=
by rw sUnion_eq_Union at hc₂;
   simpa using lebesgue_number_lemma hs (by simpa) hc₂

/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
lemma lebesgue_number_of_compact_open [uniform_space α]
  {K U : set α} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ V ∈ 𝓤 α, is_open V ∧ ∀ x ∈ K, uniform_space.ball x V ⊆ U :=
begin
  let W : K → set (α × α) := λ k, classical.some $ is_open_iff_open_ball_subset.mp hU k.1 $ hKU k.2,
  have hW : ∀ k, W k ∈ 𝓤 α ∧ is_open (W k) ∧ uniform_space.ball k.1 (W k) ⊆ U,
  { intros k,
    obtain ⟨h₁, h₂, h₃⟩ := classical.some_spec (is_open_iff_open_ball_subset.mp hU k.1 (hKU k.2)),
    exact ⟨h₁, h₂, h₃⟩, },
  let c : K → set α := λ k, uniform_space.ball k.1 (W k),
  have hc₁ : ∀ k, is_open (c k), { exact λ k, uniform_space.is_open_ball k.1 (hW k).2.1, },
  have hc₂ : K ⊆ ⋃ i, c i,
  { intros k hk,
    simp only [mem_Union, set_coe.exists],
    exact ⟨k, hk, uniform_space.mem_ball_self k (hW ⟨k, hk⟩).1⟩, },
  have hc₃ : ∀ k, c k ⊆ U, { exact λ k, (hW k).2.2, },
  obtain ⟨V, hV, hV'⟩ := lebesgue_number_lemma hK hc₁ hc₂,
  refine ⟨interior V, interior_mem_uniformity hV, is_open_interior, _⟩,
  intros k hk,
  obtain ⟨k', hk'⟩ := hV' k hk,
  exact ((ball_mono interior_subset k).trans hk').trans (hc₃ k'),
end

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/

namespace uniform

variables [uniform_space α]

theorem tendsto_nhds_right {f : filter β} {u : β → α} {a : α} :
  tendsto u f (𝓝 a) ↔ tendsto (λ x, (a, u x)) f (𝓤 α)  :=
by rw [nhds_eq_comap_uniformity, tendsto_comap_iff]

theorem tendsto_nhds_left {f : filter β} {u : β → α} {a : α} :
  tendsto u f (𝓝 a) ↔ tendsto (λ x, (u x, a)) f (𝓤 α)  :=
by rw [nhds_eq_comap_uniformity', tendsto_comap_iff]

theorem continuous_at_iff'_right [topological_space β] {f : β → α} {b : β} :
  continuous_at f b ↔ tendsto (λ x, (f b, f x)) (𝓝 b) (𝓤 α) :=
by rw [continuous_at, tendsto_nhds_right]

theorem continuous_at_iff'_left [topological_space β] {f : β → α} {b : β} :
  continuous_at f b ↔ tendsto (λ x, (f x, f b)) (𝓝 b) (𝓤 α) :=
by rw [continuous_at, tendsto_nhds_left]

theorem continuous_at_iff_prod [topological_space β] {f : β → α} {b : β} :
  continuous_at f b ↔ tendsto (λ x : β × β, (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
⟨λ H, le_trans (H.prod_map' H) (nhds_le_uniformity _),
  λ H, continuous_at_iff'_left.2 $ H.comp $ tendsto_id.prod_mk_nhds tendsto_const_nhds⟩

theorem continuous_within_at_iff'_right [topological_space β] {f : β → α} {b : β} {s : set β} :
  continuous_within_at f s b ↔ tendsto (λ x, (f b, f x)) (𝓝[s] b) (𝓤 α) :=
by rw [continuous_within_at, tendsto_nhds_right]

theorem continuous_within_at_iff'_left [topological_space β] {f : β → α} {b : β} {s : set β} :
  continuous_within_at f s b ↔ tendsto (λ x, (f x, f b)) (𝓝[s] b) (𝓤 α) :=
by rw [continuous_within_at, tendsto_nhds_left]

theorem continuous_on_iff'_right [topological_space β] {f : β → α} {s : set β} :
  continuous_on f s ↔ ∀ b ∈ s, tendsto (λ x, (f b, f x)) (𝓝[s] b) (𝓤 α) :=
by simp [continuous_on, continuous_within_at_iff'_right]

theorem continuous_on_iff'_left [topological_space β] {f : β → α} {s : set β} :
  continuous_on f s ↔ ∀ b ∈ s, tendsto (λ x, (f x, f b)) (𝓝[s] b) (𝓤 α) :=
by simp [continuous_on, continuous_within_at_iff'_left]

theorem continuous_iff'_right [topological_space β] {f : β → α} :
  continuous f ↔ ∀ b, tendsto (λ x, (f b, f x)) (𝓝 b) (𝓤 α) :=
continuous_iff_continuous_at.trans $ forall_congr $ λ b, tendsto_nhds_right

theorem continuous_iff'_left [topological_space β] {f : β → α} :
  continuous f ↔ ∀ b, tendsto (λ x, (f x, f b)) (𝓝 b) (𝓤 α) :=
continuous_iff_continuous_at.trans $ forall_congr $ λ b, tendsto_nhds_left

end uniform

lemma filter.tendsto.congr_uniformity {α β} [uniform_space β] {f g : α → β} {l : filter α} {b : β}
  (hf : tendsto f l (𝓝 b)) (hg : tendsto (λ x, (f x, g x)) l (𝓤 β)) :
  tendsto g l (𝓝 b) :=
uniform.tendsto_nhds_right.2 $ (uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

lemma uniform.tendsto_congr {α β} [uniform_space β] {f g : α → β} {l : filter α} {b : β}
  (hfg : tendsto (λ x, (f x, g x)) l (𝓤 β)) :
  tendsto f l (𝓝 b) ↔ tendsto g l (𝓝 b) :=
⟨λ h, h.congr_uniformity hfg, λ h, h.congr_uniformity hfg.uniformity_symm⟩
