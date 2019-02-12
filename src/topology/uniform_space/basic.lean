/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Theory of uniform spaces.

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* completeness
* extension of uniform continuous functions to complete spaces
* uniform contiunuity & embedding
* totally bounded
* totally bounded ∧ complete → compact

One reason to directly formalize uniform spaces is foundational: we define ℝ as a completion of ℚ.

The central concept of uniform spaces is its uniformity: a filter relating two elements of the
space. This filter is reflexive, symmetric and transitive. So a set (i.e. a relation) in this filter
represents a 'distance': it is reflexive, symmetric and the uniformity contains a set for which the
`triangular` rule holds.

The formalization is mostly based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import order.filter order.filter.lift data.quot topology.basic topology.continuity
open set lattice filter classical
local attribute [instance] prop_decidable

set_option eqn_compiler.zeta true

universes u
section
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Sort*}

/-- The identity relation, or the graph of the identity function -/
def id_rel {α : Type*} := {p : α × α | p.1 = p.2}

@[simp] theorem mem_id_rel {a b : α} : (a, b) ∈ @id_rel α ↔ a = b := iff.rfl

@[simp] theorem id_rel_subset {s : set (α × α)} : id_rel ⊆ s ↔ ∀ a, (a, a) ∈ s :=
by simp [subset_def]; exact forall_congr (λ a, by simp)

/-- The composition of relations -/
def comp_rel {α : Type u} (r₁ r₂ : set (α×α)) := {p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

@[simp] theorem mem_comp_rel {r₁ r₂ : set (α×α)}
  {x y : α} : (x, y) ∈ comp_rel r₁ r₂ ↔ ∃ z, (x, z) ∈ r₁ ∧ (z, y) ∈ r₂ := iff.rfl

@[simp] theorem swap_id_rel : prod.swap '' id_rel = @id_rel α :=
set.ext $ assume ⟨a, b⟩, by simp [image_swap_eq_preimage_swap]; exact eq_comm

theorem monotone_comp_rel [preorder β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, comp_rel (f x) (g x)) :=
assume a b h p ⟨z, h₁, h₂⟩, ⟨z, hf h h₁, hg h h₂⟩

lemma prod_mk_mem_comp_rel {a b c : α} {s t : set (α×α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
  (a, b) ∈ comp_rel s t :=
⟨c, h₁, h₂⟩

@[simp] lemma id_comp_rel {r : set (α×α)} : comp_rel id_rel r = r :=
set.ext $ assume ⟨a, b⟩, by simp

lemma comp_rel_assoc {r s t : set (α×α)} :
  comp_rel (comp_rel r s) t = comp_rel r (comp_rel s t) :=
by ext p; cases p; simp only [mem_comp_rel]; tauto

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure uniform_space.core (α : Type u) :=
(uniformity : filter (α × α))
(refl       : principal id_rel ≤ uniformity)
(symm       : tendsto prod.swap uniformity uniformity)
(comp       : uniformity.lift' (λs, comp_rel s s) ≤ uniformity)

def uniform_space.core.mk' {α : Type u} (U : filter (α × α))
  (refl : ∀ (r ∈ U.sets) x, (x, x) ∈ r)
  (symm : ∀ r ∈ U.sets, {p | prod.swap p ∈ r} ∈ U.sets)
  (comp : ∀ r ∈ U.sets, ∃ t ∈ U.sets, comp_rel t t ⊆ r) : uniform_space.core α :=
⟨U, λ r ru, id_rel_subset.2 (refl _ ru), symm,
  begin
    intros r ru,
    rw [mem_lift'_sets],
    exact comp _ ru,
    apply monotone_comp_rel; exact monotone_id,
  end⟩

/-- A uniform space generates a topological space -/
def uniform_space.core.to_topological_space {α : Type u} (u : uniform_space.core α) :
  topological_space α :=
{ is_open        := λs, ∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ u.uniformity.sets,
  is_open_univ   := by simp; intro; exact univ_mem_sets,
  is_open_inter  :=
    assume s t hs ht x ⟨xs, xt⟩, by filter_upwards [hs x xs, ht x xt]; simp {contextual := tt},
  is_open_sUnion :=
    assume s hs x ⟨t, ts, xt⟩, by filter_upwards [hs t ts x xt] assume p ph h, ⟨t, ts, ph h⟩ }

lemma uniform_space.core_eq : ∀{u₁ u₂ : uniform_space.core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
| ⟨u₁, _, _, _⟩  ⟨u₂, _, _, _⟩ h := have u₁ = u₂, from h, by simp [*]

/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
class uniform_space (α : Type u) extends topological_space α, uniform_space.core α :=
(is_open_uniformity : ∀s, is_open s ↔ (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ uniformity.sets))

@[pattern] def uniform_space.mk' {α} (t : topological_space α)
  (c : uniform_space.core α)
  (is_open_uniformity : ∀s:set α, t.is_open s ↔
    (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ c.uniformity.sets)) :
  uniform_space α := ⟨c, is_open_uniformity⟩

def uniform_space.of_core {α : Type u} (u : uniform_space.core α) : uniform_space α :=
{ to_core := u,
  to_topological_space := u.to_topological_space,
  is_open_uniformity := assume a, iff.refl _ }

def uniform_space.of_core_eq {α : Type u} (u : uniform_space.core α) (t : topological_space α)
  (h : t = u.to_topological_space) : uniform_space α :=
{ to_core := u,
  to_topological_space := t,
  is_open_uniformity := assume a, h.symm ▸ iff.refl _ }

lemma uniform_space.to_core_to_topological_space (u : uniform_space α) :
  u.to_core.to_topological_space = u.to_topological_space :=
topological_space_eq $ funext $ assume s,
  by rw [uniform_space.core.to_topological_space, uniform_space.is_open_uniformity]

@[extensionality]
lemma uniform_space_eq : ∀{u₁ u₂ : uniform_space α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
| (uniform_space.mk' t₁ u₁ o₁)  (uniform_space.mk' t₂ u₂ o₂) h :=
  have u₁ = u₂, from uniform_space.core_eq h,
  have t₁ = t₂, from topological_space_eq $ funext $ assume s, by rw [o₁, o₂]; simp [this],
  by simp [*]

lemma uniform_space.of_core_eq_to_core
  (u : uniform_space α) (t : topological_space α) (h : t = u.to_core.to_topological_space) :
  uniform_space.of_core_eq u.to_core t h = u :=
uniform_space_eq rfl

section uniform_space
variables [uniform_space α]

/-- The uniformity is a filter on α × α (inferred from an ambient uniform space
  structure on α). -/
def uniformity : filter (α × α) := (@uniform_space.to_core α _).uniformity

lemma is_open_uniformity {s : set α} :
  is_open s ↔ (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ (@uniformity α _).sets) :=
uniform_space.is_open_uniformity s

lemma refl_le_uniformity : principal id_rel ≤ @uniformity α _ :=
(@uniform_space.to_core α _).refl

lemma refl_mem_uniformity {x : α} {s : set (α × α)} (h : s ∈ (@uniformity α _).sets) :
  (x, x) ∈ s :=
refl_le_uniformity h rfl

lemma symm_le_uniformity : map (@prod.swap α α) uniformity ≤ uniformity :=
(@uniform_space.to_core α _).symm

lemma comp_le_uniformity : uniformity.lift' (λs:set (α×α), comp_rel s s) ≤ uniformity :=
(@uniform_space.to_core α _).comp

lemma tendsto_swap_uniformity : tendsto prod.swap (@uniformity α _) uniformity :=
symm_le_uniformity

lemma tendsto_const_uniformity {a : α} {f : filter β} : tendsto (λ_, (a, a)) f uniformity :=
assume s hs,
show {x | (a, a) ∈ s} ∈ f.sets,
  from univ_mem_sets' $ assume b, refl_mem_uniformity hs

lemma comp_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, comp_rel t t ⊆ s :=
have s ∈ (uniformity.lift' (λt:set (α×α), comp_rel t t)).sets,
  from comp_le_uniformity hs,
(mem_lift'_sets $ monotone_comp_rel monotone_id monotone_id).mp this

lemma symm_of_uniformity {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, (∀a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
have preimage prod.swap s ∈ (@uniformity α _).sets, from symm_le_uniformity hs,
⟨s ∩ preimage prod.swap s, inter_mem_sets hs this, assume a b ⟨h₁, h₂⟩, ⟨h₂, h₁⟩, inter_subset_left _ _⟩

lemma comp_symm_of_uniformity {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, (∀{a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ comp_rel t t ⊆ s :=
let ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs in
let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁ in
⟨t', ht', ht'₁, subset.trans (monotone_comp_rel monotone_id monotone_id ht'₂) ht₂⟩

lemma uniformity_le_symm : uniformity ≤ (@prod.swap α α) <$> uniformity :=
by rw [map_swap_eq_comap_swap];
from map_le_iff_le_comap.1 tendsto_swap_uniformity

lemma uniformity_eq_symm : uniformity = (@prod.swap α α) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

theorem uniformity_lift_le_swap {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : uniformity.lift (λs, g (preimage prod.swap s)) ≤ f) : uniformity.lift g ≤ f :=
calc uniformity.lift g ≤ (filter.map prod.swap (@uniformity α _)).lift g :
    lift_mono uniformity_le_symm (le_refl _)
  ... ≤ _ :
    by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

lemma uniformity_lift_le_comp {f : set (α×α) → filter β} (h : monotone f):
  uniformity.lift (λs, f (comp_rel s s)) ≤ uniformity.lift f :=
calc uniformity.lift (λs, f (comp_rel s s)) =
    (uniformity.lift' (λs:set (α×α), comp_rel s s)).lift f :
  begin
    rw [lift_lift'_assoc],
    exact monotone_comp_rel monotone_id monotone_id,
    exact h
  end
  ... ≤ uniformity.lift f : lift_mono comp_le_uniformity (le_refl _)

lemma comp_le_uniformity3 :
  uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s)) ≤ uniformity :=
calc uniformity.lift' (λd, comp_rel d (comp_rel d d)) =
  uniformity.lift (λs, uniformity.lift' (λt:set(α×α), comp_rel s (comp_rel t t))) :
  begin
    rw [lift_lift'_same_eq_lift'],
    exact (assume x, monotone_comp_rel monotone_const $ monotone_comp_rel monotone_id monotone_id),
    exact (assume x, monotone_comp_rel monotone_id monotone_const),
  end
  ... ≤ uniformity.lift (λs, uniformity.lift' (λt:set(α×α), comp_rel s t)) :
    lift_mono' $ assume s hs, @uniformity_lift_le_comp α _ _ (principal ∘ comp_rel s) $
      monotone_comp (monotone_comp_rel monotone_const monotone_id) monotone_principal
  ... = uniformity.lift' (λs:set(α×α), comp_rel s s) :
    lift_lift'_same_eq_lift'
      (assume s, monotone_comp_rel monotone_const monotone_id)
      (assume s, monotone_comp_rel monotone_id monotone_const)
  ... ≤ uniformity : comp_le_uniformity

lemma mem_nhds_uniformity_iff {x : α} {s : set α} :
  s ∈ (nhds x).sets ↔ {p : α × α | p.1 = x → p.2 ∈ s} ∈ (@uniformity α _).sets :=
⟨ begin
    simp only [mem_nhds_sets_iff, is_open_uniformity, and_imp, exists_imp_distrib],
    exact assume t ts ht xt, by filter_upwards [ht x xt] assume ⟨x', y⟩ h eq, ts $ h eq
  end,

  assume hs,
  mem_nhds_sets_iff.mpr ⟨{x | {p : α × α | p.1 = x → p.2 ∈ s} ∈ (@uniformity α _).sets},
    assume x' hx', refl_mem_uniformity hx' rfl,
    is_open_uniformity.mpr $ assume x' hx',
      let ⟨t, ht, tr⟩ := comp_mem_uniformity_sets hx' in
      by filter_upwards [ht] assume ⟨a, b⟩ hp' (hax' : a = x'),
      by filter_upwards [ht] assume ⟨a, b'⟩ hp'' (hab : a = b),
      have hp : (x', b) ∈ t, from hax' ▸ hp',
      have (b, b') ∈ t, from hab ▸ hp'',
      have (x', b') ∈ comp_rel t t, from ⟨b, hp, this⟩,
      show b' ∈ s,
        from tr this rfl,
    hs⟩⟩

lemma nhds_eq_comap_uniformity {x : α} : nhds x = uniformity.comap (prod.mk x) :=
by ext s; rw [mem_nhds_uniformity_iff, mem_comap_sets]; from iff.intro
  (assume hs, ⟨_, hs, assume x hx, hx rfl⟩)
  (assume ⟨t, h, ht⟩, uniformity.sets_of_superset h $
    assume ⟨p₁, p₂⟩ hp (h : p₁ = x), ht $ by simp [h.symm, hp])

lemma nhds_eq_uniformity {x : α} : nhds x = uniformity.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :=
begin
  ext s,
  rw [mem_lift'_sets], tactic.swap, apply monotone_preimage,
  simp [mem_nhds_uniformity_iff],
  exact ⟨assume h, ⟨_, h, assume y h, h rfl⟩,
    assume ⟨t, h₁, h₂⟩,
    uniformity.sets_of_superset h₁ $
    assume ⟨x', y⟩ hp (eq : x' = x), h₂ $
    show (x, y) ∈ t, from eq ▸ hp⟩
end

lemma mem_nhds_left (x : α) {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {y : α | (x, y) ∈ s} ∈ (nhds x).sets :=
have nhds x ≤ principal {y : α | (x, y) ∈ s},
  by rw [nhds_eq_uniformity]; exact infi_le_of_le s (infi_le _ h),
by simp at this; assumption

lemma mem_nhds_right (y : α) {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {x : α | (x, y) ∈ s} ∈ (nhds y).sets :=
mem_nhds_left _ (symm_le_uniformity h)

lemma tendsto_right_nhds_uniformity {a : α} : tendsto (λa', (a', a)) (nhds a) uniformity :=
assume s, mem_nhds_right a

lemma tendsto_left_nhds_uniformity {a : α} : tendsto (λa', (a, a')) (nhds a) uniformity :=
assume s, mem_nhds_left a

lemma lift_nhds_left {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x).lift g = uniformity.lift (λs:set (α×α), g {y | (x, y) ∈ s}) :=
eq.trans
  begin
    rw [nhds_eq_uniformity],
    exact (filter.lift_assoc $ monotone_comp monotone_preimage $ monotone_comp monotone_preimage monotone_principal)
  end
  (congr_arg _ $ funext $ assume s, filter.lift_principal hg)

lemma lift_nhds_right {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x).lift g = uniformity.lift (λs:set (α×α), g {y | (y, x) ∈ s}) :=
calc (nhds x).lift g = uniformity.lift (λs:set (α×α), g {y | (x, y) ∈ s}) : lift_nhds_left hg
  ... = ((@prod.swap α α) <$> uniformity).lift (λs:set (α×α), g {y | (x, y) ∈ s}) : by rw [←uniformity_eq_symm]
  ... = uniformity.lift (λs:set (α×α), g {y | (x, y) ∈ image prod.swap s}) :
    map_lift_eq2 $ monotone_comp monotone_preimage hg
  ... = _ : by simp [image_swap_eq_preimage_swap]

lemma nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
  filter.prod (nhds a) (nhds b) =
  uniformity.lift (λs:set (α×α), uniformity.lift' (λt:set (α×α),
    set.prod {y : α | (y, a) ∈ s} {y : α | (b, y) ∈ t})) :=
begin
  rw [prod_def],
  show (nhds a).lift (λs:set α, (nhds b).lift (λt:set α, principal (set.prod s t))) = _,
  rw [lift_nhds_right],
  apply congr_arg, funext s,
  rw [lift_nhds_left],
  refl,
  exact monotone_comp (monotone_prod monotone_const monotone_id) monotone_principal,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, monotone_prod monotone_id monotone_const)
end

lemma nhds_eq_uniformity_prod {a b : α} :
  nhds (a, b) =
  uniformity.lift' (λs:set (α×α), set.prod {y : α | (y, a) ∈ s} {y : α | (b, y) ∈ s}) :=
begin
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift'],
  { intro s, exact monotone_prod monotone_const monotone_preimage },
  { intro t, exact monotone_prod monotone_preimage monotone_const }
end

lemma nhdset_of_mem_uniformity {d : set (α×α)} (s : set (α×α)) (hd : d ∈ (@uniformity α _).sets) :
  ∃(t : set (α×α)), is_open t ∧ s ⊆ t ∧ t ⊆ {p | ∃x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d} :=
let cl_d := {p:α×α | ∃x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d} in
have ∀p ∈ s, ∃t ⊆ cl_d, is_open t ∧ p ∈ t, from
  assume ⟨x, y⟩ hp, mem_nhds_sets_iff.mp $
  show cl_d ∈ (nhds (x, y)).sets,
  begin
    rw [nhds_eq_uniformity_prod, mem_lift'_sets],
    exact ⟨d, hd, assume ⟨a, b⟩ ⟨ha, hb⟩, ⟨x, y, ha, hp, hb⟩⟩,
    exact monotone_prod monotone_preimage monotone_preimage
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

lemma closure_eq_inter_uniformity {t : set (α×α)} :
  closure t = (⋂ d∈(@uniformity α _).sets, comp_rel d (comp_rel t d)) :=
set.ext $ assume ⟨a, b⟩,
calc (a, b) ∈ closure t ↔ (nhds (a, b) ⊓ principal t ≠ ⊥) : by simp [closure_eq_nhds]
  ... ↔ (((@prod.swap α α) <$> uniformity).lift'
      (λ (s : set (α × α)), set.prod {x : α | (x, a) ∈ s} {y : α | (b, y) ∈ s}) ⊓ principal t ≠ ⊥) :
    by rw [←uniformity_eq_symm, nhds_eq_uniformity_prod]
  ... ↔ ((map (@prod.swap α α) uniformity).lift'
      (λ (s : set (α × α)), set.prod {x : α | (x, a) ∈ s} {y : α | (b, y) ∈ s}) ⊓ principal t ≠ ⊥) :
    by refl
  ... ↔ (uniformity.lift'
      (λ (s : set (α × α)), set.prod {y : α | (a, y) ∈ s} {x : α | (x, b) ∈ s}) ⊓ principal t ≠ ⊥) :
  begin
    rw [map_lift'_eq2],
    simp [image_swap_eq_preimage_swap, function.comp],
    exact monotone_prod monotone_preimage monotone_preimage
  end
  ... ↔ (∀s∈(@uniformity α _).sets, ∃x, x ∈ set.prod {y : α | (a, y) ∈ s} {x : α | (x, b) ∈ s} ∩ t) :
  begin
    rw [lift'_inf_principal_eq, lift'_neq_bot_iff],
    apply forall_congr, intro s, rw [ne_empty_iff_exists_mem],
    exact monotone_inter (monotone_prod monotone_preimage monotone_preimage) monotone_const
  end
  ... ↔ (∀s∈(@uniformity α _).sets, (a, b) ∈ comp_rel s (comp_rel t s)) :
    forall_congr $ assume s, forall_congr $ assume hs,
    ⟨assume ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxyt⟩⟩, ⟨x, hx, y, hxyt, hy⟩,
      assume ⟨x, hx, y, hxyt, hy⟩, ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxyt⟩⟩⟩
  ... ↔ _ : by simp

lemma uniformity_eq_uniformity_closure : (@uniformity α _) = uniformity.lift' closure :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, by simp; filter_upwards [hs] subset_closure)
  (calc uniformity.lift' closure ≤ uniformity.lift' (λd, comp_rel d (comp_rel d d)) :
      lift'_mono' (by intros s hs; rw [closure_eq_inter_uniformity]; exact bInter_subset_of_mem hs)
    ... ≤ uniformity : comp_le_uniformity3)

lemma uniformity_eq_uniformity_interior : (@uniformity α _) = uniformity.lift' interior :=
le_antisymm
  (le_infi $ assume d, le_infi $ assume hd,
    let ⟨s, hs, hs_comp⟩ := (mem_lift'_sets $
      monotone_comp_rel monotone_id $ monotone_comp_rel monotone_id monotone_id).mp (comp_le_uniformity3 hd) in
    let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs in
    have s ⊆ interior d, from
      calc s ⊆ t : hst
       ... ⊆ interior d : (subset_interior_iff_subset_of_open ht).mpr $
        assume x, assume : x ∈ t, let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp this in hs_comp ⟨x, h₁, y, h₂, h₃⟩,
    have interior d ∈ (@uniformity α _).sets, by filter_upwards [hs] this,
    by simp [this])
  (assume s hs, (uniformity.lift' interior).sets_of_superset (mem_lift' hs) interior_subset)

lemma interior_mem_uniformity {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  interior s ∈ (@uniformity α _).sets :=
by rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

lemma mem_uniformity_is_closed [uniform_space α] {s : set (α×α)} (h : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, is_closed t ∧ t ⊆ s :=
have s ∈ ((@uniformity α _).lift' closure).sets, by rwa [uniformity_eq_uniformity_closure] at h,
have ∃t∈(@uniformity α _).sets, closure t ⊆ s,
  by rwa [mem_lift'_sets] at this; apply closure_mono,
let ⟨t, ht, hst⟩ := this in
⟨closure t, uniformity.sets_of_superset ht subset_closure, is_closed_closure, hst⟩

/- uniform continuity -/

def uniform_continuous [uniform_space β] (f : α → β) :=
tendsto (λx:α×α, (f x.1, f x.2)) uniformity uniformity

theorem uniform_continuous_def [uniform_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ r ∈ (@uniformity β _).sets,
    {x : α × α | (f x.1, f x.2) ∈ r} ∈ (@uniformity α _).sets :=
iff.rfl

lemma uniform_continuous_of_const [uniform_space β] {c : α → β} (h : ∀a b, c a = c b) :
  uniform_continuous c :=
have (λ (x : α × α), (c (x.fst), c (x.snd))) ⁻¹' id_rel = univ, from
  eq_univ_iff_forall.2 $ assume ⟨a, b⟩, h a b,
le_trans (map_le_iff_le_comap.2 $ by simp [comap_principal, this, univ_mem_sets]) refl_le_uniformity

lemma uniform_continuous_id : uniform_continuous (@id α) :=
by simp [uniform_continuous]; exact tendsto_id

lemma uniform_continuous_const [uniform_space β] {b : β} : uniform_continuous (λa:α, b) :=
@tendsto_const_uniformity _ _ _ b uniformity

lemma uniform_continuous.comp [uniform_space β] [uniform_space γ] {f : α → β} {g : β → γ}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (g ∘ f) :=
hf.comp hg

def uniform_embedding [uniform_space β] (f : α → β) :=
function.injective f ∧
comap (λx:α×α, (f x.1, f x.2)) uniformity = uniformity

theorem uniform_embedding_def [uniform_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ ∀ s, s ∈ (@uniformity α _).sets ↔
    ∃ t ∈ (@uniformity β _).sets, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s :=
by rw [uniform_embedding, eq_comm, filter.ext_iff]; simp [subset_def]

theorem uniform_embedding_def' [uniform_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ s, s ∈ (@uniformity α _).sets →
      ∃ t ∈ (@uniformity β _).sets, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s :=
by simp [uniform_embedding_def, uniform_continuous_def]; exact
⟨λ ⟨I, H⟩, ⟨I, λ s su, (H _).2 ⟨s, su, λ x y, id⟩, λ s, (H s).1⟩,
 λ ⟨I, H₁, H₂⟩, ⟨I, λ s, ⟨H₂ s,
   λ ⟨t, tu, h⟩, sets_of_superset _ (H₁ t tu) (λ ⟨a, b⟩, h a b)⟩⟩⟩

lemma uniform_embedding.uniform_continuous [uniform_space β] {f : α → β}
  (hf : uniform_embedding f) : uniform_continuous f :=
(uniform_embedding_def'.1 hf).2.1

lemma uniform_embedding.uniform_continuous_iff [uniform_space β] [uniform_space γ] {f : α → β}
  {g : β → γ} (hg : uniform_embedding g) : uniform_continuous f ↔ uniform_continuous (g ∘ f) :=
by simp [uniform_continuous, tendsto]; rw [← hg.2, ← map_le_iff_le_comap, filter.map_map]

lemma uniform_embedding.embedding [uniform_space β] {f : α → β} (h : uniform_embedding f) : embedding f :=
begin
  refine ⟨h.left, eq_of_nhds_eq_nhds $ assume a, _⟩,
  rw [nhds_induced_eq_comap, nhds_eq_uniformity, nhds_eq_uniformity, ← h.right,
    comap_lift'_eq, comap_lift'_eq2];
    { refl <|> exact monotone_preimage }
end

lemma uniform_embedding.dense_embedding [uniform_space β] {f : α → β}
  (h : uniform_embedding f) (hd : ∀x, x ∈ closure (range f)) : dense_embedding f :=
{ dense   := hd,
  inj     := h.left,
  induced := assume a, by rw [h.embedding.2, nhds_induced_eq_comap] }

lemma uniform_continuous.continuous [uniform_space β] {f : α → β}
  (hf : uniform_continuous f) : continuous f :=
continuous_iff_continuous_at.mpr $ assume a,
calc map f (nhds a) ≤
    (map (λp:α×α, (f p.1, f p.2)) uniformity).lift' (λs:set (β×β), {y | (f a, y) ∈ s}) :
  begin
    rw [nhds_eq_uniformity, map_lift'_eq, map_lift'_eq2],
    exact (lift'_mono' $ assume s hs b ⟨a', (ha' : (_, a') ∈ s), a'_eq⟩,
      ⟨(a, a'), ha', show (f a, f a') = (f a, b), from a'_eq ▸ rfl⟩),
    exact monotone_preimage,
    exact monotone_preimage
  end
  ... ≤ nhds (f a) :
    by rw [nhds_eq_uniformity]; exact lift'_mono hf (le_refl _)

lemma closure_image_mem_nhds_of_uniform_embedding
  [uniform_space α] [uniform_space β] {s : set (α×α)} {e : α → β} (b : β)
  (he₁ : uniform_embedding e) (he₂ : dense_embedding e) (hs : s ∈ (@uniformity α _).sets) :
  ∃a, closure (e '' {a' | (a, a') ∈ s}) ∈ (nhds b).sets :=
have s ∈ (comap (λp:α×α, (e p.1, e p.2)) $ uniformity).sets,
  from he₁.right.symm ▸ hs,
let ⟨t₁, ht₁u, ht₁⟩ := this in
have ht₁ : ∀p:α×α, (e p.1, e p.2) ∈ t₁ → p ∈ s, from ht₁,
let ⟨t₂, ht₂u, ht₂s, ht₂c⟩ := comp_symm_of_uniformity ht₁u in
let ⟨t, htu, hts, htc⟩ := comp_symm_of_uniformity ht₂u in
have preimage e {b' | (b, b') ∈ t₂} ∈ (comap e $ nhds b).sets,
  from preimage_mem_comap $ mem_nhds_left b ht₂u,
let ⟨a, (ha : (b, e a) ∈ t₂)⟩ := inhabited_of_mem_sets (he₂.comap_nhds_neq_bot) this in
have ∀b' (s' : set (β × β)), (b, b') ∈ t → s' ∈ (@uniformity β _).sets →
  {y : β | (b', y) ∈ s'} ∩ e '' {a' : α | (a, a') ∈ s} ≠ ∅,
  from assume b' s' hb' hs',
  have preimage e {b'' | (b', b'') ∈ s' ∩ t} ∈ (comap e $ nhds b').sets,
    from preimage_mem_comap $ mem_nhds_left b' $ inter_mem_sets hs' htu,
  let ⟨a₂, ha₂s', ha₂t⟩ := inhabited_of_mem_sets (he₂.comap_nhds_neq_bot) this in
  have (e a, e a₂) ∈ t₁,
    from ht₂c $ prod_mk_mem_comp_rel (ht₂s ha) $ htc $ prod_mk_mem_comp_rel hb' ha₂t,
  have e a₂ ∈ {b'':β | (b', b'') ∈ s'} ∩ e '' {a' | (a, a') ∈ s},
    from ⟨ha₂s', mem_image_of_mem _ $ ht₁ (a, a₂) this⟩,
  ne_empty_of_mem this,
have ∀b', (b, b') ∈ t → nhds b' ⊓ principal (e '' {a' | (a, a') ∈ s}) ≠ ⊥,
begin
  intros b' hb',
  rw [nhds_eq_uniformity, lift'_inf_principal_eq, lift'_neq_bot_iff],
  exact assume s, this b' s hb',
  exact monotone_inter monotone_preimage monotone_const
end,
have ∀b', (b, b') ∈ t → b' ∈ closure (e '' {a' | (a, a') ∈ s}),
  from assume b' hb', by rw [closure_eq_nhds]; exact this b' hb',
⟨a, (nhds b).sets_of_superset (mem_nhds_left b htu) this⟩

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def cauchy (f : filter α) := f ≠ ⊥ ∧ filter.prod f f ≤ uniformity

def is_complete (s : set α) := ∀f, cauchy f → f ≤ principal s → ∃x∈s, f ≤ nhds x

lemma cauchy_iff [uniform_space α] {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀s∈(@uniformity α _).sets, ∃t∈f.sets, set.prod t t ⊆ s)) :=
and_congr (iff.refl _) $ forall_congr $ assume s, forall_congr $ assume hs, mem_prod_same_iff

lemma cauchy_map_iff [uniform_space α] {l : filter β} {f : β → α} :
  cauchy (l.map f) ↔ (l ≠ ⊥ ∧ tendsto (λp:β×β, (f p.1, f p.2)) (l.prod l) uniformity) :=
by rw [cauchy, (≠), map_eq_bot_iff, prod_map_map_eq]; refl

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (hg : g ≠ ⊥) (h_le : g ≤ f) : cauchy g :=
⟨hg, le_trans (filter.prod_mono h_le h_le) h_c.right⟩

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
⟨nhds_neq_bot,
  calc filter.prod (nhds a) (nhds a) =
    uniformity.lift (λs:set (α×α), uniformity.lift' (λt:set(α×α),
      set.prod {y : α | (y, a) ∈ s} {y : α | (a, y) ∈ t})) : nhds_nhds_eq_uniformity_uniformity_prod
    ... ≤ uniformity.lift' (λs:set (α×α), comp_rel s s) :
      le_infi $ assume s, le_infi $ assume hs,
      infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le_of_le hs $
      principal_mono.mpr $
      assume ⟨x, y⟩ ⟨(hx : (x, a) ∈ s), (hy : (a, y) ∈ s)⟩, ⟨a, hx, hy⟩
    ... ≤ uniformity : comp_le_uniformity⟩

lemma cauchy_pure {a : α} : cauchy (pure a) :=
cauchy_downwards cauchy_nhds
  (show principal {a} ≠ ⊥, by simp)
  (pure_le_nhds a)

lemma le_nhds_of_cauchy_adhp {f : filter α} {x : α} (hf : cauchy f)
  (adhs : f ⊓ nhds x ≠ ⊥) : f ≤ nhds x :=
have ∀s∈f.sets, x ∈ closure s,
begin
  intros s hs,
  simp [closure_eq_nhds, inf_comm],
  exact assume h', adhs $ bot_unique $ h' ▸ inf_le_inf (by simp; exact hs) (le_refl _)
end,
calc f ≤ f.lift' (λs:set α, {y | x ∈ closure s ∧ y ∈ closure s}) :
    le_infi $ assume s, le_infi $ assume hs,
    begin
      rw [←forall_sets_neq_empty_iff_neq_bot] at adhs,
      simp [this s hs],
      exact mem_sets_of_superset hs subset_closure
    end
  ... ≤ f.lift' (λs:set α, {y | (x, y) ∈ closure (set.prod s s)}) :
    by simp [closure_prod_eq]; exact le_refl _
  ... = (filter.prod f f).lift' (λs:set (α×α), {y | (x, y) ∈ closure s}) :
  begin
    rw [prod_same_eq],
    rw [lift'_lift'_assoc],
    exact monotone_prod monotone_id monotone_id,
    exact monotone_comp (assume s t h x h', closure_mono h h') monotone_preimage
  end
  ... ≤ uniformity.lift' (λs:set (α×α), {y | (x, y) ∈ closure s}) : lift'_mono hf.right (le_refl _)
  ... = (uniformity.lift' closure).lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
  begin
    rw [lift'_lift'_assoc],
    exact assume s t h, closure_mono h,
    exact monotone_preimage
  end
  ... = uniformity.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
    by rw [←uniformity_eq_uniformity_closure]
  ... = nhds x :
    by rw [nhds_eq_uniformity]

lemma le_nhds_iff_adhp_of_cauchy {f : filter α} {x : α} (hf : cauchy f) :
  f ≤ nhds x ↔ f ⊓ nhds x ≠ ⊥ :=
⟨assume h, (inf_of_le_left h).symm ▸ hf.left,
le_nhds_of_cauchy_adhp hf⟩

lemma cauchy_map [uniform_space β] {f : filter α} {m : α → β}
  (hm : uniform_continuous m) (hf : cauchy f) : cauchy (map m f) :=
⟨have f ≠ ⊥, from hf.left, by simp; assumption,
  calc filter.prod (map m f) (map m f) =
          map (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_map_map_eq
    ... ≤ map (λp:α×α, (m p.1, m p.2)) uniformity : map_mono hf.right
    ... ≤ uniformity : hm⟩

lemma cauchy_comap [uniform_space β] {f : filter β} {m : α → β}
  (hm : comap (λp:α×α, (m p.1, m p.2)) uniformity ≤ uniformity)
  (hf : cauchy f) (hb : comap m f ≠ ⊥) : cauchy (comap m f) :=
⟨hb,
  calc filter.prod (comap m f) (comap m f) =
          comap (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_comap_comap_eq
    ... ≤ comap (λp:α×α, (m p.1, m p.2)) uniformity : comap_mono hf.right
    ... ≤ uniformity : hm⟩

/-- A set is complete iff its image under a uniform embedding is complete. -/
lemma is_complete_image_iff [uniform_space β] {m : α → β} {s : set α}
  (hm : uniform_embedding m) : is_complete (m '' s) ↔ is_complete s :=
begin
  refine ⟨λ c f hf fs, _, λ c f hf fs, _⟩,
  { let f' := map m f,
    have cf' : cauchy f' := cauchy_map (uniform_embedding.uniform_continuous hm) hf,
    have f's : f' ≤ principal (m '' s),
    { simp only [filter.le_principal_iff, set.mem_image, filter.mem_map],
      exact mem_sets_of_superset (filter.le_principal_iff.1 fs) (λx hx, ⟨x, hx, rfl⟩) },
    rcases c f' cf' f's with ⟨y, yms, hy⟩,
    rcases mem_image_iff_bex.1 yms with ⟨x, xs, rfl⟩,
    rw [map_le_iff_le_comap, ← nhds_induced_eq_comap, ← (uniform_embedding.embedding hm).2] at hy,
    exact ⟨x, xs, hy⟩ },
  { rw filter.le_principal_iff at fs,
    let f' := comap m f,
    have cf' : cauchy f',
    { have : comap m f ≠ ⊥,
      { refine comap_neq_bot (λt ht, _),
        have A : t ∩ m '' s ∈ f.sets := filter.inter_mem_sets ht fs,
        have : t ∩ m '' s ≠ ∅,
        { by_contradiction h,
          simp only [not_not, ne.def] at h,
          simpa [h, empty_in_sets_eq_bot, hf.1] using A },
        rcases ne_empty_iff_exists_mem.1 this with ⟨x, ⟨xt, xms⟩⟩,
        rcases mem_image_iff_bex.1 xms with ⟨y, ys, yx⟩,
        rw ← yx at xt,
        exact ⟨y, xt⟩ },
      apply cauchy_comap _ hf this,
      simp only [hm.2, le_refl] },
    have : f' ≤ principal s := by simp [f']; exact
      ⟨m '' s, by simpa using fs, by simp [preimage_image_eq s hm.1]⟩,
    rcases c f' cf' this with ⟨x, xs, hx⟩,
    existsi [m x, mem_image_of_mem m xs],
    rw [(uniform_embedding.embedding hm).2, nhds_induced_eq_comap] at hx,
    calc f = map m f' : (map_comap $ filter.mem_sets_of_superset fs $ image_subset_range _ _).symm
      ... ≤ map m (comap m (nhds (m x))) : map_mono hx
      ... ≤ nhds (m x) : map_comap_le }
end

/- separated uniformity -/

/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def separation_rel (α : Type u) [u : uniform_space α] :=
⋂₀ (@uniformity α _).sets

lemma separated_equiv : equivalence (λx y, (x, y) ∈ separation_rel α) :=
⟨assume x, assume s, refl_mem_uniformity,
  assume x y, assume h (s : set (α×α)) hs,
    have preimage prod.swap s ∈ (@uniformity α _).sets,
      from symm_le_uniformity hs,
    h _ this,
  assume x y z (hxy : (x, y) ∈ separation_rel α) (hyz : (y, z) ∈ separation_rel α)
      s (hs : s ∈ (@uniformity α _).sets),
    let ⟨t, ht, (h_ts : comp_rel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs in
    h_ts $ show (x, z) ∈ comp_rel t t,
      from ⟨y, hxy t ht, hyz t ht⟩⟩

@[class] def separated (α : Type u) [uniform_space α] :=
separation_rel α = id_rel

theorem separated_def {α : Type u} [uniform_space α] :
  separated α ↔ ∀ x y, (∀ r ∈ (@uniformity α _).sets, (x, y) ∈ r) → x = y :=
by simp [separated, id_rel_subset.2 separated_equiv.1, subset.antisymm_iff];
   simp [subset_def, separation_rel]

theorem separated_def' {α : Type u} [uniform_space α] :
  separated α ↔ ∀ x y, x ≠ y → ∃ r ∈ (@uniformity α _).sets, (x, y) ∉ r :=
separated_def.trans $ forall_congr $ λ x, forall_congr $ λ y,
by rw ← not_imp_not; simp [classical.not_forall]

instance separated_t2 [s : separated α] : t2_space α :=
⟨assume x y, assume h : x ≠ y,
let ⟨d, hd, (hxy : (x, y) ∉ d)⟩ := separated_def'.1 s x y h in
let ⟨d', hd', (hd'd' : comp_rel d' d' ⊆ d)⟩ := comp_mem_uniformity_sets hd in
have {y | (x, y) ∈ d'} ∈ (nhds x).sets,
  from mem_nhds_left x hd',
let ⟨u, hu₁, hu₂, hu₃⟩ := mem_nhds_sets_iff.mp this in
have {x | (x, y) ∈ d'} ∈ (nhds y).sets,
  from mem_nhds_right y hd',
let ⟨v, hv₁, hv₂, hv₃⟩ := mem_nhds_sets_iff.mp this in
have u ∩ v = ∅, from
  eq_empty_of_subset_empty $
  assume z ⟨(h₁ : z ∈ u), (h₂ : z ∈ v)⟩,
  have (x, y) ∈ comp_rel d' d', from ⟨z, hu₁ h₁, hv₁ h₂⟩,
  hxy $ hd'd' this,
⟨u, v, hu₂, hv₂, hu₃, hv₃, this⟩⟩

instance separated_regular [separated α] : regular_space α :=
{ regular := λs a hs ha,
    have -s ∈ (nhds a).sets,
      from mem_nhds_sets hs ha,
    have {p : α × α | p.1 = a → p.2 ∈ -s} ∈ uniformity.sets,
      from mem_nhds_uniformity_iff.mp this,
    let ⟨d, hd, h⟩ := comp_mem_uniformity_sets this in
    let e := {y:α| (a, y) ∈ d} in
    have hae : a ∈ closure e, from subset_closure $ refl_mem_uniformity hd,
    have set.prod (closure e) (closure e) ⊆ comp_rel d (comp_rel (set.prod e e) d),
    begin
      rw [←closure_prod_eq, closure_eq_inter_uniformity],
      change (⨅d' ∈ uniformity.sets, _) ≤ comp_rel d (comp_rel _ d),
      exact (infi_le_of_le d $ infi_le_of_le hd $ le_refl _)
    end,
    have e_subset : closure e ⊆ -s,
      from assume a' ha',
        let ⟨x, (hx : (a, x) ∈ d), y, ⟨hx₁, hx₂⟩, (hy : (y, _) ∈ d)⟩ := @this ⟨a, a'⟩ ⟨hae, ha'⟩ in
        have (a, a') ∈ comp_rel d d, from ⟨y, hx₂, hy⟩,
        h this rfl,
    have closure e ∈ (nhds a).sets, from (nhds a).sets_of_superset (mem_nhds_left a hd) subset_closure,
    have nhds a ⊓ principal (-closure e) = ⊥,
      from (@inf_eq_bot_iff_le_compl _ _ _ (principal (- closure e)) (principal (closure e))
        (by simp [principal_univ, union_comm]) (by simp)).mpr (by simp [this]),
    ⟨- closure e, is_closed_closure, assume x h₁ h₂, @e_subset x h₂ h₁, this⟩,
  ..separated_t2 }

/-In a separated space, a complete set is closed -/
lemma is_closed_of_is_complete [separated α] {s : set α} (h : is_complete s) : is_closed s :=
is_closed_iff_nhds.2 $ λ a ha, begin
  let f := nhds a ⊓ principal s,
  have : cauchy f := cauchy_downwards (cauchy_nhds) ha (lattice.inf_le_left),
  rcases h f this (lattice.inf_le_right) with ⟨y, ys, fy⟩,
  rwa (tendsto_nhds_unique ha lattice.inf_le_left fy : a = y)
end

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def totally_bounded (s : set α) : Prop :=
∀d ∈ (@uniformity α _).sets, ∃t : set α, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d})

theorem totally_bounded_iff_subset {s : set α} : totally_bounded s ↔
  ∀d ∈ (@uniformity α _).sets, ∃t ⊆ s, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}) :=
⟨λ H d hd, begin
  rcases comp_symm_of_uniformity hd with ⟨r, hr, rs, rd⟩,
  rcases H r hr with ⟨k, fk, ks⟩,
  let u := {y ∈ k | ∃ x, x ∈ s ∧ (x, y) ∈ r},
  let f : u → α := λ x, classical.some x.2.2,
  have : ∀ x : u, f x ∈ s ∧ (f x, x.1) ∈ r := λ x, classical.some_spec x.2.2,
  refine ⟨range f, _, _, _⟩,
  { exact range_subset_iff.2 (λ x, (this x).1) },
  { have : finite u := finite_subset fk (λ x h, h.1),
    exact ⟨@set.fintype_range _ _ _ _ this.fintype⟩ },
  { intros x xs,
    have := ks xs, simp at this,
    rcases this with ⟨y, hy, xy⟩,
    let z : coe_sort u := ⟨y, hy, x, xs, xy⟩,
    exact mem_bUnion_iff.2 ⟨_, ⟨z, rfl⟩, rd $ mem_comp_rel.2 ⟨_, xy, rs (this z).2⟩⟩ }
end,
λ H d hd, let ⟨t, _, ht⟩ := H d hd in ⟨t, ht⟩⟩

lemma totally_bounded_subset [uniform_space α] {s₁ s₂ : set α} (hs : s₁ ⊆ s₂)
  (h : totally_bounded s₂) : totally_bounded s₁ :=
assume d hd, let ⟨t, ht₁, ht₂⟩ := h d hd in ⟨t, ht₁, subset.trans hs ht₂⟩

lemma totally_bounded_empty [uniform_space α] : totally_bounded (∅ : set α) :=
λ d hd, ⟨∅, finite_empty, empty_subset _⟩

lemma totally_bounded_closure [uniform_space α] {s : set α} (h : totally_bounded s) :
  totally_bounded (closure s) :=
assume t ht,
let ⟨t', ht', hct', htt'⟩ := mem_uniformity_is_closed ht, ⟨c, hcf, hc⟩ := h t' ht' in
⟨c, hcf,
  calc closure s ⊆ closure (⋃ (y : α) (H : y ∈ c), {x : α | (x, y) ∈ t'}) : closure_mono hc
    ... = _ : closure_eq_of_is_closed $ is_closed_Union hcf $ assume i hi,
      continuous_iff_is_closed.mp (continuous_id.prod_mk continuous_const) _ hct'
    ... ⊆ _ : bUnion_subset $ assume i hi, subset.trans (assume x, @htt' (x, i))
      (subset_bUnion_of_mem hi)⟩

lemma totally_bounded_image [uniform_space α] [uniform_space β] {f : α → β} {s : set α}
  (hf : uniform_continuous f) (hs : totally_bounded s) : totally_bounded (f '' s) :=
assume t ht,
have {p:α×α | (f p.1, f p.2) ∈ t} ∈ (@uniformity α _).sets,
  from hf ht,
let ⟨c, hfc, hct⟩ := hs _ this in
⟨f '' c, finite_image f hfc,
  begin
    simp [image_subset_iff],
    simp [subset_def] at hct,
    intros x hx, simp [-mem_image],
    exact let ⟨i, hi, ht⟩ := hct x hx in ⟨f i, mem_image_of_mem f hi, ht⟩
  end⟩

lemma totally_bounded_preimage [uniform_space α] [uniform_space β] {f : α → β} {s : set β}
  (hf : uniform_embedding f) (hs : totally_bounded s) : totally_bounded (f ⁻¹' s) :=
λ t ht, begin
  rw ← hf.2 at ht,
  rcases mem_comap_sets.2 ht with ⟨t', ht', ts⟩,
  rcases totally_bounded_iff_subset.1
    (totally_bounded_subset (image_preimage_subset f s) hs) _ ht' with ⟨c, cs, hfc, hct⟩,
  refine ⟨f ⁻¹' c, finite_preimage hf.1 hfc, λ x h, _⟩,
  have := hct (mem_image_of_mem f h), simp at this ⊢,
  rcases this with ⟨z, zc, zt⟩,
  rcases cs zc with ⟨y, yc, rfl⟩,
  exact ⟨y, zc, ts (by exact zt)⟩
end

lemma cauchy_of_totally_bounded_of_ultrafilter {s : set α} {f : filter α}
  (hs : totally_bounded s) (hf : is_ultrafilter f) (h : f ≤ principal s) : cauchy f :=
⟨hf.left, assume t ht,
  let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht in
  let ⟨i, hi, hs_union⟩ := hs t' ht'₁ in
  have (⋃y∈i, {x | (x,y) ∈ t'}) ∈ f.sets,
    from mem_sets_of_superset (le_principal_iff.mp h) hs_union,
  have ∃y∈i, {x | (x,y) ∈ t'} ∈ f.sets,
    from mem_of_finite_Union_ultrafilter hf hi this,
  let ⟨y, hy, hif⟩ := this in
  have set.prod {x | (x,y) ∈ t'} {x | (x,y) ∈ t'} ⊆ comp_rel t' t',
    from assume ⟨x₁, x₂⟩ ⟨(h₁ : (x₁, y) ∈ t'), (h₂ : (x₂, y) ∈ t')⟩,
      ⟨y, h₁, ht'_symm h₂⟩,
  (filter.prod f f).sets_of_superset (prod_mem_prod hif hif) (subset.trans this ht'_t)⟩

lemma totally_bounded_iff_filter {s : set α} :
  totally_bounded s ↔ (∀f, f ≠ ⊥ → f ≤ principal s → ∃c ≤ f, cauchy c) :=
⟨assume : totally_bounded s, assume f hf hs,
  ⟨ultrafilter_of f, ultrafilter_of_le,
    cauchy_of_totally_bounded_of_ultrafilter this
      (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hs)⟩,

  assume h : ∀f, f ≠ ⊥ → f ≤ principal s → ∃c ≤ f, cauchy c, assume d hd,
  classical.by_contradiction $ assume hs,
  have hd_cover : ∀{t:set α}, finite t → ¬ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}),
    by simpa using hs,
  let
    f := ⨅t:{t : set α // finite t}, principal (s \ (⋃y∈t.val, {x | (x,y) ∈ d})),
    ⟨a, ha⟩ := @exists_mem_of_ne_empty α s
      (assume h, hd_cover finite_empty $ h.symm ▸ empty_subset _)
  in
  have f ≠ ⊥,
    from infi_neq_bot_of_directed ⟨a⟩
      (assume ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩, ⟨⟨t₁ ∪ t₂, finite_union ht₁ ht₂⟩,
        principal_mono.mpr $ diff_subset_diff_right $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inl,
        principal_mono.mpr $ diff_subset_diff_right $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inr⟩)
      (assume ⟨t, ht⟩, by simp [diff_eq_empty]; exact hd_cover ht),
  have f ≤ principal s, from infi_le_of_le ⟨∅, finite_empty⟩ $ by simp; exact subset.refl s,
  let
    ⟨c, (hc₁ : c ≤ f), (hc₂ : cauchy c)⟩ := h f ‹f ≠ ⊥› this,
    ⟨m, hm, (hmd : set.prod m m ⊆ d)⟩ := (@mem_prod_same_iff α c d).mp $ hc₂.right hd
  in
  have c ≤ principal s, from le_trans ‹c ≤ f› this,
  have m ∩ s ∈ c.sets, from inter_mem_sets hm $ le_principal_iff.mp this,
  let ⟨y, hym, hys⟩ := inhabited_of_mem_sets hc₂.left this in
  let ys := (⋃y'∈({y}:set α), {x | (x, y') ∈ d}) in
  have m ⊆ ys,
    from assume y' hy',
      show  y' ∈ (⋃y'∈({y}:set α), {x | (x, y') ∈ d}),
        by simp; exact @hmd (y', y) ⟨hy', hym⟩,
  have c ≤ principal (s - ys),
    from le_trans hc₁ $ infi_le_of_le ⟨{y}, finite_singleton _⟩ $ le_refl _,
  have (s - ys) ∩ (m ∩ s) ∈ c.sets,
    from inter_mem_sets (le_principal_iff.mp this) ‹m ∩ s ∈ c.sets›,
  have ∅ ∈ c.sets,
    from c.sets_of_superset this $ assume x ⟨⟨hxs, hxys⟩, hxm, _⟩, hxys $ ‹m ⊆ ys› hxm,
  hc₂.left $ empty_in_sets_eq_bot.mp this⟩

lemma totally_bounded_iff_ultrafilter {s : set α} :
  totally_bounded s ↔ (∀f, is_ultrafilter f → f ≤ principal s → cauchy f) :=
⟨assume hs f, cauchy_of_totally_bounded_of_ultrafilter hs,
  assume h, totally_bounded_iff_filter.mpr $ assume f hf hfs,
  have cauchy (ultrafilter_of f),
    from h (ultrafilter_of f) (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hfs),
  ⟨ultrafilter_of f, ultrafilter_of_le, this⟩⟩

lemma compact_iff_totally_bounded_complete {s : set α} :
  compact s ↔ totally_bounded s ∧ is_complete s :=
⟨λ hs, ⟨totally_bounded_iff_ultrafilter.2 (λ f hf1 hf2,
    let ⟨x, xs, fx⟩ := compact_iff_ultrafilter_le_nhds.1 hs f hf1 hf2 in
    cauchy_downwards (cauchy_nhds) (hf1.1) fx),
  λ f fc fs,
    let ⟨a, as, fa⟩ := hs f fc.1 fs in
    ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
λ ⟨ht, hc⟩, compact_iff_ultrafilter_le_nhds.2
  (λf hf hfs, hc _ (totally_bounded_iff_ultrafilter.1 ht _ hf hfs) hfs)⟩

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def cauchy_seq [inhabited β] [semilattice_sup β] (u : β → α) := cauchy (at_top.map u)

lemma cauchy_seq_iff_prod_map [inhabited β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ map (prod.map u u) at_top ≤ uniformity :=
iff.trans (and_iff_right (map_ne_bot at_top_ne_bot)) (prod_map_at_top_eq u u ▸ iff.rfl)

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class complete_space (α : Type u) [uniform_space α] : Prop :=
(complete : ∀{f:filter α}, cauchy f → ∃x, f ≤ nhds x)

lemma complete_univ {α : Type u} [uniform_space α] [complete_space α] :
  is_complete (univ : set α) :=
begin
  assume f hf _,
  rcases complete_space.complete hf with ⟨x, hx⟩,
  exact ⟨x, by simp, hx⟩
end

/--If `univ` is complete, the space is a complete space -/
lemma complete_space_of_is_complete_univ (h : is_complete (univ : set α)) : complete_space α :=
⟨λ f hf, let ⟨x, _, hx⟩ := h f hf ((@principal_univ α).symm ▸ le_top) in ⟨x, hx⟩⟩

lemma cauchy_iff_exists_le_nhds [uniform_space α] [complete_space α] {l : filter α} (hl : l ≠ ⊥) :
  cauchy l ↔ (∃x, l ≤ nhds x) :=
⟨complete_space.complete, assume ⟨x, hx⟩, cauchy_downwards cauchy_nhds hl hx⟩

lemma cauchy_map_iff_exists_tendsto [uniform_space α] [complete_space α] {l : filter β} {f : β → α}
  (hl : l ≠ ⊥) : cauchy (l.map f) ↔ (∃x, tendsto f l (nhds x)) :=
cauchy_iff_exists_le_nhds (map_ne_bot hl)

/-- A Cauchy sequence in a complete space converges -/
theorem cauchy_seq_tendsto_of_complete [inhabited β] [semilattice_sup β] [complete_space α]
  {u : β → α} (H : cauchy_seq u) : ∃x, tendsto u at_top (nhds x) :=
complete_space.complete H

theorem le_nhds_lim_of_cauchy {α} [uniform_space α] [complete_space α]
  [inhabited α] {f : filter α} (hf : cauchy f) : f ≤ nhds (lim f) :=
lim_spec (complete_space.complete hf)

lemma is_complete_of_is_closed [complete_space α] {s : set α}
  (h : is_closed s) : is_complete s :=
λ f cf fs, let ⟨x, hx⟩ := complete_space.complete cf in
⟨x, is_closed_iff_nhds.mp h x (neq_bot_of_le_neq_bot cf.left (le_inf hx fs)), hx⟩

instance complete_of_compact {α : Type u} [uniform_space α] [compact_space α] : complete_space α :=
⟨λf hf, by simpa [principal_univ] using (compact_iff_totally_bounded_complete.1 compact_univ).2 f hf⟩

lemma compact_of_totally_bounded_is_closed [complete_space α] {s : set α}
  (ht : totally_bounded s) (hc : is_closed s) : compact s :=
(@compact_iff_totally_bounded_complete α _ s).2 ⟨ht, is_complete_of_is_closed hc⟩

lemma complete_space_extension [uniform_space β] {m : β → α}
  (hm : uniform_embedding m)
  (dense : ∀x, x ∈ closure (range m))
  (h : ∀f:filter β, cauchy f → ∃x:α, map m f ≤ nhds x) :
  complete_space α :=
⟨assume (f : filter α), assume hf : cauchy f,
let
  p : set (α × α) → set α → set α := λs t, {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s},
  g := uniformity.lift (λs, f.lift' (p s))
in
have mp₀ : monotone p,
  from assume a b h t s ⟨x, xs, xa⟩, ⟨x, xs, h xa⟩,
have mp₁ : ∀{s}, monotone (p s),
  from assume s a b h x ⟨y, ya, yxs⟩, ⟨y, h ya, yxs⟩,

have f ≤ g, from
  le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
  le_principal_iff.mpr $
  mem_sets_of_superset ht $ assume x hx, ⟨x, hx, refl_mem_uniformity hs⟩,

have g ≠ ⊥, from neq_bot_of_le_neq_bot hf.left this,

have comap m g ≠ ⊥, from comap_neq_bot $ assume t ht,
  let ⟨t', ht', ht_mem⟩ := (mem_lift_sets $ monotone_lift' monotone_const mp₀).mp ht in
  let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem in
  let ⟨x, (hx : x ∈ t'')⟩ := inhabited_of_mem_sets hf.left ht'' in
  have h₀ : nhds x ⊓ principal (range m) ≠ ⊥,
    by simp [closure_eq_nhds] at dense; exact dense x,
  have h₁ : {y | (x, y) ∈ t'} ∈ (nhds x ⊓ principal (range m)).sets,
    from @mem_inf_sets_of_left α (nhds x) (principal (range m)) _ $ mem_nhds_left x ht',
  have h₂ : range m ∈ (nhds x ⊓ principal (range m)).sets,
    from @mem_inf_sets_of_right α (nhds x) (principal (range m)) _ $ subset.refl _,
  have {y | (x, y) ∈ t'} ∩ range m ∈ (nhds x ⊓ principal (range m)).sets,
    from @inter_mem_sets α (nhds x ⊓ principal (range m)) _ _ h₁ h₂,
  let ⟨y, xyt', b, b_eq⟩ := inhabited_of_mem_sets h₀ this in
  ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩,

have cauchy g, from
  ⟨‹g ≠ ⊥›, assume s hs,
  let
    ⟨s₁, hs₁, (comp_s₁ : comp_rel s₁ s₁ ⊆ s)⟩ := comp_mem_uniformity_sets hs,
    ⟨s₂, hs₂, (comp_s₂ : comp_rel s₂ s₂ ⊆ s₁)⟩ := comp_mem_uniformity_sets hs₁,
    ⟨t, ht, (prod_t : set.prod t t ⊆ s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
  in
  have hg₁ : p (preimage prod.swap s₁) t ∈ g.sets,
    from mem_lift (symm_le_uniformity hs₁) $ @mem_lift' α α f _ t ht,
  have hg₂ : p s₂ t ∈ g.sets,
    from mem_lift hs₂ $ @mem_lift' α α f _ t ht,
  have hg : set.prod (p (preimage prod.swap s₁) t) (p s₂ t) ∈ (filter.prod g g).sets,
    from @prod_mem_prod α α _ _ g g hg₁ hg₂,
  (filter.prod g g).sets_of_superset hg
    (assume ⟨a, b⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩,
      have (c₁, c₂) ∈ set.prod t t, from ⟨c₁t, c₂t⟩,
      comp_s₁ $ prod_mk_mem_comp_rel hc₁ $
      comp_s₂ $ prod_mk_mem_comp_rel (prod_t this) hc₂)⟩,

have cauchy (filter.comap m g),
  from cauchy_comap (le_of_eq hm.right) ‹cauchy g› (by assumption),

let ⟨x, (hx : map m (filter.comap m g) ≤ nhds x)⟩ := h _ this in
have map m (filter.comap m g) ⊓ nhds x ≠ ⊥,
  from (le_nhds_iff_adhp_of_cauchy (cauchy_map hm.uniform_continuous this)).mp hx,
have g ⊓ nhds x ≠ ⊥,
  from neq_bot_of_le_neq_bot this (inf_le_inf (assume s hs, ⟨s, hs, subset.refl _⟩) (le_refl _)),

⟨x, calc f ≤ g : by assumption
  ... ≤ nhds x : le_nhds_of_cauchy_adhp ‹cauchy g› this⟩⟩

section uniform_extension

variables
  [uniform_space β]
  [uniform_space γ]
  {e : β → α}
  (h_e : uniform_embedding e)
  (h_dense : ∀x, x ∈ closure (range e))
  {f : β → γ}
  (h_f : uniform_continuous f)

local notation `ψ` := (h_e.dense_embedding h_dense).extend f

lemma uniformly_extend_of_emb (b : β) : ψ (e b) = f b :=
dense_embedding.extend_e_eq _ b

lemma uniformly_extend_exists [complete_space γ] (a : α) :
  ∃c, tendsto f (comap e (nhds a)) (nhds c) :=
let de := (h_e.dense_embedding h_dense) in
have cauchy (nhds a), from cauchy_nhds,
have cauchy (comap e (nhds a)), from
  cauchy_comap (le_of_eq h_e.right) this de.comap_nhds_neq_bot,
have cauchy (map f (comap e (nhds a))), from
  cauchy_map h_f this,
complete_space.complete this

lemma uniformly_extend_spec [complete_space γ] (h_f : uniform_continuous f) (a : α) :
  tendsto f (comap e (nhds a)) (nhds (ψ a)) :=
let de := (h_e.dense_embedding h_dense) in
begin
  by_cases ha : a ∈ range e,
  { rcases ha with ⟨b, rfl⟩,
    rw [uniformly_extend_of_emb, de.induced],
    exact h_f.continuous.tendsto _ },
  { simp only [dense_embedding.extend, dif_neg ha],
    exact (@lim_spec _ (id _) _ _ $ uniformly_extend_exists h_e h_dense h_f _) }
end

lemma uniform_continuous_uniformly_extend [cγ : complete_space γ] : uniform_continuous ψ :=
assume d hd,
let ⟨s, hs, hs_comp⟩ := (mem_lift'_sets $
  monotone_comp_rel monotone_id $ monotone_comp_rel monotone_id monotone_id).mp (comp_le_uniformity3 hd) in
have h_pnt : ∀{a m}, m ∈ (nhds a).sets → ∃c, c ∈ f '' preimage e m ∧ (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s,
  from assume a m hm,
  have nb : map f (comap e (nhds a)) ≠ ⊥,
    from map_ne_bot (h_e.dense_embedding h_dense).comap_nhds_neq_bot,
  have (f '' preimage e m) ∩ ({c | (c, ψ a) ∈ s } ∩ {c | (ψ a, c) ∈ s }) ∈ (map f (comap e (nhds a))).sets,
    from inter_mem_sets (image_mem_map $ preimage_mem_comap $ hm)
      (uniformly_extend_spec h_e h_dense h_f _ (inter_mem_sets (mem_nhds_right _ hs) (mem_nhds_left _ hs))),
  inhabited_of_mem_sets nb this,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ (@uniformity β _).sets,
  from h_f hs,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ (comap (λx:β×β, (e x.1, e x.2)) uniformity).sets,
  by rwa [h_e.right.symm] at this,
let ⟨t, ht, ts⟩ := this in
show preimage (λp:(α×α), (ψ p.1, ψ p.2)) d ∈ uniformity.sets,
  from (@uniformity α _).sets_of_superset (interior_mem_uniformity ht) $
  assume ⟨x₁, x₂⟩ hx_t,
  have nhds (x₁, x₂) ≤ principal (interior t),
    from is_open_iff_nhds.mp is_open_interior (x₁, x₂) hx_t,
  have interior t ∈ (filter.prod (nhds x₁) (nhds x₂)).sets,
    by rwa [nhds_prod_eq, le_principal_iff] at this,
  let ⟨m₁, hm₁, m₂, hm₂, (hm : set.prod m₁ m₂ ⊆ interior t)⟩ := mem_prod_iff.mp this in
  let ⟨a, ha₁, _, ha₂⟩ := h_pnt hm₁ in
  let ⟨b, hb₁, hb₂, _⟩ := h_pnt hm₂ in
  have set.prod (preimage e m₁) (preimage e m₂) ⊆ preimage (λp:(β×β), (f p.1, f p.2)) s,
    from calc _ ⊆ preimage (λp:(β×β), (e p.1, e p.2)) (interior t) : preimage_mono hm
    ... ⊆ preimage (λp:(β×β), (e p.1, e p.2)) t : preimage_mono interior_subset
    ... ⊆ preimage (λp:(β×β), (f p.1, f p.2)) s : ts,
  have set.prod (f '' preimage e m₁) (f '' preimage e m₂) ⊆ s,
    from calc set.prod (f '' preimage e m₁) (f '' preimage e m₂) =
      (λp:(β×β), (f p.1, f p.2)) '' (set.prod (preimage e m₁) (preimage e m₂)) : prod_image_image_eq
    ... ⊆ (λp:(β×β), (f p.1, f p.2)) '' preimage (λp:(β×β), (f p.1, f p.2)) s : mono_image this
    ... ⊆ s : image_subset_iff.mpr $ subset.refl _,
  have (a, b) ∈ s, from @this (a, b) ⟨ha₁, hb₁⟩,
  hs_comp $ show (ψ x₁, ψ x₂) ∈ comp_rel s (comp_rel s s),
    from ⟨a, ha₂, ⟨b, this, hb₂⟩⟩

end uniform_extension
end uniform_space
end

section constructions
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ι : Sort*}

instance : partial_order (uniform_space α) :=
{ le          := λt s, s.uniformity ≤ t.uniformity,
  le_antisymm := assume t s h₁ h₂, uniform_space_eq $ le_antisymm h₂ h₁,
  le_refl     := assume t, le_refl _,
  le_trans    := assume a b c h₁ h₂, @le_trans _ _ c.uniformity b.uniformity a.uniformity h₂ h₁ }

instance : has_Sup (uniform_space α) :=
⟨assume s, uniform_space.of_core {
  uniformity := (⨅u∈s, @uniformity α u),
  refl       := le_infi $ assume u, le_infi $ assume hu, u.refl,
  symm       := le_infi $ assume u, le_infi $ assume hu,
    le_trans (map_mono $ infi_le_of_le _ $ infi_le _ hu) u.symm,
  comp       := le_infi $ assume u, le_infi $ assume hu,
    le_trans (lift'_mono (infi_le_of_le _ $ infi_le _ hu) $ le_refl _) u.comp }⟩

private lemma le_Sup {tt : set (uniform_space α)} {t : uniform_space α} (h : t ∈ tt) :
  t ≤ Sup tt :=
show (⨅u∈tt, @uniformity α u) ≤ t.uniformity,
  from infi_le_of_le t $ infi_le _ h

private lemma Sup_le {tt : set (uniform_space α)} {t : uniform_space α} (h : ∀t'∈tt, t' ≤ t) :
  Sup tt ≤ t :=
show t.uniformity ≤ (⨅u∈tt, @uniformity α u),
  from le_infi $ assume t', le_infi $ assume ht', h t' ht'

instance : has_bot (uniform_space α) :=
⟨uniform_space.of_core { uniformity := ⊤, refl := le_top, symm := le_top, comp := le_top }⟩

instance : has_top (uniform_space α) :=
⟨{ to_topological_space := ⊤,
  uniformity  := principal id_rel,
  refl        := le_refl _,
  symm        := by simp [tendsto]; apply subset.refl,
  comp        :=
  begin
    rw [lift'_principal], {simp},
    exact monotone_comp_rel monotone_id monotone_id
  end,
  is_open_uniformity :=
    assume s, by simp [is_open_fold, subset_def, id_rel] {contextual := tt } } ⟩

instance : complete_lattice (uniform_space α) :=
{ sup           := λa b, Sup {a, b},
  le_sup_left   := assume a b, le_Sup $ by simp,
  le_sup_right  := assume a b, le_Sup $ by simp,
  sup_le        := assume a b c h₁ h₂, Sup_le $ assume t',
    begin simp, intro h, cases h with h h, repeat { subst h; assumption } end,
  inf           := λa b, Sup {x | x ≤ a ∧ x ≤ b},
  le_inf        := assume a b c h₁ h₂, le_Sup ⟨h₁, h₂⟩,
  inf_le_left   := assume a b, Sup_le $ assume x ⟨ha, hb⟩, ha,
  inf_le_right  := assume a b, Sup_le $ assume x ⟨ha, hb⟩, hb,
  top           := ⊤,
  le_top        := assume u, u.refl,
  bot           := ⊥,
  bot_le        := assume a, show a.uniformity ≤ ⊤, from le_top,
  Sup           := Sup,
  le_Sup        := assume s u, le_Sup,
  Sup_le        := assume s u, Sup_le,
  Inf           := λtt, Sup {t | ∀t'∈tt, t ≤ t'},
  le_Inf        := assume s a hs, le_Sup hs,
  Inf_le        := assume s a ha, Sup_le $ assume u hs, hs _ ha,
  ..uniform_space.partial_order }

lemma supr_uniformity {ι : Sort*} {u : ι → uniform_space α} :
  (supr u).uniformity = (⨅i, (u i).uniformity) :=
show (⨅a (h : ∃i:ι, u i = a), a.uniformity) = _, from
le_antisymm
  (le_infi $ assume i, infi_le_of_le (u i) $ infi_le _ ⟨i, rfl⟩)
  (le_infi $ assume a, le_infi $ assume ⟨i, (ha : u i = a)⟩, ha ▸ infi_le _ _)

lemma sup_uniformity {u v : uniform_space α} :
  (u ⊔ v).uniformity = u.uniformity ⊓ v.uniformity :=
have (u ⊔ v) = (⨆i (h : i = u ∨ i = v), i), by simp [supr_or, supr_sup_eq],
calc (u ⊔ v).uniformity = ((⨆i (h : i = u ∨ i = v), i) : uniform_space α).uniformity : by rw [this]
  ... = _ : by simp [supr_uniformity, infi_or, infi_inf_eq]

instance inhabited_uniform_space : inhabited (uniform_space α) := ⟨⊤⟩

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`. -/
def uniform_space.comap (f : α → β) (u : uniform_space β) : uniform_space α :=
{ uniformity := u.uniformity.comap (λp:α×α, (f p.1, f p.2)),
  to_topological_space := u.to_topological_space.induced f,
  refl := le_trans (by simp; exact assume ⟨a, b⟩ (h : a = b), h ▸ rfl) (comap_mono u.refl),
  symm := by simp [tendsto_comap_iff, prod.swap, (∘)]; exact tendsto_comap.comp tendsto_swap_uniformity,
  comp := le_trans
    begin
      rw [comap_lift'_eq, comap_lift'_eq2],
      exact (lift'_mono' $ assume s hs ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩, ⟨f x, h₁, h₂⟩),
      repeat { exact monotone_comp_rel monotone_id monotone_id }
    end
    (comap_mono u.comp),
  is_open_uniformity := λ s, begin
    change (@is_open α (u.to_topological_space.induced f) s ↔ _),
    simp [is_open_iff_nhds, nhds_induced_eq_comap, mem_nhds_uniformity_iff, filter.comap, and_comm],
    refine ball_congr (λ x hx, ⟨_, _⟩),
    { rintro ⟨t, hts, ht⟩, refine ⟨_, ht, _⟩,
      rintro ⟨x₁, x₂⟩ h rfl, exact hts (h rfl) },
    { rintro ⟨t, ht, hts⟩,
      exact ⟨{y | (f x, y) ∈ t}, λ y hy, @hts (x, y) hy rfl,
        mem_nhds_uniformity_iff.1 $ mem_nhds_left _ ht⟩ }
  end }

lemma uniform_space_comap_id {α : Type*} : uniform_space.comap (id : α → α) = id :=
by ext u ; dsimp [uniform_space.comap] ; rw [prod.id_prod, filter.comap_id]

lemma uniform_space.comap_comap_comp {α β γ} [uγ : uniform_space γ] {f : α → β} {g : β → γ} :
  uniform_space.comap (g ∘ f) uγ = uniform_space.comap f (uniform_space.comap g uγ) :=
by ext ; dsimp [uniform_space.comap] ; rw filter.comap_comap_comp

lemma uniform_continuous_iff {α β} [uα : uniform_space α] [uβ : uniform_space β] (f : α → β) :
  uniform_continuous f ↔ uβ.comap f ≤ uα :=
filter.map_le_iff_le_comap

lemma uniform_continuous_comap {f : α → β} [u : uniform_space β] :
  @uniform_continuous α β (uniform_space.comap f u) u f :=
tendsto_comap

lemma uniform_embedding_comap {f : α → β} [u : uniform_space β] (hf : function.injective f) :
  @uniform_embedding α β (uniform_space.comap f u) u f :=
⟨hf, rfl⟩

theorem to_topological_space_comap {f : α → β} {u : uniform_space β} :
  @uniform_space.to_topological_space _ (uniform_space.comap f u) =
  topological_space.induced f (@uniform_space.to_topological_space β u) :=
eq_of_nhds_eq_nhds $ assume a,
begin
  simp [nhds_induced_eq_comap, nhds_eq_uniformity, nhds_eq_uniformity],
  change comap f (uniformity.lift' (preimage (λb, (f a, b)))) =
      (u.uniformity.comap (λp:α×α, (f p.1, f p.2))).lift' (preimage (λa', (a, a'))),
  rw [comap_lift'_eq monotone_preimage, comap_lift'_eq2 monotone_preimage],
  exact rfl
end

lemma uniform_continuous_comap' {f : γ → β} {g : α → γ} [v : uniform_space β] [u : uniform_space α]
  (h : uniform_continuous (f ∘ g)) : @uniform_continuous α γ u (uniform_space.comap f v) g :=
tendsto_comap_iff.2 h

lemma to_topological_space_mono {u₁ u₂ : uniform_space α} (h : u₁ ≤ u₂) :
  @uniform_space.to_topological_space _ u₁ ≤ @uniform_space.to_topological_space _ u₂ :=
le_of_nhds_le_nhds $ assume a,
  by rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a]; exact (lift'_mono h $ le_refl _)

lemma to_topological_space_top : @uniform_space.to_topological_space α ⊤ = ⊤ := rfl

lemma to_topological_space_bot : @uniform_space.to_topological_space α ⊥ = ⊥ :=
bot_unique $ assume s hs, classical.by_cases
  (assume : s = ∅, this.symm ▸ @is_open_empty _ ⊥)
  (assume : s ≠ ∅,
    let ⟨x, hx⟩ := exists_mem_of_ne_empty this in
    have s = univ, from top_unique $ assume y hy, hs x hx (x, y) rfl,
    this.symm ▸ @is_open_univ _ ⊥)

lemma to_topological_space_supr {ι : Sort*} {u : ι → uniform_space α} :
  @uniform_space.to_topological_space α (supr u) = (⨆i, @uniform_space.to_topological_space α (u i)) :=
classical.by_cases
  (assume h : nonempty ι,
    eq_of_nhds_eq_nhds $ assume a,
    begin
      rw [nhds_supr, nhds_eq_uniformity],
      change _ = (supr u).uniformity.lift' (preimage $ prod.mk a),
      begin
        rw [supr_uniformity, lift'_infi],
        exact (congr_arg _ $ funext $ assume i, @nhds_eq_uniformity α (u i) a),
        exact h,
        exact assume a b, rfl
      end
    end)
  (assume : ¬ nonempty ι,
    le_antisymm
      (have supr u = ⊥, from bot_unique $ supr_le $ assume i, (this ⟨i⟩).elim,
        have @uniform_space.to_topological_space _ (supr u) = ⊥,
          from this.symm ▸ to_topological_space_bot,
        this.symm ▸ bot_le)
      (supr_le $ assume i, to_topological_space_mono $ le_supr _ _))

lemma to_topological_space_Sup {s : set (uniform_space α)} :
  @uniform_space.to_topological_space α (Sup s) = (⨆i∈s, @uniform_space.to_topological_space α i) :=
begin
  rw [Sup_eq_supr, to_topological_space_supr],
  apply congr rfl,
  funext x,
  exact to_topological_space_supr
end

lemma to_topological_space_sup {u v : uniform_space α} :
  @uniform_space.to_topological_space α (u ⊔ v) =
    @uniform_space.to_topological_space α u ⊔ @uniform_space.to_topological_space α v :=
ord_continuous_sup $ assume s, to_topological_space_Sup

instance : uniform_space empty := ⊤
instance : uniform_space unit := ⊤
instance : uniform_space bool := ⊤
instance : uniform_space ℕ := ⊤
instance : uniform_space ℤ := ⊤

instance {p : α → Prop} [t : uniform_space α] : uniform_space (subtype p) :=
uniform_space.comap subtype.val t

lemma uniformity_subtype {p : α → Prop} [t : uniform_space α] :
  (@uniformity (subtype p) _) = comap (λq:subtype p × subtype p, (q.1.1, q.2.1)) uniformity :=
rfl

lemma uniform_continuous_subtype_val {p : α → Prop} [uniform_space α] :
  uniform_continuous (subtype.val : {a : α // p a} → α) :=
uniform_continuous_comap

lemma uniform_continuous_subtype_mk {p : α → Prop} [uniform_space α] [uniform_space β]
  {f : β → α} (hf : uniform_continuous f) (h : ∀x, p (f x)) :
  uniform_continuous (λx, ⟨f x, h x⟩ : β → subtype p) :=
uniform_continuous_comap' hf

lemma tendsto_of_uniform_continuous_subtype
  [uniform_space α] [uniform_space β] {f : α → β} {s : set α} {a : α}
  (hf : uniform_continuous (λx:s, f x.val)) (ha : s ∈ (nhds a).sets) :
  tendsto f (nhds a) (nhds (f a)) :=
by rw [(@map_nhds_subtype_val_eq α _ s a (mem_of_nhds ha) ha).symm]; exact
tendsto_map' (continuous_iff_continuous_at.mp hf.continuous _)

lemma uniform_embedding_subtype_emb {α : Type*} {β : Type*} [uniform_space α] [uniform_space β]
  (p : α → Prop) {e : α → β} (ue : uniform_embedding e) (de : dense_embedding e) :
  uniform_embedding (de.subtype_emb p) :=
⟨(de.subtype p).inj,
  by simp [comap_comap_comp, (∘), dense_embedding.subtype_emb, uniformity_subtype, ue.right.symm]⟩

lemma uniform_extend_subtype {α : Type*} {β : Type*} {γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ] [complete_space γ]
  {p : α → Prop} {e : α → β} {f : α → γ} {b : β} {s : set α}
  (hf : uniform_continuous (λx:subtype p, f x.val))
  (he : uniform_embedding e) (hd : ∀x:β, x ∈ closure (range e))
  (hb : closure (e '' s) ∈ (nhds b).sets) (hs : is_closed s) (hp : ∀x∈s, p x) :
  ∃c, tendsto f (comap e (nhds b)) (nhds c) :=
have de : dense_embedding e,
  from he.dense_embedding hd,
have de' : dense_embedding (de.subtype_emb p),
  by exact de.subtype p,
have ue' : uniform_embedding (de.subtype_emb p),
  from uniform_embedding_subtype_emb _ he de,
have b ∈ closure (e '' {x | p x}),
  from (closure_mono $ mono_image $ hp) (mem_of_nhds hb),
let ⟨c, (hc : tendsto (f ∘ subtype.val) (comap (de.subtype_emb p) (nhds ⟨b, this⟩)) (nhds c))⟩ :=
  uniformly_extend_exists ue' de'.dense hf _ in
begin
  rw [nhds_subtype_eq_comap] at hc,
  simp [comap_comap_comp] at hc,
  change (tendsto (f ∘ @subtype.val α p) (comap (e ∘ @subtype.val α p) (nhds b)) (nhds c)) at hc,
  rw [←comap_comap_comp, tendsto_comap'_iff] at hc,
  exact ⟨c, hc⟩,
  exact ⟨_, hb, assume x,
    begin
      change e x ∈ (closure (e '' s)) → x ∈ range subtype.val,
      rw [←closure_induced, closure_eq_nhds, mem_set_of_eq, (≠), nhds_induced_eq_comap, de.induced],
      change x ∈ {x | nhds x ⊓ principal s ≠ ⊥} → x ∈ range subtype.val,
      rw [←closure_eq_nhds, closure_eq_of_is_closed hs],
      exact assume hxs, ⟨⟨x, hp x hxs⟩, rfl⟩,
      exact de.inj
    end⟩
end

section prod

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance [u₁ : uniform_space α] [u₂ : uniform_space β] : uniform_space (α × β) :=
uniform_space.of_core_eq
  (u₁.comap prod.fst ⊔ u₂.comap prod.snd).to_core
  prod.topological_space
  (calc prod.topological_space = (u₁.comap prod.fst ⊔ u₂.comap prod.snd).to_topological_space :
      by rw [to_topological_space_sup, to_topological_space_comap, to_topological_space_comap]; refl
    ... = _ : by rw [uniform_space.to_core_to_topological_space])

theorem uniformity_prod [uniform_space α] [uniform_space β] : @uniformity (α × β) _ =
  uniformity.comap (λp:(α × β) × α × β, (p.1.1, p.2.1)) ⊓
  uniformity.comap (λp:(α × β) × α × β, (p.1.2, p.2.2)) :=
sup_uniformity

lemma uniformity_prod_eq_prod [uniform_space α] [uniform_space β] :
  @uniformity (α×β) _ =
    map (λp:(α×α)×(β×β), ((p.1.1, p.2.1), (p.1.2, p.2.2))) (filter.prod uniformity uniformity) :=
have map (λp:(α×α)×(β×β), ((p.1.1, p.2.1), (p.1.2, p.2.2))) =
  comap (λp:(α×β)×(α×β), ((p.1.1, p.2.1), (p.1.2, p.2.2))),
  from funext $ assume f, map_eq_comap_of_inverse
    (funext $ assume ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl) (funext $ assume ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl),
by rw [this, uniformity_prod, filter.prod, comap_inf, comap_comap_comp, comap_comap_comp]

lemma mem_uniformity_of_uniform_continuous_invarant [uniform_space α] {s:set (α×α)} {f : α → α → α}
  (hf : uniform_continuous (λp:α×α, f p.1 p.2)) (hs : s ∈ (@uniformity α _).sets) :
  ∃u∈(@uniformity α _).sets, ∀a b c, (a, b) ∈ u → (f a c, f b c) ∈ s :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff, (∘)] at hf,
  rcases mem_map_sets_iff.1 (hf hs) with ⟨t, ht, hts⟩, clear hf,
  rcases mem_prod_iff.1 ht with ⟨u, hu, v, hv, huvt⟩, clear ht,
  refine ⟨u, hu, assume a b c hab, hts $ (mem_image _ _ _).2 ⟨⟨⟨a, b⟩, ⟨c, c⟩⟩, huvt ⟨_, _⟩, _⟩⟩,
  exact hab,
  exact refl_mem_uniformity hv,
  refl
end

lemma mem_uniform_prod [t₁ : uniform_space α] [t₂ : uniform_space β] {a : set (α × α)} {b : set (β × β)}
  (ha : a ∈ (@uniformity α _).sets) (hb : b ∈ (@uniformity β _).sets) :
  {p:(α×β)×(α×β) | (p.1.1, p.2.1) ∈ a ∧ (p.1.2, p.2.2) ∈ b } ∈ (@uniformity (α × β) _).sets :=
by rw [uniformity_prod]; exact inter_mem_inf_sets (preimage_mem_comap ha) (preimage_mem_comap hb)

lemma tendsto_prod_uniformity_fst [uniform_space α] [uniform_space β] :
  tendsto (λp:(α×β)×(α×β), (p.1.1, p.2.1)) uniformity uniformity :=
le_trans (map_mono (@le_sup_left (uniform_space (α×β)) _ _ _)) map_comap_le

lemma tendsto_prod_uniformity_snd [uniform_space α] [uniform_space β] :
  tendsto (λp:(α×β)×(α×β), (p.1.2, p.2.2)) uniformity uniformity :=
le_trans (map_mono (@le_sup_right (uniform_space (α×β)) _ _ _)) map_comap_le

lemma uniform_continuous_fst [uniform_space α] [uniform_space β] : uniform_continuous (λp:α×β, p.1) :=
tendsto_prod_uniformity_fst

lemma uniform_continuous_snd [uniform_space α] [uniform_space β] : uniform_continuous (λp:α×β, p.2) :=
tendsto_prod_uniformity_snd

variables [uniform_space α] [uniform_space β] [uniform_space γ]
lemma uniform_continuous.prod_mk
  {f₁ : α → β} {f₂ : α → γ} (h₁ : uniform_continuous f₁) (h₂ : uniform_continuous f₂) :
  uniform_continuous (λa, (f₁ a, f₂ a)) :=
by rw [uniform_continuous, uniformity_prod]; exact
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma uniform_continuous.prod_mk_left {f : α × β → γ} (h : uniform_continuous f) (b) :
  uniform_continuous (λ a, f (a,b)) :=
uniform_continuous.comp (uniform_continuous.prod_mk uniform_continuous_id uniform_continuous_const) h

lemma uniform_continuous.prod_mk_right {f : α × β → γ} (h : uniform_continuous f) (a) :
  uniform_continuous (λ b, f (a,b)) :=
uniform_continuous.comp (uniform_continuous.prod_mk uniform_continuous_const uniform_continuous_id) h

lemma cauchy_prod [uniform_space β] {f : filter α} {g : filter β} :
  cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_neq_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).comap p_α ⊓ (g.prod g).comap p_β ≤ uniformity.comap p_α ⊓ uniformity.comap p_β,
    by simpa [uniformity_prod, filter.prod, filter.comap_inf, filter.comap_comap_comp, (∘),
        lattice.inf_assoc, lattice.inf_comm, lattice.inf_left_comm],
  lattice.inf_le_inf (filter.comap_mono hf) (filter.comap_mono hg)⟩

instance complete_space.prod [complete_space α] [complete_space β] : complete_space (α × β) :=
{ complete := λ f hf,
    let ⟨x1, hx1⟩ := complete_space.complete $ cauchy_map uniform_continuous_fst hf in
    let ⟨x2, hx2⟩ := complete_space.complete $ cauchy_map uniform_continuous_snd hf in
    ⟨(x1, x2), by rw [nhds_prod_eq, filter.prod_def];
      from filter.le_lift (λ s hs, filter.le_lift' $ λ t ht,
        have H1 : prod.fst ⁻¹' s ∈ f.sets := hx1 hs,
        have H2 : prod.snd ⁻¹' t ∈ f.sets := hx2 ht,
        filter.inter_mem_sets H1 H2)⟩ }

lemma uniform_embedding.prod {α' : Type*} {β' : Type*}
  [uniform_space α] [uniform_space β] [uniform_space α'] [uniform_space β']
  {e₁ : α → α'} {e₂ : β → β'} (h₁ : uniform_embedding e₁) (h₂ : uniform_embedding e₂) :
  uniform_embedding (λp:α×β, (e₁ p.1, e₂ p.2)) :=
⟨assume ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  by simp [prod.mk.inj_iff]; exact assume eq₁ eq₂, ⟨h₁.left eq₁, h₂.left eq₂⟩,
  by simp [(∘), uniformity_prod, h₁.right.symm, h₂.right.symm, comap_inf, comap_comap_comp]⟩

lemma to_topological_space_prod [u : uniform_space α] [v : uniform_space β] :
  @uniform_space.to_topological_space (α × β) prod.uniform_space =
    @prod.topological_space α β u.to_topological_space v.to_topological_space := rfl

end prod

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
  (map (λ p : α × α, (inl p.1, inl p.2)) uniformity ⊔ map (λ p : β × β, (inr p.1, inr p.2)) uniformity)
  (λ r ⟨H₁, H₂⟩ x, by cases x; [apply refl_mem_uniformity H₁, apply refl_mem_uniformity H₂])
  (λ r ⟨H₁, H₂⟩, ⟨symm_le_uniformity H₁, symm_le_uniformity H₂⟩)
  (λ r ⟨Hrα, Hrβ⟩, begin
    rcases comp_mem_uniformity_sets Hrα with ⟨tα, htα, Htα⟩,
    rcases comp_mem_uniformity_sets Hrβ with ⟨tβ, htβ, Htβ⟩,
    refine ⟨_,
      ⟨mem_map_sets_iff.2 ⟨tα, htα, subset_union_left _ _⟩,
       mem_map_sets_iff.2 ⟨tβ, htβ, subset_union_right _ _⟩⟩, _⟩,
    rintros ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩,
                       ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩,
    { have A : (a, c) ∈ comp_rel tα tα := ⟨b, hab, hbc⟩,
      exact Htα A },
    { have A : (a, c) ∈ comp_rel tβ tβ := ⟨b, hab, hbc⟩,
      exact Htβ A }
  end)

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage of the diagonal. -/
lemma union_mem_uniformity_sum
  {a : set (α × α)} (ha : a ∈ (@uniformity α _).sets) {b : set (β × β)} (hb : b ∈ (@uniformity β _).sets) :
  ((λ p : (α × α), (inl p.1, inl p.2)) '' a ∪ (λ p : (β × β), (inr p.1, inr p.2)) '' b) ∈ (@uniform_space.core.sum α β _ _).uniformity.sets :=
⟨mem_map_sets_iff.2 ⟨_, ha, subset_union_left _ _⟩, mem_map_sets_iff.2 ⟨_, hb, subset_union_right _ _⟩⟩

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/
lemma uniformity_sum_of_open_aux {s : set (α ⊕ β)} (hs : is_open s) {x : α ⊕ β} (xs : x ∈ s) :
  { p : ((α ⊕ β) × (α ⊕ β)) | p.1 = x → p.2 ∈ s } ∈ (@uniform_space.core.sum α β _ _).uniformity.sets :=
begin
  cases x,
  { refine mem_sets_of_superset
      (union_mem_uniformity_sum (mem_nhds_uniformity_iff.1 (mem_nhds_sets hs.1 xs)) univ_mem_sets)
      (union_subset _ _);
    rintro _ ⟨⟨_, b⟩, h, ⟨⟩⟩ ⟨⟩,
    exact h rfl },
  { refine mem_sets_of_superset
      (union_mem_uniformity_sum univ_mem_sets (mem_nhds_uniformity_iff.1 (mem_nhds_sets hs.2 xs)))
      (union_subset _ _);
    rintro _ ⟨⟨a, _⟩, h, ⟨⟩⟩ ⟨⟩,
    exact h rfl },
end

lemma open_of_uniformity_sum_aux {s : set (α ⊕ β)}
  (hs : ∀x ∈ s, { p : ((α ⊕ β) × (α ⊕ β)) | p.1 = x → p.2 ∈ s } ∈ (@uniform_space.core.sum α β _ _).uniformity.sets) :
  is_open s :=
begin
  split,
  { refine (@is_open_iff_mem_nhds α _ _).2 (λ a ha, mem_nhds_uniformity_iff.2 _),
    rcases mem_map_sets_iff.1 (hs _ ha).1 with ⟨t, ht, st⟩,
    refine mem_sets_of_superset ht _,
    rintro p pt rfl, exact st ⟨_, pt, rfl⟩ rfl },
  { refine (@is_open_iff_mem_nhds β _ _).2 (λ b hb, mem_nhds_uniformity_iff.2 _),
    rcases mem_map_sets_iff.1 (hs _ hb).2 with ⟨t, ht, st⟩,
    refine mem_sets_of_superset ht _,
    rintro p pt rfl, exact st ⟨_, pt, rfl⟩ rfl }
end

/- We can now define the uniform structure on the disjoint union -/
instance sum.uniform_space [u₁ : uniform_space α] [u₂ : uniform_space β] : uniform_space (α ⊕ β) :=
{ to_core := uniform_space.core.sum,
  is_open_uniformity := λ s, ⟨uniformity_sum_of_open_aux, open_of_uniformity_sum_aux⟩ }

lemma sum.uniformity [uniform_space α] [uniform_space β] :
  @uniformity (α ⊕ β) _ =
    map (λ p : α × α, (inl p.1, inl p.2)) uniformity ⊔
    map (λ p : β × β, (inr p.1, inr p.2)) uniformity := rfl

end sum

end constructions

lemma lebesgue_number_lemma {α : Type u} [uniform_space α] {s : set α} {ι} {c : ι → set α}
  (hs : compact s) (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ n ∈ (@uniformity α _).sets, ∀ x ∈ s, ∃ i, {y | (x, y) ∈ n} ⊆ c i :=
begin
  let u := λ n, {x | ∃ i (m ∈ (@uniformity α _).sets), {y | (x, y) ∈ comp_rel m n} ⊆ c i},
  have hu₁ : ∀ n ∈ (@uniformity α _).sets, is_open (u n),
  { refine λ n hn, is_open_uniformity.2 _,
    rintro x ⟨i, m, hm, h⟩,
    rcases comp_mem_uniformity_sets hm with ⟨m', hm', mm'⟩,
    apply uniformity.sets_of_superset hm',
    rintros ⟨x, y⟩ hp rfl,
    refine ⟨i, m', hm', λ z hz, h (monotone_comp_rel monotone_id monotone_const mm' _)⟩,
    dsimp at hz ⊢, rw comp_rel_assoc,
    exact ⟨y, hp, hz⟩ },
  have hu₂ : s ⊆ ⋃ n ∈ (@uniformity α _).sets, u n,
  { intros x hx,
    rcases mem_Union.1 (hc₂ hx) with ⟨i, h⟩,
    rcases comp_mem_uniformity_sets (is_open_uniformity.1 (hc₁ i) x h) with ⟨m', hm', mm'⟩,
    exact mem_bUnion hm' ⟨i, _, hm', λ y hy, mm' hy rfl⟩ },
  rcases compact_elim_finite_subcover_image hs hu₁ hu₂ with ⟨b, bu, b_fin, b_cover⟩,
  refine ⟨_, Inter_mem_sets b_fin bu, λ x hx, _⟩,
  rcases mem_bUnion_iff.1 (b_cover hx) with ⟨n, bn, i, m, hm, h⟩,
  refine ⟨i, λ y hy, h _⟩,
  exact prod_mk_mem_comp_rel (refl_mem_uniformity hm) (bInter_subset_of_mem bn hy)
end

lemma lebesgue_number_lemma_sUnion {α : Type u} [uniform_space α] {s : set α} {c : set (set α)}
  (hs : compact s) (hc₁ : ∀ t ∈ c, is_open t) (hc₂ : s ⊆ ⋃₀ c) :
  ∃ n ∈ (@uniformity α _).sets, ∀ x ∈ s, ∃ t ∈ c, ∀ y, (x, y) ∈ n → y ∈ t :=
by rw sUnion_eq_Union at hc₂;
   simpa using lebesgue_number_lemma hs (by simpa) hc₂

namespace dense_embedding
open filter
variables {α : Type*} [topological_space α]
variables {β : Type*} [topological_space β]
variables {γ : Type*} [uniform_space γ] [complete_space γ] [separated γ]

lemma continuous_extend_of_cauchy {e : α → β} {f : α → γ}
  (de : dense_embedding e) (h : ∀ b : β, cauchy (map f (comap e $ nhds b))) :
  continuous (de.extend f) :=
continuous_extend de $ λ b, complete_space.complete (h b)

end dense_embedding
