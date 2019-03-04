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

The central concept of uniform spaces is its uniformity: a filter relating two elements of the
space. This filter is reflexive, symmetric and transitive. So a set (i.e. a relation) in this filter
represents a 'distance': it is reflexive, symmetric and the uniformity contains a set for which the
`triangular` rule holds.

The formalization is mostly based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import order.filter order.filter.lift data.quot topology.constructions

open set lattice filter classical
local attribute [instance, priority 0] prop_decidable

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
