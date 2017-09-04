/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* completeness
* completion (on Cauchy filters instead of Cauchy sequences)
* extension of uniform continuous functions to complete spaces
* uniform contiunuity & embedding
* totally bounded
* totally bounded ∧ complete → compact

One reason to directly formalize uniform spaces is foundational: we define ℝ as a completion of ℚ.

The central concept of uniform spaces is its uniformity: a filter relating two elemenets of the
space. This filter is reflexive, symmetric and transitive. So a set (i.e. a relation) in this filter
represents a 'distance': it is reflexive, symmetric and the uniformity contains a set for which the
`triangular` rule holds.

The formalization is mostly based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import order.filter topology.topological_space topology.continuity
open set lattice filter classical
local attribute [instance] decidable_inhabited prop_decidable

set_option eqn_compiler.zeta true

universes u v w x y

section
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y}

lemma forall_quotient_iff [r : setoid α] {p : quotient r → Prop} :
  (∀a:quotient r, p a) ↔ (∀a:α, p ⟦a⟧) :=
⟨assume h x, h _, assume h a, a.induction_on h⟩

def id_rel {α : Type u} := {p : α × α | p.1 = p.2}

def comp_rel {α : Type u} (r₁ r₂ : set (α×α)) := {p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

@[simp] theorem swap_id_rel : prod.swap '' id_rel = @id_rel α :=
set.ext $ assume ⟨a, b⟩, by simp [image_swap_eq_preimage_swap]; exact eq_comm

theorem monotone_comp_rel [preorder β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, comp_rel (f x) (g x)) :=
assume a b h p ⟨z, h₁, h₂⟩, ⟨z, hf h h₁, hg h h₂⟩

lemma prod_mk_mem_comp_rel {a b c : α} {s t : set (α×α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
  (a, b) ∈ comp_rel s t :=
⟨c, h₁, h₂⟩

@[simp] lemma id_comp_rel {r : set (α×α)} : comp_rel id_rel r = r :=
set.ext $ assume ⟨a, b⟩, ⟨assume ⟨a', heq, ha'⟩,
  (show a' = a, from heq.symm) ▸ ha',
  assume ha, ⟨a, rfl, ha⟩⟩

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure uniform_space.core (α : Type u) :=
(uniformity : filter (α × α))
(refl       : principal id_rel ≤ uniformity)
(symm       : tendsto prod.swap uniformity uniformity)
(comp       : uniformity.lift' (λs, comp_rel s s) ≤ uniformity)

def uniform_space.core.to_topological_space {α : Type u} (u : uniform_space.core α) :
  topological_space α :=
{ topological_space .
  is_open       := λs, ∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ u.uniformity.sets,
  is_open_univ   := by simp; intro; exact univ_mem_sets,
  is_open_inter  := assume s t hs ht x ⟨xs, xt⟩,
    u.uniformity.upwards_sets (inter_mem_sets (hs x xs) (ht x xt)) $ assume p ⟨ps, pt⟩ h, ⟨ps h, pt h⟩,
  is_open_sUnion := assume s hs x ⟨t, ts, xt⟩,
    u.uniformity.upwards_sets (hs t ts x xt) $ assume p ph h, ⟨t, ts, ph h⟩ }

lemma uniform_space.core_eq : ∀{u₁ u₂ : uniform_space.core α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
| ⟨u₁, _, _, _⟩  ⟨u₂, _, _, _⟩ h := have u₁ = u₂, from h, by simp [*]

/-- uniformity: usable typeclass incorporating a topology -/
class uniform_space (α : Type u) extends topological_space α, uniform_space.core α :=
(is_open_uniformity : ∀s, is_open s ↔ (∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ uniformity.sets))

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

lemma uniform_space_eq : ∀{u₁ u₂ : uniform_space α}, u₁.uniformity = u₂.uniformity → u₁ = u₂
| ⟨t₁, u₁, o₁⟩  ⟨t₂, u₂, o₂⟩ h :=
  have u₁ = u₂, from uniform_space.core_eq h,
  have t₁ = t₂, from topological_space_eq $ funext $ assume s, by rw [o₁, o₂]; simp [this],
  by simp [*]

lemma uniform_space.of_core_eq_to_core
  (u : uniform_space α) (t : topological_space α) (h : t = u.to_core.to_topological_space) :
  uniform_space.of_core_eq u.to_core t h = u :=
uniform_space_eq rfl

section uniform_space
variables [uniform_space α]

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
(mem_lift'_iff $ monotone_comp_rel monotone_id monotone_id).mp this

lemma symm_of_uniformity {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, (∀a b, (a, b) ∈ t → (b, a) ∈ t) ∧ t ⊆ s :=
have preimage prod.swap s ∈ (@uniformity α _).sets, from symm_le_uniformity hs,
⟨s ∩ preimage prod.swap s, inter_mem_sets hs this, assume a b ⟨h₁, h₂⟩, ⟨h₂, h₁⟩, inter_subset_left _ _⟩

lemma comp_symm_of_uniformity {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, (∀{a b}, (a, b) ∈ t → (b, a) ∈ t) ∧ comp_rel t t ⊆ s :=
let ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs in
let ⟨t', ht', ht'₁, ht'₂⟩ := symm_of_uniformity ht₁ in
⟨t', ht', ht'₁, subset.trans (monotone_comp_rel monotone_id monotone_id ht'₂) ht₂⟩

lemma uniformity_le_symm : uniformity ≤ map (@prod.swap α α) uniformity :=
calc uniformity = id <$> uniformity : (functor.id_map _).symm
  ... = (prod.swap.{u u} ∘ prod.swap) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map prod.swap ∘ map prod.swap) uniformity :
    congr map_compose rfl
  ... ≤ prod.swap.{u u} <$> uniformity : map_mono symm_le_uniformity

lemma uniformity_eq_symm : uniformity = (@prod.swap α α) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

theorem uniformity_lift_le_swap {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : uniformity.lift (λs, g (preimage prod.swap s)) ≤ f) : uniformity.lift g ≤ f :=
le_trans
  (lift_mono uniformity_le_symm (le_refl _))
  (by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h)

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
  (s ∈ (nhds x).sets) ↔ ({p : α × α | p.1 = x → p.2 ∈ s} ∈ (@uniformity α _).sets) :=
⟨ begin
    simp [mem_nhds_sets_iff, is_open_uniformity],
    exact assume t ts xt ht, uniformity.upwards_sets (ht x xt) $ assume ⟨x', y⟩ h eq, ts $ h eq
  end,

  assume hs,
  mem_nhds_sets_iff.mpr ⟨{x | {p : α × α | p.1 = x → p.2 ∈ s} ∈ (@uniformity α _).sets},
    assume x', assume hx' : {p : α × α | p.fst = x' → p.snd ∈ s} ∈ (@uniformity α _).sets,
      refl_mem_uniformity hx' rfl,
    is_open_uniformity.mpr $ assume x' hx',
      let ⟨t, ht, tr⟩ := comp_mem_uniformity_sets hx' in
      uniformity.upwards_sets ht $
      assume ⟨a, b⟩ hp' (eq : a = x'),
      have hp : (x', b) ∈ t, from eq ▸ hp',
      show {p : α × α | p.fst = b → p.snd ∈ s} ∈ (@uniformity α _).sets,
        from uniformity.upwards_sets ht $
          assume ⟨a, b'⟩ hp' (heq : a = b),
          have (b, b') ∈ t, from heq ▸ hp',
          have (x', b') ∈ comp_rel t t, from ⟨b, hp, this⟩,
          show b' ∈ s,
            from tr this rfl,
    hs⟩⟩

lemma nhds_eq_uniformity {x : α} : nhds x = uniformity.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :=
filter_eq $ set.ext $ assume s,
  begin
    rw [mem_lift'_iff], tactic.swap, apply monotone_preimage,
    simp [mem_nhds_uniformity_iff],
    exact ⟨assume h, ⟨_, h, assume y h, h rfl⟩,
      assume ⟨t, h₁, h₂⟩,
      uniformity.upwards_sets h₁ $
      assume ⟨x', y⟩ hp (eq : x' = x), h₂ $
      show (x, y) ∈ t, from eq ▸ hp⟩
  end

lemma mem_nhds_left {x : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {y : α | (x, y) ∈ s} ∈ (nhds x).sets :=
have nhds x ≤ principal {y : α | (x, y) ∈ s},
  by rw [nhds_eq_uniformity]; exact infi_le_of_le s (infi_le _ h),
by simp at this; assumption

lemma mem_nhds_right {y : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {x : α | (x, y) ∈ s} ∈ (nhds y).sets :=
mem_nhds_left (symm_le_uniformity h)

lemma tendsto_right_nhds_uniformity {a : α} : tendsto (λa', (a', a)) (nhds a) uniformity :=
assume s hs, show {a' | (a', a) ∈ s} ∈ (nhds a).sets, from mem_nhds_right hs

lemma tendsto_left_nhds_uniformity {a : α} : tendsto (λa', (a, a')) (nhds a) uniformity :=
assume s hs, show {a' | (a, a') ∈ s} ∈ (nhds a).sets, from mem_nhds_left hs

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
show (nhds a).lift (λs:set α, (nhds b).lift (λt:set α, principal (set.prod s t))) = _,
begin
  rw [lift_nhds_right],
  apply congr_arg, apply funext, intro s,
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
    rw [nhds_eq_uniformity_prod, mem_lift'_iff],
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
  (le_infi $ assume s, le_infi $ assume hs, by simp; exact uniformity.upwards_sets hs subset_closure)
  (calc uniformity.lift' closure ≤ uniformity.lift' (λd, comp_rel d (comp_rel d d)) :
      lift'_mono' (by intros s hs; rw [closure_eq_inter_uniformity]; exact bInter_subset_of_mem hs)
    ... ≤ uniformity : comp_le_uniformity3)

lemma uniformity_eq_uniformity_interior : (@uniformity α _) = uniformity.lift' interior :=
le_antisymm
  (le_infi $ assume d, le_infi $ assume hd,
    let ⟨s, hs, hs_comp⟩ := (mem_lift'_iff $
      monotone_comp_rel monotone_id $ monotone_comp_rel monotone_id monotone_id).mp (comp_le_uniformity3 hd) in
    let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs in
    have s ⊆ interior d, from
      calc s ⊆ t : hst
       ... ⊆ interior d : (subset_interior_iff_subset_of_open ht).mpr $
        assume x, assume : x ∈ t, let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp this in hs_comp ⟨x, h₁, y, h₂, h₃⟩,
    have interior d ∈ (@uniformity α _).sets,
      from (@uniformity α _).upwards_sets hs $ this,
    by simp [this])
  (assume s hs, (uniformity.lift' interior).upwards_sets (mem_lift' hs) interior_subset)

lemma interior_mem_uniformity {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  interior s ∈ (@uniformity α _).sets :=
by rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

lemma mem_uniformity_is_closed [uniform_space α] {s : set (α×α)} (h : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, is_closed t ∧ t ⊆ s :=
have s ∈ ((@uniformity α _).lift' closure).sets, by rwa [uniformity_eq_uniformity_closure] at h,
have ∃t∈(@uniformity α _).sets, closure t ⊆ s,
  by rwa [mem_lift'_iff] at this; apply closure_mono,
let ⟨t, ht, hst⟩ := this in
⟨closure t, uniformity.upwards_sets ht subset_closure, is_closed_closure, hst⟩

/- uniform continuity -/

definition uniform_continuous [uniform_space β] (f : α → β) :=
tendsto (λx:α×α, (f x.1, f x.2)) uniformity uniformity

lemma uniform_continuous_const [uniform_space β] {b : β} : uniform_continuous (λa:α, b) :=
@tendsto_const_uniformity _ _ _ b uniformity

lemma uniform_continuous_compose [uniform_space β] [uniform_space γ] {f : α → β} {g : β → γ}
  (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (g ∘ f) :=
tendsto_compose hf hg

definition uniform_embedding [uniform_space β] (f : α → β) :=
(∀a₁ a₂, f a₁ = f a₂ → a₁ = a₂) ∧
vmap (λx:α×α, (f x.1, f x.2)) uniformity = uniformity

lemma uniform_continuous_of_embedding [uniform_space β] {f : α → β}
  (hf : uniform_embedding f) : uniform_continuous f :=
by simp [uniform_continuous, hf.right.symm]; exact tendsto_vmap

lemma dense_embedding_of_uniform_embedding [uniform_space β] {f : α → β}
  (h : uniform_embedding f) (hd : ∀x, x ∈ closure (f '' univ)) : dense_embedding f :=
{ dense_embedding .
  dense   := hd,
  inj     := h.left,
  induced :=
  begin
    intro a,
    simp [h.right.symm, nhds_eq_uniformity],
    rw [vmap_lift'_eq, vmap_lift'_eq2],
    refl,
    exact monotone_preimage,
    exact monotone_preimage
  end }

lemma continuous_of_uniform [uniform_space β] {f : α → β}
  (hf : uniform_continuous f) : continuous f :=
continuous_iff_tendsto.mpr $ assume a,
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
have s ∈ (vmap (λp:α×α, (e p.1, e p.2)) $ uniformity).sets,
  from he₁.right.symm ▸ hs,
let ⟨t₁, ht₁u, ht₁⟩ := this in
have ht₁ : ∀p:α×α, (e p.1, e p.2) ∈ t₁ → p ∈ s, from ht₁,
let ⟨t₂, ht₂u, ht₂s, ht₂c⟩ := comp_symm_of_uniformity ht₁u in
let ⟨t, htu, hts, htc⟩ := comp_symm_of_uniformity ht₂u in
have preimage e {b' | (b, b') ∈ t₂} ∈ (vmap e $ nhds b).sets,
  from preimage_mem_vmap $ mem_nhds_left ht₂u,
let ⟨a, (ha : (b, e a) ∈ t₂)⟩ := inhabited_of_mem_sets (he₂.vmap_nhds_neq_bot) this in
have ∀b' (s' : set (β × β)), (b, b') ∈ t → s' ∈ (@uniformity β _).sets →
  {y : β | (b', y) ∈ s'} ∩ e '' {a' : α | (a, a') ∈ s} ≠ ∅,
  from assume b' s' hb' hs',
  have preimage e {b'' | (b', b'') ∈ s' ∩ t} ∈ (vmap e $ nhds b').sets,
    from preimage_mem_vmap $ mem_nhds_left $ inter_mem_sets hs' htu,
  let ⟨a₂, ha₂s', ha₂t⟩ := inhabited_of_mem_sets (he₂.vmap_nhds_neq_bot) this in
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
⟨a, (nhds b).upwards_sets (mem_nhds_left htu) this⟩

/- cauchy filters -/
definition cauchy (f : filter α) := f ≠ ⊥ ∧ filter.prod f f ≤ uniformity

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
  (return_le_nhds a)

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
      exact f.upwards_sets hs subset_closure
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

lemma cauchy_vmap [uniform_space β] {f : filter β} {m : α → β}
  (hm : vmap (λp:α×α, (m p.1, m p.2)) uniformity ≤ uniformity)
  (hf : cauchy f) (hb : vmap m f ≠ ⊥) : cauchy (vmap m f) :=
⟨hb,
  calc filter.prod (vmap m f) (vmap m f) =
          vmap (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_vmap_vmap_eq
    ... ≤ vmap (λp:α×α, (m p.1, m p.2)) uniformity : vmap_mono hf.right
    ... ≤ uniformity : hm⟩

/- separated uniformity -/

protected def separation_rel (α : Type u) [u : uniform_space α] :=
(⋂₀ (@uniformity α _).sets)

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

protected def separation_setoid (α : Type u) [u : uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ separation_rel α, separated_equiv⟩

@[class] definition separated (α : Type u) [u : uniform_space α] :=
separation_rel α = id_rel

instance separated_t2 [s : separated α] : t2_space α :=
⟨assume x y, assume h : x ≠ y,
have separation_rel α = id_rel,
  from s,
have (x, y) ∉ separation_rel α,
  by simp [this]; exact h,
let ⟨d, hd, (hxy : (x, y) ∉ d)⟩ := classical.not_ball.1 this in
let ⟨d', hd', (hd'd' : comp_rel d' d' ⊆ d)⟩ := comp_mem_uniformity_sets hd in
have {y | (x, y) ∈ d'} ∈ (nhds x).sets,
  from mem_nhds_left hd',
let ⟨u, hu₁, hu₂, hu₃⟩ := mem_nhds_sets_iff.mp this in
have {x | (x, y) ∈ d'} ∈ (nhds y).sets,
  from mem_nhds_right hd',
let ⟨v, hv₁, hv₂, hv₃⟩ := mem_nhds_sets_iff.mp this in
have u ∩ v = ∅, from
  eq_empty_of_subset_empty $
  assume z ⟨(h₁ : z ∈ u), (h₂ : z ∈ v)⟩,
  have (x, y) ∈ comp_rel d' d', from ⟨z, hu₁ h₁, hv₁ h₂⟩,
  hxy $ hd'd' this,
⟨u, v, hu₂, hv₂, hu₃, hv₃, this⟩⟩

instance separated_regular [separated α] : regular_space α :=
{ separated_t2 with
  regular := λs a hs ha,
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
    have closure e ∈ (nhds a).sets, from (nhds a).upwards_sets (mem_nhds_left hd) subset_closure,
    have nhds a ⊓ principal (-closure e) = ⊥,
      from (@inf_eq_bot_iff_le_compl _ _ _ (principal (- closure e)) (principal (closure e))
        (by simp [principal_univ]) (by simp)).mpr (by simp [this]),
    ⟨- closure e, is_closed_closure, assume x h₁ h₂, @e_subset x h₂ h₁, this⟩ }

/- totally bounded -/
def totally_bounded (s : set α) : Prop :=
∀d ∈ (@uniformity α _).sets, ∃t : set α, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d})

lemma totally_bounded_subset [uniform_space α] {s₁ s₂ : set α} (hs : s₁ ⊆ s₂)
  (h : totally_bounded s₂) : totally_bounded s₁ :=
assume d hd, let ⟨t, ht₁, ht₂⟩ := h d hd in ⟨t, ht₁, subset.trans hs ht₂⟩

lemma totally_bounded_closure [uniform_space α] {s : set α} (h : totally_bounded s) :
  totally_bounded (closure s) :=
assume t ht,
let ⟨t', ht', hct', htt'⟩ := mem_uniformity_is_closed ht, ⟨c, hcf, hc⟩ := h t' ht' in
⟨c, hcf,
  calc closure s ⊆ closure (⋃ (y : α) (H : y ∈ c), {x : α | (x, y) ∈ t'}) : closure_mono hc
    ... = _ : closure_eq_of_is_closed $ is_closed_Union hcf $ assume i hi,
      continuous_iff_is_closed.mp (continuous_prod_mk continuous_id continuous_const) _ hct'
    ... ⊆ _ : bUnion_subset $ assume i hi, subset.trans (assume x, @htt' (x, i))
      (subset_bUnion_of_mem hi)⟩

lemma totally_bounded_image [uniform_space α] [uniform_space β] {f : α → β} {s : set α}
  (hf : uniform_continuous f) (hs : totally_bounded s) : totally_bounded (f '' s) :=
assume t ht,
have {p:α×α | (f p.1, f p.2) ∈ t} ∈ (@uniformity α _).sets,
  from hf ht,
let ⟨c, hfc, hct⟩ := hs _ this in
⟨f '' c, finite_image hfc,
  begin
    simp [image_subset_iff_subset_preimage],
    simp [subset_def] at hct,
    exact (assume x hx, let ⟨i, hi, ht⟩ := hct x hx in ⟨f i, mem_image_of_mem f hi, ht⟩)
  end⟩

lemma cauchy_of_totally_bounded_of_ultrafilter {s : set α} {f : filter α}
  (hs : totally_bounded s) (hf : ultrafilter f) (h : f ≤ principal s) : cauchy f :=
⟨hf.left, assume t ht,
  let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht in
  let ⟨i, hi, hs_union⟩ := hs t' ht'₁ in
  have (⋃y∈i, {x | (x,y) ∈ t'}) ∈ f.sets,
    from f.upwards_sets (le_principal_iff.mp h) hs_union,
  have ∃y∈i, {x | (x,y) ∈ t'} ∈ f.sets,
    from mem_of_finite_Union_ultrafilter hf hi this,
  let ⟨y, hy, hif⟩ := this in
  have set.prod {x | (x,y) ∈ t'} {x | (x,y) ∈ t'} ⊆ comp_rel t' t',
    from assume ⟨x₁, x₂⟩ ⟨(h₁ : (x₁, y) ∈ t'), (h₂ : (x₂, y) ∈ t')⟩,
      ⟨y, h₁, ht'_symm h₂⟩,
  (filter.prod f f).upwards_sets (prod_mem_prod hif hif) (subset.trans this ht'_t)⟩

lemma totally_bounded_iff_filter {s : set α} :
  totally_bounded s ↔ (∀f, f ≠ ⊥ → f ≤ principal s → ∃c ≤ f, cauchy c) :=
⟨assume : totally_bounded s, assume f hf hs,
  ⟨ultrafilter_of f, ultrafilter_of_le,
    cauchy_of_totally_bounded_of_ultrafilter this
      (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hs)⟩,

  assume h : ∀f, f ≠ ⊥ → f ≤ principal s → ∃c ≤ f, cauchy c, assume d hd,
  classical.by_contradiction $ assume hs,
  have hd_cover : ∀{t:set α}, finite t → ¬ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}),
    by simpf at hs,
  let
    f := ⨅t:{t : set α // finite t}, principal (s \ (⋃y∈t.val, {x | (x,y) ∈ d})),
    ⟨a, ha⟩ := @exists_mem_of_ne_empty α s
      (assume h, hd_cover finite.empty $ h.symm ▸ empty_subset _)
  in
  have f ≠ ⊥,
    from infi_neq_bot_of_directed ⟨a⟩
      (assume ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩, ⟨⟨t₁ ∪ t₂, finite_union ht₁ ht₂⟩,
        principal_mono.mpr $ diff_right_antimono $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inl,
        principal_mono.mpr $ diff_right_antimono $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inr⟩)
      (assume ⟨t, ht⟩, by simp [diff_neq_empty]; exact hd_cover ht),
  have f ≤ principal s, from infi_le_of_le ⟨∅, finite.empty⟩ $ by simp; exact subset.refl s,
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
    from le_trans hc₁ $ infi_le_of_le ⟨{y}, finite_insert finite.empty⟩ $ le_refl _,
  have (s - ys) ∩ (m ∩ s) ∈ c.sets,
    from inter_mem_sets (le_principal_iff.mp this) ‹m ∩ s ∈ c.sets›,
  have ∅ ∈ c.sets,
    from c.upwards_sets this $ assume x ⟨⟨hxs, hxys⟩, hxm, _⟩, hxys $ ‹m ⊆ ys› hxm,
  hc₂.left $ empty_in_sets_eq_bot.mp this⟩

lemma totally_bounded_iff_ultrafilter {s : set α} :
  totally_bounded s ↔ (∀f, ultrafilter f → f ≤ principal s → cauchy f) :=
⟨assume hs f, cauchy_of_totally_bounded_of_ultrafilter hs,
  assume h, totally_bounded_iff_filter.mpr $ assume f hf hfs,
  have cauchy (ultrafilter_of f),
    from h (ultrafilter_of f) (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hfs),
  ⟨ultrafilter_of f, ultrafilter_of_le, this⟩⟩

lemma compact_of_totally_bounded_complete {s : set α}
  (ht : totally_bounded s) (hc : ∀{f:filter α}, cauchy f → f ≤ principal s → ∃x∈s, f ≤ nhds x) :
  compact s :=
begin
  rw [compact_iff_ultrafilter_le_nhds],
  rw [totally_bounded_iff_ultrafilter] at ht,
  exact assume f hf hfs, hc (ht _ hf hfs) hfs
end

/- complete space -/
class complete_space (α : Type u) [uniform_space α] : Prop :=
(complete : ∀{f:filter α}, cauchy f → ∃x, f ≤ nhds x)

lemma complete_of_is_closed [complete_space α] {s : set α} {f : filter α}
  (h : is_closed s) (hf : cauchy f) (hfs : f ≤ principal s) : ∃x∈s, f ≤ nhds x :=
let ⟨x, hx⟩ := complete_space.complete hf in
have x ∈ s, from is_closed_iff_nhds.mp h x $ neq_bot_of_le_neq_bot hf.left $
  le_inf hx hfs,
⟨x, this, hx⟩

lemma compact_of_totally_bounded_is_closed [complete_space α] {s : set α}
  (ht : totally_bounded s) (hc : is_closed s) : compact s :=
@compact_of_totally_bounded_complete α _ s ht $ assume f, complete_of_is_closed hc

lemma complete_space_extension [uniform_space β] {m : β → α}
  (hm : uniform_embedding m)
  (dense : ∀x, x ∈ closure (m '' univ))
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
  f.upwards_sets ht $ assume x hx, ⟨x, hx, refl_mem_uniformity hs⟩,

have g ≠ ⊥, from neq_bot_of_le_neq_bot hf.left this,

have vmap m g ≠ ⊥, from vmap_neq_bot $ assume t ht,
  let ⟨t', ht', ht_mem⟩ := (mem_lift_iff $ monotone_lift' monotone_const mp₀).mp ht in
  let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_iff mp₁).mp ht_mem in
  let ⟨x, (hx : x ∈ t'')⟩ := inhabited_of_mem_sets hf.left ht'' in
  have h₀ : nhds x ⊓ principal (m '' univ) ≠ ⊥,
    by simp [closure_eq_nhds] at dense; exact dense x,
  have h₁ : {y | (x, y) ∈ t'} ∈ (nhds x ⊓ principal (m '' univ)).sets,
    from @mem_inf_sets_of_left α (nhds x) (principal (m '' univ)) _ $ mem_nhds_left ht',
  have h₂ : m '' univ ∈ (nhds x ⊓ principal (m '' univ)).sets,
    from @mem_inf_sets_of_right α (nhds x) (principal (m '' univ)) _ $ subset.refl _,
  have {y | (x, y) ∈ t'} ∩ m '' univ ∈ (nhds x ⊓ principal (m '' univ)).sets,
    from @inter_mem_sets α (nhds x ⊓ principal (m '' univ)) _ _ h₁ h₂,
  let ⟨y, xyt', b, _, b_eq⟩ := inhabited_of_mem_sets h₀ this in
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
  (filter.prod g g).upwards_sets hg
    (assume ⟨a, b⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩,
      have (c₁, c₂) ∈ set.prod t t, from ⟨c₁t, c₂t⟩,
      comp_s₁ $ prod_mk_mem_comp_rel hc₁ $
      comp_s₂ $ prod_mk_mem_comp_rel (prod_t this) hc₂)⟩,

have cauchy (filter.vmap m g),
  from cauchy_vmap (le_of_eq hm.right) ‹cauchy g› (by assumption),

let ⟨x, (hx : map m (filter.vmap m g) ≤ nhds x)⟩ := h _ this in
have map m (filter.vmap m g) ⊓ nhds x ≠ ⊥,
  from (le_nhds_iff_adhp_of_cauchy (cauchy_map (uniform_continuous_of_embedding hm) this)).mp hx,
have g ⊓ nhds x ≠ ⊥,
  from neq_bot_of_le_neq_bot this (inf_le_inf (assume s hs, ⟨s, hs, subset.refl _⟩) (le_refl _)),

⟨x, calc f ≤ g : by assumption
  ... ≤ nhds x : le_nhds_of_cauchy_adhp ‹cauchy g› this⟩⟩

/- separation space -/
section separation_space

local attribute [instance] separation_setoid

instance {α : Type u} [u : uniform_space α] : uniform_space (quotient (separation_setoid α)) :=
{ uniform_space .
  to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity,
  refl  := assume s hs ⟨a, b⟩ (h : a = b),
    have ∀a:α, (a, a) ∈ preimage (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) s,
      from assume a, refl_mem_uniformity hs,
    h ▸ quotient.induction_on a this,
  symm  := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_compose tendsto_swap_uniformity tendsto_map,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity).lift' (λs, comp_rel s s) =
          uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
    ... ≤ uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘ (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ separation_rel α := quotient.exact h,
        simp [function.comp, set.image, comp_rel],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) (uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets ↔
          {p:α×α | ⟦p.1⟧ = ⟦a⟧ → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, ⟦a₁⟧ = ⟦a₂⟧ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht (quotient.exact h),
        uniformity.upwards_sets ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' h₂.symm) h₁,
        assume h, uniformity.upwards_sets h $ by simp {contextual := tt}⟩,
    begin
      simp [topological_space.coinduced, u.is_open_uniformity, uniformity, forall_quotient_iff],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniform_continuous_quotient_mk :
  uniform_continuous (quotient.mk : α → quotient (separation_setoid α)) :=
le_refl _

lemma vmap_quotient_le_uniformity : vmap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity ≤ uniformity :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (@uniformity α _).upwards_sets hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma vmap_quotient_eq_uniformity : vmap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity = uniformity :=
le_antisymm vmap_quotient_le_uniformity
  (assume s ⟨t, ht, hs⟩, uniformity.upwards_sets ht hs)

lemma complete_space_separation [h : complete_space α] :
  complete_space (quotient (separation_setoid α)) :=
⟨assume f, assume hf : cauchy f,
  have cauchy (vmap (λx, ⟦x⟧) f), from
    cauchy_vmap vmap_quotient_le_uniformity hf $
      vmap_neq_bot_of_surj hf.left $ assume b, quotient.exists_rep _,
  let ⟨x, (hx : vmap (λx, ⟦x⟧) f ≤ nhds x)⟩ := complete_space.complete this in
  ⟨⟦x⟧, calc f ≤ map (λx, ⟦x⟧) (vmap (λx, ⟦x⟧) f) : le_map_vmap $ assume b, quotient.exists_rep _
    ... ≤ map (λx, ⟦x⟧) (nhds x) : map_mono hx
    ... ≤ _ : continuous_iff_tendsto.mp (continuous_of_uniform uniform_continuous_quotient_mk) _⟩⟩

lemma separated_separation [h : complete_space α] : separated (quotient (separation_setoid α)) :=
set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (vmap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity).sets,
        from vmap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp, exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩

end separation_space

section uniform_extension

variables
  [uniform_space β]
  [uniform_space γ]
  {e : β → α}
  (h_e : uniform_embedding e)
  (h_dense : ∀x, x ∈ closure (e '' univ))
  {f : β → γ}
  (h_f : uniform_continuous f)
  [inhabited γ]

local notation `ψ` := (dense_embedding_of_uniform_embedding h_e h_dense).ext f

lemma uniformly_extend_of_emb [cγ : complete_space γ] [sγ : separated γ] {b : β} :
  ψ (e b) = f b :=
dense_embedding.ext_e_eq _ $ continuous_iff_tendsto.mp (continuous_of_uniform h_f) b

lemma uniformly_extend_exists [complete_space γ] [sγ : separated γ] {a : α} :
  ∃c, tendsto f (vmap e (nhds a)) (nhds c) :=
let de := (dense_embedding_of_uniform_embedding h_e h_dense) in
have cauchy (nhds a), from cauchy_nhds,
have cauchy (vmap e (nhds a)), from
  cauchy_vmap (le_of_eq h_e.right) this de.vmap_nhds_neq_bot,
have cauchy (map f (vmap e (nhds a))), from
  cauchy_map h_f this,
complete_space.complete this

lemma uniformly_extend_spec [complete_space γ] [sγ : separated γ] {a : α} :
  tendsto f (vmap e (nhds a)) (nhds (ψ a)) :=
lim_spec $ uniformly_extend_exists h_e h_dense h_f

lemma uniform_continuous_uniformly_extend [cγ : complete_space γ] [sγ : separated γ] :
  uniform_continuous ψ :=
assume d hd,
let ⟨s, hs, hs_comp⟩ := (mem_lift'_iff $
  monotone_comp_rel monotone_id $ monotone_comp_rel monotone_id monotone_id).mp (comp_le_uniformity3 hd) in
have h_pnt : ∀{a m}, m ∈ (nhds a).sets → ∃c, c ∈ f '' preimage e m ∧ (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s,
  from assume a m hm,
  have nb : map f (vmap e (nhds a)) ≠ ⊥,
    from map_ne_bot (dense_embedding_of_uniform_embedding h_e h_dense).vmap_nhds_neq_bot,
  have (f '' preimage e m) ∩ ({c | (c, ψ a) ∈ s } ∩ {c | (ψ a, c) ∈ s }) ∈ (map f (vmap e (nhds a))).sets,
    from inter_mem_sets (image_mem_map $ preimage_mem_vmap $ hm)
      (uniformly_extend_spec h_e h_dense h_f $ inter_mem_sets (mem_nhds_right hs) (mem_nhds_left hs)),
  inhabited_of_mem_sets nb this,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ (@uniformity β _).sets,
  from h_f hs,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ (vmap (λx:β×β, (e x.1, e x.2)) uniformity).sets,
  by rwa [h_e.right.symm] at this,
let ⟨t, ht, ts⟩ := this in
show preimage (λp:(α×α), (ψ p.1, ψ p.2)) d ∈ uniformity.sets,
  from (@uniformity α _).upwards_sets (interior_mem_uniformity ht) $
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
    ... ⊆ s : image_subset_iff_subset_preimage.mpr $ subset.refl _,
  have (a, b) ∈ s, from @this (a, b) ⟨ha₁, hb₁⟩,
  hs_comp $ show (ψ x₁, ψ x₂) ∈ comp_rel s (comp_rel s s),
    from ⟨a, ha₂, ⟨b, this, hb₂⟩⟩

end uniform_extension
end uniform_space
end

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f }

namespace Cauchy

section
parameters {α : Type u} [uniform_space α]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ (filter.prod (p.1.val) (p.2.val)).sets }

lemma monotone_gen : monotone gen :=
monotone_set_of $ assume p, @monotone_mem_sets (α×α) (filter.prod (p.1.val) (p.2.val))

private lemma symm_gen : map prod.swap (uniformity.lift' gen) ≤ uniformity.lift' gen :=
calc map prod.swap (uniformity.lift' gen) =
  uniformity.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2.val) (p.1.val)).sets }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_preimage_swap]
  end
  ... ≤ uniformity.lift' gen :
    uniformity_lift_le_swap
      (monotone_comp (monotone_set_of $ assume p,
        @monotone_mem_sets (α×α) ((filter.prod ((p.2).val) ((p.1).val)))) monotone_principal)
      begin
        have h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h],
        exact le_refl _
      end

private lemma comp_rel_gen_gen_subset_gen_comp_rel {s t : set (α×α)} : comp_rel (gen s) (gen t) ⊆
  (gen (comp_rel s t) : set (Cauchy α × Cauchy α)) :=
assume ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.left) this in
(filter.prod f.val g.val).upwards_sets
  (prod_mem_prod ht₁ ht₄)
  (assume ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma comp_gen :
  (uniformity.lift' gen).lift' (λs, comp_rel s s) ≤ uniformity.lift' gen :=
calc (uniformity.lift' gen).lift' (λs, comp_rel s s) =
    uniformity.lift' (λs, comp_rel (gen s) (gen s)) :
  begin
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_comp_rel monotone_id monotone_id)
  end
  ... ≤ uniformity.lift' (λs, gen $ comp_rel s s) :
    lift'_mono' $ assume s hs, comp_rel_gen_gen_subset_gen_comp_rel
  ... = (uniformity.lift' $ λs:set(α×α), comp_rel s s).lift' gen :
  begin
    rw [lift'_lift'_assoc],
    exact (monotone_comp_rel monotone_id monotone_id),
    exact monotone_gen
  end
  ... ≤ uniformity.lift' gen : lift'_mono comp_le_uniformity (le_refl _)

instance completion_space : uniform_space (Cauchy α) :=
uniform_space.of_core
{ uniformity  := uniformity.lift' gen,
  refl        := principal_le_lift' $ assume s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a.property.right hs,
  symm        := symm_gen,
  comp        := comp_gen }

def pure_cauchy (a : α) : Cauchy α :=
⟨pure a, cauchy_pure⟩

lemma uniform_embedding_pure_cauchy : uniform_embedding (pure_cauchy : α → Cauchy α) :=
⟨assume a₁ a₂ h,
  have (pure_cauchy a₁).val = (pure_cauchy a₂).val, from congr_arg _ h,
  have {a₁} = ({a₂} : set α),
    from principal_eq_iff_eq.mp this,
  by simp at this; assumption,

  have (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) = id,
    from funext $ assume s, set.ext $ assume ⟨a₁, a₂⟩,
      by simp [preimage, gen, pure_cauchy, prod_principal_principal],
  calc vmap (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) (uniformity.lift' gen)
        = uniformity.lift' (preimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) :
      vmap_lift'_eq monotone_gen
    ... = uniformity : by simp [this]⟩

lemma pure_cauchy_dense : ∀x, x ∈ closure (pure_cauchy '' univ) :=
assume f,
have h_ex : ∀s∈(@uniformity (Cauchy α) _).sets, ∃y:α, (f, pure_cauchy y) ∈ s, from
  assume s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_iff monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁ in
  have t' ∈ (filter.prod (f.val) (f.val)).sets,
    from f.property.right ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := inhabited_of_mem_sets f.property.left ht in
  have t'' ∈ (filter.prod f.val (pure x)).sets,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'},
      assume y, begin simp, intro h, simp [h], exact refl_mem_uniformity ht'₁ end,
      assume ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp [closure_eq_nhds, nhds_eq_uniformity, lift'_inf_principal_eq],
  exact (lift'_neq_bot_iff $ monotone_inter monotone_const monotone_preimage).mpr
    (assume s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have pure_cauchy y ∈ pure_cauchy '' univ ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_image_of_mem _ $ mem_univ y, hy⟩,
      ne_empty_of_mem this)
end

instance : complete_space (Cauchy α) :=
complete_space_extension
  uniform_embedding_pure_cauchy
  pure_cauchy_dense $
  assume f hf,
  let f' : Cauchy α := ⟨f, hf⟩ in
  have map pure_cauchy f ≤ uniformity.lift' (preimage (prod.mk f')),
    from le_lift' $ assume s hs,
    let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_iff monotone_gen).mp hs in
    let ⟨t', ht', (h : set.prod t' t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁) in
    have t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t },
      from assume x hx, (filter.prod f (pure x)).upwards_sets (prod_mem_prod ht' $ mem_pure hx) h,
    f.upwards_sets ht' $ subset.trans this (preimage_mono ht₂),
  ⟨f', by simp [nhds_eq_uniformity]; assumption⟩

end

end Cauchy

instance nonempty_Cauchy {α : Type u} [h : nonempty α] [uniform_space α] : nonempty (Cauchy α) :=
h.rec_on $ assume a, nonempty.intro $ Cauchy.pure_cauchy a

instance inhabited_Cauchy {α : Type u} [inhabited α] [uniform_space α] : inhabited (Cauchy α) :=
⟨Cauchy.pure_cauchy $ default α⟩

section constructions
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y}

instance : partial_order (uniform_space α) :=
{ le          := λt s, s.uniformity ≤ t.uniformity,
  le_antisymm := assume t s h₁ h₂, uniform_space_eq $ le_antisymm h₂ h₁,
  le_refl     := assume t, le_refl _,
  le_trans    := assume a b c h₁ h₂, @le_trans _ _ c.uniformity b.uniformity a.uniformity h₂ h₁ }

instance : has_Sup (uniform_space α) :=
⟨assume s, uniform_space.of_core { uniform_space.core .
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
  uniformity := principal id_rel,
  refl        := le_refl _,
  symm        := by simp [tendsto]; apply subset.refl,
  comp        :=
  begin
    rw [lift'_principal],
    { simp, apply subset.refl },
    exact monotone_comp_rel monotone_id monotone_id
  end,
  is_open_uniformity :=
    by rw [topological_space.lattice.has_top]; simp [subset_def, id_rel] {contextual := tt }
}⟩

instance : complete_lattice (uniform_space α) :=
{ uniform_space.partial_order with
  sup           := λa b, Sup {a, b},
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
  Inf_le        := assume s a ha, Sup_le $ assume u hs, hs _ ha }

lemma supr_uniformity {ι : Sort v} {u : ι → uniform_space α} :
  (supr u).uniformity = (⨅i, (u i).uniformity) :=
show (⨅a (h : ∃i:ι, a = u i), a.uniformity) = _, from
le_antisymm
  (le_infi $ assume i, infi_le_of_le (u i) $ infi_le _ ⟨i, rfl⟩)
  (le_infi $ assume a, le_infi $ assume ⟨i, (ha : a = u i)⟩, ha.symm ▸ infi_le _ _)

lemma sup_uniformity {u v : uniform_space α} :
  (u ⊔ v).uniformity = u.uniformity ⊓ v.uniformity :=
have (u ⊔ v) = (⨆i (h : i = u ∨ i = v), i), by simp [supr_or, supr_sup_eq],
calc (u ⊔ v).uniformity = ((⨆i (h : i = u ∨ i = v), i) : uniform_space α).uniformity : by rw [this]
  ... = _ : by simp [supr_uniformity, infi_or, infi_inf_eq]

instance inhabited_uniform_space : inhabited (uniform_space α) := ⟨⊤⟩

def uniform_space.vmap (f : α → β) (u : uniform_space β) : uniform_space α :=
{ uniformity := u.uniformity.vmap (λp:α×α, (f p.1, f p.2)),
  to_topological_space := u.to_topological_space.induced f,
  refl := le_trans (by simp; exact assume ⟨a, b⟩ (h : a = b), h ▸ rfl) (vmap_mono u.refl),
  symm := tendsto_vmap' $ by simp [prod.swap, (∘)]; exact tendsto_compose tendsto_vmap tendsto_swap_uniformity,
  comp := le_trans
    begin
      rw [vmap_lift'_eq, vmap_lift'_eq2],
      exact (lift'_mono' $ assume s hs ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩, ⟨f x, h₁, h₂⟩),
      repeat { exact monotone_comp_rel monotone_id monotone_id }
    end
    (vmap_mono u.comp),
  is_open_uniformity :=
  begin
    intro s,
    change (@is_open α (u.to_topological_space.induced f) s ↔ _),
    simp [is_open_iff_nhds, nhds_induced_eq_vmap, mem_nhds_uniformity_iff, filter.vmap],
    exact (ball_congr $ assume x hx,
      ⟨assume ⟨t, hts, ht⟩, ⟨_, ht, assume ⟨x₁, x₂⟩, by simp [*, subset_def] at * {contextual := tt} ⟩,
        assume ⟨t, ht, hts⟩, ⟨{y:β | (f x, y) ∈ t},
          assume y (hy : (f x, f y) ∈ t), @hts (x, y) hy rfl,
          mem_nhds_uniformity_iff.mp $ mem_nhds_left ht⟩⟩)
  end }

lemma uniform_continuous_vmap {f : α → β} [u : uniform_space β] :
  @uniform_continuous α β (uniform_space.vmap f u) u f :=
tendsto_vmap

theorem to_topological_space_vmap {f : α → β} {u : uniform_space β} :
  @uniform_space.to_topological_space _ (uniform_space.vmap f u) =
  topological_space.induced f (@uniform_space.to_topological_space β u) :=
eq_of_nhds_eq_nhds $ assume a,
begin
  simp [nhds_induced_eq_vmap, nhds_eq_uniformity, nhds_eq_uniformity],
  change vmap f (uniformity.lift' (preimage (λb, (f a, b)))) =
      (u.uniformity.vmap (λp:α×α, (f p.1, f p.2))).lift' (preimage (λa', (a, a'))),
  rw [vmap_lift'_eq monotone_preimage, vmap_lift'_eq2 monotone_preimage],
  exact rfl
end

lemma uniform_continuous_vmap' {f : γ → β} {g : α → γ} [v : uniform_space β] [u : uniform_space α]
  (h : uniform_continuous (f ∘ g)) : @uniform_continuous α γ u (uniform_space.vmap f v) g :=
tendsto_vmap' h

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
    have univ ⊆ _,
      from hs x hx,
    have s = univ,
      from top_unique $ assume y hy, @this (x, y) ⟨⟩ rfl,
    this.symm ▸ @is_open_univ _ ⊥)

lemma to_topological_space_supr {ι : Sort v} {u : ι → uniform_space α} :
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
  apply funext,
  intro x,
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
uniform_space.vmap subtype.val t

lemma uniformity_subtype {p : α → Prop} [t : uniform_space α] :
  (@uniformity (subtype p) _) = vmap (λq:subtype p × subtype p, (q.1.1, q.2.1)) uniformity :=
rfl

lemma uniform_continuous_subtype_val {p : α → Prop} [uniform_space α] :
  uniform_continuous (subtype.val : {a : α // p a} → α) :=
uniform_continuous_vmap

lemma uniform_continuous_subtype_mk {p : α → Prop} [uniform_space α] [uniform_space β]
  {f : β → α} (hf : uniform_continuous f) (h : ∀x, p (f x)) :
  uniform_continuous (λx, ⟨f x, h x⟩ : β → subtype p) :=
uniform_continuous_vmap' hf

instance [u₁ : uniform_space α] [u₂ : uniform_space β] : uniform_space (α × β) :=
uniform_space.of_core_eq
  (u₁.vmap prod.fst ⊔ u₂.vmap prod.snd).to_core
  prod.topological_space
  (calc prod.topological_space = (u₁.vmap prod.fst ⊔ u₂.vmap prod.snd).to_topological_space :
      by rw [to_topological_space_sup, to_topological_space_vmap, to_topological_space_vmap]; refl
    ... = _ : by rw [uniform_space.to_core_to_topological_space])

lemma uniform_embedding_subtype_emb {α : Type u} {β : Type v} [uniform_space α] [uniform_space β]
  (p : α → Prop) {e : α → β} (ue : uniform_embedding e) (de : dense_embedding e) :
  uniform_embedding (de.subtype_emb p) :=
⟨(de.subtype p).inj,
  by simp [vmap_vmap_comp, (∘), dense_embedding.subtype_emb, uniformity_subtype, ue.right.symm]⟩

lemma uniform_extend_subtype {α : Type u} {β : Type v} {γ : Type w}
  [uniform_space α] [uniform_space β] [uniform_space γ] [complete_space γ]
  [inhabited γ] [separated γ]
  {p : α → Prop} {e : α → β} {f : α → γ} {b : β} {s : set α}
  (hf : uniform_continuous (λx:subtype p, f x.val))
  (he : uniform_embedding e) (hd : ∀x, x ∈ closure (e '' univ))
  (hb : closure (e '' s) ∈ (nhds b).sets) (hs : is_closed s) (hp : ∀x∈s, p x) :
  ∃c, tendsto f (vmap e (nhds b)) (nhds c) :=
have de : dense_embedding e,
  from dense_embedding_of_uniform_embedding he hd,
have de' : dense_embedding (de.subtype_emb p),
  by exact de.subtype p,
have ue' : uniform_embedding (de.subtype_emb p),
  from uniform_embedding_subtype_emb _ he de,
have b ∈ closure (e '' {x | p x}),
  from (closure_mono $ mono_image $ hp) (mem_of_nhds hb),
let ⟨c, (hc : tendsto (f ∘ subtype.val) (vmap (de.subtype_emb p) (nhds ⟨b, this⟩)) (nhds c))⟩ :=
  uniformly_extend_exists ue' de'.dense hf in
begin
  rw [nhds_subtype_eq_vmap] at hc,
  simp [vmap_vmap_comp] at hc,
  change (tendsto (f ∘ @subtype.val α p) (vmap (e ∘ @subtype.val α p) (nhds b)) (nhds c)) at hc,
  rw [←vmap_vmap_comp] at hc,
  existsi c,
  apply tendsto_vmap'' s _ _ hc,
  exact ⟨_, hb, assume x,
    begin
      change e x ∈ (closure (e '' s)) → x ∈ s,
      rw [←closure_induced, closure_eq_nhds],
      dsimp,
      rw [nhds_induced_eq_vmap, de.induced],
      change x ∈ {x | nhds x ⊓ principal s ≠ ⊥} → x ∈ s,
      rw [←closure_eq_nhds, closure_eq_of_is_closed hs],
      exact id,
      exact de.inj
    end⟩,
  exact (assume x hx, ⟨⟨x, hp x hx⟩, rfl⟩)
end

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/

lemma uniformity_prod [uniform_space α] [uniform_space β] :
  @uniformity (α×β) _ =
    vmap (λp:(α×β)×(α×β), (p.1.1, p.2.1)) uniformity ⊓
    vmap (λp:(α×β)×(α×β), (p.1.2, p.2.2)) uniformity :=
by rw [prod.uniform_space, uniform_space.of_core_eq_to_core, uniformity, sup_uniformity]; refl

lemma uniformity_prod_eq_prod [uniform_space α] [uniform_space β] :
  @uniformity (α×β) _ =
    map (λp:(α×α)×(β×β), ((p.1.1, p.2.1), (p.1.2, p.2.2))) (filter.prod uniformity uniformity) :=
have map (λp:(α×α)×(β×β), ((p.1.1, p.2.1), (p.1.2, p.2.2))) =
  vmap (λp:(α×β)×(α×β), ((p.1.1, p.2.1), (p.1.2, p.2.2))),
  from funext $ assume f, map_eq_vmap_of_inverse
    (funext $ assume ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl) (funext $ assume ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl),
by rw [this, uniformity_prod, prod_def, vmap_inf, vmap_vmap_comp, vmap_vmap_comp]

lemma mem_uniform_prod [t₁ : uniform_space α] [t₂ : uniform_space β] {a : set (α × α)} {b : set (β × β)}
  (ha : a ∈ (@uniformity α _).sets) (hb : b ∈ (@uniformity β _).sets) :
  {p:(α×β)×(α×β) | (p.1.1, p.2.1) ∈ a ∧ (p.1.2, p.2.2) ∈ b } ∈ (@uniformity (α × β) _).sets :=
by rw [uniformity_prod]; exact inter_mem_inf_sets (preimage_mem_vmap ha) (preimage_mem_vmap hb)

lemma tendsto_prod_uniformity_fst [uniform_space α] [uniform_space β] :
  tendsto (λp:(α×β)×(α×β), (p.1.1, p.2.1)) uniformity uniformity :=
le_trans (map_mono (@le_sup_left (uniform_space (α×β)) _ _ _)) map_vmap_le

lemma tendsto_prod_uniformity_snd [uniform_space α] [uniform_space β] :
  tendsto (λp:(α×β)×(α×β), (p.1.2, p.2.2)) uniformity uniformity :=
le_trans (map_mono (@le_sup_right (uniform_space (α×β)) _ _ _)) map_vmap_le

lemma uniform_continuous_fst [uniform_space α] [uniform_space β] : uniform_continuous (λp:α×β, p.1) :=
tendsto_prod_uniformity_fst

lemma uniform_continuous_snd [uniform_space α] [uniform_space β] : uniform_continuous (λp:α×β, p.2) :=
tendsto_prod_uniformity_snd

lemma uniform_continuous_prod_mk [uniform_space α] [uniform_space β] [uniform_space γ]
  {f₁ : α → β} {f₂ : α → γ} (h₁ : uniform_continuous f₁) (h₂ : uniform_continuous f₂) :
  uniform_continuous (λa, (f₁ a, f₂ a)) :=
by
  rw [uniform_continuous, uniformity_prod];
  exact tendsto_inf (tendsto_vmap' h₁) (tendsto_vmap' h₂)

lemma uniform_embedding_prod {α' : Type w} {β' : Type x}
  [uniform_space α] [uniform_space β] [uniform_space α'] [uniform_space β']
  {e₁ : α → α'} {e₂ : β → β'} (h₁ : uniform_embedding e₁) (h₂ : uniform_embedding e₂) :
  uniform_embedding (λp:α×β, (e₁ p.1, e₂ p.2)) :=
⟨assume ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  by simp [prod.mk.inj_iff]; exact assume eq₁ eq₂, ⟨h₁.left _ _ eq₁, h₂.left _ _ eq₂⟩,
  by simp [(∘), uniformity_prod, h₁.right.symm, h₂.right.symm, vmap_inf, vmap_vmap_comp]⟩

lemma to_topological_space_prod [u : uniform_space α] [v : uniform_space β] :
  @uniform_space.to_topological_space (α × β) prod.uniform_space =
    @prod.topological_space α β u.to_topological_space v.to_topological_space := rfl

lemma to_topological_space_subtype [u : uniform_space α] {p : α → Prop} :
  @uniform_space.to_topological_space (subtype p) subtype.uniform_space =
    @subtype.topological_space α p u.to_topological_space := rfl

end constructions
