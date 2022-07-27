/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import linear_algebra.linear_pmap
import topology.algebra.module.basic
import topology.sequences

/-!
# Linear Pmap

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open_locale topological_space

variables {R E F 𝕜: Type*}

variables [comm_ring R] [add_comm_group E] [add_comm_group F]
variables [module R E] [module R F] [topological_space R]

namespace linear_pmap

lemma le_graph_of_le {f g : linear_pmap R E F} (h : f ≤ g) : f.graph ≤ g.graph :=
begin
  intros x hx,
  rw mem_graph_iff at hx ⊢,
  cases hx with y hx,
  use y,
  { exact h.1 y.2 },
  cases x,
  simp at hx,
  simp only [hx.1, submodule.coe_mk, eq_self_iff_true, true_and],
  let hx' := hx.2,
  rw hx',
  refine h.2 _,
  simp only [submodule.coe_mk],
end

/-- An operator is closed if its graph is closed. -/
def closed (f : linear_pmap R E F) : Prop :=
is_closed (↑f.graph : set (E × F))

lemma closed_iff (f : linear_pmap R E F) : f.closed ↔ is_closed (f.graph : set (E × F)) := iff.rfl

variables [has_continuous_smul R E] [has_continuous_smul R F]

lemma mem_domain_of_mem_graph {f : linear_pmap R E F} {x : E} {y : F} (h : (x,y) ∈ f.graph) :
  x ∈ f.domain :=
begin
  rw mem_domain_iff,
  exact ⟨y, h⟩,
end

/-- The topological closure of a closed submodule `s` is equal to `s`. -/
lemma _root_.is_closed.topological_closure_eq {s : submodule R E} (hs : is_closed (s : set E)) :
  s.topological_closure = s :=
le_antisymm (s.topological_closure_minimal rfl.le hs) s.submodule_topological_closure

/-- An operator is closable if the closure of the graph is a graph. -/
def closable (f : linear_pmap R E F) : Prop :=
∃ (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph

/-- A closed operator is trivially closable. -/
lemma closed.closable {f : linear_pmap R E F} (hf : f.closed) : f.closable :=
⟨f, hf.topological_closure_eq⟩

lemma closed.le_closable {f g : linear_pmap R E F} (hf : f.closable) (hfg : g ≤ f) : g.closable :=
begin
  cases hf with f' hf,
  sorry,
end

/-- The closure is unique. -/
lemma closable.exists_unique {f g g' : linear_pmap R E F} (hf : f.closable) :
  ∃! (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph :=
begin
  refine exists_unique_of_exists_of_unique hf (λ _ _ hy₁ hy₂, eq_of_eq_graph _),
  rw [←hy₁, ←hy₂],
end

noncomputable
def closable.closure {f : linear_pmap R E F} (hf : f.closable) : linear_pmap R E F :=
hf.some

/-- The closure (as a submodule) of the graph is equal to the graph of the closure
  (as a `linear_pmap`). -/
lemma closable.graph_closure_eq_closure_graph {f : linear_pmap R E F} (hf : f.closable) :
  f.graph.topological_closure = hf.closure.graph :=
hf.some_spec

/-- A closable `linear_pmap` is contained in its closure. -/
lemma closable.le_closure {f : linear_pmap R E F} (hf : f.closable) : f ≤ hf.closure :=
begin
  refine le_of_le_graph _,
  rw ←hf.graph_closure_eq_closure_graph,
  exact (graph f).submodule_topological_closure,
end

lemma closable.closure_mono {f g : linear_pmap R E F} (hf : f.closable) (hg : g.closable) (h : f ≤ g) :
  hf.closure ≤ hg.closure :=
begin
  refine le_of_le_graph _,
  rw ←hf.graph_closure_eq_closure_graph,
  rw ←hg.graph_closure_eq_closure_graph,
  exact submodule.topological_closure_mono (le_graph_of_le h),
end

/-- The closure is closed. -/
lemma closable.closure_closed {f : linear_pmap R E F} (hf : f.closable) : hf.closure.closed :=
begin
  rw [closed_iff, ←hf.graph_closure_eq_closure_graph],
  exact f.graph.is_closed_topological_closure,
end

end linear_pmap
