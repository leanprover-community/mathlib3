/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import linear_algebra.linear_pmap
import topology.algebra.module.basic

/-!
# Linear operators over topological vector spaces

We define basic notions of linear operators (also known as `linear_pmap`s in mathlib).
In this file we prove all elementary properties that do not assume that the underlying spaces
are normed.

## Main definitions

* `linear_pmap.closed`: an operator is closed iff its graph is closed
* `linear_pmap.closable`: an operator is closable iff the closure of its graph is a graph
* `linear_pmap.closure`: the closure of a closable operator
* `linear_pmap.is_core`: a submodule contained in the domain is a core if restricting to the core
  does not lose information about the operator

## Main statements

* `closable_iff_exists_closed_extension`: an operator is closable iff it has a closed extension
* `closable.exists_unique`: there exists a unique closure

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/


open_locale topological_space

variables {R E F 𝕜: Type*}

variables [comm_ring R] [add_comm_group E] [add_comm_group F]
variables [module R E] [module R F]
variables [topological_space E] [topological_space F]

namespace linear_pmap

/-! ### Closed and closable operators -/

/-- An operator is closed if its graph is closed. -/
def closed (f : linear_pmap R E F) : Prop :=
is_closed (f.graph : set (E × F))

variables [has_continuous_add E] [has_continuous_add F]
variables [topological_space R] [has_continuous_smul R E] [has_continuous_smul R F]

/-- An operator is closable if the closure of the graph is a graph. -/
def closable (f : linear_pmap R E F) : Prop :=
∃ (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph

/-- A closed operator is trivially closable. -/
lemma closed.closable {f : linear_pmap R E F} (hf : f.closed) : f.closable :=
⟨f, hf.submodule_topological_closure_eq⟩

/-- If `f` has a closable extension `g`, then `f` itself is closable. -/
lemma closable.le_closable {f g : linear_pmap R E F} (hf : f.closable) (hfg : g ≤ f) : g.closable :=
begin
  cases hf with f' hf,
  have : g.graph.topological_closure ≤ f'.graph :=
  by { rw ←hf, exact submodule.topological_closure_mono (le_graph_of_le hfg) },
  refine ⟨g.graph.topological_closure.to_linear_pmap _, _⟩,
  { intros x hx hx',
    cases x,
    exact f'.graph_fst_eq_zero_snd (this hx) hx' },
  rw [submodule.to_linear_pmap_graph_eq],
end

/-- The closure is unique. -/
lemma closable.exists_unique {f : linear_pmap R E F} (hf : f.closable) :
  ∃! (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph :=
begin
  refine exists_unique_of_exists_of_unique hf (λ _ _ hy₁ hy₂, eq_of_eq_graph _),
  rw [←hy₁, ←hy₂],
end

/-- The closure of a closable operator. -/
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

lemma closable.closure_mono {f g : linear_pmap R E F} (hf : f.closable) (hg : g.closable)
  (h : f ≤ g) :
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
  rw [closed, ←hf.graph_closure_eq_closure_graph],
  exact f.graph.is_closed_topological_closure,
end

lemma closable_iff_exists_closed_extension {f : linear_pmap R E F} : f.closable ↔
  ∃ (g : linear_pmap R E F) (hg : g.closed), f ≤ g :=
⟨λ h, ⟨h.closure, h.closure_closed, h.le_closure⟩, λ ⟨_, hg, h⟩, hg.closable.le_closable h⟩

lemma congr_closure {f g : linear_pmap R E F} (hf : f.closable) (hg : g.closable) (h : f = g)
  : hf.closure = hg.closure :=
begin
  refine eq_of_eq_graph _,
  rw [←hf.graph_closure_eq_closure_graph, ←hg.graph_closure_eq_closure_graph, h],
end

/-! ### The core of a linear operator -/

/-- A submodule `S` is a core of `f` if the closure of the restriction of `f` to `S` is again `f`.-/
def is_core {f : linear_pmap R E F} {S : submodule R E} (hS : S ≤ f.domain)
  (hf : f.closed) : Prop :=
(hf.closable.le_closable (linear_pmap.dom_restrict_le hS)).closure = f

@[simp] lemma is_core_def {f : linear_pmap R E F} {S : submodule R E} (hS : S ≤ f.domain)
  (hf : f.closed) (h : is_core hS hf) :
  (hf.closable.le_closable (dom_restrict_le hS)).closure = f := h

/-- For every closable operator `f` the submodule `f.domain` is a core of its closure. -/
lemma core_of_closure {f : linear_pmap R E F} (hf : f.closable) :
  is_core hf.le_closure.1 hf.closure_closed :=
begin
  refine congr_closure _ _ _,
  ext,
  { simp },
  intros x y hxy,
  let z : hf.closure.domain := ⟨y.1, hf.le_closure.1 y.2⟩,
  have hyz : (y : E) = z := by simp,
  rw hf.le_closure.2 hyz,
  exact dom_restrict_apply _ (hxy.trans hyz),
end

end linear_pmap
