/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import linear_algebra.linear_pmap
import topology.algebra.module.basic

/-!
# Partially defined linear operators over topological vector spaces

We define basic notions of partially defined linear operators, which we call unbounded operators
for short.
In this file we prove all elementary properties of unbounded operators that do not assume that the
underlying spaces are normed.

## Main definitions

* `linear_pmap.is_closed`: An unbounded operator is closed iff its graph is closed.
* `linear_pmap.is_closable`: An unbounded operator is closable iff the closure of its graph is a
  graph.
* `linear_pmap.closure`: For a closable unbounded operator `f : linear_pmap 𝕜 E F` the closure is
  the smallest closed extension of `f`. If `f` is not closable, then `f.closure` is defined as `f`.
* `linear_pmap.has_core`: a submodule contained in the domain is a core if restricting to the core
  does not lose information about the unbounded operator.

## Main statements

* `linear_pmap.closable_iff_exists_closed_extension`: an unbounded operator is closable iff it has a
  closed extension.
* `linear_pmap.closable.exists_unique`: there exists a unique closure
* `linear_pmap.closure_has_core`: the domain of `f` is a core of its closure

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

/-- An unbounded operator is closed iff its graph is closed. -/
def is_closed (f : linear_pmap R E F) : Prop :=
is_closed (f.graph : set (E × F))

variables [has_continuous_add E] [has_continuous_add F]
variables [topological_space R] [has_continuous_smul R E] [has_continuous_smul R F]

/-- An unbounded operator is closable iff the closure of its graph is a graph. -/
def is_closable (f : linear_pmap R E F) : Prop :=
∃ (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph

/-- A closed operator is trivially closable. -/
lemma is_closed.is_closable {f : linear_pmap R E F} (hf : f.is_closed) : f.is_closable :=
⟨f, hf.submodule_topological_closure_eq⟩

/-- If `f` has a closable extension `g`, then `f` itself is closable. -/
lemma is_closable.le_is_closable {f g : linear_pmap R E F} (hf : f.is_closable) (hfg : g ≤ f) :
  g.is_closable :=
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
lemma is_closable.exists_unique {f : linear_pmap R E F} (hf : f.is_closable) :
  ∃! (f' : linear_pmap R E F), f.graph.topological_closure = f'.graph :=
begin
  refine exists_unique_of_exists_of_unique hf (λ _ _ hy₁ hy₂, eq_of_eq_graph _),
  rw [←hy₁, ←hy₂],
end

open_locale classical

/-- If `f` is closable, then `f.closure` is the closure. Otherwise it is defined
as `f.closure = f`. -/
noncomputable
def closure (f : linear_pmap R E F) : linear_pmap R E F :=
if hf : f.is_closable then hf.some else f

lemma closure_def {f : linear_pmap R E F} (hf : f.is_closable) :
  f.closure = hf.some :=
by simp [closure, hf]

lemma closure_def' {f : linear_pmap R E F} (hf : ¬f.is_closable) :
  f.closure = f :=
by simp [closure, hf]

/-- The closure (as a submodule) of the graph is equal to the graph of the closure
  (as a `linear_pmap`). -/
lemma is_closable.graph_closure_eq_closure_graph {f : linear_pmap R E F} (hf : f.is_closable) :
  f.graph.topological_closure = f.closure.graph :=
begin
  rw closure_def hf,
  exact hf.some_spec,
end

/-- A `linear_pmap` is contained in its closure. -/
lemma le_closure (f : linear_pmap R E F) : f ≤ f.closure :=
begin
  by_cases hf : f.is_closable,
  { refine le_of_le_graph _,
    rw ←hf.graph_closure_eq_closure_graph,
    exact (graph f).submodule_topological_closure },
  rw closure_def' hf,
end

lemma is_closable.closure_mono {f g : linear_pmap R E F} (hg : g.is_closable) (h : f ≤ g) :
  f.closure ≤ g.closure :=
begin
  refine le_of_le_graph _,
  rw ←(hg.le_is_closable h).graph_closure_eq_closure_graph,
  rw ←hg.graph_closure_eq_closure_graph,
  exact submodule.topological_closure_mono (le_graph_of_le h),
end

/-- If `f` is closable, then the closure is closed. -/
lemma is_closable.closure_is_closed {f : linear_pmap R E F} (hf : f.is_closable) :
  f.closure.is_closed :=
begin
  rw [is_closed, ←hf.graph_closure_eq_closure_graph],
  exact f.graph.is_closed_topological_closure,
end

/-- If `f` is closable, then the closure is closable. -/
lemma is_closable.closure_is_closable {f : linear_pmap R E F} (hf : f.is_closable) :
  f.closure.is_closable :=
hf.closure_is_closed.is_closable

lemma is_closable_iff_exists_closed_extension {f : linear_pmap R E F} : f.is_closable ↔
  ∃ (g : linear_pmap R E F) (hg : g.is_closed), f ≤ g :=
⟨λ h, ⟨f.closure, h.closure_is_closed, f.le_closure⟩, λ ⟨_, hg, h⟩, hg.is_closable.le_is_closable h⟩

/-! ### The core of a linear operator -/

/-- A submodule `S` is a core of `f` if the closure of the restriction of `f` to `S` is again `f`.-/
structure has_core (f : linear_pmap R E F) (S : submodule R E) : Prop :=
(le_domain : S ≤ f.domain)
(closure_eq : (f.dom_restrict S).closure = f)

lemma has_core_def {f : linear_pmap R E F} {S : submodule R E} (h : f.has_core S) :
(f.dom_restrict S).closure = f := h.2

/-- For every unbounded operator `f` the submodule `f.domain` is a core of its closure.

Note that we don't require that `f` is closable, due to the definition of the closure. -/
lemma closure_has_core (f : linear_pmap R E F) : f.closure.has_core f.domain :=
begin
  refine ⟨f.le_closure.1, _⟩,
  congr,
  ext,
  { simp only [dom_restrict_domain, submodule.mem_inf, and_iff_left_iff_imp],
    intro hx,
    exact f.le_closure.1 hx },
  intros x y hxy,
  let z : f.closure.domain := ⟨y.1, f.le_closure.1 y.2⟩,
  have hyz : (y : E) = z := by simp,
  rw f.le_closure.2 hyz,
  exact dom_restrict_apply (hxy.trans hyz),
end

end linear_pmap
