/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.local_extr
import topology.order.basic

/-!
# Maximum/minimum on the closure of a set

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove several versions of the following statement: if `f : X → Y` has a (local or
not) maximum (or minimum) on a set `s` at a point `a` and is continuous on the closure of `s`, then
`f` has an extremum of the same type on `closure s` at `a`.
-/

open filter set
open_locale topology

variables {X Y : Type*} [topological_space X] [topological_space Y] [preorder Y]
  [order_closed_topology Y] {f g : X → Y} {s : set X} {a : X}

protected lemma is_max_on.closure (h : is_max_on f s a) (hc : continuous_on f (closure s)) :
  is_max_on f (closure s) a :=
λ x hx, continuous_within_at.closure_le hx ((hc x hx).mono subset_closure)
  continuous_within_at_const h

protected lemma is_min_on.closure (h : is_min_on f s a) (hc : continuous_on f (closure s)) :
  is_min_on f (closure s) a :=
h.dual.closure hc

protected lemma is_extr_on.closure (h : is_extr_on f s a) (hc : continuous_on f (closure s)) :
  is_extr_on f (closure s) a :=
h.elim (λ h, or.inl $ h.closure hc) (λ h, or.inr $ h.closure hc)

protected lemma is_local_max_on.closure (h : is_local_max_on f s a)
  (hc : continuous_on f (closure s)) :
  is_local_max_on f (closure s) a :=
begin
  rcases mem_nhds_within.1 h with ⟨U, Uo, aU, hU⟩,
  refine mem_nhds_within.2 ⟨U, Uo, aU, _⟩,
  rintro x ⟨hxU, hxs⟩,
  refine continuous_within_at.closure_le _ _ continuous_within_at_const hU,
  { rwa [mem_closure_iff_nhds_within_ne_bot, nhds_within_inter_of_mem,
      ← mem_closure_iff_nhds_within_ne_bot],
    exact nhds_within_le_nhds (Uo.mem_nhds hxU) },
  { exact (hc _ hxs).mono ((inter_subset_right _ _).trans subset_closure) }
end

protected lemma is_local_min_on.closure (h : is_local_min_on f s a)
  (hc : continuous_on f (closure s)) :
  is_local_min_on f (closure s) a :=
is_local_max_on.closure h.dual hc

protected lemma is_local_extr_on.closure (h : is_local_extr_on f s a)
  (hc : continuous_on f (closure s)) :
  is_local_extr_on f (closure s) a :=
h.elim (λ h, or.inl $ h.closure hc) (λ h, or.inr $ h.closure hc)
