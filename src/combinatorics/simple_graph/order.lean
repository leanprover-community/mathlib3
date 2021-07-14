/-
Copyright (c) 2021 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import combinatorics.simple_graph.subgraph

namespace simple_graph

variable {V : Type*}

def is_subgraph (x y : simple_graph V) := ∀ {v w : V}, x.adj v w → y.adj v w

/-- The union of two `simple_graph`s. -/
def union (x y : simple_graph V) : simple_graph V :=
{ adj := λ v w, x.adj v w ∨ y.adj v w,
  sym := λ v w h, by rwa [x.adj_comm, y.adj_comm] }

/-- The intersection of two `simple_graph`s. -/
def inter (x y : simple_graph V) : simple_graph V :=
{ adj := λ v w, x.adj v w ∧ y.adj v w }

instance : has_union (simple_graph V) := ⟨union⟩
instance : has_inter (simple_graph V) := ⟨inter⟩

instance : bounded_lattice (simple_graph V) :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  top := complete_graph V,
  bot := empty_graph V,
  le_refl := λ _ _ _ h, h,
  le_trans := λ x y z hxy hyz _ _ h, hyz (hxy h),
  le_antisymm := λ x y hxy hyx, by { ext v w, exact ⟨λ h, hxy h, λ h, hyx h⟩ },
  le_top := λ x v w h, x.ne_of_adj h,
  bot_le := λ x v w h, h.elim,
  sup_le := λ x y z hxy hyz v w h, h.cases_on (λ h, hxy h) (λ h, hyz h),
  le_sup_left := λ x y v w h, or.inl h,
  le_sup_right := λ x y v w h, or.inr h,
  le_inf := λ x y z hxy hyz v w h, ⟨hxy h, hyz h⟩,
  inf_le_left := λ x y v w h, h.1,
  inf_le_right := λ x y v w h, h.2 }

end simple_graph
