/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.basic

/-!
# Weighted graphs

This file defines weighted adirected graphs.
-/

variables {ι α β W W' : Type*} {σ : ι → Type*}

/-- `W`-weighted graphs on `α`. `weight a b = some w` represents an edge between `a, b : α` of
weight `w : W`. `weight a b = none` represents no edge between `a` and `b`. -/
structure weighted_graph (α : Type*) (W : Type*) :=
(weight : α → α → option W)
(weight_self (a : α) : weight a a = none)
(weight_comm (a b : α) : weight a b = weight b a)

namespace weighted_graph

/-- Turns a weighted graph into a simple graph by forgetting the weights. -/
def to_simple_graph (G : weighted_graph α W) : simple_graph α :=
{ adj := λ a b, G.weight a b ≠ none,
  symm := λ a b h, by rwa G.weight_comm,
  loopless := λ a h, h $ G.weight_self a }

instance (G : weighted_graph α W) : decidable_rel G.to_simple_graph.adj :=
λ a b, @not.decidable _ option.decidable_eq_none

/-- Weights a simple graph. -/
def _root_.simple_graph.to_weighted_graph (G : simple_graph α) [decidable_rel G.adj]
  (f : sym2 α → W) :
  weighted_graph α W :=
{ weight := λ a b, if G.adj a b then f ⟦(a, b)⟧ else none,
  weight_self := λ a, if_neg (G.loopless a),
  weight_comm := λ a b, begin
    simp_rw G.adj_comm a b,
    split_ifs,
    { rw sym2.eq_swap },
    { refl }
  end }

/-- The disjoint sum of two weighted graphs -/
protected def sum (G : weighted_graph α W) (H : weighted_graph β W) : weighted_graph (α ⊕ β) W :=
{ weight := λ a b, a.elim (λ a', b.elim (G.weight a') $ λ b', none)
                          (λ a', b.elim (λ b', none) $ λ b', H.weight a' b'),
  weight_self := begin
    rintro (a | a),
    { exact G.weight_self a },
    { exact H.weight_self a }
  end,
  weight_comm := begin
    rintro (a | a) (b | b),
    { exact G.weight_comm a b },
    { refl },
    { refl },
    { exact H.weight_comm a b }
  end }

/-- The disjoint sum of weighted graphs. -/
protected def sigma [decidable_eq ι] (G : Π i, weighted_graph (σ i) W) :
  weighted_graph (Σ i, σ i) W :=
{ weight := λ a b, if h : a.1 = b.1 then ((G a.1).weight a.2 $ (congr_arg _ h).mpr b.2) else none,
  weight_self := λ a, (dif_pos rfl).trans ((G a.1).weight_self _),
  weight_comm := λ a b, begin
    split_ifs with h h' h' h',
    sorry,
    { exact (h' h.symm).elim },
    { exact (h h'.symm).elim },
    { refl }
  end }

/-- The product of two weighted graphs. -/
protected def prod (G : weighted_graph α W) (H : weighted_graph β W') :
  weighted_graph (α × β) (W × W') :=
{ weight := λ a b, (G.weight a.1 b.1).elim none (λ w, (H.weight a.2 b.2).elim none $ λ w', (w, w')),
  weight_self := λ a, by { rw G.weight_self, refl },
  weight_comm := λ a b, by rw [G.weight_comm, H.weight_comm] }

open_locale classical

/-- The product of weighted graphs. -/
protected noncomputable def pi [nonempty ι] {W : ι → Type*} (G : Π i, weighted_graph (σ i) (W i)) :
  weighted_graph (Π i, σ i) (Π i, W i) :=
{ weight := λ a b, begin
    refine if h : (∀ i, (G i).weight (a i) (b i) ≠ none) then
      (some $ λ i, ((G i).weight (a i) (b i)).elim _ id) else none,
    sorry
  end,
  weight_self := λ a, dif_neg (λ h, h (classical.arbitrary ι) ((G _).weight_self _)),
  weight_comm := λ a b, begin
    split_ifs with h h' h' h',
    { ext i,
      rw (G i).weight_comm },
    { exact h' (λ i, λ H, h i $ ((G i).weight_comm _ _).trans H) },
    { exact h (λ i, λ H, h' i $ ((G i).weight_comm _ _).trans H) },
    { refl }
  end }

end weighted_graph
