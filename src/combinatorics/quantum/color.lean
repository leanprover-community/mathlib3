/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import .hierarchy
import data.sym.sym2

/-!
# Edge coloring of multigraphs
-/

section
variables {F : Type*} (α W : Type*) [weight_multigraph_class F α W] (G : F) (a b : α)
include W

--this one is easy, I just haven't done the def
def hom_equiv : (a ⟶[G] b) ≃ (b ⟶[G] a) := sorry

def hom_edges (α W : Type*) [weight_multigraph_class F α W] (G : F) : sym2 α → Sort* := sorry

def hom_edges_equiv_left : hom_edges α W G ⟦(a, b)⟧ ≃ (a ⟶[G] b) := sorry

def hom_edges_equiv_right : hom_edges α W G ⟦(a, b)⟧ ≃ (b ⟶[G] a) := sorry

lemma hom_edges_left_right :
  (hom_edges_equiv_left α W G a b).symm.trans (hom_edges_equiv_right α W G a b)
    = hom_equiv α W G a b := sorry

end
#exit
variables {α F W 𝒸 : Type*}

namespace graph
section quiver

-- `hom_bicoloring α Prop G` is the type of subgraphs of `G`
@[ext] structure hom_bicoloring (α 𝒸 : Sort*) [quiver_class F α] (G : F) :=
(hom_color ⦃a b : α⦄ : (a ⟶[G] b) → 𝒸)

variables [quiver_class F α] {G : F} {a b : α} (c : hom_bicoloring α 𝒸 G) (e : a ⟶[G] b)

end quiver

section multigraph
variables [multigraph_class F α] {G : F}

@[ext] structure hom_coloring (α 𝒸 : Type*) [multigraph_class F α] (G : F)
  extends hom_bicoloring α 𝒸 G :=
(hom_color_comm ⦃a b : α⦄ (e : a ⟶[G] b) : hom_color e.symm = hom_color e)

end multigraph

section weight_quiver
variables [weight_quiver_class F α W] {G : F} {a b : α} (c : hom_bicoloring α 𝒸 G) (e : a ⟶[G] b)

/-- The edge weight of a graph as an edge bicoloring. -/
def hom_weight_bicoloring (α W : Type*) [weight_quiver_class F α W] (G : F) :
  hom_bicoloring α W G :=
⟨λ a b e, e.weight⟩

@[simp] lemma hom_weight_bicoloring_color :
  (hom_weight_bicoloring α W G).hom_color e = e.weight := rfl

end weight_quiver

section weight_multigraph
variables [weight_multigraph_class F α W] {G : F} {a b : α} (c : hom_bicoloring α 𝒸 G)
  (e : a ⟶[G] b)

/-- The edge weight of a graph as an edge coloring. -/
def hom_weight_coloring (α W : Type*) [weight_multigraph_class F α W] (G : F) :
  hom_coloring α W G :=
{ hom_color := λ a b e, hom.weight e,
  hom_color_comm := λ a b e, weight_multigraph_class.hom_weight_comm _ _ _ _ }

@[simp] lemma hom_weight_coloring_color : (hom_weight_coloring α W G).hom_color e = e.weight := rfl

@[simp] lemma hom_weight_coloring_to_bicoloring :
  (hom_weight_coloring α W G).to_hom_bicoloring = hom_weight_bicoloring α W G :=
by { ext, refl }



example {α β W : Type*} (e : α ≃ β) (f : α → β → W) (g : β → α → W)
  (h : ∀ a b, g (e a) (e.symm b) = f a b) : ∃ (γ : Type*) (lift : γ → W), true

end weight_multigraph
end graph
