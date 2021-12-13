/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.weighted_graph.basic

/-!
# Weighted graphs homomorphisms

This file defines morphisms, embeddings and isomorphisms of weighted graphs.

## Main declarations

* `weighted_graph_hom`: Homomorphism of weighted graphs.
* `weighted_graph_embedding`: Embedding of weighted graphs.
* `weighted_graph_iso`: Isomorphism of weighted graphs.

## Notation

* `G₁ →wg G₂`: Homomorphism of weighted graphs.
* `G₁ ↪wg G₂`: Embedding of weighted graphs.
* `G₁ ≃wg G₂`: Isomorphism of weighted graphs.
-/

open function

variables {F α β γ W : Type*} {G G₁ : weighted_graph α W} {G₂ : weighted_graph β W}
  {G₃ : weighted_graph γ W}

/-- Morphisms between weighted graphs `G₁` and `G₂`. -/
structure weighted_graph_hom (G₁ : weighted_graph α W) (G₂ : weighted_graph β W) :=
(to_fun : α → β)
(weight_map' (a b : α) : G₂.weight (to_fun a) (to_fun b) = G₁.weight a b)

infix  ` →wg `:25 := weighted_graph_hom

/-- `weighted_graph_hom_class F G₁ G₂` states that `F` is a type of morphisms between weighted
graphs `G₁` and `G₂`.
You should extend this class when you extend `weighted_graph_hom`. -/
class weighted_graph_hom_class (F : Type*) (G₁ : out_param $ weighted_graph α W)
  (G₂ : out_param $ weighted_graph β W) extends fun_like F α (λ _, β) :=
(weight_map (f : F) (a b : α) : G₂.weight (f a) (f b) = G₁.weight a b)

@[simp] lemma weighted_graph.weight_map [weighted_graph_hom_class F G₁ G₂] (f : F) (a b : α) :
  G₂.weight (f a) (f b) = G₁.weight a b :=
weighted_graph_hom_class.weight_map f a b

open weighted_graph

namespace weighted_graph_hom

instance weighted_graph_hom_class : weighted_graph_hom_class (G₁ →wg G₂) G₁ G₂ :=
{ coe := weighted_graph_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  weight_map := weighted_graph_hom.weight_map' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (G₁ →wg G₂) (λ _, α → β) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe {f : G₁ →wg G₂} : f.to_fun = (f : α → β) := rfl

-- @[ext] theorem ext {f g : G₁ →wg G₂} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `weighted_graph_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : G₁ →wg G₂) (f' : α → β) (h : f' = ⇑f) : G₁ →wg G₂ :=
{ to_fun := f',
  weight_map' := h.symm ▸ f.weight_map' }

protected lemma weight_map (f : G₁ →wg G₂) (a b : α) : G₂.weight (f a) (f b) = G₁.weight a b :=
f.weight_map' a b

/-- Composition of weighted graph embeddings. -/
@[simps] def comp (g : G₂ →wg G₃) (f : G₁ →wg G₂) : G₁ →wg G₃ :=
{ to_fun := λ a, g (f a),
  weight_map' := λ a b, (g.weight_map _ _).trans (f.weight_map _ _) }

end weighted_graph_hom

/-- Embeddings from weighted graph `G₁` to weighted graph `G₂`. -/
structure weighted_graph_embedding (G₁ : weighted_graph α W) (G₂ : weighted_graph β W)
  extends α ↪ β :=
(weight_map' (a b : α) : G₂.weight (to_fun a) (to_fun b) = G₁.weight a b)

infix  ` ↪wg `:25 := weighted_graph_embedding

namespace weighted_graph_embedding

instance : weighted_graph_hom_class (G₁ ↪wg G₂) G₁ G₂ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨f⟩⟩ := f; obtain ⟨⟨g⟩⟩ := g; congr',
  weight_map := weighted_graph_embedding.weight_map' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (G₁ ↪wg G₂) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : G₁ ↪wg G₂} : f.to_fun = (f : α → β) := rfl

-- @[ext] theorem ext {f g : G₁ →wg G₂} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `weighted_graph_embedding` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : G₁ ↪wg G₂) (f' : α → β) (h : f' = ⇑f) : G₁ ↪wg G₂ :=
{ to_fun := f',
  inj' := by { rw h, exact f.inj' },
  weight_map' := λ a b, by { simp_rw h, exact f.weight_map' a b } }

/-- Composition of weighted graph embeddings. -/
@[simps] def comp (g : G₂ ↪wg G₃) (f : G₁ ↪wg G₂) : G₁ ↪wg G₃ :=
{ to_fun := λ a, g (f a),
  inj' := sorry,
  weight_map' := sorry }

end weighted_graph_embedding

/-- Isomorphism between weighted graph `G₁` to weighted graph `G₂`. -/
@[ext] structure weighted_graph_iso (G₁ : weighted_graph α W) (G₂ : weighted_graph β W)
  extends α ≃ β :=
(weight_map' (a b : α) : G₂.weight (to_fun a) (to_fun b) = G₁.weight a b)

infix  ` ≃wg `:25 := weighted_graph_iso

namespace weighted_graph_iso

instance weighted_graph_hom_class : weighted_graph_hom_class (G₁ ≃wg G₂) G₁ G₂ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, sorry,
  weight_map := weighted_graph_iso.weight_map' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
instance : has_coe_to_fun (G₁ ≃wg G₂) (λ _, α → β) := ⟨λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : G₁ ≃wg G₂} : f.to_fun = (f : α → β) := rfl

-- @[ext] theorem ext {f g : G₁ ≃wg G₂} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

/-- Copy of a `weighted_graph_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : G₁ ≃wg G₂) (f' : α → β) (g' : β → α) (hf : f' = ⇑f)
  (hg : g' = f.to_equiv.symm) : G₁ ≃wg G₂ :=
{ to_fun := f',
  inv_fun := g',
  left_inv := by { rw [hf, hg], exact f.left_inv },
  right_inv := by { rw [hf, hg], exact f.right_inv },
  weight_map' := λ a b, by { simp_rw hf, exact f.weight_map' a b } }

@[simps] protected def symm (f : G₁ ≃wg G₂) : G₂ ≃wg G₁ :=
{ to_fun := f.inv_fun,
  inv_fun := f.to_fun,
  left_inv := f.right_inv,
  right_inv := f.left_inv,
  weight_map' := λ a b, begin
    sorry,
  end }

protected def trans (g : G₂ ≃wg G₃) (f : G₁ ≃wg G₂) : G₁ ≃wg G₃ :=
sorry

end weighted_graph_iso

namespace weighted_graph
variables (G)

/-- The identity as a weighted graph homomorphism. -/
@[simps] protected def hom_id : G →wg G :=
{ to_fun := id,
  weight_map' := λ a b, rfl }

instance : inhabited (G →wg G) := ⟨G.hom_id⟩

/-- The identity as a weighted graph embedding. -/
@[simps] protected def embedding_id : G ↪wg G :=
{ to_fun := id,
  inj' := λ a b, id,
  weight_map' := λ a b, rfl }

instance : inhabited (G ↪wg G) := ⟨G.embedding_id⟩

/-- The identity as a weighted graph isomorphism. -/
@[simps] protected def iso_id : G ≃wg G :=
{ to_fun := id,
  inv_fun := id,
  left_inv := λ a, rfl,
  right_inv := λ a, rfl,
  weight_map' := λ a b, rfl }

instance : inhabited (G ≃wg G) := ⟨G.iso_id⟩

namespace hom
variables {G₁ G₂} (f : G₁ →wg G₂)

lemma map_mem_edge_set {e : sym2 α} (h : e ∈ G₁.edge_set) : e.map f ∈ G₂.edge_set :=
quotient.ind (λ e h, sym2.from_rel_prop.mpr (f.map_rel' h)) e h

lemma apply_mem_neighbor_set {v w : α} (h : w ∈ G.neighbor_set v) : f w ∈ G₂.neighbor_set (f v) :=
map_adj f h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `sym2.map`. -/
@[simps] def map_edge_set (e : G.edge_set) : G₂.edge_set :=
⟨sym2.map f e, f.map_mem_edge_set e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps] def map_neighbor_set (v : α) (w : G.neighbor_set v) : G₂.neighbor_set (f v) :=
⟨f w, f.apply_mem_neighbor_set w.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
def map_spanning_subgraphs {G₁ G₂ : simple_graph V} (h : G ≤ G₂) : G →wg G₂ :=
{ to_fun := λ x, x,
  map_rel' := h }

lemma map_edge_set.injective (hinj : function.injective f) : function.injective f.map_edge_set :=
begin
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩,
  dsimp [hom.map_edge_set],
  repeat { rw subtype.mk_eq_mk },
  apply sym2.map.injective hinj,
end

end hom

namespace embedding
variables {G₁ G₂} (f : G ↪wg G₂)

lemma map_adj_iff {v w : α} : G₂.adj (f v) (f w) ↔ G.adj v w := f.map_rel_iff

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ G₂.edge_set ↔ e ∈ G.edge_set :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

lemma apply_mem_neighbor_set_iff {v w : α} : f w ∈ G₂.neighbor_set (f v) ↔ w ∈ G.neighbor_set v :=
map_adj_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps] def map_edge_set : G.edge_set ↪ G₂.edge_set :=
{ to_fun := hom.map_edge_set f,
  inj' := hom.map_edge_set.injective f f.inj' }

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps] def map_neighbor_set (v : α) : G.neighbor_set v ↪ G₂.neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inj' := begin
    rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
    rw subtype.mk_eq_mk at h ⊢,
    exact f.inj' h,
  end }

end embedding

namespace iso
variables {G₁ G₂} (f : G ≃wg G₂)

lemma map_adj_iff {v w : α} : G₂.adj (f v) (f w) ↔ G.adj v w := f.map_rel_iff

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ G₂.edge_set ↔ e ∈ G.edge_set :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

lemma apply_mem_neighbor_set_iff {v w : α} : f w ∈ G₂.neighbor_set (f v) ↔ w ∈ G.neighbor_set v :=
map_adj_iff f

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps] def map_edge_set : G.edge_set ≃ G₂.edge_set :=
{ to_fun := hom.map_edge_set f,
  inv_fun := hom.map_edge_set f.symm,
  left_inv := begin
    rintro ⟨e, h⟩,
    simp only [hom.map_edge_set, sym2.map_map, rel_iso.coe_coe_fn,
      rel_embedding.coe_coe_fn, subtype.mk_eq_mk, subtype.coe_mk, coe_coe],
    apply congr_fun,
    convert sym2.map_id,
    exact funext (λ _, rel_iso.symm_apply_apply _ _),
  end,
  right_inv := begin
    rintro ⟨e, h⟩,
    simp only [hom.map_edge_set, sym2.map_map, rel_iso.coe_coe_fn,
      rel_embedding.coe_coe_fn, subtype.mk_eq_mk, subtype.coe_mk, coe_coe],
    apply congr_fun,
    convert sym2.map_id,
    exact funext (λ _, rel_iso.apply_symm_apply _ _),
  end }

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps] def map_neighbor_set (v : α) : G.neighbor_set v ≃ G₂.neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inv_fun := λ w, ⟨f.symm w, begin
    convert f.symm.apply_mem_neighbor_set_iff.mpr w.2,
    simp only [rel_iso.symm_apply_apply],
  end⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

lemma card_eq_of_iso [fintype V] [fintype W] (f : G ≃wg G₂) : fintype.card V = fintype.card W :=
by convert (fintype.of_equiv_card f.to_equiv).symm

end iso

end weighted_graph
