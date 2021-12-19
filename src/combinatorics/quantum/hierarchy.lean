/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.quiver
import combinatorics.simple_graph.basic

/-!
# Graph typeclasses

The hierarchy of graph-like structures
-/

/-!
### `fun_fun_like`

Thanks Anne!
-/

universes u₁ u₂ u₃

abbreviation fun_fun_like (F : Sort*) (α β γ : out_param Sort*) := fun_like F α (λ _, β → γ)

namespace fun_like

variables {F α β γ : Sort*} [i : fun_fun_like F α β γ] {f g : F} {a a' : α} {b b' : β}

include i

lemma ext₂' (h : (f : α → β → γ) = g) : f = g := coe_injective h

lemma ext₂'_iff : f = g ↔ (f : α → β → γ) = g := coe_fn_eq.symm

lemma ext₂ (f g : F) (h : ∀ a b, f a b = g a b) : f = g :=
coe_injective $ funext $ λ a, funext $ h a

lemma ext₂_iff : f = g ↔ ∀ a b, f a b = g a b :=
coe_fn_eq.symm.trans $ function.funext_iff.trans $ forall_congr $ λ a, function.funext_iff

protected lemma congr_fun₂ (h₁ : f = g) (a : α) (b : β) : f a b = g a b :=
congr_fun (congr_fun (congr_arg _ h₁) a) b

protected lemma congr₂ {b b' : β} (h₁ : f = g) (h₂ : a = a') (h₃ : b = b') : f a b = g a' b' :=
congr (congr (congr_arg _ h₁) h₂) h₃

protected lemma congr_arg₂ (f : F) (h₂ : a = a') (h₃ : b = b') : f a b = f a' b' :=
congr (congr_arg _ h₂) h₃

end fun_like

variables {F α β W : Type*}

/-! ### Prop world -/

/-- Equips a type `F` with an adjacency relation.

This is meant to be instantiated for concrete types. In particular, it should not be instantiated
from `fun_fun_like F α β Prop`. -/
class has_adj (F α β : Sort*) :=
(adj : F → α → β → Prop)

-- better?
abbreviation has_adj' (F α β : Sort*) := fun_fun_like F α β Prop


/-- Symmetric relation -/
structure symm_rel (α : Type*) :=
(to_fun : α → α → Prop)
(to_fun_symm (a b : α) : to_fun a b → to_fun b a)

class symm_rel_class (F : Type*) (α : out_param $ Type*) extends has_adj F α α :=
(adj_symm (f : F) (a b : α) : adj f a b → adj f b a)

instance symm_rel.symm_rel_class : symm_rel_class (symm_rel α) α :=
{ adj := symm_rel.to_fun,
  adj_symm := symm_rel.to_fun_symm }


structure simple_digraph (α : Type*) :=
(to_fun : α → α → Prop)
(to_fun_self (a : α) : ¬ to_fun a a)

class simple_digraph_class (F : Type*) (α : out_param $ Type*) extends has_adj F α α :=
(adj_self (f : F) (a : α) : ¬ adj f a a)

instance simple_digraph.simple_digraph_class : simple_digraph_class (simple_digraph α) α :=
{ adj := simple_digraph.to_fun,
  adj_self := simple_digraph.to_fun_self }


-- definition of simple graph here

class simple_graph_class (F : Type*) (α : out_param $ Type*) extends symm_rel_class F α :=
(adj_self (f : F) (a : α) : ¬ adj f a a)

instance simple_graph_class.to_simple_digraph_class (F α : Type*) [simple_graph_class F α] :
  simple_digraph_class F α :=
{ .. ‹simple_graph_class F α› }

instance simple_graph.simple_graph_class : simple_graph_class (simple_graph α) α :=
{ adj := simple_graph.adj,
  adj_symm := simple_graph.symm,
  adj_self := simple_graph.loopless }


structure hypergraph (α : Type*) :=
(faces : set (set α))
(not_empty_mem : ∅ ∉ faces)

def hypergraph.adj (G : hypergraph α) (a b : α) : Prop := a ≠ b ∧ ∃ s ∈ G.faces, a ∈ s ∧ b ∈ s

lemma hypergraph.adj_self (G : hypergraph α) (a : α) : ¬ G.adj a a := λ h, h.1 rfl

lemma hypergraph.adj_symm (G : hypergraph α) (a b : α) (h : G.adj a b) : G.adj b a :=
⟨h.1.symm, let ⟨s, hs, ha, hb⟩ := h.2 in ⟨s, hs, hb, ha⟩⟩

instance hypergraph.simple_graph_class : simple_graph_class (hypergraph α) α :=
{ adj := hypergraph.adj,
  adj_symm := hypergraph.adj_symm,
  adj_self := hypergraph.adj_self }

/-! #### Weight subworld -/

/-- `W`-weighted digraphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_digraph (α : Type*) (W : Type*) :=
(weight : α → α → option W)

class weight_digraph_class (F : Type*) (α W : out_param $ Type*) :=
(weight : F → α → α → option W)

def graph.weight [weight_digraph_class F α W] : F → α → α → option W := weight_digraph_class.weight

instance weight_digraph.weight_digraph_class : weight_digraph_class (weight_digraph α W) α W :=
⟨weight_digraph.weight⟩

/-- Two vertices of a weighted digraph are adjacent if their weight is not `none`. -/
instance weight_digraph_class.to_has_adj (F α W : Type*) [weight_digraph_class F α W] :
  has_adj F α α :=
⟨λ f a b, graph.weight f a b ≠ none⟩


/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_symm_digraph (α : Type*) (W : Type*) extends weight_digraph α W :=
(weight_comm (a b : α) : weight a b = weight b a)

class weight_symm_digraph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_digraph_class F α W :=
(weight_comm (f : F) (a b : α) : weight f a b = weight f b a)

instance weight_symm_digraph.weight_symm_digraph_class :
  weight_symm_digraph_class (weight_symm_digraph α W) α W :=
{ weight := λ G, G.weight,
  weight_comm := weight_symm_digraph.weight_comm }

lemma graph.weight_comm [weight_symm_digraph_class F α W] (f : F) (a b : α) :
  graph.weight f a b = graph.weight f b a :=
weight_symm_digraph_class.weight_comm f a b

/-- Two vertices of a weighted digraph are adjacent if their weight is not `none`. -/
instance weight_symm_digraph_class.to_symm_rel_class [weight_symm_digraph_class F α W] :
  symm_rel_class F α :=
{ adj_symm := λ G a b, begin
    change graph.weight G a b ≠ none → graph.weight G b a ≠ none,
    rw graph.weight_comm,
    exact id,
  end,
  .. weight_digraph_class.to_has_adj F α W }


/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_simple_digraph (α : Type*) (W : Type*) extends weight_digraph α W :=
(weight_self (a : α) : weight a a = none)

class weight_simple_digraph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_digraph_class F α W :=
(weight_self (f : F) (a : α) : weight f a a = none)

instance weight_simple_digraph.weight_simple_digraph_class :
  weight_simple_digraph_class (weight_simple_digraph α W) α W :=
{ weight := λ f, f.weight,
  weight_self := weight_simple_digraph.weight_self }

lemma graph.weight_self [weight_simple_digraph_class F α W] (f : F) (a : α) :
  graph.weight f a a = none :=
weight_simple_digraph_class.weight_self f a

instance weight_simple_digraph_class.to_simple_digraph_class (F α W : Type*)
  [weight_simple_digraph_class F α W] :
  simple_digraph_class F α :=
{ adj_self := λ f a h, h $ graph.weight_self f a,
  .. weight_digraph_class.to_has_adj F α W }


/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_graph (α : Type*) (W : Type*) extends weight_simple_digraph α W :=
(weight_comm (a b : α) : weight a b = weight b a)

def weight_graph.to_weight_symm_digraph (G : weight_graph α W) : weight_symm_digraph α W := { .. G }

class weight_graph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_simple_digraph_class F α W :=
(weight_comm (f : F) (a b : α) : weight f a b = weight f b a)

instance weight_graph.weight_graph_class : weight_graph_class (weight_graph α W) α W :=
{ weight := λ f, f.weight,
  weight_self := λ f, f.weight_self,
  weight_comm := weight_graph.weight_comm }

instance weight_graph_class.to_simple_graph_class (F α W : Type*) [weight_graph_class F α W] :
  simple_graph_class F α :=
{ .. weight_simple_digraph_class.to_simple_digraph_class F α W }


/-! ### Sort world -/

structure multigraph (α : Type*) extends quiver α :=
(hom_fun (a b : α) : (a ⟶ b) → (b ⟶ a))
(hom_fun_comp (a b : α) : hom_fun a b ∘ hom_fun b a = id)

structure simple_multigraph (α : Type*) extends multigraph α :=
(hom_self (a : α) : is_empty (a ⟶ a))



/-! #### Weight subworld -/

-- insert `quiver` definition here

class quiver_class (F : Type*) (α : out_param $ Type*) :=
(hom : F → α → α → Sort*)

def graph.hom [quiver_class F α] : F → α → α → Sort* := quiver_class.hom

-- `u₃ + 1` is here to avoid providing an adjacency relation for stuff that already has one, ie
-- when `hom` is already Prop-valued
instance quiver_class.to_has_adj (F : Type u₁) (α : Type u₂) [quiver_class.{u₁ u₂ (u₃ + 1)} F α] :
  has_adj F α α :=
⟨λ f a b, is_empty (graph.hom f a b)⟩


structure weight_multigraph (α W : Type*) extends multigraph α :=
(weight' {a b : α} : (a ⟶ b) → W)
(weight_symm' (a b : α) (e : a ⟶ b) : weight' (hom_fun _ _ e) = weight' e)


structure simple_weight_multigraph (α W : Type*) extends weight_multigraph α W :=
(hom_self (a : α) : is_empty (a ⟶ a))
