/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.quiver

/-!
# Graph typeclasses

The hierarchy of graph-like structures
-/

/-!
### `fun_fun_like`

Thanks Anne!
-/

universes u u₀ u₁ u₂ u₃ u₄

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

-- This is an offer to refactor `rel` as well. It feels like it belongs to this hierarchy and
-- refactoring it should be fine as it's not used much.
/-- Relation. -/
structure rel (α β : Sort*) :=
(to_fun : α → β → Prop)

/-- Equips a type `F` with an adjacency relation.

This is a duplicate of `fun_fun_like F α β Prop`. However, we can't use `fun_fun_like` because some (actually most) graph types have several conflicting `fun_fun_like` instances: one of the form
`fun_fun_like F α α Prop` and one of the form `fun_fun_like F α α  Prop`. Only one of them would
ever get synthesized. -/
class rel_class (F α β : Sort*) :=
(to_fun : F → α → β → Prop)

instance rel.rel_class : rel_class (rel α β) α β :=
⟨rel.to_fun⟩

def graph.adj {F α β : Sort*} [rel_class F α β] : F → α → β → Prop := rel_class.to_fun


/-- Symmetric relation -/
structure symm_rel (α : Type*) extends rel α α :=
(to_fun_symm : symmetric to_fun . obviously)

class symm_rel_class (F : Type*) (α : out_param $ Type*) extends rel_class F α α :=
(to_fun_symm (f : F) : symmetric (to_fun f) . obviously)

instance symm_rel.symm_rel_class : symm_rel_class (symm_rel α) α :=
{ to_fun := λ G, G.to_fun,
  to_fun_symm := λ G, G.to_fun_symm }

lemma graph.adj.symm [symm_rel_class F α] {f : F} {a b : α} (h : graph.adj f a b) :
  graph.adj f b a :=
symm_rel_class.to_fun_symm _ h


structure simple_digraph (α : Type*) extends rel α α :=
(to_fun_self (a : α) : ¬ to_fun a a . obviously)

class simple_digraph_class (F : Type*) (α : out_param $ Type*) extends rel_class F α α :=
(to_fun_self (f : F) (a : α) : ¬ to_fun f a a . obviously)

instance simple_digraph.simple_digraph_class : simple_digraph_class (simple_digraph α) α :=
{ to_fun := λ G, G.to_fun,
  to_fun_self := λ G, G.to_fun_self }

lemma graph.adj_self [simple_digraph_class F α] (f : F) (a : α) : ¬ graph.adj f a a :=
simple_digraph_class.to_fun_self f a


/-- A simple graph is an irreflexive symmetric relation `adj` on a vertex type `α`.
The relation describes which pairs of vertices are adjacent. There is exactly one edge for every
pair of adjacent edges. See `simple_graph.edge_set` for the corresponding edge set. -/
@[ext]
structure simple_graph (α : Type*) extends simple_digraph α :=
(to_fun_symm : symmetric to_fun . obviously)

def simple_graph.to_symm_rel (G : simple_graph α) : symm_rel α := { .. G }

class simple_graph_class (F : Type*) (α : out_param $ Type*) extends symm_rel_class F α :=
(to_fun_self (f : F) (a : α) : ¬ to_fun f a a)

@[priority 100] -- see Note [lower instance priority]
instance simple_graph_class.to_simple_digraph_class (F α : Type*) [simple_graph_class F α] :
  simple_digraph_class F α :=
{ .. ‹simple_graph_class F α› }

instance simple_graph.simple_graph_class : simple_graph_class (simple_graph α) α :=
{ to_fun := λ G, G.to_fun,
  to_fun_self := λ G, G.to_fun_self,
  to_fun_symm := λ G, G.to_fun_symm }


structure hypergraph (α : Type*) :=
(faces : set (set α))
(not_empty_mem : ∅ ∉ faces)

instance hypergraph.simple_graph_class : simple_graph_class (hypergraph α) α :=
{ to_fun := λ G a b, a ≠ b ∧ ∃ s ∈ G.faces, a ∈ s ∧ b ∈ s,
  to_fun_self := λ G a h, h.1 rfl,
  to_fun_symm := λ G a b h, ⟨h.1.symm, let ⟨s, hs, ha, hb⟩ := h.2 in ⟨s, hs, hb, ha⟩⟩ }

/-! #### Weight subworld -/

/-- `W`-weighted digraphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_digraph (α β W : Type*) :=
(weight : α → β → option W)

class weight_digraph_class (F : Type*) (α β W : out_param $ Type*) :=
(weight : F → α → β → option W)

instance weight_digraph.weight_digraph_class : weight_digraph_class (weight_digraph α β W) α β W :=
⟨weight_digraph.weight⟩

def graph.weight [weight_digraph_class F α β W] : F → α → β → option W :=
weight_digraph_class.weight

/-- Two vertices of a weighted digraph are adjacent if their weight is not `none`. -/
@[priority 100] -- see Note [lower instance priority]
instance weight_digraph_class.to_rel_class (F α β W : Type*) [weight_digraph_class F α β W] :
  rel_class F α β :=
⟨λ f a b, graph.weight f a b ≠ none⟩


/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_symm_digraph (α : Type*) (W : Type*) extends weight_digraph α α W :=
(weight_comm (a b : α) : weight a b = weight b a)

class weight_symm_digraph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_digraph_class F α α W :=
(weight_comm (f : F) (a b : α) : weight f a b = weight f b a)

instance weight_symm_digraph.weight_symm_digraph_class :
  weight_symm_digraph_class (weight_symm_digraph α W) α W :=
{ weight := λ G, G.weight,
  weight_comm := weight_symm_digraph.weight_comm }

lemma graph.weight_comm [weight_symm_digraph_class F α W] (f : F) (a b : α) :
  graph.weight f a b = graph.weight f b a :=
weight_symm_digraph_class.weight_comm f a b

/-- Two vertices of a weighted digraph are adjacent if their weight is not `none`. -/
@[priority 100] -- see Note [lower instance priority]
instance weight_symm_digraph_class.to_symm_rel_class (F α W : Type*)
  [weight_symm_digraph_class F α W] :
  symm_rel_class F α :=
{ to_fun_symm := λ G a b, begin
    change graph.weight G a b ≠ none → graph.weight G b a ≠ none,
    rw graph.weight_comm,
    exact id,
  end,
  .. weight_digraph_class.to_rel_class F α α W }


/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_simple_digraph (α : Type*) (W : Type*) extends weight_digraph α α W :=
(weight_self (a : α) : weight a a = none)

class weight_simple_digraph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_digraph_class F α α W :=
(weight_self (f : F) (a : α) : weight f a a = none)

instance weight_simple_digraph.weight_simple_digraph_class :
  weight_simple_digraph_class (weight_simple_digraph α W) α W :=
{ weight := λ f, f.weight,
  weight_self := weight_simple_digraph.weight_self }

lemma graph.weight_self [weight_simple_digraph_class F α W] (f : F) (a : α) :
  graph.weight f a a = none :=
weight_simple_digraph_class.weight_self f a

@[priority 100] -- see Note [lower instance priority]
instance weight_simple_digraph_class.to_simple_digraph_class (F α W : Type*)
  [weight_simple_digraph_class F α W] :
  simple_digraph_class F α :=
{ to_fun := graph.adj,
  to_fun_self := λ f a h, h $ graph.weight_self f a }


/-- `W`-weighted graphs on `α`. `weight a b = some b` represents an edge between `a, b : α` of
weight `b : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_graph (α : Type*) (W : Type*) extends weight_simple_digraph α W :=
(weight_comm (a b : α) : weight a b = weight b a)

def weight_graph.to_weight_symm_digraph (G : weight_graph α W) : weight_symm_digraph α W := { .. G }

class weight_graph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_simple_digraph_class F α W :=
(weight_comm (f : F) (a b : α) : weight f a b = weight f b a)

@[priority 100] -- see Note [lower instance priority]
instance weight_graph_class.to_weight_symm_digraph_class [weight_graph_class F α W] :
  weight_symm_digraph_class F α W :=
{ .. ‹weight_graph_class F α W› }

instance weight_graph.weight_graph_class : weight_graph_class (weight_graph α W) α W :=
{ weight := λ f, f.weight,
  weight_self := λ f, f.weight_self,
  weight_comm := weight_graph.weight_comm }

@[priority 100] -- see Note [lower instance priority]
instance weight_graph_class.to_simple_graph_class (F α W : Type*) [weight_graph_class F α W] :
  simple_graph_class F α :=
{ ..weight_simple_digraph_class.to_simple_digraph_class F α W  }


/-! ### Sort world -/

-- insert `quiver` definition here

class quiver_class (F : Type*) (α : out_param $ Type*) :=
(hom : F → α → α → Sort*)

instance quiver.quiver_class : quiver_class (quiver α) α :=
⟨@quiver.hom α⟩

@[nolint inhabited] def graph.hom [quiver_class F α] : F → α → α → Sort* := quiver_class.hom

notation a ` ⟶[`:25 G `] ` b := graph.hom G a b

-- We might need to replace `u₃` by `u₃ + 1` here to avoid providing an adjacency relation for stuff
-- that already has one, ie when `hom` is already Prop-valued
@[priority 100] -- see Note [lower instance priority]
instance quiver_class.to_rel_class (F : Type u₁) (α : Type u₂) [quiver_class.{u₁ u₂ u₃} F α] :
  rel_class F α α :=
⟨λ f a b, nonempty (a ⟶[f] b)⟩


structure multigraph (α : Type u₂) extends quiver.{u₁ u₂} α : Type (max u₁ u₂) :=
(hom_fun (a b : α) : (a ⟶ b) → (b ⟶ a))
(hom_fun_comp (a b : α) : hom_fun a b ∘ hom_fun b a = id)

class multigraph_class (F : Type u₁) (α : out_param $ Type u₂)
  extends quiver_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃) :=
(hom_fun (f : F) (a b : α) : (a ⟶[f] b) → (b ⟶[f] a))
(hom_fun_comp (f : F) (a b : α) : hom_fun f a b ∘ hom_fun f b a = id)

instance multigraph.multigraph_class : multigraph_class (multigraph α) α :=
{ hom := λ G, G.hom,
  hom_fun := λ G, G.hom_fun,
  hom_fun_comp := λ G, G.hom_fun_comp }

protected def graph.hom.symm [multigraph_class F α] {f : F} {a b : α} : (a ⟶[f] b) → (b ⟶[f] a) :=
multigraph_class.hom_fun _ _ _

lemma graph.hom_symm_symm [multigraph_class F α] {f : F} {a b : α} (e : a ⟶[f] b) :
  e.symm.symm = e :=
begin
  change _ = id e,
  rw ←multigraph_class.hom_fun_comp f b a,
  refl,
end

@[priority 100] -- see Note [lower instance priority]
instance multigraph_class.to_symm_rel_class [multigraph_class F α] : symm_rel_class F α :=
{ to_fun := graph.adj,
  to_fun_symm := λ f a b h, h.map graph.hom.symm }


structure simple_quiver (α : Type*) extends quiver α :=
(hom_self (a : α) : is_empty (a ⟶ a))

class simple_quiver_class (F : Type*) (α : out_param $ Type*)
  extends quiver_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃) :=
(hom_self (f : F) (a : α) : is_empty (a ⟶[f] a))

instance simple_quiver.simple_quiver_class : simple_quiver_class (simple_quiver α) α :=
{ hom := λ G, G.hom,
  hom_self := λ G, G.hom_self }

lemma graph.hom_self [simple_quiver_class F α] (f : F) (a : α) : is_empty (a ⟶[f] a) :=
simple_quiver_class.hom_self _ _

lemma graph.hom.elim [simple_quiver_class F α] {f : F} {a : α} (e : a ⟶[f] a) : false :=
(graph.hom_self _ _).elim' e

@[priority 100] -- see Note [lower instance priority]
instance simple_quiver_class.to_simple_digraph_class [simple_quiver_class F α] :
  simple_digraph_class F α :=
{ to_fun := graph.adj,
  to_fun_self := λ f a h, @not_is_empty_of_nonempty _ h (graph.hom_self f a) }


structure simple_multigraph (α : Type u₂) extends multigraph.{u₁ u₂} α : Type (max u₁ u₂) :=
(hom_self (a : α) : is_empty (a ⟶ a))

def simple_multigraph.to_simple_quiver (G : simple_multigraph α) : simple_quiver α := { .. G }

class simple_multigraph_class (F : Type u₁) (α : out_param $ Type u₂)
  extends multigraph_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃) :=
(hom_self (f : F) (a : α) : is_empty (a ⟶[f] a))

@[priority 100] -- see Note [lower instance priority]
instance simple_multigraph_class.to_simple_quiver_class [simple_multigraph_class F α] :
  simple_quiver_class F α :=
{ .. ‹simple_multigraph_class F α› }

lemma is_empty.lift {α β : Type*} (h : is_empty β) (f : α → β) : is_empty α :=
⟨λ a, is_empty_elim (f a)⟩

@[priority 100] -- see Note [lower instance priority]
instance simple_multigraph_class.to_simple_graph_class [simple_multigraph_class F α] :
  simple_graph_class F α :=
{ to_fun := graph.adj,
  to_fun_symm := λ f a b h, h.map graph.hom.symm,
  to_fun_self := graph.adj_self }

instance simple_multigraph.simple_multigraph_class :
  simple_multigraph_class (simple_multigraph α) α :=
{ hom := λ G, G.hom,
  hom_fun := λ G, G.hom_fun,
  hom_fun_comp := λ G, G.hom_fun_comp,
  hom_self := λ G, G.hom_self }

/-! #### Weight subworld -/


structure weight_quiver (α W : Type*) extends quiver α :=
(hom_weight (a b : α) : (a ⟶ b) → W)

class weight_quiver_class (F : Type*) (α W : out_param $ Type*) extends quiver_class F α :=
(hom_weight (f : F) (a b : α) : (a ⟶[f] b) → W)

instance weight_quiver.weight_quiver_class : weight_quiver_class (weight_quiver α W) α W :=
{ hom := λ G, G.hom,
  hom_weight := λ G, G.hom_weight }

/-- The weight of a multiedge. -/
protected def graph.hom.weight [weight_quiver_class F α W] {f : F} {a b : α} : (a ⟶[f] b) → W :=
weight_quiver_class.hom_weight _ _ _


structure weight_multigraph (α : Type u₂) (W : Type u₃) extends multigraph.{u₁ u₂} α :
  Type (max u₁ u₂ u₃) :=
(hom_weight (a b : α) : (a ⟶ b) → W)
(hom_weight_comm (a b : α) (e : a ⟶ b) : hom_weight _ _ (hom_fun _ _ e) = hom_weight _ _ e)

def weight_multigraph.to_weight_quiver (G : weight_multigraph α W) : weight_quiver α W := { .. G }

class weight_multigraph_class (F : Type u₁) (α : out_param $ Type u₂) (W : out_param $ Type u₄)
  extends multigraph_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃ u₄) :=
(hom_weight (f : F) (a b : α) : (a ⟶[f] b) → W)
(hom_weight_comm (f : F) (a b : α) (e : a ⟶[f] b) :
  hom_weight _ _ _ (hom_fun _ _ _ e) = hom_weight _ _ _ e)

@[priority 100] -- see Note [lower instance priority]
instance weight_multigraph_class.to_weight_quiver_class [weight_multigraph_class F α W] :
  weight_quiver_class F α W :=
{ .. ‹weight_multigraph_class F α W› }

instance weight_multigraph.weight_multigraph_class :
  weight_multigraph_class (weight_multigraph α W) α W :=
{ hom := λ G, G.hom,
  hom_fun := λ G, G.hom_fun,
  hom_fun_comp := λ G, G.hom_fun_comp,
  hom_weight := λ G, G.hom_weight,
  hom_weight_comm := λ G, G.hom_weight_comm }


-- Universe problem. I think I need to universe-ascript `hom_fun` and `hom_weight`
@[simp] lemma graph.hom.weight_symm {F α W : Type*} [weight_multigraph_class F α W] {f : F}
  {a b : α} (e : a ⟶[f] b) :
  e.symm.weight = e.weight :=
weight_quiver_class.hom_weight _ _ _

structure weight_simple_quiver (α W : Type*) extends simple_quiver α :=
(hom_weight (a b : α) : (a ⟶ b) → W)

def weight_simple_quiver.to_weight_quiver (G : weight_simple_quiver α W) : weight_quiver α W :=
{ .. G }

class weight_simple_quiver_class (F : Type u₁) (α : out_param $ Type u₂)
  (W : out_param $ Type u₄)
  extends simple_quiver_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃ u₄) :=
(hom_weight (f : F) (a b : α) : (a ⟶[f] b) → W)

@[priority 100] -- see Note [lower instance priority]
instance weight_simple_quiver_class.to_weight_quiver_class [weight_multigraph_class F α W] :
  weight_quiver_class F α W :=
{ .. ‹weight_multigraph_class F α W› }

instance weight_multigraph.weight_simple_quiver_class :
  weight_simple_quiver_class (weight_simple_quiver α W) α W :=
{ hom := λ G, G.hom,
  hom_self := λ G, G.hom_self,
  hom_weight := λ G, G.hom_weight }


structure weight_simple_multigraph (α : Type u₂) (W : Type u₃)
  extends simple_multigraph.{u₁ u₂} α : Type (max u₁ u₂ u₃) :=
(hom_weight (a b : α) : (a ⟶ b) → W)
(hom_weight_comm (a b : α) (e : a ⟶ b) : hom_weight _ _ (hom_fun _ _ e) = hom_weight _ _ e)

def weight_simple_multigraph.to_weight_multigraph (G : weight_simple_multigraph α W) :
  weight_multigraph α W :=
{ .. G }

class weight_simple_multigraph_class (F : Type u₁) (α : out_param $ Type u₂)
  (W : out_param $ Type u₄)
  extends multigraph_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃ u₄) :=
(hom_weight (f : F) (a b : α) : (a ⟶[f] b) → W)
(hom_weight_comm (f : F) (a b : α) (e : a ⟶[f] b) :
  hom_weight _ _ _ (hom_fun _ _ _ e) = hom_weight _ _ _ e)

@[priority 100] -- see Note [lower instance priority]
instance weight_simple_multigraph_class.to_weight_multigraph_class
  [weight_simple_multigraph_class F α W] :
  weight_multigraph_class F α W :=
{ .. ‹weight_simple_multigraph_class F α W› }

instance weight_simple_multigraph.weight_simple_multigraph_class :
  weight_simple_multigraph_class (weight_simple_multigraph α W) α W :=
{ hom := λ G, G.hom,
  hom_fun := λ G, G.hom_fun,
  hom_fun_comp := λ G, G.hom_fun_comp,
  hom_weight := λ G, G.hom_weight,
  hom_weight_comm := λ G, G.hom_weight_comm }
#lint
