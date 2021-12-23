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

universes u u₀ u₁ u₂ u₃ u₄
variables {F α β W : Type*}

/-! ### Prop world -/

-- This is an offer to refactor `rel` as well. It feels like it belongs to this hierarchy and
-- refactoring it should be fine as it's not used much.
/-- Relation. -/
structure rel (α β : Sort*) :=
(to_fun : α → β → Prop)

/-- `rel_class F α` states that `F` is a type of relations between `α` and `β`.

Extend this class when you extend `rel`. -/
class rel_class (F α β : Sort*) :=
(to_fun : F → α → β → Prop)

instance rel.rel_class : rel_class (rel α β) α β :=
⟨rel.to_fun⟩

/-- The adjacency relation of a graph. -/
def graph.adj {F α β : Sort*} [rel_class F α β] : F → α → β → Prop := rel_class.to_fun

instance : has_bot (rel α β) := ⟨⟨λ _ _, false⟩⟩
instance : inhabited (rel α β) := ⟨⊥⟩


/-- Type of symmetric relations on `α`. -/
structure symm_rel (α : Type*) extends rel α α :=
(to_fun_symm : symmetric to_fun . obviously)

/-- `symm_rel_class F α` states that `F` is a type of symmetric relations on `α`.

Extend this class when you extend `symm_rel`. -/
class symm_rel_class (F : Type*) (α : out_param $ Type*) extends rel_class F α α :=
(to_fun_symm (f : F) : symmetric (to_fun f) . obviously)

instance symm_rel.symm_rel_class : symm_rel_class (symm_rel α) α :=
{ to_fun := λ G, G.to_fun,
  to_fun_symm := λ G, G.to_fun_symm }

lemma graph.adj.symm [symm_rel_class F α] {f : F} {a b : α} (h : graph.adj f a b) :
  graph.adj f b a :=
symm_rel_class.to_fun_symm _ h

lemma graph.adj_comm [symm_rel_class F α] {f : F} {a b : α} : graph.adj f a b ↔ graph.adj f b a :=
⟨graph.adj.symm, graph.adj.symm⟩

instance : has_bot (symm_rel α) :=
⟨{ to_fun := λ _ _, false,
  to_fun_symm := λ _ _, id  }⟩

instance : inhabited (symm_rel α) := ⟨⊥⟩


/-- Type of simple digraphs on `α`. A simple digraph is an irreflexive adjacency relation. -/
structure simple_digraph (α : Type*) extends rel α α :=
(to_fun_self (a : α) : ¬ to_fun a a . obviously)

/-- `simple_digraph_class F α` states that `F` is a type of irreflexive relations on `α`.

Extend this class when you extend `simple_digraph`. -/
class simple_digraph_class (F : Type*) (α : out_param $ Type*) extends rel_class F α α :=
(to_fun_self (f : F) (a : α) : ¬ to_fun f a a . obviously)

instance simple_digraph.simple_digraph_class : simple_digraph_class (simple_digraph α) α :=
{ to_fun := λ G, G.to_fun,
  to_fun_self := λ G, G.to_fun_self }

lemma graph.adj_self [simple_digraph_class F α] (f : F) (a : α) : ¬ graph.adj f a a :=
simple_digraph_class.to_fun_self f a

instance : has_bot (simple_digraph α) :=
⟨{ to_fun := λ _ _, false,
  to_fun_self := λ _, not_false  }⟩

instance : inhabited (simple_digraph α) := ⟨⊥⟩


/-- The type of simple graphs on `α`. A simple graph is an irreflexive symmetric relation `adj` on a
vertex type `α`.

The relation describes which pairs of vertices are adjacent. There is exactly one edge for every
pair of adjacent edges. See `simple_graph.edge_set` for the corresponding edge set. -/
@[ext]
structure simple_graph (α : Type*) extends simple_digraph α :=
(to_fun_symm : symmetric to_fun . obviously)

/-- Reinterprets a simple graph as a symmetric relation. -/
def simple_graph.to_symm_rel (G : simple_graph α) : symm_rel α := { .. G }

/-- `simple_graph_class F α` states that `F` is a type of symmetric irreflexive relations on `α`.

Extend this class when you extend `simple_graph`. -/
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

instance : has_bot (simple_graph α) :=
⟨{ to_fun := λ _ _, false,
  to_fun_self := λ _, not_false,
  to_fun_symm := λ _ _, id }⟩

instance : inhabited (simple_graph α) := ⟨⊥⟩


/-- The type of hypergraphs on `α`. An hypergraph is a set of nonempty sets of vertices. -/
structure hypergraph (α : Type*) :=
(faces : set (set α))
(not_empty_mem : ∅ ∉ faces)

/-- `hypergraph_class F α` states that `F` is a type of hypergraphs on `α`.

Extend this class when you extend `hypergraph`. -/
class hypergraph_class (F α : Type*) :=
(faces (f : F) : set (set α))
(not_empty_mem (f : F) : ∅ ∉ faces f)

instance hypergraph.hypergraph_class : hypergraph_class (hypergraph α) α :=
{ faces := hypergraph.faces,
  not_empty_mem := hypergraph.not_empty_mem }

/-- The faces of an hypergraph. -/
def graph.hyperfaces (α : Type*) [hypergraph_class F α] : F → set (set α) := hypergraph_class.faces

lemma graph.not_empty_mem_hyperfaces [hypergraph_class F α] (G : F) : ∅ ∉ graph.hyperfaces α G :=
hypergraph_class.not_empty_mem _

@[priority 100] -- see Note [lower instance priority]
instance hypergraph_class.to_simple_graph_class [hypergraph_class F α] : simple_graph_class F α :=
{ to_fun := λ G a b, a ≠ b ∧ ∃ s ∈ graph.hyperfaces α G, a ∈ s ∧ b ∈ s,
  to_fun_self := λ G a h, h.1 rfl,
  to_fun_symm := λ G a b h, ⟨h.1.symm, let ⟨s, hs, ha, hb⟩ := h.2 in ⟨s, hs, hb, ha⟩⟩ }

instance : has_bot (hypergraph α) :=
⟨{ faces := ∅,
  not_empty_mem := set.not_mem_empty _ }⟩

instance : inhabited (hypergraph α) := ⟨⊥⟩


/-! #### Weight subworld -/

/-- The type of `W`-weighted digraphs between `α` and `β`. `weight a b = some w` represents an edge
between `a : α` and `b : β` of weight `w : W`. `weight a b = none` represents no edge between `a`
and `b`. -/
@[ext] structure weight_digraph (α β W : Type*) :=
(weight : α → β → option W)

/-- `weight_digraph_class F α β W` states that `F` is a type of `W`-weighted digraphs between `α`
and `β`.

Extend this class when you extend `weight_digraph`. -/
class weight_digraph_class (F : Type*) (α β W : out_param $ Type*) :=
(weight : F → α → β → option W)

instance weight_digraph.weight_digraph_class : weight_digraph_class (weight_digraph α β W) α β W :=
⟨weight_digraph.weight⟩

/-- The weight between two vertices. Note that this is different from `graph.hom.weight`, the weight
of an edge. -/
def graph.weight [weight_digraph_class F α β W] : F → α → β → option W :=
weight_digraph_class.weight

/-- Two vertices of a weighted digraph are adjacent if their weight is not `none`. -/
-- `dangerous_instance` does not know that `W` is used only as an `out_param`.
@[priority 100, nolint dangerous_instance] -- see Note [lower instance priority]
instance weight_digraph_class.to_rel_class (F α β W : Type*) [weight_digraph_class F α β W] :
  rel_class F α β :=
⟨λ G a b, graph.weight G a b ≠ none⟩

instance : has_bot (weight_digraph α β W) := ⟨⟨λ _ _, none⟩⟩
instance : inhabited (weight_digraph α β W) := ⟨⊥⟩


/-- The type of `W`-weighted graphs on `α`.`weight a b = some w` represents an edge between
`a b : α` of weight `w : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_graph (α : Type*) (W : Type*) extends weight_digraph α α W :=
(weight_comm (a b : α) : weight a b = weight b a)

/-- `weight_graph_class F α β W` states that `F` is a type of `W`-weighted graphs on `α`.

Extend this class when you extend `weight_graph`. -/
class weight_graph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_digraph_class F α α W :=
(weight_comm (f : F) (a b : α) : weight f a b = weight f b a)

instance weight_graph.weight_graph_class :
  weight_graph_class (weight_graph α W) α W :=
{ weight := λ G, G.weight,
  weight_comm := λ G, G.weight_comm }

lemma graph.weight_comm [weight_graph_class F α W] (f : F) (a b : α) :
  graph.weight f a b = graph.weight f b a :=
weight_graph_class.weight_comm f a b

/-- Two vertices of a weighted digraph are adjacent if their weight is not `none`. -/
@[priority 100] -- see Note [lower instance priority]
instance weight_graph_class.to_symm_rel_class (F α W : Type*)
  [weight_graph_class F α W] :
  symm_rel_class F α :=
{ to_fun := graph.adj,
  to_fun_symm := λ G a b, begin
    change graph.weight G a b ≠ none → graph.weight G b a ≠ none,
    rw graph.weight_comm,
    exact id,
  end }

instance : has_bot (weight_graph α W) :=
⟨{ weight := λ _ _, none,
  weight_comm := λ _ _, rfl }⟩

instance : inhabited (weight_graph α W) := ⟨⊥⟩


/-- The type of `W`-weighted simple digraphs on `α`.`weight a b = some w` represents an edge between
`a b : α` of weight `w : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_simple_digraph (α : Type*) (W : Type*) extends weight_digraph α α W :=
(weight_self (a : α) : weight a a = none)

/-- `weight_graph_class F α β W` states that `F` is a type of `W`-weighted simple digraphs on `α`.

Extend this class when you extend `weight_simple_digraph`. -/
class weight_simple_digraph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_digraph_class F α α W :=
(weight_self (f : F) (a : α) : weight f a a = none)

instance weight_simple_digraph.weight_simple_digraph_class :
  weight_simple_digraph_class (weight_simple_digraph α W) α W :=
{ weight := λ G, G.weight,
  weight_self := λ G, G.weight_self }

lemma graph.weight_self [weight_simple_digraph_class F α W] (f : F) (a : α) :
  graph.weight f a a = none :=
weight_simple_digraph_class.weight_self f a

-- `dangerous_instance` does not know that `W` is used only as an `out_param`.
@[priority 100, nolint dangerous_instance] -- see Note [lower instance priority]
instance weight_simple_digraph_class.to_simple_digraph_class (F α W : Type*)
  [weight_simple_digraph_class F α W] :
  simple_digraph_class F α :=
{ to_fun := graph.adj,
  to_fun_self := λ G a h, h $ graph.weight_self G a }

instance : has_bot (weight_simple_digraph α W) :=
⟨{ weight := λ _ _, none,
  weight_self := λ _, rfl }⟩

instance : inhabited (weight_simple_digraph α W) := ⟨⊥⟩


/-- The type of `W`-weighted simple graphs on `α`.`weight a b = some w` represents an edge between
`a b : α` of weight `w : W`. `weight a b = none` represents no edge between `a` and `b`. -/
@[ext] structure weight_simple_graph (α : Type*) (W : Type*) extends weight_simple_digraph α W :=
(weight_comm (a b : α) : weight a b = weight b a)

/-- Reinterprets a weighted simple graph as a simple graph. -/
def weight_simple_graph.to_weight_graph (G : weight_simple_graph α W) : weight_graph α W := { .. G }

/-- `weight_simple_graph_class F α β W` states that `F` is a type of `W`-weighted simple graphs on
`α`.

Extend this class when you extend `weight_simple_graph`. -/
class weight_simple_graph_class (F : Type*) (α W : out_param $ Type*)
  extends weight_simple_digraph_class F α W :=
(weight_comm (f : F) (a b : α) : weight f a b = weight f b a)

@[priority 100] -- see Note [lower instance priority]
instance weight_simple_graph_class.to_weight_graph_class [weight_simple_graph_class F α W] :
  weight_graph_class F α W :=
{ .. ‹weight_simple_graph_class F α W› }

instance weight_simple_graph.weight_simple_graph_class : weight_simple_graph_class (weight_simple_graph α W) α W :=
{ weight := λ G, G.weight,
  weight_self := λ G, G.weight_self,
  weight_comm := weight_simple_graph.weight_comm }

@[priority 100] -- see Note [lower instance priority]
instance weight_simple_graph_class.to_simple_graph_class (F α W : Type*) [weight_simple_graph_class F α W] :
  simple_graph_class F α :=
{ ..weight_simple_digraph_class.to_simple_digraph_class F α W  }

instance : has_bot (weight_simple_graph α W) :=
⟨{ weight := λ _ _, none,
  weight_self := λ _, rfl,
  weight_comm := λ _ _, rfl  }⟩

instance : inhabited (weight_simple_graph α W) := ⟨⊥⟩


/-! ### Sort world -/

-- insert `quiver` definition here
-- Note, `quiver` itself is a class.
-- Note, we could generalize `quiver α` to `quiver α β`

/-- `quiver_class F α` states that `F` is a type of quivers on `α`.

Extend this class when you extend `quiver`. -/
class quiver_class (F : Type*) (α : out_param $ Type*) :=
(hom : F → α → α → Sort*)

instance quiver.quiver_class : quiver_class (quiver α) α :=
⟨@quiver.hom α⟩

/-- `a ⟶[G] b` is the type of edges from `a` to `b` in `G`. -/
@[nolint has_inhabited_instance] def graph.hom [quiver_class F α] : F → α → α → Sort* := quiver_class.hom

notation a ` ⟶[`:25 G `] ` b := graph.hom G a b

-- We might need to replace `u₃` by `u₃ + 1` here to avoid providing an adjacency relation for stuff
-- that already has one, ie when `hom` is already Prop-valued
@[priority 100] -- see Note [lower instance priority]
instance quiver_class.to_rel_class (F : Type u₁) (α : Type u₂) [quiver_class.{u₁ u₂ u₃} F α] :
  rel_class F α α :=
⟨λ f a b, nonempty (a ⟶[f] b)⟩

instance : has_bot (quiver α) := ⟨⟨λ _ _, pempty⟩⟩
instance : inhabited (quiver α) := ⟨⊥⟩


/-- The type of multigraphs on `α`. -/
structure multigraph (α : Type u₂) extends quiver.{u₁ u₂} α : Type (max u₁ u₂) :=
(hom_fun (a b : α) : (a ⟶ b) → (b ⟶ a))
(hom_fun_comp (a b : α) : hom_fun a b ∘ hom_fun b a = id)

/-- `multigraph_class F α` states that `F` is a type of multigraphs on `α`.

Extend this class when you extend `multigraph`. -/
class multigraph_class (F : Type u₁) (α : out_param $ Type u₂)
  extends quiver_class.{u₁ u₂ u₃} F α : Type (max u₁ u₂ u₃) :=
(hom_fun (f : F) (a b : α) : (a ⟶[f] b) → (b ⟶[f] a))
(hom_fun_comp (f : F) (a b : α) : hom_fun f a b ∘ hom_fun f b a = id)

instance multigraph.multigraph_class : multigraph_class (multigraph α) α :=
{ hom := λ G, G.hom,
  hom_fun := λ G, G.hom_fun,
  hom_fun_comp := λ G, G.hom_fun_comp }

/-- Turns an edge around. -/
protected def graph.hom.symm [multigraph_class F α] {f : F} {a b : α} : (a ⟶[f] b) → (b ⟶[f] a) :=
multigraph_class.hom_fun _ _ _

lemma graph.hom_symm_symm [multigraph_class F α] {f : F} {a b : α} (e : a ⟶[f] b) :
  e.symm.symm = e :=
begin
  change _ = id e,
  rw ←multigraph_class.hom_fun_comp f b a,
  refl,
end

-- `dangerous_instance` does not know that `W` is used only as an `out_param`.
@[priority 100, nolint dangerous_instance] -- see Note [lower instance priority]
instance multigraph_class.to_symm_rel_class [multigraph_class F α] : symm_rel_class F α :=
{ to_fun := graph.adj,
  to_fun_symm := λ f a b h, h.map graph.hom.symm }

instance : has_bot (multigraph α) :=
⟨{ hom := λ _ _, pempty,
  hom_fun := λ _ _, id,
  hom_fun_comp := λ _ _, rfl }⟩

instance : inhabited (multigraph α) := ⟨⊥⟩


/-- The type of simple quivers on `α`, aka simple multidigraphs. -/
structure simple_quiver (α : Type*) extends quiver α :=
(hom_self (a : α) : is_empty (a ⟶ a))

/-- `simple_quiver_class F α` states that `F` is a type of simple quivers on `α`.

Extend this class when you extend `simple_quiver`. -/
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

instance : has_bot (simple_quiver α) :=
⟨{ hom := λ _ _, pempty,
  hom_self := λ _, pempty.is_empty }⟩

instance : inhabited (simple_quiver α) := ⟨⊥⟩


/-- The type of simple multigraphs on `α`. -/
structure simple_multigraph (α : Type u₂) extends multigraph.{u₁ u₂} α : Type (max u₁ u₂) :=
(hom_self (a : α) : is_empty (a ⟶ a))

/-- Reinterprets a simple multigraph as a simple quiver. -/
def simple_multigraph.to_simple_quiver (G : simple_multigraph α) : simple_quiver α := { .. G }

/-- `simple_multigraph_class F α` states that `F` is a type of simple multigraphs on `α`.

Extend this class when you extend `simple_multigraph`. -/
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

instance : has_bot (simple_multigraph α) :=
⟨{ hom := λ _ _, pempty,
  hom_self := λ _, pempty.is_empty ,
  hom_fun := λ _ _, id,
  hom_fun_comp := λ _ _, rfl }⟩

instance : inhabited (simple_multigraph α) := ⟨⊥⟩


/-! #### Weight subworld -/

/-- Type of `W`-weighted quivers on `α`. -/
structure weight_quiver (α W : Type*) extends quiver α :=
(hom_weight (a b : α) : (a ⟶ b) → W)

/-- `weight_quiver_class F α W` states that `F` is a type of `W`-weighted quivers on `α`.

Extend this class when you extend `weight_quiver`. -/
class weight_quiver_class (F : Type*) (α W : out_param $ Type*) extends quiver_class F α :=
(hom_weight (f : F) (a b : α) : (a ⟶[f] b) → W)

instance weight_quiver.weight_quiver_class : weight_quiver_class (weight_quiver α W) α W :=
{ hom := λ G, G.hom,
  hom_weight := λ G, G.hom_weight }

/-- The weight of a multiedge. -/
protected def graph.hom.weight [weight_quiver_class F α W] {f : F} {a b : α} : (a ⟶[f] b) → W :=
weight_quiver_class.hom_weight _ _ _

instance : has_bot (weight_quiver α W) :=
⟨{ hom := λ _ _, pempty,
  hom_weight := λ _ _, pempty.elim }⟩

instance : inhabited (weight_quiver α W) := ⟨⊥⟩


/-- Type of `W`-weighted multigraphs on `α`. -/
structure weight_multigraph (α : Type u₂) (W : Type u₃) extends multigraph.{u₁ u₂} α :
  Type (max u₁ u₂ u₃) :=
(hom_weight (a b : α) : (a ⟶ b) → W)
(hom_weight_comm (a b : α) (e : a ⟶ b) : hom_weight _ _ (hom_fun _ _ e) = hom_weight _ _ e)

/-- Reinterprets a weighted multigraph as a weighted quiver. -/
def weight_multigraph.to_weight_quiver (G : weight_multigraph α W) : weight_quiver α W := { .. G }

/-- `weight_multigraph_class F α W` states that `F` is a type of `W`-weighted multigraphs on `α`.

Extend this class when you extend `weight_multigraph`. -/
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

instance : has_bot (weight_multigraph α W) :=
⟨{ hom := λ _ _, pempty,
  hom_fun := λ _ _, id,
  hom_fun_comp := λ _ _, rfl,
  hom_weight := λ _ _, pempty.elim,
  hom_weight_comm := λ _ _ e, e.elim }⟩

instance : inhabited (weight_multigraph α W) := ⟨⊥⟩


/-- The type of `W`-weighted simple quivers on `α`. -/
structure weight_simple_quiver (α W : Type*) extends simple_quiver α :=
(hom_weight (a b : α) : (a ⟶ b) → W)

/-- Reinterprets a weighted simple quiver as a weighted quiver. -/
def weight_simple_quiver.to_weight_quiver (G : weight_simple_quiver α W) : weight_quiver α W :=
{ .. G }

/-- `weight_simple_quiver_class F α W` states that `F` is a type of `W`-weighted simple quiver on
`α`.

Extend this class when you extend `weight_simple_quiver`. -/
class weight_simple_quiver_class (F : Type u₁) (α : out_param $ Type u₂) (W : out_param $ Type u₄)
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

instance : has_bot (weight_simple_quiver α W) :=
⟨{ hom := λ _ _, pempty,
  hom_self := λ _, pempty.is_empty,
  hom_weight := λ _ _, pempty.elim }⟩

instance : inhabited (weight_simple_quiver α W) := ⟨⊥⟩


/-- The type of `W`-weighted simple multigraphs on `α`. -/
structure weight_simple_multigraph (α : Type u₂) (W : Type u₃)
  extends simple_multigraph.{u₁ u₂} α : Type (max u₁ u₂ u₃) :=
(hom_weight (a b : α) : (a ⟶ b) → W)
(hom_weight_comm (a b : α) (e : a ⟶ b) : hom_weight _ _ (hom_fun _ _ e) = hom_weight _ _ e)

/-- Reinterprets a weighted simple multigraph as a weighted multigraph -/
def weight_simple_multigraph.to_weight_multigraph (G : weight_simple_multigraph α W) :
  weight_multigraph α W :=
{ .. G }

/-- `weight_simple_multigraph_class F α W` states that `F` is a type of `W`-weighted simple
multigraphs on `α`.

Extend this class when you extend `weight_simple_multigraph`. -/
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

instance : has_bot (weight_simple_multigraph α W) :=
⟨{ hom := λ _ _, pempty,
  hom_self := λ _, pempty.is_empty,
  hom_fun := λ _ _, id,
  hom_fun_comp := λ _ _, rfl,
  hom_weight := λ _ _, pempty.elim,
  hom_weight_comm := λ _ _ e, e.elim }⟩

instance : inhabited (weight_simple_multigraph α W) := ⟨⊥⟩
