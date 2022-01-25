import data.equiv.basic
import logic.relation
import tactic.obviously

/-!
# Definitions of graphs
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃ u₄

structure directed_multigraph (V : Type u) :=
(edge : V → V → Sort v)

def directed_multigraph.vertices {V : Type u} (G : directed_multigraph V) := V

structure multigraph (V : Type u) extends directed_multigraph.{v} V :=
(inv : Π (x y), edge x y ≃ edge y x)

def multigraph_of_edges {n : ℕ} (e : list (fin n × fin n)) : multigraph (fin n) :=
{ edge := λ x y, fin (e.countp (λ p, p = (x, y) ∨ p = (y, x))),
  inv := λ x y, by { dsimp, convert equiv.refl _, funext, rw or_comm, } }

structure directed_graph (V : Type u) extends directed_multigraph.{0} V.

def directed_graph.vertices {V : Type u} (G : directed_graph V) := V

structure graph (V : Type u) extends multigraph.{0} V :=
(symm {} : symmetric edge)
(inv := λ x y, equiv.of_iff ⟨@symm _ _, @symm _ _⟩)

def graph_of_edges {n : ℕ} (e : list (fin n × fin n)) : graph (fin n) :=
{ edge := λ x y, (x, y) ∈ e ∨ (y, x) ∈ e,
  symm := λ x y h, by { dsimp, rw [or_comm], apply h } }

notation x `~[`G`]` y := G.edge x y

namespace graph
variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {V₄ : Type u₄}
variables (G : graph V) (G₁ : graph V₁) (G₂ : graph V₂) (G₃ : graph V₃) (G₄ : graph V₄)

def vertices (G : graph V) := V

def edge.symm {G : graph V} {x y : V} (e : x ~[G] y) : y ~[G] x := G.symm e

def is_linked (G : graph V) (x y : V) : Prop :=
relation.refl_trans_gen G.edge x y

def is_connected (G : graph V) : Prop :=
∀ ⦃x y⦄, G.is_linked x y

def is_loopless (G : graph V) : Prop :=
∀ ⦃x⦄, ¬ (x ~[G] x)

def complete (V : Type u) : graph V :=
{ edge := λ x y, x ≠ y,
  symm := λ x y h, h.symm }

localized "notation `K_` n := complete (fin n)" in graph_theory

lemma complete_is_loopless (V : Type u) : (complete V).is_loopless :=
assume x, ne.irrefl

lemma ne_of_edge {G : graph V} (h : G.is_loopless) {x y : V} (e : x ~[G] y) :
  x ≠ y :=
by { rintro rfl, exact h e }

section

/-- A homomorphism of graphs is a function on the vertices that preserves edges. -/
structure hom (G₁ : graph V₁) (G₂ : graph V₂) :=
(to_fun    : V₁ → V₂)
(map_edge' : ∀ {x y}, (x ~[G₁] y) → (to_fun x ~[G₂] to_fun y) . obviously)

instance hom.has_coe_to_fun : has_coe_to_fun (hom G₁ G₂) (λ _, V₁ → V₂) := ⟨hom.to_fun⟩

@[simp] lemma hom.to_fun_eq_coe (f : hom G₁ G₂) (x : V₁) : f.to_fun x = f x := rfl

@[simp] lemma hom.mk_coe {G₁ : graph V₁} {G₂ : graph V₂}
  (to_fun : V₁ → V₂) (map_edge' : ∀ {x y}, (x ~[G₁] y) → (to_fun x ~[G₂] to_fun y)) (x : V₁) :
  (hom.mk to_fun @map_edge') x = to_fun x :=
rfl

section
variables {G₁ G₂ G₃ G₄}

@[simp, ematch] lemma hom.map_edge (f : hom G₁ G₂) :
  ∀ {x y}, (x ~[G₁] y) → (f x ~[G₂] f y) :=
f.map_edge'

@[ext] lemma hom.ext {f g : hom G₁ G₂} (h : (f : V₁ → V₂) = g) : f = g :=
by { cases f, cases g, congr, exact h }

lemma hom.ext_iff (f g : hom G₁ G₂) : f = g ↔ (f : V₁ → V₂) = g :=
⟨congr_arg _, hom.ext⟩

def hom.id : hom G G :=
{ to_fun := id }

@[simp]
lemma hom.id_coe (x) : (hom.id G) x = x := rfl

def hom.comp (g : hom G₂ G₃) (f : hom G₁ G₂) : hom G₁ G₃ :=
{ to_fun    := g ∘ f,
  map_edge' := assume x y, g.map_edge ∘ f.map_edge }

@[simp]
lemma hom.comp_coe (g : hom G₂ G₃) (f : hom G₁ G₂) (x) : (hom.comp g f) x = g (f x) := rfl

@[simp]
lemma hom.comp_id (g : hom G₁ G₂) : hom.comp g (hom.id _) = g := by { ext, simp, }
@[simp]
lemma hom.id_comp (g : hom G₁ G₂) : hom.comp (hom.id _) g = g := by { ext, simp, }

@[simp]
lemma hom.assoc (f : hom G₁ G₂) (g : hom G₂ G₃) (h : hom G₃ G₄) :
  hom.comp h (hom.comp g f) = hom.comp (hom.comp h g) f := by { ext, simp, }

end

/-- The internal hom in the category of graphs. -/
def ihom : graph (V₁ → V₂) :=
{ edge := assume f g, ∀ ⦃x y⦄, (x ~[G₁] y) → (f x ~[G₂] g y),
  symm := assume f g h x y e,
          show g x ~[G₂] f y, from G₂.symm $ h (G₁.symm e) }

/-- The product in the category of graphs. -/
def prod : graph (V₁ × V₂) :=
{ edge := assume p q, (p.1 ~[G₁] q.1) ∧ (p.2 ~[G₂] q.2),
  symm := assume p q ⟨e₁, e₂⟩, ⟨G₁.symm e₁, G₂.symm e₂⟩ }

def prod.fst : hom (G₁.prod G₂) G₁ :=
{ to_fun := λ p, p.1 }

def prod.snd : hom (G₁.prod G₂) G₂ :=
{ to_fun := λ p, p.2 }

@[simps]
def hom.pair (f : hom G G₁) (g : hom G G₂) : hom G (G₁.prod G₂) :=
{ to_fun    := λ x, (f x, g x),
  map_edge' := by { intros x y e, split; simp only [e, hom.map_edge] } }

@[simps]
def icurry : hom ((G₁.prod G₂).ihom G₃) (G₁.ihom (G₂.ihom G₃)) :=
{ to_fun    := function.curry,
  map_edge' := assume f g h x₁ y₁ e₁ x₂ y₂ e₂, h $ by exact ⟨e₁, e₂⟩ }

@[simps]
def iuncurry : hom (G₁.ihom (G₂.ihom G₃)) ((G₁.prod G₂).ihom G₃) :=
{ to_fun    := λ f p, f p.1 p.2,
  map_edge' := assume f g h p q e, h e.1 e.2 }

section
variables {G₁ G₂ G₃}

@[simps]
def hom.curry (f : hom (G₁.prod G₂) G₃) : hom G₁ (G₂.ihom G₃) :=
{ to_fun    := icurry G₁ G₂ G₃ f,
  map_edge' := assume x₁ y₁ e₁ x₂ y₂ e₂, f.map_edge ⟨e₁, e₂⟩ }

@[simps]
def hom.uncurry (f : hom G₁ (G₂.ihom G₃)) : hom (G₁.prod G₂) G₃ :=
{ to_fun    := iuncurry G₁ G₂ G₃ f,
  map_edge' := assume p q e, f.map_edge e.1 e.2 }

end

def adj : (hom (G.prod G₁) G₂) ≃ (hom G (graph.ihom G₁ G₂)) :=
{ to_fun := hom.curry,
  inv_fun := hom.uncurry,
  left_inv := λ f, hom.ext $ funext $ λ ⟨x,y⟩, rfl,
  right_inv := λ f, hom.ext $ funext $ λ p, rfl }

end

def induced_graph (G₂ : graph V₂) (f : V₁ → V₂) : graph V₁ :=
{ edge := assume x y, f x ~[G₂] f y,
  symm := assume x y e, G₂.symm e }

def closed_neighbourhood (G : graph V) (x : V) :=
{ y // y = x ∨ (y ~[G] x) }

def closed_neighbourhood.graph (G : graph V) (x : V) : graph (closed_neighbourhood G x) :=
induced_graph G subtype.val

end graph

section

structure graph_hom {V V'} (G : directed_multigraph V) (G' : directed_multigraph V') :=
(obj : V → V')
(edge : Π {s t}, G.edge s t → G'.edge (obj s) (obj t))

variables {V : Type*} (G : directed_multigraph.{v+1} V)

/-- A subgraph of a directed multigraph, obtained by deleting edges. -/
def subgraph := Π a b, set (G.edge a b) -- how to allow for Prop-valued edge-sets?
instance : inhabited (subgraph G) := ⟨λ a b, ∅⟩

variable {G}

/-- A subgraph is genuinely a graph. -/
def graph_of_subgraph (S : subgraph G) : directed_multigraph V :=
⟨λ s t, S s t⟩

def subgraph_embedding (S : subgraph G) : graph_hom (graph_of_subgraph S) G :=
{ obj := id, edge := λ _ _ e, e.val }

def as_graph (C) [category_theory.category C] : directed_multigraph C :=
{ edge := λ x y, x ⟶ y }

end
