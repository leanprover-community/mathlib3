import tactic
import data.fin

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

set_option old_structure_cmd true

structure multigraph (V : Type u) :=
(edge : V → V → Sort v)

attribute [class] multigraph

def multigraph.vertices {V : Type u} (G : multigraph V) := V

structure directed_graph (V : Type u) extends multigraph.{0} V.

attribute [class] directed_graph

def directed_graph.vertices {V : Type u} (G : directed_graph V) := V

structure graph (V : Type u) extends directed_graph V :=
(symm {} : symmetric edge)

attribute [class] graph

notation x `~[`G`]` y := G.edge x y

namespace graph
variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃}
variables (G : graph V) (G₁ : graph V₁) (G₂ : graph V₂) (G₃ : graph V₃)

def vertices (G : graph V) := V

def edge.symm {G : graph V} {x y : V} (e : x ~[G] y) : y ~[G] x := G.symm e

def is_linked (G : graph V) (x y : V) : Prop :=
relation.refl_trans_gen G.edge x y

def is_connected (G : graph V) : Prop :=
∀ ⦃x y⦄, G.is_linked x y

def is_loopless (G : graph V) : Prop :=
∀ ⦃x⦄, ¬ (x ~[G] x)

def complete (V : Type u) : graph V :=
{ edge := assume x y, x ≠ y,
  symm := assume x y h, h.symm }

lemma complete_is_loopless (V : Type u) :
  (complete V).is_loopless :=
assume x, ne.irrefl

lemma ne_of_edge {G : graph V} (h : G.is_loopless) {x y : V} (e : x ~[G] y) :
  x ≠ y :=
by { rintro rfl, exact h e }

section

/-- A homomorphism of graphs is a function on the vertices that preserves edges. -/
structure hom (G₁ : graph V₁) (G₂ : graph V₂) :=
(to_fun    : V₁ → V₂)
(map_edge' : ∀ {x y}, (x ~[G₁] y) → (to_fun x ~[G₂] to_fun y) . obviously)

instance hom.has_coe_to_fun : has_coe_to_fun (hom G₁ G₂) :=
{ F := λ f, V₁ → V₂,
  coe := hom.to_fun }

@[simp] lemma hom.to_fun_eq_coe (f : hom G₁ G₂) (x : V₁) :
  f.to_fun x = f x := rfl

section
variables {G₁ G₂ G₃}

@[simp, ematch] lemma hom.map_edge (f : hom G₁ G₂) :
  ∀ {x y}, (x ~[G₁] y) → (f x ~[G₂] f y) :=
f.map_edge'

@[ext] lemma hom.ext {f g : hom G₁ G₂} (h : (f : V₁ → V₂) = g) : f = g :=
by { cases f, cases g, congr, exact h }

lemma hom.ext_iff (f g : hom G₁ G₂) : f = g ↔ (f : V₁ → V₂) = g :=
⟨congr_arg _, hom.ext⟩

def hom.id : hom G G :=
{ to_fun := id }

def hom.comp (g : hom G₂ G₃) (f : hom G₁ G₂) : hom G₁ G₃ :=
{ to_fun    := g ∘ f,
  map_edge' := assume x y, g.map_edge ∘ f.map_edge }

end

/-- The internal hom in the category of graphs. -/
instance ihom : graph (V₁ → V₂) :=
{ edge := assume f g, ∀ {x y}, (x ~[G₁] y) → (f x ~[G₂] g y),
  symm := assume f g h x y e,
          show g x ~[G₂] f y, from G₂.symm $ h e.symm }

/-- The product in the category of graphs. -/
instance prod : graph (V₁ × V₂) :=
{ edge := assume p q, (p.1 ~[G₁] q.1) ∧ (p.2 ~[G₂] q.2),
  symm := assume p q ⟨e₁, e₂⟩, ⟨e₁.symm, e₂.symm⟩ }

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

variables {G G₁ G₂ G₃}

abbreviation colouring (W : Type u₁) (G : graph V) := hom G (complete W)

def colouring_id (G : graph V) (h : G.is_loopless) : colouring V G :=
{ to_fun    := id,
  map_edge' := assume x y e, show x ≠ y, from ne_of_edge h e }

lemma colouring.is_loopless {W : Type*} (c : colouring W G) :
  G.is_loopless :=
assume x e, c.map_edge e rfl

def colouring.extend {W₁ : Type u₁} {W₂ : Type u₂}
  (c : colouring W₁ G) (f : W₁ → W₂) (hf : function.injective f) :
  colouring W₂ G :=
{ to_fun    := f ∘ c,
  map_edge' := assume x y e, hf.ne $ c.map_edge e }

structure chromatic_number (G : graph V) (n : ℕ) : Prop :=
(col_exists : nonempty (colouring (fin n) G))
(min        : ∀ {k}, colouring (fin k) G → n ≤ k)

variables {G G₁ G₂ G₃}

section hedetniemi
variables {n₁ n₂ n : ℕ}
variables (h₁ : chromatic_number G₁ n₁)
variables (h₂ : chromatic_number G₂ n₂)
variables (h : chromatic_number (G₁.prod G₂) n)

include h₁ h₂ h

/-- Hedetniemi's conjecture, which has been disproven in <https://arxiv.org/pdf/1905.02167.pdf>. -/
def hedetniemi : Prop :=
n = min n₁ n₂

lemma chromatic_number_prod_le_min : n ≤ min n₁ n₂ :=
begin
  obtain ⟨c₁⟩ : nonempty (colouring (fin n₁) G₁) := h₁.col_exists,
  obtain ⟨c₂⟩ : nonempty (colouring (fin n₂) G₂) := h₂.col_exists,
  rw le_min_iff,
  split,
  { exact h.min (c₁.comp (prod.fst G₁ G₂)) },
  { exact h.min (c₂.comp (prod.snd G₁ G₂)) }
end

end hedetniemi

lemma chromatic_number.is_loopless {n} (h : chromatic_number G n) :
  G.is_loopless :=
begin
  rcases h.col_exists with ⟨c⟩,
  exact c.is_loopless
end

lemma chromatic_number_le_card_of_colouring {W : Type*} [fintype W] {n m}
  (c : colouring W G) (hn : chromatic_number G n) (hm : m = fintype.card W) :
  n ≤ m :=
begin
  obtain ⟨k, ⟨f⟩⟩ : ∃ k, nonempty (W ≃ fin k) :=
    fintype.exists_equiv_fin W,
  obtain rfl : m = k,
  { rw [hm, fintype.card_congr f, fintype.card_fin] },
  apply hn.min,
  exact c.extend f f.injective
end

lemma chromatic_number_le_card [fintype V] {n m}
  (hn : chromatic_number G n) (hm : m = fintype.card V) :
  n ≤ m :=
chromatic_number_le_card_of_colouring (colouring_id G hn.is_loopless) hn hm

def induced_graph (G₂ : graph V₂) (f : V₁ → V₂) : graph V₁ :=
{ edge := assume x y, f x ~[G₂] f y,
  symm := assume x y e, e.symm }

def closed_neighbourhood (G : graph V) (x : V) :=
{ y // y = x ∨ (y ~[G] x) }

instance closed_neighbourhood.graph (G : graph V) (x : V) : graph (closed_neighbourhood G x) :=
induced_graph G subtype.val

def is_robust {W : Type*} (w : W) (G : graph V) (x : V) (s : set (V → W)) : Prop :=
∀ φ ∈ s, ∃ y : closed_neighbourhood G x, w = (φ : V → W) y.val



end graph
