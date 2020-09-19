import combinatorics.simple_graph.basic

universes u v

namespace simple_graph

/--
A graph homomorphism is a map on vertex sets that respects the adjacency relations.
-/
abbreviation hom (G : simple_graph.{u}) (G' : simple_graph.{v}) : Type (max u v) :=
rel_hom (@adj' G) (@adj' G')

infix ` →g ` : 50 := hom

namespace hom
variables {G : simple_graph} {G' : simple_graph} (f : G →g G')

lemma map_adj {v w : V G} : v ~g w → f v ~g f w :=
by apply f.map_rel'

def map_edge_set : G.edge_set → G'.edge_set :=
λ e, ⟨sym2.map f e.val, begin
  rcases e with ⟨e, h⟩,
  refine quotient.rec_on_subsingleton e (λ e h, _) h,
  rcases e with ⟨v, w⟩,
  rw sym2.map_pair_eq, rw mem_edge_set at ⊢ h,
  exact f.map_rel' h,
end⟩

def map_neighbor_set (v : V G) : neighbor_set v → neighbor_set (f v) :=
λ w, ⟨f w.val, begin
  rcases w with ⟨w, h⟩,
  rw mem_neighbor_set at h ⊢,
  exact map_adj f h,
end⟩

variables {G'' : simple_graph}

/--
Composition of graph homomorphisms
-/
def comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
f'.comp f

@[simp] lemma comp_app (f' : G' →g G'') (f : G →g G') (v : V G) : (f'.comp f) v = f' (f v) := rfl

@[simp] lemma coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f := rfl

class mono (f : G →g G') : Prop :=
(injective [] : function.injective f)

lemma mono_iff_injective (f : G →g G') : mono f ↔ function.injective f :=
⟨@mono.injective _ _ f, mono.mk⟩

instance mono.comp (f' : G' →g G'') (f : G →g G') [mono f'] [mono f] : mono (f'.comp f) :=
begin
  split, rw coe_comp,
  apply function.injective.comp (mono.injective f') (mono.injective f),
end

lemma map_neighbor_set.inj [mono f] (v : V G) : function.injective (map_neighbor_set f v) :=
begin
  rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
  dsimp [map_neighbor_set] at h,
  rw subtype.mk_eq_mk at h ⊢,
  exact mono.injective f h,
end

end hom

/--
A graph embedding is an embedding on vertex sets onto an induced subgraph.
-/

abbreviation embedding (G : simple_graph.{u}) (G' : simple_graph.{v}) : Type (max u v) :=
rel_embedding (@adj' G) (@adj' G')

infix ` ↪g ` : 50 := embedding

namespace embedding

variables {G : simple_graph.{u}} {G' : simple_graph.{v}} (f : G ↪g G')

/--
An embedding of graphs gives rise to a homomorphism of graphs.
-/
def to_hom (f : G ↪g G') : G →g G' := f.to_rel_hom

instance mono : hom.mono f.to_hom :=
{ injective := f.injective }

lemma map_adj {v w : V G} : v ~g w ↔ f v ~g f w :=
by apply f.map_rel_iff'

def map_edge_set : G.edge_set ↪ G'.edge_set :=
{ to_fun := hom.map_edge_set ↑f,
  inj' := begin
    rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ h,
    dsimp [hom.map_edge_set] at h,
    rw subtype.mk_eq_mk at h ⊢,
    refine quotient.rec_on_subsingleton e₁ (λ e₁ h₁ h, _) h₁ h,
    refine quotient.rec_on_subsingleton e₂ (λ e₂ h₂ h, _) h₂ h,
    rcases e₁ with ⟨x₁, y₁⟩, rcases e₂ with ⟨x₂, y₂⟩,
    repeat { rw sym2.map_pair_eq at h },
    rw sym2.eq_iff at h ⊢,
    cases h; rw [f.inj' h_1.1, f.inj' h_1.2]; simp,
  end }

def map_neighbor_set (v : V G) : neighbor_set v ↪ neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w.val, begin
    rcases w with ⟨w, h⟩,
    rw mem_neighbor_set at h ⊢,
    exact f.map_adj.mp h,
  end⟩,
  inj' := begin
    rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
    rw subtype.mk_eq_mk at h ⊢,
    exact f.inj' h,
  end }

variables {G'' : simple_graph}

/--
Composition of graph embeddings
-/
def comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' := f.trans f'

@[simp] lemma comp_app (f' : G' ↪g G'') (f : G ↪g G') (v : V G) : (f'.comp f) v = f' (f v) := rfl

@[simp] lemma coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end embedding

/--
A graph isomorphism is an equivalence on vertex sets that preserves the adjacency relations exactly.
-/
abbreviation iso (G : simple_graph.{u}) (G' : simple_graph.{v}) : Type (max u v):=
rel_iso (@adj' G) (@adj' G')

infix ` ≃g ` : 50 := iso

namespace iso

variables {G : simple_graph.{u}} {G' : simple_graph.{v}} (f : G ≃g G')

def to_embedding (f : G ≃g G') : G ↪g G' := f.to_rel_embedding

def to_hom (f : G ≃g G') : G →g G' := f.to_embedding.to_hom

@[simp] lemma normalize_coe (f : G ≃g G') : f.to_embedding.to_hom = f.to_hom := rfl

instance mono : hom.mono f.to_hom :=
{ injective := f.injective }

lemma map_adj_iff {v w : V G} : v ~g w ↔ f v ~g f w :=
by apply f.map_rel_iff'

def map_edge_set : G.edge_set ≃ G'.edge_set :=
{ to_fun := hom.map_edge_set ↑f,
  inv_fun := hom.map_edge_set ↑f.symm,
  left_inv := begin
    rintro ⟨e, h⟩,
    refine quotient.rec_on_subsingleton e (λ e h, _) h,
    rcases e with ⟨v, w⟩,
    dsimp [hom.map_edge_set],
    simp,
  end,
  right_inv := begin
    rintro ⟨e, h⟩,
    refine quotient.rec_on_subsingleton e (λ e h, _) h,
    rcases e with ⟨v, w⟩,
    dsimp [hom.map_edge_set],
    simp,
  end }

variables {G'' : simple_graph}

/--
Composition of graph isomorphisms
-/
def comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' := f.trans f'

@[simp] lemma comp_app (f' : G' ≃g G'') (f : G ≃g G') (v : V G) : (f'.comp f) v = f' (f v) := rfl

@[simp] lemma coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f := rfl

lemma iso_has_eq_order [fintype (V G)] [fintype (V G')] (f : G ≃g G') : fintype.card (V G) = fintype.card (V G') :=
by { convert (fintype.of_equiv_card f.to_equiv).symm }

lemma iso_has_eq_size [fintype G.edge_set] [fintype G'.edge_set] (f : G ≃g G') :
  (edge_finset G).card = (edge_finset G').card :=
begin
  convert_to fintype.card G.edge_set = fintype.card G'.edge_set; try { exact multiset.card_map subtype.val _ },
  convert (fintype.of_equiv_card (map_edge_set f)).symm,
end

end iso


def complete_equiv_complete_partite (α : Type u) :
  ↟(complete_graph α) ≃g ↟(complete_partite_graph (λ v : α, punit)) :=
{ to_fun := λ v, ⟨v, punit.star⟩,
  inv_fun := λ v, v.1,
  left_inv := by tidy,
  right_inv := by tidy,
  map_rel_iff' := by tidy }

end simple_graph
