import combinatorics.graphs.basic4
open graph

universes u v

namespace multigraphs
open graph.multigraphs

structure hom {α : Type*} {β : Type*} [multigraphs α] [multigraphs β] (G : α) (G' : β) :=
(on_vertices : vertices G → vertices G')
(on_edges : edges G → edges G')
(on_links : ∀ ⦃x⦄, x ∈ links G → link.induce on_vertices on_edges x ∈ links G')

namespace hom
--variables {α : Type*} {β : Type*} [multigraphs α]  [multigraphs β]

def id {α : Type*} [multigraphs α] {G : α} : hom G G :=
{ on_vertices := id,
  on_edges := id,
  on_links := by simp [link.induce] }

section composition
variables {α₁ α₂ α₃ : Type*}

def comp [multigraphs α₁] [multigraphs α₂] [multigraphs α₃] {G₁ : α₁} {G₂ : α₂} {G₃ : α₃}
(g : hom G₂ G₃) (f : hom G₁ G₂) : hom G₁ G₃ :=
{ on_vertices := g.on_vertices ∘ f.on_vertices,
  on_edges := g.on_edges ∘ f.on_edges,
  on_links := begin
    rintro x xel,
    rw link.induce_functorial,
    exact g.on_links (f.on_links xel),
  end }

@[simp]
lemma hom.comp_id [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂} (f : hom G₁ G₂) :
hom.comp f hom.id = f :=
by { cases f, dsimp [hom.comp], congr, }

@[simp]
lemma hom.id_comp [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂} (f : hom G₁ G₂) :
hom.comp hom.id f = f :=
by { cases f, dsimp [hom.comp], congr, }

lemma hom.assoc {α₄ : Type*} [multigraphs α₁] [multigraphs α₂] [multigraphs α₃] [multigraphs α₄] {G₁ : α₁} {G₂ : α₂} {G₃ : α₃} {G₄ : α₄}
(f₃ : hom G₃ G₄) (f₂ : hom G₂ G₃) (f₁ : hom G₁ G₂):
(f₃.comp f₂).comp f₁ = f₃.comp (f₂.comp f₁) :=
by { cases f₁, cases f₂, cases f₃, dsimp [hom.comp], congr, }

end composition

section equiv
variables {α₁ : Type*} {α₂ : Type*} {α₃ : Type*}

structure equiv [multigraphs α₁] [multigraphs α₂] (G₁ : α₁) (G₂ : α₂) :=
(to_fun    : hom G₁ G₂)
(inv_fun   : hom G₂ G₁)
(left_inv  : inv_fun.comp to_fun = hom.id)
(right_inv : to_fun.comp inv_fun = hom.id)

def equiv.id [multigraphs α₁] {G₁ : α₁} : equiv G₁ G₁ :=
{ to_fun := hom.id,
  inv_fun := hom.id,
  left_inv := by simp,
  right_inv := by simp }

@[symm]
def equiv.symm [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂} (f : equiv G₁ G₂) : equiv G₂ G₁ :=
{ to_fun := f.inv_fun,
  inv_fun := f.to_fun,
  left_inv := f.right_inv,
  right_inv := f.left_inv }

@[trans]
def equiv.trans [multigraphs α₁] [multigraphs α₂] [multigraphs α₃] {G₁ : α₁} {G₂ : α₂} {G₃ : α₃}
(f : equiv G₁ G₂) (g : equiv G₂ G₃) : equiv G₁ G₃ :=
{ to_fun := hom.comp g.to_fun f.to_fun,
  inv_fun := hom.comp f.inv_fun g.inv_fun,
  left_inv := by rw [hom.assoc, ←hom.assoc g.inv_fun, g.left_inv, hom.id_comp, f.left_inv],
  right_inv := by rw [hom.assoc, ←hom.assoc f.to_fun, f.right_inv, hom.id_comp, g.right_inv] }

@[simp]
def equiv.trans_id [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂}
(f : equiv G₁ G₂) : equiv.trans f equiv.id = f :=
by { cases f, simp [equiv.trans, equiv.id] }

@[simp]
def equiv.id_trans [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂}
(f : equiv G₁ G₂) : equiv.trans equiv.id f = f :=
by { cases f, simp [equiv.trans, equiv.id] }

@[simp]
def equiv.trans_symm [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂}
(f : equiv G₁ G₂) : equiv.trans f f.symm = equiv.id :=
by { cases f, simp [equiv.trans, equiv.symm, equiv.id, f_left_inv] }

@[simp]
def equiv.symm_trans [multigraphs α₁] [multigraphs α₂] {G₁ : α₁} {G₂ : α₂}
(f : equiv G₁ G₂) : equiv.trans f.symm f = equiv.id :=
by { cases f, simp [equiv.trans, equiv.symm, equiv.id, f_right_inv] }

-- Two graphs are isomorphic if there is an equivalence between them.
def isomorphic [multigraphs α₁] [multigraphs α₂] (G₁ : α₁) (G₂ : α₂) : Prop :=
nonempty (equiv G₁ G₂)

end equiv

end hom

end multigraphs
