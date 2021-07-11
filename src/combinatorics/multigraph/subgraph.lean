import combinatorics.multigraph.basic

namespace multigraph
universes u v
variables {V : Type u} {α : Type v}

@[ext]
structure subgraph (G : multigraph V α) :=
(verts : set V)
(labels : V → V → set α)
(labels_sub : ∀ {v w : V}, labels v w ⊆ G.labels v w)
(edge_vert : ∀ {v w : V} {a : α}, a ∈ labels v w → v ∈ verts)
(symm : ∀ (v w : V), labels v w = labels w v)

namespace subgraph
variables {G : multigraph V α}

def is_subgraph (X Y : G.subgraph) : Prop := X.verts ⊆ Y.verts ∧ ∀ {v w : V}, X.labels v w ⊆ Y.labels v w

def union (X Y : G.subgraph) : G.subgraph :=
{ verts := X.verts ∪ Y.verts,
  labels := λ v w, X.labels v w ∪ Y.labels v w,
  labels_sub := λ v w a h, or.cases_on h (λ h, X.labels_sub h) (λ h, Y.labels_sub h),
  edge_vert := λ v w a h, or.cases_on h (λ h, or.inl (X.edge_vert h)) (λ h, or.inr (Y.edge_vert h)),
  symm := λ v w, by rw [X.symm, Y.symm] }

def inter (X Y : G.subgraph) : G.subgraph :=
{ verts := X.verts ∩ Y.verts,
  labels := λ v w, X.labels v w ∩ Y.labels v w,
  labels_sub := λ v w a h, X.labels_sub h.1,
  edge_vert := λ v w a h, ⟨X.edge_vert h.1, Y.edge_vert h.2⟩,
  symm := λ v w, by rw [X.symm, Y.symm] }

instance : has_union G.subgraph := ⟨union⟩
instance : has_inter G.subgraph := ⟨inter⟩

def top : G.subgraph :=
{ verts := set.univ,
  labels := G.labels,
  labels_sub := λ v w a h, h,
  edge_vert := λ v w a h, set.mem_univ _,
  symm := G.symm }

def bot : G.subgraph :=
{ verts := ∅,
  labels := λ _ _, ∅,
  labels_sub := λ v w a h, false.rec _ h,
  edge_vert := λ v w a h, false.rec _ h,
  symm := λ v w, rfl }

instance : inhabited G.subgraph := ⟨bot⟩

instance : bounded_lattice G.subgraph :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  top := top,
  bot := bot,
  le_refl := λ x, ⟨rfl.subset, λ _ _ _ h, h⟩,
  le_trans := λ x y z hxy hyz, ⟨hxy.1.trans hyz.1, λ _ _ _ h, hyz.2 (hxy.2 h)⟩,
  le_antisymm := begin
    intros x y hxy hyx,
    ext1 v,
    exact set.subset.antisymm hxy.1 hyx.1,
    ext v w,
    exact iff.intro (λ h, hxy.2 h) (λ h, hyx.2 h),
  end,
  le_top := λ x, ⟨set.subset_univ _, (λ _ _ _ h, x.labels_sub h)⟩,
  bot_le := λ x, ⟨set.empty_subset _, (λ _ _ _ h, false.rec _ h)⟩,
  sup_le := λ x y z hxy hyz,
            ⟨set.union_subset hxy.1 hyz.1,
              (λ _ _ _ h, h.cases_on (λ h, hxy.2 h) (λ h, hyz.2 h))⟩,
  le_sup_left := λ x y, ⟨set.subset_union_left x.verts y.verts, (λ _ _ _ h, or.inl h)⟩,
  le_sup_right := λ x y, ⟨set.subset_union_right x.verts y.verts, (λ _ _ _ h, or.inr h)⟩,
  le_inf := λ x y z hxy hyz, ⟨set.subset_inter hxy.1 hyz.1, (λ _ _ _ h, ⟨hxy.2 h, hyz.2 h⟩)⟩,
  inf_le_left := λ x y, ⟨set.inter_subset_left x.verts y.verts, (λ _ _ _ h, h.1)⟩,
  inf_le_right := λ x y, ⟨set.inter_subset_right x.verts y.verts, (λ _ _ _ h, h.2)⟩ }

end subgraph

end multigraph
