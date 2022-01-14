import data.finset.basic
import data.set.finite
import data.nat.enat

universes u v w

@[ext]
structure ASC (V : Type u) :=
(faces : set (finset V))
(nonempty_of_mem : ∀ {s : finset V}, s ∈ faces → s.nonempty)
(down_closed : ∀ {s t : finset V}, s ∈ faces → t ⊆ s → t.nonempty → t ∈ faces)

namespace ASC

variables {V : Type u}

instance : has_mem (finset V) (ASC V) := ⟨λ s K, s ∈ K.faces⟩

def vertices (K : ASC V) : set V := {v : V | {v} ∈ K}

lemma mem_vertices (K : ASC V) (v : V) : v ∈ K.vertices ↔ {v} ∈ K := iff.rfl

lemma vertices_eq (K : ASC V) : K.vertices = ⋃ s ∈ K.faces, (s : set V) :=
begin
  ext v,
  refine ⟨λ h, set.mem_bUnion h $ finset.mem_coe.2 $ finset.mem_singleton_self _, λ h, _⟩,
  obtain ⟨s, hs, hv⟩ := set.mem_bUnion_iff.1 h,
  exact K.down_closed hs (finset.singleton_subset_iff.2 $ finset.mem_coe.1 hv)
    (finset.singleton_nonempty _)
end

def facets (K : ASC V) : set (finset V) := {s : finset V | ∀ ⦃t⦄, t ∈ K → s ⊆ t → s = t}

section lattice

instance : partial_order (ASC V) := partial_order.lift faces ext

instance : has_inf (ASC V) :=
⟨λ K L,
{ faces := K.faces ∩ L.faces,
  nonempty_of_mem := λ s hs, K.nonempty_of_mem hs.1,
  down_closed := λ s t ⟨hsK, hsL⟩ hts ht, ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩ }⟩

lemma inf_faces {K L : ASC V} : (K ⊓ L).faces = K.faces ⊓ L.faces := rfl

instance : has_sup (ASC V) :=
⟨λ K L,
{ faces := K.faces ∪ L.faces,
  nonempty_of_mem := λ s hs, hs.cases_on (λ h, K.nonempty_of_mem h) (λ h, L.nonempty_of_mem h),
  down_closed := λ s t hs hts ht, hs.cases_on
    (λ hsK, or.inl $ K.down_closed hsK hts ht)
    (λ hsL, or.inr $ L.down_closed hsL hts ht) }⟩

lemma sup_faces {K L : ASC V} : (K ⊔ L).faces = K.faces ⊔ L.faces := rfl

instance : distrib_lattice (ASC V) :=
{ le_sup_left := λ K L, @le_sup_left _ _ K.faces L.faces,
  le_sup_right := λ K L, @le_sup_right _ _ K.faces L.faces,
  sup_le := λ K L M (hKM : K.faces ≤ M.faces) (hLM : L.faces ≤ M.faces), sup_le hKM hLM,
  inf_le_left := λ K L, @inf_le_left _ _ K.faces L.faces,
  inf_le_right := λ K L, @inf_le_right _ _ K.faces L.faces,
  le_inf := λ K L M (hKL : K.faces ≤ L.faces) (hKM : K.faces ≤ M.faces), le_inf hKL hKM,
  le_sup_inf := λ K L M, @le_sup_inf _ _ K.faces L.faces M.faces,
  ..ASC.partial_order,
  ..ASC.has_sup,
  ..ASC.has_inf }

instance : has_top (ASC V) :=
⟨{ faces := {s : finset V | s.nonempty},
  nonempty_of_mem := λ s hs, hs,
  down_closed := λ s t hs hts ht, ht }⟩

instance : has_bot (ASC V) :=
⟨{ faces := ∅,
  nonempty_of_mem := λ s hs, hs.rec _,
  down_closed := λ s t hs, hs.rec _ }⟩

instance : has_Sup (ASC V) :=
⟨λ s,
{ faces := Sup $ faces '' s,
  nonempty_of_mem := λ σ ⟨k, ⟨K, hK, rfl⟩, h⟩, K.nonempty_of_mem h,
  down_closed := λ k l ⟨_, ⟨K, hKs, rfl⟩, hk⟩ hlk hl,
    ⟨K.faces, ⟨K, hKs, rfl⟩, K.down_closed hk hlk hl⟩ }⟩

lemma Sup_faces (s : set (ASC V)) : (Sup s).faces = Sup (faces '' s) := rfl

instance : has_Inf (ASC V) :=
⟨λ s,
{ faces := {t ∈ Inf $ faces '' s | t.nonempty},
  nonempty_of_mem := λ σ ⟨_, hσ⟩, hσ,
  down_closed := λ k l ⟨hk₁, (hk₂ : k.nonempty)⟩ hlk hl, ⟨begin
    rintros m ⟨M, hM, rfl⟩,
    exact M.down_closed (hk₁ M.faces ⟨M, hM, rfl⟩) hlk hl,
  end, hl⟩ }⟩

lemma Inf_faces (s : set (ASC V)) : (Inf s).faces = {t ∈ Inf $ faces '' s | t.nonempty} :=
rfl

-- TODO: Move
lemma set.sep_eq_iff_forall {α : Type*} {s : set α} {p : α → Prop} :
  {x ∈ s | p x} = s ↔ ∀ x ∈ s, p x :=
⟨λ h x hx, by { rw ←h at hx, exact hx.2 },
λ h, set.subset.antisymm (set.sep_subset _ _) (λ x hx, ⟨hx, h _ hx⟩)⟩

lemma Inf_faces_of_nonempty {s : set (ASC V)} (h : s.nonempty) :
  faces (Inf s) = Inf (faces '' s) :=
begin
  rw [Inf_faces, set.sep_eq_iff_forall],
  intros σ hσ,
  obtain ⟨K, hK⟩ := h,
  exact K.nonempty_of_mem (hσ K.faces ⟨K, hK, rfl⟩),
end

-- Abstract simplicial complexes with vertices in `V` form a `complete_distrib_lattice`
instance : complete_distrib_lattice (ASC V) :=
{ le_Sup := λ s K hK σ hσ, ⟨K.faces, ⟨K, hK, rfl⟩, hσ⟩,
  Sup_le := λ s K h σ ⟨_, ⟨L, hLs, rfl⟩, hσL⟩, h _ hLs hσL,
  Inf_le := λ s K hK σ hσ, begin
    rw Inf_faces_of_nonempty ⟨K, hK⟩ at hσ,
    exact hσ K.faces ⟨K, hK, rfl⟩,
  end ,
  le_Inf := λ s K h σ hσ, begin
    split,
    { rintros l ⟨L, hL, rfl⟩,
      exact h _ hL hσ },
    { exact K.nonempty_of_mem hσ}
  end,
  le_top := λ K σ hσ, K.nonempty_of_mem hσ,
  bot_le := λ K σ hσ, hσ.rec _,
  infi_sup_le_sup_Inf := λ K s σ hσ, begin
    classical, -- we need prop decidable
    rw [infi, Inf_faces] at hσ,
    obtain ⟨hσ₁, hσ₂ : σ.nonempty⟩ := hσ,
    rw [sup_faces, Inf_faces],
    by_cases hσK : σ ∈ K,
    { left,
      exact hσK },
    { right,
      refine ⟨_, hσ₂⟩,
      rintros l ⟨L, hL, rfl⟩,
      specialize hσ₁ (K ⊔ L).faces ⟨K ⊔ L, ⟨L, _⟩, rfl⟩,
      dsimp only,
      rw [infi_eq_if, if_pos hL],
      exact or.resolve_left hσ₁ hσK }
  end,
  inf_Sup_le_supr_inf := λ K s σ hσ, begin
    classical,
    obtain ⟨hσ₁, l, ⟨L, hL, rfl⟩, hσ₂⟩ := hσ,
    rw [supr, Sup_faces],
    refine ⟨(K ⊓ L).faces, ⟨K ⊓ L, ⟨L, _⟩, rfl⟩, ⟨hσ₁, hσ₂⟩⟩,
    dsimp only,
    rw [supr_eq_if, if_pos hL],
  end,
  ..ASC.distrib_lattice,
  ..ASC.has_Sup,
  ..ASC.has_Inf,
  ..ASC.has_top,
  ..ASC.has_bot }

end lattice

def finite (K : ASC V) : Prop := K.faces.finite

section classical

open_locale classical

noncomputable def dimension (K : ASC V) : enat :=
  enat.find (λ n, ∀ ⦃s : finset V⦄, s ∈ K → s.card ≤ n + 1)

-- TODO: Check nat subtraction
def pure (K : ASC V) : Prop :=
  ∀ ⦃s : finset V⦄, s ∈ K.facets → ((s.card - 1 : ℕ) : enat) = K.dimension

end classical

def skeleton (K : ASC V) (d : ℕ) : ASC V :=
{ faces := {s ∈ K.faces | s.card ≤ d + 1},
  nonempty_of_mem := λ s hs, K.nonempty_of_mem hs.1,
  down_closed := λ s t ⟨hsK, hsd⟩ hts ht, ⟨K.down_closed hsK hts ht,
    le_trans (finset.card_le_of_subset hts) hsd⟩}

section

variable [decidable_eq V]

lemma finset.union_nonempty_left {s t : finset V} (hs : s.nonempty) : (s ∪ t).nonempty :=
let ⟨x, hx⟩ := hs in ⟨x, finset.mem_union.2 $ or.inl hx⟩

lemma finset.union_nonempty_right {s t : finset V} (ht : t.nonempty) : (s ∪ t).nonempty :=
let ⟨x, hx⟩ := ht in ⟨x, finset.mem_union.2 $ or.inr hx⟩

def link (K : ASC V) (s : finset V) : ASC V :=
{ faces := {t ∈ K.faces | s ∩ t = ∅ ∧ s ∪ t ∈ K},
  nonempty_of_mem := λ σ hσ, K.nonempty_of_mem hσ.1,
  down_closed := λ σ τ ⟨hσK, hσint, hσunion⟩ hτσ hτ, ⟨K.down_closed hσK hτσ hτ,
    eq_bot_iff.2 $ le_trans (finset.inter_subset_inter_left hτσ) (eq_bot_iff.1 hσint),
    K.down_closed hσunion (finset.union_subset_union (finset.subset.refl _) hτσ)
      (finset.union_nonempty_right hτ)⟩ }

end

end ASC

@[ext]
structure simplicial_map {U : Type u} {V : Type v} [decidable_eq V] (K : ASC U) (L : ASC V) :=
(vertex_map : U → V)
(face : ∀ s ∈ K, (s : finset U).image vertex_map ∈ L)

notation K ` →ₛ ` L := simplicial_map K L

namespace simplicial_map

variables {U : Type u} {V : Type v} {W : Type w}
variables [decidable_eq V] [decidable_eq W]
variables {K : ASC U} {L : ASC V} {M : ASC W}

def comp (g : L →ₛ M) (f : K →ₛ L) : K →ₛ M :=
{ vertex_map := g.vertex_map ∘ f.vertex_map,
  face := λ s hs, begin
    rw ←finset.image_image,
    apply g.face,
    apply f.face,
    exact hs
  end }

def id (L : ASC V) : L →ₛ L :=
{ vertex_map := id,
  face := λ s hs, by rwa finset.image_id }

end simplicial_map
