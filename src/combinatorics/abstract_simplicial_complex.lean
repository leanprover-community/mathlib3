import data.finset.basic

universes u

@[ext]
structure ASC (V : Type u) :=
(faces : set (finset V))
(not_empty_mem : ∅ ∉ faces)
(down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces)

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
    (finset.singleton_ne_empty _)
end

def facets (K : ASC V) : set (finset V) := {s : finset V | ∀ ⦃t⦄, t ∈ K → s ⊆ t → s = t}

section lattice

instance : partial_order (ASC V) := partial_order.lift faces ext

instance : has_inf (ASC V) :=
⟨λ K L,
{ faces := K.faces ∩ L.faces,
  not_empty_mem := λ h, K.not_empty_mem h.1,
  down_closed := λ s t ⟨hsK, hsL⟩ hts ht, ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩ }⟩

instance : has_sup (ASC V) :=
⟨λ K L,
{ faces := K.faces ∪ L.faces,
  not_empty_mem := λ h, h.cases_on K.not_empty_mem L.not_empty_mem,
  down_closed := λ s t hs hts ht, hs.cases_on
    (λ hsK, or.inl $ K.down_closed hsK hts ht)
    (λ hsL, or.inr $ L.down_closed hsL hts ht) }⟩

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
⟨{ faces := {s : finset V | s ≠ ∅},
  not_empty_mem := λ h, h rfl,
  down_closed := λ s t hs hts ht, ht }⟩

instance : has_bot (ASC V) :=
⟨{ faces := ∅,
  not_empty_mem := set.not_mem_empty _,
  down_closed := λ s t hs, hs.rec _ }⟩

instance : has_Sup (ASC V) :=
⟨λ s,
{ faces := Sup $ faces '' s,
  not_empty_mem := λ h, begin
    rw [set.Sup_eq_sUnion, set.mem_sUnion] at h,
    obtain ⟨k, ⟨K, hKs, rfl⟩, hk⟩ := h,
    exact K.not_empty_mem hk,
  end,
  down_closed := λ k l hk hlk hl, begin
    rw [set.Sup_eq_sUnion, set.mem_sUnion] at hk ⊢,
    obtain ⟨_, ⟨K, hKs, rfl⟩, hk⟩ := hk,
    exact ⟨K.faces, ⟨K, hKs, rfl⟩, K.down_closed hk hlk hl⟩,
  end }⟩

end lattice

end ASC
