/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import combinatorics.additive.behrend

/-!
# The Ruzsa-Szemerédi problem

This file proves the lower bound of the Ruzsa-Szemerédi problem. The problem is to find the maximum
number of edges that a graph on `n` vertices can have if all edges belong to a most one triangle.
The lower bound comes from turning the big Salem-Spencer set from Behrend's lower bound on Roth
numbers into a graph that has the property that every triangle gives a (possibly trivial)
arithmetic progression on the original set.

## Main declarations

* `simple_graph.edge_disjoint_triangles`: Predicate for a graph whose triangles are edge-disjoint.
* `simple_graph.ruzsa_szemeredi`: The Ruzsa-Szemerédi property.
* `ruzsa_szemeredi.add_graph`: The Ruzsa-Szemerédi graph associated to a set `s`.
* `add_salem_spencer.edge_disjoint_triangles`: If `s` is Salem-Spencer, then `add_graph s` has
  edge-disjoint triangles.
-/

namespace equiv
variables {α β : Type*}

@[simp] lemma coe_coe (e : α ≃ β) : ⇑(e : α ↪ β) = e := rfl

end equiv

namespace finset
variables {α β : Type*} {s : finset α}

@[simp] lemma preimage_map (f : α ↪ β) (s : finset α) :
  (s.map f).preimage f (f.injective.inj_on _) = s :=
coe_injective $ by simp only [coe_preimage, coe_map, set.preimage_image_eq _ f.injective]

lemma exists_mem_ne (hs : 1 < s.card) (a : α) : ∃ b ∈ s, b ≠ a :=
begin
  by_contra',
  haveI : nonempty α := ⟨a⟩,
  exact hs.not_le (card_le_one_iff_subset_singleton.2 ⟨a, subset_singleton_iff'.2 this⟩),
end

open_locale pointwise

variables {m n : ℕ}

lemma range_add_range_subset : range m + range n ⊆ range (m + n - 1) :=
begin
  simp_rw [subset_iff, mem_add, mem_range, lt_tsub_iff_right, ←nat.add_one_le_iff],
  rintro _ ⟨a, b, ha, hb, rfl⟩,
  rw [add_assoc, add_add_add_comm],
  exact add_le_add ha hb,
end

end finset

namespace relation
variables {α β γ δ ε κ : Type*} {r : α → β → Prop} {f : α → γ} {g : β → δ}

@[simp] lemma map_apply {c : γ} {d : δ} :
  relation.map r f g c d ↔ ∃ a b, r a b ∧ f a = c ∧ g b = d := iff.rfl

@[simp] lemma map_id_id (r : α → β → Prop) : relation.map r id id = r := by simp [relation.map]

@[simp] lemma map_map (r : α → β → Prop) (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g₂ : δ → κ) :
  relation.map (relation.map r f₁ g₁) f₂ g₂ = relation.map r (f₂ ∘ f₁) (g₂ ∘ g₁) :=
begin
  ext a b,
  simp only [map_apply, function.comp_app, ←exists_and_distrib_right, @exists₂_comm γ],
  refine exists₂_congr (λ a b, _),
  simp [and_assoc],
end

instance (r : α → β → Prop) (f : α → γ) (g : β → δ) [fintype α] [fintype β]
  [Π a, decidable_pred (r a)] [decidable_eq γ] [decidable_eq δ] :
  Π c, decidable_pred (relation.map r f g c) :=
λ c d, fintype.decidable_exists_fintype

end relation

namespace simple_graph
variables {α β V W X : Type*} {n : ℕ}

open finset function

instance [fintype V] [decidable_eq W] (f : V ↪ W) (G : simple_graph V) [decidable_rel G.adj] :
  decidable_rel (simple_graph.map f G).adj :=
relation.map.decidable_pred _ _ _

@[simp] lemma map_id {G : simple_graph V} : G.map (function.embedding.refl _) = G :=
ext _ _ $ relation.map_id_id _

@[simp] lemma map_map {G : simple_graph V} (f : V ↪ W) (g : W ↪ X) :
  (G.map f).map g = G.map (f.trans g) :=
ext _ _ $ relation.map_map _ _ _ _ _

@[simp] lemma comap_id {G : simple_graph V} : G.comap id = G := ext _ _ rfl

@[simp] lemma comap_comap {G : simple_graph X} (f : V → W) (g : W → X) :
  (G.comap g).comap f = G.comap (g ∘ f) := rfl

lemma comap_symm (G : simple_graph V) (e : V ≃ W) : G.comap e.symm = G.map e :=
by { ext, simp only [equiv.apply_eq_iff_eq_symm_apply, comap_adj, equiv.coe_eq_to_embedding,
  map_adj, equiv.to_embedding_apply, exists_eq_right_right, exists_eq_right] }

lemma map_symm (G : simple_graph W) (e : V ≃ W) : G.map (e.symm : W ↪ V) = G.comap e :=
by rw [←comap_symm, e.symm_symm]

lemma map_adj_apply {G : simple_graph V} {f : V ↪ W} {a b : V} :
  (G.map f).adj (f a) (f b) ↔ G.adj a b := by simp

@[simp] lemma clique_set_map (hn : 1 < n) (G : simple_graph V) (f : V ↪ W) :
  (G.map f).clique_set n = map f '' G.clique_set n :=
begin
  ext s,
  split,
  { rintro ⟨hs, rfl⟩,
    have hs' : (s.preimage f $ f.injective.inj_on _).map f = s,
    { classical,
      rw [map_eq_image, image_preimage, filter_true_of_mem],
      rintro a ha,
      obtain ⟨b, hb, hba⟩ := exists_mem_ne hn a,
      obtain ⟨c, _, _, hc, _⟩ := hs ha hb hba.symm,
      exact ⟨c, hc⟩ },
    refine ⟨s.preimage f $ f.injective.inj_on _, ⟨_, by rw [←card_map f, hs']⟩, hs'⟩,
    rw coe_preimage,
    exact λ a ha b hb hab, map_adj_apply.1 (hs ha hb $ f.injective.ne hab) },
  { rintro ⟨s, hs, rfl⟩,
    exact is_n_clique.map hs }
end

@[simp] lemma clique_finset_map [fintype V] [fintype W] [decidable_eq V] [decidable_eq W]
  (G : simple_graph V) [decidable_rel G.adj] (f : V ↪ W) (hn : 1 < n) :
  (G.map f).clique_finset n = (G.clique_finset n).map ⟨map f, finset.map_injective _⟩ :=
coe_injective $
  by simp_rw [coe_clique_finset, clique_set_map hn, coe_map, coe_clique_finset, embedding.coe_fn_mk]

@[simp] lemma clique_set_map' (G : simple_graph V) (e : V ≃ W) :
  ∀ n, (G.map (e : V ↪ W)).clique_set n = map (e : V ↪ W) '' G.clique_set n
| 0 := by simp_rw [clique_set_zero, set.image_singleton, map_empty]
| 1 := by { ext, simp only [e.exists_congr_left, equiv.coe_eq_to_embedding, clique_set_one,
    set.mem_range, set.mem_image, exists_exists_eq_and, map_singleton, equiv.to_embedding_apply,
    equiv.apply_symm_apply] }
| (n + 2) := clique_set_map (by norm_num) _ _

@[simp] lemma clique_finset_map' [fintype V] [fintype W] [decidable_eq V] [decidable_eq W]
  (G : simple_graph V) [decidable_rel G.adj] (e : V ≃ W) (n : ℕ) :
  (G.map (e : V ↪ W)).clique_finset n = (G.clique_finset n).map ⟨map e, finset.map_injective _⟩ :=
coe_injective $
  by simp_rw [coe_clique_finset, clique_set_map', coe_map, coe_clique_finset, embedding.coe_fn_mk]

end simple_graph

section
variables {α β : Type*}

/-- Equivalent types have equivalent simple graphs. -/
@[simps] protected def equiv.simple_graph (e : α ≃ β) : simple_graph α ≃ simple_graph β :=
{ to_fun := simple_graph.comap e.symm,
  inv_fun := simple_graph.comap e,
  left_inv := λ _, by simp,
  right_inv := λ _, by simp }

@[simp] lemma equiv.symm_simple_graph (e : α ≃ β) : e.simple_graph.symm = e.symm.simple_graph := rfl

end

open finset fintype (card) nat simple_graph sum3
open_locale pointwise

variables {α β : Type*}

/-! ### The Ruzsa-Szemerédi property -/

namespace simple_graph
variables [decidable_eq α] [decidable_eq β] {G H : simple_graph α}

/-- A graph has edge-disjoint triangles if each edge belongs to at most one triangle. -/
def edge_disjoint_triangles (G : simple_graph α) : Prop :=
(G.clique_set 3).pairwise $ λ x y, (x ∩ y).card ≤ 1

/-- A graph is Ruzsa-Szemerédi if each edge belongs to exactly one triangle. -/
def ruzsa_szemeredi (G : simple_graph α) : Prop :=
G.edge_disjoint_triangles ∧ ∀ ⦃x y⦄, G.adj x y → ∃ s, G.is_n_clique 3 s ∧ x ∈ s ∧ y ∈ s

protected lemma ruzsa_szemeredi.edge_disjoint_triangles :
  G.ruzsa_szemeredi → G.edge_disjoint_triangles :=
and.left

lemma edge_disjoint_triangles.mono (h : G ≤ H) (hH : H.edge_disjoint_triangles) :
  G.edge_disjoint_triangles :=
hH.mono $ clique_set_mono h

@[simp] lemma edge_disjoint_triangles_bot : (⊥ : simple_graph α).edge_disjoint_triangles :=
by simp [edge_disjoint_triangles]

@[simp] lemma ruzsa_szemeredi_bot : (⊥ : simple_graph α).ruzsa_szemeredi :=
by simp [ruzsa_szemeredi]

lemma edge_disjoint_triangles.map (f : α ↪ β) (hG : G.edge_disjoint_triangles) :
  (G.map f).edge_disjoint_triangles :=
begin
  rw [edge_disjoint_triangles, clique_set_map (bit1_lt_bit1.2 zero_lt_one),
    ((finset.map_injective f).inj_on _).pairwise_image],
  rintro s hs t ht,
  dsimp [function.on_fun],
  rw [←map_inter, card_map],
  exact hG hs ht,
end

lemma ruzsa_szemeredi.map (f : α ↪ β) (hG : G.ruzsa_szemeredi) : (G.map f).ruzsa_szemeredi :=
begin
  refine ⟨hG.1.map _, _⟩,
  rintro _ _ ⟨a, b, h, rfl, rfl⟩,
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h,
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩,
end

lemma ruzsa_szemeredi_comap {G : simple_graph β} {e : α ≃ β} :
  (G.comap e).ruzsa_szemeredi ↔ G.ruzsa_szemeredi :=
begin
  refine ⟨λ h, _, _⟩,
  { rw [←comap_map_eq (e.symm : β ↪ α) G, equiv.coe_coe, comap_symm, map_symm],
    exact h.map _ },
  { rw ←map_symm,
    exact ruzsa_szemeredi.map _ }
end

/-- Whether a given finite graph has edge-disjoint triangles is decidable. -/
instance [fintype α] (G : simple_graph α) [decidable_rel G.adj] :
  decidable G.edge_disjoint_triangles :=
decidable_of_iff ((G.clique_finset 3 : set (finset α)).pairwise $ λ x y, (x ∩ y).card ≤ 1) $
  by { rw coe_clique_finset, refl }

/-- Whether a given finite graph is Ruzsa-Szemerédi is decidable. -/
instance [fintype α] (G : simple_graph α) [decidable_rel G.adj] : decidable G.ruzsa_szemeredi :=
and.decidable

variables (α) [fintype α] [fintype β]
include α

/-- The Ruzsa-Szemerédi number of a fintype is the cardinality of its biggest Ruzsa-Szemerédi simple
graph. -/
noncomputable def ruzsa_szemeredi_number : ℕ :=
by classical; exact nat.find_greatest
  (λ m, ∃ G : simple_graph α, (G.clique_finset 3).card = m ∧ G.ruzsa_szemeredi) (2 ^ card α)

omit α

lemma ruzsa_szemeredi_number_le : ruzsa_szemeredi_number α ≤ 2 ^ card α := nat.find_greatest_le _

lemma ruzsa_szemeredi_number_spec :
  ∃ G : simple_graph α, (G.clique_finset 3).card = ruzsa_szemeredi_number α ∧ G.ruzsa_szemeredi :=
@nat.find_greatest_spec _
  (λ m, ∃ G : simple_graph α, (G.clique_finset 3).card = m ∧ G.ruzsa_szemeredi) _ _ (nat.zero_le _)
  ⟨⊥, by simp, ruzsa_szemeredi_bot⟩

variables {α} {n : ℕ}

lemma ruzsa_szemeredi.le_ruzsa_szemeredi_number (hG : G.ruzsa_szemeredi) :
  (G.clique_finset 3).card ≤ ruzsa_szemeredi_number α :=
le_find_greatest (by { rw ←fintype.card_finset, exact finset.card_le_univ _ }) ⟨G, rfl, hG⟩

lemma ruzsa_szemeredi_number_mono (f : α ↪ β) :
  ruzsa_szemeredi_number α ≤ ruzsa_szemeredi_number β :=
begin
  refine find_greatest_mono _ (pow_le_pow one_le_two $ fintype.card_le_of_embedding f),
  rintro n ⟨G, rfl, hG⟩,
  refine ⟨G.map f, _, hG.map _⟩,
  rw [←card_map ⟨map f, finset.map_injective _⟩, ←clique_finset_map G f],
  congr',
  dec_trivial,
end

lemma ruzsa_szemeredi_number_congr (e : α ≃ β) :
  ruzsa_szemeredi_number α = ruzsa_szemeredi_number β :=
(ruzsa_szemeredi_number_mono (e : α ↪ β)).antisymm $ ruzsa_szemeredi_number_mono e.symm

noncomputable def ruzsa_szemeredi_number_nat (n : ℕ) : ℕ := ruzsa_szemeredi_number (fin n)

lemma ruzsa_szemeredi_number_eq : ruzsa_szemeredi_number α = ruzsa_szemeredi_number_nat (card α) :=
ruzsa_szemeredi_number_congr $ fintype.equiv_fin _

lemma ruzsa_szemeredi_number_nat_mono : monotone ruzsa_szemeredi_number_nat :=
λ m n h, ruzsa_szemeredi_number_mono (fin.cast_le h).to_embedding

end simple_graph

open simple_graph

/-! ### The Ruzsa-Szemerédi construction -/

namespace ruzsa_szemeredi
section vertices
variables [has_mul α]

/-- The vertices of the Ruzsa-Szemerédi graph. -/
@[to_additive "The vertices of the Ruzsa-Szemerédi graph."]
abbreviation mul_vertices (s : set α) : Type* := s ⊕ ↥(s * s) ⊕ ↥(s * s * s)

instance (a : α) : inhabited (mul_vertices ({a} : set α)) := ⟨in₀ ⟨a, set.mem_singleton _⟩⟩

open finset fintype

@[to_additive] instance [decidable_eq α] (s : finset α) : fintype (mul_vertices (s : set α)) :=
of_equiv (s ⊕ ↥(s * s) ⊕ ↥(s * s * s)) $
  by refine (equiv.refl _).sum_congr (equiv.sum_congr _ _); { simp_rw ←coe_mul, refl }

@[simp, to_additive]
lemma card_mul_vertices [decidable_eq α] (s : finset α) :
  card (mul_vertices (s : set α)) = s.card + (s * s).card + (s * s * s).card :=
begin
  have e : mul_vertices (s : set α) ≃ (s ⊕ ↥(s * s) ⊕ ↥(s * s * s)),
  { refine (equiv.refl _).sum_congr (equiv.sum_congr _ _); { simp_rw ←coe_mul, refl } },
  simp_rw [fintype.card_congr e, card_sum, card_coe, add_assoc],
end

end vertices

section edges

/-- The edges of the Ruzsa-Szemerédi graph. -/
@[mk_iff] inductive add_edges [add_monoid α] (s : set α) : add_vertices s → add_vertices s → Prop
| in₀₁ {a : s}     {b} : ↑b ∈ (a : α) +ᵥ s               → add_edges (in₀ a) (in₁ b)
| in₁₀ {a : s}     {b} : ↑b ∈ (a : α) +ᵥ s               → add_edges (in₁ b) (in₀ a)
| in₁₂ {b : s + s} {c} : ↑c ∈ (b : α) +ᵥ s               → add_edges (in₁ b) (in₂ c)
| in₂₁ {b : s + s} {c} : ↑c ∈ (b : α) +ᵥ s               → add_edges (in₂ c) (in₁ b)
| in₂₀ {a : s}     {c} : ↑c ∈ (a : α) +ᵥ s.image ((•) 2) → add_edges (in₂ c) (in₀ a)
| in₀₂ {a : s}     {c} : ↑c ∈ (a : α) +ᵥ s.image ((•) 2) → add_edges (in₀ a) (in₂ c)

variables [monoid α] {s : set α} {a : s} {b : ↥(s * s)} {c : ↥(s * s * s)}

/-- The edges of the Ruzsa-Szemerédi graph. -/
@[to_additive, mk_iff] inductive mul_edges (s : set α) : mul_vertices s → mul_vertices s → Prop
| in₀₁ {a : s}     {b} : ↑b ∈ (a : α) • s            → mul_edges (in₀ a) (in₁ b)
| in₁₀ {a : s}     {b} : ↑b ∈ (a : α) • s            → mul_edges (in₁ b) (in₀ a)
| in₁₂ {b : s * s} {c} : ↑c ∈ (b : α) • s            → mul_edges (in₁ b) (in₂ c)
| in₂₁ {b : s * s} {c} : ↑c ∈ (b : α) • s            → mul_edges (in₂ c) (in₁ b)
| in₂₀ {a : s}     {c} : ↑c ∈ (a : α) • s.image (^2) → mul_edges (in₂ c) (in₀ a)
| in₀₂ {a : s}     {c} : ↑c ∈ (a : α) • s.image (^2) → mul_edges (in₀ a) (in₂ c)

@[to_additive] noncomputable instance : decidable_rel (mul_edges s) := classical.dec_rel _

open mul_edges

@[to_additive] lemma mul_edges_symm : symmetric (mul_edges s) :=
λ x y h, by cases h; constructor; assumption

@[to_additive] lemma mul_edges_irrefl : ∀ x, ¬ mul_edges s x x.

@[simp, to_additive] lemma mul_edges_inl_inm_iff : mul_edges s (in₀ a) (in₁ b) ↔ ↑b ∈ (a : α) • s :=
⟨by { rintro ⟨⟩, assumption }, in₀₁⟩

@[simp, to_additive] lemma mul_edges_inm_inr_iff : mul_edges s (in₁ b) (in₂ c) ↔ ↑c ∈ (b : α) • s :=
⟨by { rintro ⟨⟩, assumption }, in₁₂⟩

@[simp, to_additive] lemma mul_edges_inr_inl_iff :
  mul_edges s (in₂ c) (in₀ a) ↔ ↑c ∈ (a : α) • s.image (^2) :=
⟨by { rintro ⟨⟩, assumption }, in₂₀⟩

/-- The Ruzsa-Szemerédi graph associated to the set `s`. -/
@[to_additive "The Ruzsa-Szemerédi graph associated to the set `s`.", simps]
def mul_graph (s : set α) : simple_graph (mul_vertices s) :=
⟨mul_edges s, mul_edges_symm, mul_edges_irrefl⟩

@[to_additive] noncomputable instance mul_graph.decidable : decidable_rel (mul_graph s).adj :=
mul_edges.decidable_rel

/-- Throwaway tactic. -/
meta def sets_simp : tactic unit :=
`[ext] >> `[simp only [finset.mem_insert, finset.mem_singleton]] >> `[try {tauto}]

@[to_additive] lemma mul_graph_triple [decidable_eq α] :
  ∀ x y z, (mul_graph s).adj x y → (mul_graph s).adj y z → (mul_graph s).adj z x →
    ∃ a b c, ({in₀ a, in₁ b, in₂ c} : finset (mul_vertices s)) = {x, y, z} ∧
      (mul_graph s).adj (in₀ a) (in₁ b) ∧
      (mul_graph s).adj (in₁ b) (in₂ c) ∧
      (mul_graph s).adj (in₂ c) (in₀ a)
| _ _ _ (in₀₁ h₁) (in₁₂ h₂) (in₂₀ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₁, in₁₂ h₂, in₂₀ h₃⟩
| _ _ _ (in₁₀ h₁) (in₀₂ h₂) (in₂₁ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₁, in₁₂ h₃, in₂₀ h₂⟩
| _ _ _ (in₁₂ h₁) (in₂₀ h₂) (in₀₁ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₃, in₁₂ h₁, in₂₀ h₂⟩
| _ _ _ (in₂₁ h₁) (in₁₀ h₂) (in₀₂ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₂, in₁₂ h₁, in₂₀ h₃⟩
| _ _ _ (in₂₀ h₁) (in₀₁ h₂) (in₁₂ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₂, in₁₂ h₃, in₂₀ h₁⟩
| _ _ _ (in₀₂ h₁) (in₂₁ h₂) (in₁₀ h₃) := ⟨_, _, _, by sets_simp, in₀₁ h₃, in₁₂ h₂, in₂₀ h₁⟩

end edges

section cancel_monoid
open mul_edges
open_locale classical

@[to_additive] lemma mul_triangle_iff [cancel_monoid α] {s : set α} {a b c} :
  (mul_graph s).adj (in₀ a) (in₁ b) ∧ (mul_graph s).adj (in₁ b) (in₂ c) ∧
    (mul_graph s).adj (in₂ c) (in₀ a) ↔
      ∃ d e f ∈ s, (a : α) * d = b ∧ (a : α) * e ^ 2 = c ∧ (b : α) * f = c ∧ (d : α) * f = e * e :=
begin
  simp only [mul_graph_adj, mul_edges_inr_inl_iff, mul_edges_inm_inr_iff, mul_edges_inl_inm_iff],
  split,
  { rintro ⟨⟨d, hd, hab⟩, ⟨f, hf, hbc⟩, _, ⟨e, he, rfl⟩, hca⟩,
    refine ⟨_, hd, _, he, _, hf, hab, hca, hbc, _⟩,
    simp_rw [←hca, ←hab, smul_eq_mul, mul_assoc, pow_two] at hbc,
    exact mul_left_cancel hbc },
  { rintro ⟨d, hd, e, he, f, hf, hab, hca, hbc, -⟩,
    exact ⟨⟨d, hd, hab⟩, ⟨f, hf, hbc⟩, _, ⟨e, he, rfl⟩, hca⟩ }
end

end cancel_monoid

section set
variables {s : set ℕ}

open add_edges set

lemma triangle_iff (h : add_salem_spencer s) {t : finset (add_vertices s)} :
  (add_graph s).is_n_clique 3 t ↔
    ∃ a d (hd : d ∈ s), t = {in₀ a, in₁ ⟨a + d, add_mem_add a.2 hd⟩, in₂ ⟨a + 2 * d,
      by { rw [two_mul, add_assoc], exact add_mem_add a.2 (add_mem_add hd hd) }⟩} :=
begin
  refine is_3_clique_iff.trans ⟨_, _⟩,
  { rintro ⟨a', b', c', hab, hac, hbc, rfl⟩,
    obtain ⟨a, b, c, habc, hab, hbc, hca⟩ := add_graph_triple _ _ _ hab hbc hac.symm,
    obtain ⟨d, hd, e, he, f, hf, hab, hca, hbc, hdef⟩ := add_triangle_iff.1 ⟨hab, hbc, hca⟩,
    rw ←h hd hf he hdef at hbc,
    rw [←add_salem_spencer_iff_eq_right.1 h hd hf he hdef, smul_eq_mul] at hca,
    exact ⟨a, d, hd, habc.symm.trans $ by simp_rw [hab, hca, subtype.coe_eta]⟩ },
  rintro ⟨a, d, hd, rfl⟩,
  exact ⟨in₀ a,
         in₁ ⟨a + d, add_mem_add a.2 hd⟩,
         in₂ ⟨a + 2 * d, by { rw [two_mul, add_assoc], exact add_mem_add a.2 (add_mem_add hd hd) }⟩,
    in₀₁ $ vadd_mem_vadd_set hd,
    in₀₂ $ vadd_mem_vadd_set $ mem_image_of_mem _ hd,
    in₁₂ $ by { simp_rw [two_mul, ←add_assoc], exact vadd_mem_vadd_set hd }, rfl⟩,
end

protected lemma _root_.add_salem_spencer.edge_disjoint_triangles (hs : add_salem_spencer s) :
  (add_graph s).edge_disjoint_triangles :=
begin
  refine λ t ht u hu htu, not_lt.1 (λ h, htu _),
  rw [mem_clique_set_iff, triangle_iff hs] at ht hu,
  obtain ⟨a, ha, b, hb, hab⟩ := finset.one_lt_card.1 h,
  obtain ⟨c, e, he, rfl⟩ := ht,
  obtain ⟨d, f, hf, rfl⟩ := hu,
  simp only [finset.mem_inter, finset.mem_insert, finset.mem_singleton, in₀, in₁, in₂] at ha hb,
  obtain a | a | a := a; obtain b | b | b := b; simp only [or_false, false_or] at ha hb;
    obtain ⟨⟨rfl, ha⟩, rfl, hb⟩ := ⟨ha, hb⟩,
  { cases hab rfl },
  { rw [subtype.mk_eq_mk, ha, add_right_inj] at hb,
    simp_rw [ha, hb] },
  { rw [subtype.mk_eq_mk, ha, add_right_inj, mul_right_inj' (@two_ne_zero ℕ _ _)] at hb,
    simp_rw [ha, hb] },
  { rw [subtype.mk_eq_mk, hb, add_right_inj] at ha,
    simp_rw [ha, hb] },
  { rw ha.trans hb.symm at hab,
    cases hab rfl },
  { simp only [subtype.mk_eq_mk, two_mul, ←add_assoc] at ha hb,
    rw [ha, add_right_inj] at hb,
    rw [hb, add_left_inj, subtype.coe_inj] at ha,
    simp_rw [ha, hb] },
  { rw [subtype.mk_eq_mk, hb, add_right_inj, mul_right_inj' (@two_ne_zero ℕ _ _)] at ha,
    simp_rw [ha, hb] },
  { simp only [subtype.mk_eq_mk, two_mul, ←add_assoc] at ha hb,
    rw [hb, add_right_inj] at ha,
    rw [ha, add_left_inj, subtype.coe_inj] at hb,
    simp_rw [ha, hb] },
  { rw ha.trans hb.symm at hab,
    cases hab rfl }
end

protected lemma _root_.add_salem_spencer.ruzsa_szemeredi (hs : add_salem_spencer s) :
  (add_graph s).ruzsa_szemeredi :=
⟨hs.edge_disjoint_triangles, sorry⟩

end set

variables {s : finset ℕ}

def thing (s : finset ℕ) :
  (add_graph (s : set ℕ)).dart ≃ s × s ⊕ (s + s : finset ℕ) × s ⊕ (s + s + s : finset ℕ) × s :=
{ to_fun := begin
    rintro ⟨⟨a | b | c, a | b | c⟩, h⟩,
    { simpa only [add_edges_iff, in₁, in₂, add_graph_adj, and_false, exists_false, false_and,
      or_self] using h },
    sorry,sorry,sorry,sorry,sorry,sorry,sorry,sorry,
  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

@[simp] lemma card_edge_finset : (add_graph (s : set ℕ)).edge_finset.card = 3 * s.card :=
begin
  refine mul_right_injective zero_lt_two ((dart_card_eq_twice_card_edges _).symm.trans _),
  rw fintype.card_congr (thing s),
  sorry,
end

open real

variables (α) [fintype α] [decidable_eq α]

lemma roth_number_nat_le_ruzsa_szemeredi_number :
  card α * roth_number_nat (card α / 6) ≤ ruzsa_szemeredi_number α :=
begin
  classical,
  obtain ⟨s, hα, hcard, hs⟩ := roth_number_nat_spec (card α / 6),
  rw ←hcard,
  transitivity ((add_graph (s : set ℕ)).clique_finset 3).card,
  sorry,
  transitivity,
  exact hs.ruzsa_szemeredi.le_ruzsa_szemeredi_number,
  simp_rw ruzsa_szemeredi_number_eq,
  refine ruzsa_szemeredi_number_nat_mono _,
  rw card_add_vertices,
  have aux : ∀ {s t m n}, s ⊆ range m → t ⊆ range n → s + t ⊆ range (m + n) := λ s t m n hs ht,
    (add_subset_add hs ht).trans (range_add_range_subset.trans $ range_mono tsub_le_self),
  refine (add_le_add_three (card_le_of_subset hα) (card_le_of_subset $ aux hα hα) $
    card_le_of_subset $ aux (aux hα hα) hα).trans _,
  simp_rw card_range,
  refine (div_mul_le_self _ 6).trans_eq' _,
  ring_nf,
end

lemma roth_number_nat_le_ruzsa_szemeredi_number_nat (n : ℕ) :
  n * roth_number_nat (n / 6) ≤ ruzsa_szemeredi_number_nat n :=
sorry

lemma ruzsa_szemeredi_number_lower_bound :
  (card α : ℝ)^2 / 6 * exp (-4 * sqrt (log (card α / 6))) ≤ ruzsa_szemeredi_number α :=
sorry

lemma ruzsa_szemeredi_number_nat_lower_bound (n : ℕ) :
  (n : ℝ)^2 / 6 * exp (-4 * sqrt (log (n / 6))) ≤ ruzsa_szemeredi_number_nat n :=
sorry


end ruzsa_szemeredi
