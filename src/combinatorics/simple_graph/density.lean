/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import order.partition.finpartition

/-!
# Edge density

This file defines the number and density of edges of a relation/graph.

## Main declarations

Between two finsets of vertices,
* `rel.interedges`: Finset of edges of a relation.
* `rel.edge_density`: Edge density of a relation.
* `simple_graph.interedges`: Finset of edges of a graph.
* `simple_graph.edge_density`: Edge density of a graph.
-/

open finset

variables {ι κ α β : Type*}

/-! ### Density of a relation -/

namespace rel
section asymmetric
variables (r : α → β → Prop) [Π a, decidable_pred (r a)] {s s₁ s₂ : finset α} {t t₁ t₂ : finset β}
  {a : α} {b : β}

/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s : finset α) (t : finset β) : finset (α × β) :=
(s.product t).filter $ λ e, r e.1 e.2

/-- Edge density of a relation between two finsets of vertices. -/
def edge_density (s : finset α) (t : finset β) : ℚ := (interedges r s t).card / (s.card * t.card)

variables {r}

lemma mem_interedges_iff {x : α × β} : x ∈ interedges r s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ r x.1 x.2 :=
by simp only [interedges, and_assoc, mem_filter, finset.mem_product]

lemma mk_mem_interedges_iff : (a, b) ∈ interedges r s t ↔ a ∈ s ∧ b ∈ t ∧ r a b :=
mem_interedges_iff

@[simp] lemma interedges_empty_left (t : finset β) : interedges r ∅ t = ∅ :=
by rw [interedges, finset.empty_product, filter_empty]

lemma interedges_mono (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) : interedges r s₂ t₂ ⊆ interedges r s₁ t₁ :=
λ x, by { simp_rw mem_interedges_iff, exact λ h, ⟨hs h.1, ht h.2.1, h.2.2⟩ }

variables (r)

lemma card_interedges_add_card_interedges_compl (s : finset α) (t : finset β) :
  (interedges r s t).card + (interedges (λ x y, ¬r x y) s t).card = s.card * t.card :=
begin
  classical,
  rw [←card_product, interedges, interedges, ←card_union_eq, filter_union_filter_neg_eq],
  convert disjoint_filter.2 (λ x _, not_not.2),
end

section decidable_eq
variables [decidable_eq α] [decidable_eq β]

lemma interedges_disjoint_left {s s' : finset α} (hs : disjoint s s') (t : finset β) :
  disjoint (interedges r s t) (interedges r s' t) :=
begin
  rintro x hx,
  rw [inf_eq_inter, mem_inter, mem_interedges_iff, mem_interedges_iff] at hx,
  exact hs (mem_inter.2 ⟨hx.1.1, hx.2.1⟩),
end

lemma interedges_disjoint_right (s : finset α) {t t' : finset β} (ht : disjoint t t') :
  disjoint (interedges r s t) (interedges r s t') :=
begin
  rintro x hx,
  rw [inf_eq_inter, mem_inter, mem_interedges_iff, mem_interedges_iff] at hx,
  exact ht (mem_inter.2 ⟨hx.1.2.1, hx.2.2.1⟩),
end

lemma interedges_bUnion_left (s : finset ι) (t : finset β) (f : ι → finset α) :
  interedges r (s.bUnion f) t = s.bUnion (λ a, interedges r (f a) t) :=
ext $ λ a, by simp only [mem_bUnion, mem_interedges_iff, exists_and_distrib_right]

lemma interedges_bUnion_right (s : finset α) (t : finset ι) (f : ι → finset β) :
  interedges r s (t.bUnion f) = t.bUnion (λ b, interedges r s (f b)) :=
ext $ λ a, by simp only [mem_interedges_iff, mem_bUnion, ←exists_and_distrib_left,
  ←exists_and_distrib_right]

lemma interedges_bUnion (s : finset ι) (t : finset κ) (f : ι → finset α) (g : κ → finset β) :
  interedges r (s.bUnion f) (t.bUnion g) =
    (s.product t).bUnion (λ ab, interedges r (f ab.1) (g ab.2)) :=
by simp_rw [product_bUnion, interedges_bUnion_left, interedges_bUnion_right]

end decidable_eq

lemma card_interedges_le_mul (s : finset α) (t : finset β) :
  (interedges r s t).card ≤ s.card * t.card :=
(card_filter_le _ _).trans (card_product _ _).le

lemma edge_density_nonneg (s : finset α) (t : finset β) : 0 ≤ edge_density r s t :=
by { apply div_nonneg; exact_mod_cast nat.zero_le _ }

lemma edge_density_le_one (s : finset α) (t : finset β) : edge_density r s t ≤ 1 :=
div_le_one_of_le (by exact_mod_cast (card_interedges_le_mul _ _ _)) $
  by exact_mod_cast (nat.zero_le _)

lemma edge_density_add_edge_density_compl (hs : s.nonempty) (ht : t.nonempty) :
  edge_density r s t + edge_density (λ x y, ¬r x y) s t = 1 :=
begin
  rw [edge_density, edge_density, div_add_div_same, div_eq_one_iff_eq],
  { exact_mod_cast card_interedges_add_card_interedges_compl r s t },
  { exact_mod_cast (mul_pos hs.card_pos ht.card_pos).ne' }
end

@[simp] lemma edge_density_empty_left (t : finset β) : edge_density r ∅ t = 0 :=
by rw [edge_density, finset.card_empty, nat.cast_zero, zero_mul, div_zero]

@[simp] lemma edge_density_empty_right (s : finset α) : edge_density r s ∅ = 0 :=
by rw [edge_density, finset.card_empty, nat.cast_zero, mul_zero, div_zero]

end asymmetric

section symmetric
variables (r : α → α → Prop) [decidable_rel r] {s s₁ s₂ t t₁ t₂ : finset α} {a b : α}
variables {r} (hr : symmetric r)
include hr

@[simp] lemma swap_mem_interedges_iff {x : α × α} :
  x.swap ∈ interedges r s t ↔ x ∈ interedges r t s :=
by { rw [mem_interedges_iff, mem_interedges_iff, hr.iff], exact and.left_comm }

lemma mk_mem_interedges_comm : (a, b) ∈ interedges r s t ↔ (b, a) ∈ interedges r t s :=
@swap_mem_interedges_iff _ _ _ _ _ hr (b, a)

lemma card_interedges_comm (s t : finset α) : (interedges r s t).card = (interedges r t s).card :=
finset.card_congr (λ (x : α × α) _, x.swap) (λ x, (swap_mem_interedges_iff hr).2)
  (λ _ _ _ _ h, prod.swap_injective h)
  (λ x h, ⟨x.swap, (swap_mem_interedges_iff hr).2 h, x.swap_swap⟩)

lemma edge_density_comm (s t : finset α) : edge_density r s t = edge_density r t s :=
by rw [edge_density, mul_comm, card_interedges_comm hr, edge_density]

end symmetric
end rel

open rel

/-! ### Density of a graph -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj] {s s₁ s₂ t t₁ t₂ : finset α} {a b : α}

/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s t : finset α) : finset (α × α) := interedges G.adj s t

/-- Density of edges of a graph between two finsets of vertices. -/
def edge_density : finset α → finset α → ℚ := edge_density G.adj

lemma interedges_def (s t : finset α) :
  G.interedges s t = (s.product t).filter (λ e, G.adj e.1 e.2) := rfl

lemma edge_density_def (s t : finset α) :
  G.edge_density s t = (G.interedges s t).card / (s.card * t.card) := rfl

@[simp] lemma card_interedges_div_card (s t : finset α) :
  ((G.interedges s t).card : ℚ) / (s.card * t.card) = G.edge_density s t := rfl

lemma mem_interedges_iff {x : α × α} : x ∈ G.interedges s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ G.adj x.1 x.2 :=
mem_interedges_iff

lemma mk_mem_interedges_iff : (a, b) ∈ G.interedges s t ↔ a ∈ s ∧ b ∈ t ∧ G.adj a b :=
mk_mem_interedges_iff

@[simp] lemma interedges_empty_left (t : finset α) : G.interedges ∅ t = ∅ := interedges_empty_left _

lemma interedges_mono : s₂ ⊆ s₁ → t₂ ⊆ t₁ → G.interedges s₂ t₂ ⊆ G.interedges s₁ t₁ :=
interedges_mono

section decidable_eq
variables [decidable_eq α]

lemma interedges_disjoint_left (hs : disjoint s₁ s₂) (t : finset α) :
  disjoint (G.interedges s₁ t) (G.interedges s₂ t) :=
interedges_disjoint_left _ hs _

lemma interedges_disjoint_right (s : finset α) (ht : disjoint t₁ t₂) :
  disjoint (G.interedges s t₁) (G.interedges s t₂) :=
interedges_disjoint_right _ _ ht

lemma interedges_bUnion_left (s : finset ι) (t : finset α) (f : ι → finset α) :
  G.interedges (s.bUnion f) t = s.bUnion (λ a, G.interedges (f a) t) :=
interedges_bUnion_left _ _ _ _

lemma interedges_bUnion_right (s : finset α) (t : finset ι) (f : ι → finset α) :
  G.interedges s (t.bUnion f) = t.bUnion (λ b, G.interedges s (f b)) :=
interedges_bUnion_right _ _ _ _

lemma interedges_bUnion (s : finset ι) (t : finset κ) (f : ι → finset α) (g : κ → finset α) :
  G.interedges (s.bUnion f) (t.bUnion g) =
    (s.product t).bUnion (λ ab, G.interedges (f ab.1) (g ab.2)) :=
interedges_bUnion _ _ _ _ _

lemma card_interedges_add_card_interedges_compl (h : disjoint s t) :
  (G.interedges s t).card + (Gᶜ.interedges s t).card = s.card * t.card :=
begin
  rw [←card_product, interedges_def, interedges_def],
  have : (s.product t).filter (λ e , Gᶜ.adj e.1 e.2) = (s.product t).filter (λ e , ¬ G.adj e.1 e.2),
  { refine filter_congr (λ x hx, _),
    rw mem_product at hx,
    rw [compl_adj, and_iff_right (h.forall_ne_finset hx.1 hx.2)] },
  rw [this, ←card_union_eq, filter_union_filter_neg_eq],
  exact disjoint_filter.2 (λ x _, not_not.2),
end

lemma edge_density_add_edge_density_compl (hs : s.nonempty) (ht : t.nonempty) (h : disjoint s t) :
  G.edge_density s t + Gᶜ.edge_density s t = 1 :=
begin
  rw [edge_density_def, edge_density_def, div_add_div_same, div_eq_one_iff_eq],
  { exact_mod_cast card_interedges_add_card_interedges_compl _ h },
  { exact_mod_cast (mul_pos hs.card_pos ht.card_pos).ne' }
end

end decidable_eq

lemma card_interedges_le_mul (s t : finset α) : (G.interedges s t).card ≤ s.card * t.card :=
card_interedges_le_mul _ _ _

lemma edge_density_nonneg (s t : finset α) : 0 ≤ G.edge_density s t := edge_density_nonneg _ _ _
lemma edge_density_le_one (s t : finset α) : G.edge_density s t ≤ 1 := edge_density_le_one _ _ _

@[simp] lemma edge_density_empty_left (t : finset α) : G.edge_density ∅ t = 0 :=
edge_density_empty_left _ _

@[simp] lemma edge_density_empty_right (s : finset α) : G.edge_density s ∅ = 0 :=
edge_density_empty_right _ _

@[simp] lemma swap_mem_interedges_iff {x : α × α} :
  x.swap ∈ G.interedges s t ↔ x ∈ G.interedges t s :=
swap_mem_interedges_iff G.symm

lemma mk_mem_interedges_comm : (a, b) ∈ G.interedges s t ↔ (b, a) ∈ G.interedges t s :=
mk_mem_interedges_comm G.symm

lemma edge_density_comm (s t : finset α) : G.edge_density s t = G.edge_density t s :=
edge_density_comm G.symm s t

end simple_graph
