/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.basic
import order.partition.finpartition

/-!
# Edge density and uniform graphs

This file defines the number and density of edges of a relation/graph and define uniformity in
graphs.

Two finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if the density of edges between
any pair of big subsets of `s` and `t` is within `ε` of the density of edges between `s` and `t`.
This captures the idea of the edges between `s` and `t` being randomly distributed.

## Main declarations

Between two finsets of vertices,
* `relation.edge_finset`: Finset of edges of a relation.
* `relation.edge_count`: Number of edges of a relation.
* `relation.edge_density`: Edge density of a relation.
* `simple_graph.edge_count`: Number of edges of a graph.
* `simple_graph.edge_density`: Edge density of a graph.

* `simple_graph.is_uniform`: `G.is_uniform ε s t` means that `s` and `t` are `ε`-uniform in `G`.
-/

open finset

variables {ι κ α β 𝕜 : Type*}

/-! ### Density of a relation -/

namespace relation
section asymmetric
variables (r : α → β → Prop) [Π a, decidable_pred (r a)] {s s₁ s₂ : finset α} {t t₁ t₂ : finset β}
  {a : α} {b : β}

/-- Finset of edges of a relation between two finsets of vertices. -/
def edge_finset (s : finset α) (t : finset β) : finset (α × β) :=
(s.product t).filter $ λ e, r e.1 e.2

/-- Number of edges of a relation between two finsets of vertices. -/
def edge_count (s : finset α) (t : finset β) : ℕ := (edge_finset r s t).card

/-- Edge density of a relation between two finsets of vertices. -/
def edge_density (s : finset α) (t : finset β) : ℚ := edge_count r s t / (s.card * t.card)

variables {r}

lemma mem_edge_finset_iff {x : α × β} : x ∈ edge_finset r s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ r x.1 x.2 :=
by simp only [edge_finset, and_assoc, mem_filter, finset.mem_product]

lemma mk_mem_edge_finset_iff : (a, b) ∈ edge_finset r s t ↔ a ∈ s ∧ b ∈ t ∧ r a b :=
mem_edge_finset_iff

@[simp] lemma edge_finset_empty_left (t : finset β) : edge_finset r ∅ t = ∅ :=
by rw [edge_finset, finset.empty_product, filter_empty]

lemma edge_finset_mono (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) : edge_finset r s₂ t₂ ⊆ edge_finset r s₁ t₁ :=
λ x, by { simp_rw mem_edge_finset_iff, exact λ h, ⟨hs h.1, ht h.2.1, h.2.2⟩ }

variables (r)

lemma card_edge_finset_compl (s : finset α) (t : finset β) :
  (edge_finset r s t).card + (edge_finset (λ x y, ¬r x y) s t).card = s.card * t.card :=
begin
  classical,
  rw [←card_product, edge_finset, edge_finset, ←card_union_eq, filter_union_filter_neg_eq],
  convert disjoint_filter.2 (λ x _, not_not.2),
end

section decidable_eq
variables [decidable_eq α] [decidable_eq β]

lemma edge_finset_disjoint_left {s s' : finset α} (hs : disjoint s s') (t : finset β) :
  disjoint (edge_finset r s t) (edge_finset r s' t) :=
begin
  rintro x hx,
  rw [inf_eq_inter, mem_inter, mem_edge_finset_iff, mem_edge_finset_iff] at hx,
  exact hs (mem_inter.2 ⟨hx.1.1, hx.2.1⟩),
end

lemma edge_finset_disjoint_right (s : finset α) {t t' : finset β} (ht : disjoint t t') :
  disjoint (edge_finset r s t) (edge_finset r s t') :=
begin
  rintro x hx,
  rw [inf_eq_inter, mem_inter, mem_edge_finset_iff, mem_edge_finset_iff] at hx,
  exact ht (mem_inter.2 ⟨hx.1.2.1, hx.2.2.1⟩),
end

lemma edge_finset_bUnion_left (s : finset ι) (t : finset β) (f : ι → finset α) :
  edge_finset r (s.bUnion f) t = s.bUnion (λ a, edge_finset r (f a) t) :=
ext $ λ a, by simp only [mem_bUnion, mem_edge_finset_iff, exists_and_distrib_right]

lemma edge_finset_bUnion_right (s : finset α) (t : finset ι) (f : ι → finset β) :
  edge_finset r s (t.bUnion f) = t.bUnion (λ b, edge_finset r s (f b)) :=
ext $ λ a, by simp only [mem_edge_finset_iff, mem_bUnion, ←exists_and_distrib_left,
  ←exists_and_distrib_right]

lemma edge_finset_bUnion (s : finset ι) (t : finset κ) (f : ι → finset α) (g : κ → finset β) :
  edge_finset r (s.bUnion f) (t.bUnion g) =
    (s.product t).bUnion (λ ab, edge_finset r (f ab.1) (g ab.2)) :=
by simp_rw [product_bUnion, edge_finset_bUnion_left, edge_finset_bUnion_right]

end decidable_eq

lemma edge_count_le_mul (s : finset α) (t : finset β) : edge_count r s t ≤ s.card * t.card :=
begin
  rw [edge_count, edge_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

lemma edge_density_nonneg (s : finset α) (t : finset β) : 0 ≤ edge_density r s t :=
by { apply div_nonneg; exact_mod_cast nat.zero_le _ }

lemma edge_density_le_one (s : finset α) (t : finset β) : edge_density r s t ≤ 1 :=
div_le_one_of_le (by exact_mod_cast (edge_count_le_mul _ _ _)) (by exact_mod_cast (nat.zero_le _))

lemma edge_density_compl (hs : s.nonempty) (ht : t.nonempty) :
  edge_density r s t + edge_density (λ x y, ¬r x y) s t = 1 :=
begin
  rw [edge_density, edge_density, div_add_div_same, div_eq_one_iff_eq],
  { exact_mod_cast card_edge_finset_compl r s t },
  { exact_mod_cast (mul_pos hs.card_pos ht.card_pos).ne' },
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

@[simp] lemma swap_mem_edge_finset_iff {x : α × α} :
  x.swap ∈ edge_finset r s t ↔ x ∈ edge_finset r t s :=
by { rw [mem_edge_finset_iff, mem_edge_finset_iff, hr.iff], exact and.left_comm }

lemma mk_mem_edge_finset_comm : (a, b) ∈ edge_finset r s t ↔ (b, a) ∈ edge_finset r t s :=
@swap_mem_edge_finset_iff _ _ _ _ _ hr (b, a)

lemma edge_count_comm (s t : finset α) : edge_count r s t = edge_count r t s :=
finset.card_congr (λ (x : α × α) _, x.swap) (λ x, (swap_mem_edge_finset_iff hr).2)
  (λ _ _ _ _ h, prod.swap_injective h)
  (λ x h, ⟨x.swap, (swap_mem_edge_finset_iff hr).2 h, x.swap_swap⟩)

lemma edge_density_comm (s t : finset α) : edge_density r s t = edge_density r t s :=
by rw [edge_density, mul_comm, edge_count_comm hr, edge_density]

end symmetric
end relation

open relation

/-! ### Density of a graph -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj]

/-- Number of edges of a graph between two finsets of vertices. -/
def edge_count (s t : finset α) : ℕ := edge_count G.adj s t

/-- Density of edges of a graph between two finsets of vertices. -/
def edge_density : finset α → finset α → ℚ := edge_density G.adj

lemma edge_density_eq_edge_count_div_card (s t : finset α) :
  G.edge_density s t = G.edge_count s t/(s.card * t.card) := rfl

lemma edge_density_comm (s t : finset α) : G.edge_density s t = G.edge_density t s :=
edge_density_comm G.symm s t

lemma edge_density_nonneg (s t : finset α) : 0 ≤ G.edge_density s t := edge_density_nonneg _ s t
lemma edge_density_le_one (s t : finset α) : G.edge_density s t ≤ 1 := edge_density_le_one _ s t

/-! ###  Uniform graphs -/

variables [linear_ordered_field 𝕜] (ε : 𝕜) {s t : finset α} {a b : α}

/-- A pair of finsets of vertices is `ε`-uniform iff their edge density is close to the density of
any big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (s t : finset α) : Prop :=
∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (s.card : 𝕜) * ε ≤ s'.card → (t.card : 𝕜) * ε ≤ t'.card →
  |(edge_density G s' t' : 𝕜) - (edge_density G s t : 𝕜)| < ε

variables {G ε}

/-- If the pair `(s, t)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform.mono {ε' : 𝕜} (hε : is_uniform G ε s t) (h : ε ≤ ε') : is_uniform G ε' s t :=
λ s' hs' t' ht' hs ht, by refine (hε hs' ht' (le_trans _ hs) (le_trans _ ht)).trans_le h;
  exact mul_le_mul_of_nonneg_left h (nat.cast_nonneg _)

lemma is_uniform.symm : symmetric (is_uniform G ε) :=
λ s t h t' ht' s' hs' ht hs,
  by { rw [edge_density_comm _ t', edge_density_comm _ t], exact h hs' ht' hs ht }

variables (G)

lemma is_uniform_comm : is_uniform G ε s t ↔ is_uniform G ε t s := ⟨λ h, h.symm, λ h, h.symm⟩

lemma is_uniform_singleton (hε : 0 < ε) : G.is_uniform ε {a} {b} :=
begin
  intros s' hs' t' ht' hs ht,
  rw [card_singleton, nat.cast_one, one_mul] at hs ht,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hs',
  { exact (hε.not_le hs).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 ht',
  { exact (hε.not_le ht).elim },
  { rwa [sub_self, abs_zero] }
end

lemma not_is_uniform_zero : ¬ G.is_uniform (0 : 𝕜) s t :=
λ h, (abs_nonneg _).not_lt $ h (empty_subset _) (empty_subset _) (by simp) (by simp)

lemma is_uniform_of_one_le (hε : 1 ≤ ε) : G.is_uniform ε s t :=
begin
  intros s' hs' t' ht' hs ht,
  have h : ∀ n : ℕ, (n : 𝕜) ≤ n * ε := λ n, le_mul_of_one_le_right n.cast_nonneg hε,
  rw [eq_of_subset_of_card_le hs' (nat.cast_le.1 ((h _).trans hs)),
    eq_of_subset_of_card_le ht' (nat.cast_le.1 ((h _).trans ht)), sub_self, abs_zero],
  exact zero_lt_one.trans_le hε,
end

end simple_graph
