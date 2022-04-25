/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.density
import data.real.basic

/-! # Things that belong to mathlib -/

open finset function sum
open_locale big_operators

variables {α β γ ι ι' : Type*}

namespace sum3

/-- The map from the first summand into a ternary sum. -/
@[pattern, simp, reducible] def in₀ (a) : α ⊕ β ⊕ γ := inl a
/-- The map from the second summand into a ternary sum. -/
@[pattern, simp, reducible] def in₁ (b) : α ⊕ β ⊕ γ := inr $ inl b
/-- The map from the third summand into a ternary sum. -/
@[pattern, simp, reducible] def in₂ (c) : α ⊕ β ⊕ γ := inr $ inr c

end sum3

namespace finset

lemma sum_mod (s : finset α) {m : ℕ} (f : α → ℕ) :
  (∑ i in s, f i) % m = (∑ i in s, (f i % m)) % m :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simp },
  rw [sum_insert hi, sum_insert hi, nat.add_mod, ih, nat.add_mod],
  simp,
end

lemma dumb_thing [decidable_eq α]
  {X Y Z : finset α} (hXY : disjoint X Y) (hXZ : disjoint X Z) (hYZ : disjoint Y Z)
  {x₁ x₂ y₁ y₂ z₁ z₂ : α} (h : ({x₁, y₁, z₁} : finset α) = {x₂, y₂, z₂})
  (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) (hz₁ : z₁ ∈ Z) (hz₂ : z₂ ∈ Z) :
  (x₁, y₁, z₁) = (x₂, y₂, z₂) :=
begin
  simp only [finset.subset.antisymm_iff, subset_iff, mem_insert, mem_singleton, forall_eq_or_imp,
    forall_eq] at h,
  rw disjoint_left at hXY hXZ hYZ,
  rw [prod.mk.inj_iff, prod.mk.inj_iff],
  simp only [and.assoc, @or.left_comm _ (y₁ = y₂), @or.comm _ (z₁ = z₂),
    @or.left_comm _ (z₁ = z₂)] at h,
  refine ⟨h.1.resolve_right (not_or _ _), h.2.1.resolve_right (not_or _ _),
    h.2.2.1.resolve_right (not_or _ _)⟩;
  { rintro rfl,
    solve_by_elim },
end

end finset

namespace nat

lemma annoying_thing {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : n < 2 * k * (n / k) :=
begin
  rw [mul_assoc, two_mul, ←add_lt_add_iff_right (n % k), add_right_comm, add_assoc,
    nat.mod_add_div n k, add_comm, add_lt_add_iff_right],
  apply (nat.mod_lt n hk).trans_le,
  have : 1 ≤ n / k,
  { rwa [nat.le_div_iff_mul_le _ _ hk, one_mul] },
  simpa using nat.mul_le_mul_left k this,
end

lemma thing2 (i j : ℕ) (hj : 0 < j) : j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2 :=
begin
  have : j * (j-1) < j^2,
  { rw sq,
    exact nat.mul_lt_mul_of_pos_left (nat.sub_lt hj zero_lt_one) hj },
  apply (nat.mul_lt_mul_of_pos_right this $ pow_pos nat.succ_pos' _).trans_le,
  rw ←mul_pow,
  exact nat.pow_le_pow_of_le_left (add_le_add_right (nat.mul_div_le i j) _) _,
end

end nat

lemma exists_ne_ne_fin {n : ℕ} (hn : 3 ≤ n) (a b : fin n) : ∃ c, a ≠ c ∧ b ≠ c :=
begin
  obtain ⟨c, hc⟩ : ({a,b}ᶜ : finset (fin n)).nonempty,
  { rw [←finset.card_pos, card_compl, fintype.card_fin],
    apply nat.sub_pos_of_lt ((card_insert_le _ _).trans_lt _),
    rw card_singleton,
    linarith },
  exact ⟨c, by simpa [not_or_distrib, @eq_comm _ c] using hc⟩,
end

lemma fin3_cases (i j : fin 3) : i = j ∨ i = j + 1 ∨ i = j + 2 :=
by { fin_cases i; fin_cases j; finish }

protected lemma set.pairwise_disjoint.disjoint [semilattice_inf α] [order_bot α] {s : set α}
  (h : s.pairwise_disjoint id) :
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → disjoint x y := h

section linear_ordered_field
variables [linear_ordered_field α] {x y z : α}

lemma one_div_le_one_of_one_le {a : α} (ha : 1 ≤ a) : 1 / a ≤ 1 :=
(div_le_one $ zero_lt_one.trans_le ha).2 ha

lemma mul_le_of_nonneg_of_le_div (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ≤ y / z) : x * z ≤ y :=
begin
  rcases hz.eq_or_lt with rfl | hz,
  { simpa using hy },
  rwa le_div_iff hz at h,
end

end linear_ordered_field

lemma disjoint.eq_bot_of_ge [semilattice_inf α] [order_bot α] {a b : α} (hab : disjoint a b)
  (h : b ≤ a) : b = ⊥ :=
hab.symm.eq_bot_of_le h

lemma sum_mul_sq_le_sq_mul_sq (s : finset α) (f g : α → ℝ) :
  (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * ∑ i in s, (g i)^2 :=
begin
  have h : 0 ≤ ∑ i in s, (f i * ∑ j in s, (g j)^2 - g i * ∑ j in s, f j * g j)^2 :=
    sum_nonneg (λ i hi, sq_nonneg _),
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum, ←sum_mul,
    mul_left_comm, ←mul_assoc, ←sum_mul, mul_right_comm, ←sq, mul_comm, sub_add, two_mul,
    add_sub_cancel, mul_comm (∑ j in s, (g j)^2), sq (∑ j in s, (g j)^2),
    ←mul_assoc, ←mul_sub_right_distrib] at h,
  obtain h' | h' := (sum_nonneg (λ i (hi : i ∈ s), sq_nonneg (g i))).eq_or_lt,
  { have h'' : ∀ i ∈ s, g i = 0 :=
      λ i hi, by simpa using (sum_eq_zero_iff_of_nonneg (λ i _, sq_nonneg (g i))).1 h'.symm i hi,
    rw [←h', sum_congr rfl (show ∀ i ∈ s, f i * g i = 0, from λ i hi, by simp [h'' i hi])],
    simp },
  rw ←sub_nonneg,
  apply nonneg_of_mul_nonneg_right h h',
end

@[simp, norm_cast]
lemma rat.cast_sum [division_ring α] [char_zero α] (s : finset ι) (f : ι → ℚ) :
  (↑(∑ i in s, f i) : α) = ∑ i in s, f i :=
map_sum (rat.cast_hom α) f s

@[simp, norm_cast]
lemma rat.cast_prod [field α] [char_zero α] (s : finset ι) (f : ι → ℚ) :
  (↑(∏ i in s, f i) : α) = ∏ i in s, f i :=
map_prod (rat.cast_hom α) f s

lemma chebyshev' (s : finset α) (f : α → ℝ) :
  (∑ (i : α) in s, f i) ^ 2 ≤ (∑ (i : α) in s, f i ^ 2) * s.card :=
by simpa using sum_mul_sq_le_sq_mul_sq s f (λ _, 1)

lemma chebyshev (s : finset α) (f : α → ℝ) :
  ((∑ i in s, f i) / s.card)^2 ≤ (∑ i in s, (f i)^2) / s.card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rw div_pow,
  have hs' : 0 < (s.card : ℝ) := nat.cast_pos.2 hs.card_pos,
  rw [div_le_div_iff (sq_pos_of_ne_zero _ hs'.ne') hs', sq (s.card : ℝ), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right (chebyshev' _ _) hs'.le,
end

namespace simple_graph
variables {G G' : simple_graph α} {s : finset α}

/-- Abbreviation for a graph relation to be decidable. -/
protected abbreviation decidable (G : simple_graph α) := decidable_rel G.adj

instance {r : α → α → Prop} [h : decidable_rel r] : decidable_pred (uncurry r) := λ x, h x.1 x.2

@[mono] lemma edge_set_mono (h : G ≤ G') : G.edge_set ⊆ G'.edge_set :=
λ s, sym2.induction_on s $ λ x y h', h h'

@[simp] lemma dart.adj (d : G.dart) : G.adj d.fst d.snd := d.is_adj

variables (G G') [decidable_eq α] [decidable_rel G.adj] [decidable_rel G'.adj]

/-- The edges of a graph over a finset as a finset. -/
def edge_finset_on (s : finset α) : finset (sym2 α) :=
((s.product s).filter $ uncurry G.adj).image quotient.mk

variables {G G'}

lemma mem_edge_finset_on {x : sym2 α} :
  x ∈ G.edge_finset_on s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ G.adj a b ∧ x = ⟦(a, b)⟧ :=
begin
  simp_rw [edge_finset_on, mem_image, exists_prop, mem_filter, mem_product],
  split,
  { rintro ⟨⟨a, b⟩, ⟨⟨hsa, hsb⟩, hGab⟩, h⟩,
    exact ⟨a, b, hsa, hsb, hGab, h.symm⟩ },
  { rintro ⟨a, b, hsa, hsb, hGab, h⟩,
    exact ⟨⟨a, b⟩, ⟨⟨hsa, hsb⟩, hGab⟩, h.symm⟩ }
end

variables [fintype α]

lemma double_edge_finset_card_eq :
  2 * G.edge_finset.card = (univ.filter (λ (xy : α × α), G.adj xy.1 xy.2)).card :=
begin
  rw [←dart_card_eq_twice_card_edges, ←card_univ],
  refine card_congr (λ i _, (i.fst, i.snd)) (by simp) (by simp [dart.ext_iff, ←and_imp]) _,
  exact λ xy h, ⟨⟨xy, (mem_filter.1 h).2⟩, mem_univ _, prod.mk.eta⟩,
end

@[mono] lemma edge_finset_mono (h : G ≤ G') : G.edge_finset ⊆ G'.edge_finset :=
set.to_finset_mono.2 (edge_set_mono h)

end simple_graph

/-! ## `interedges` with `finpartition` -/

namespace rel
variables [decidable_eq α] {r : α → α → Prop} [decidable_rel r]

lemma card_interedges_finpartition_left {U : finset α} (P : finpartition U) (V : finset α) :
  (interedges r U V).card = ∑ a in P.parts, (interedges r a V).card :=
begin
  simp_rw [←P.bUnion_parts, interedges_bUnion_left, id.def],
  rw card_bUnion,
  exact λ x hx y hy h, interedges_disjoint_left r (P.disjoint hx hy h) _,
end

lemma card_interedges_finpartition_right (U : finset α) {V : finset α} (P : finpartition V) :
  (interedges r U V).card = ∑ b in P.parts, (interedges r U b).card :=
begin
  simp_rw [←P.bUnion_parts, interedges_bUnion_right, id],
  rw card_bUnion,
  exact λ x hx y hy h, interedges_disjoint_right r _ (P.disjoint hx hy h),
end

lemma card_interedges_finpartition {U V : finset α} (P : finpartition U) (Q : finpartition V) :
  (interedges r U V).card = ∑ ab in P.parts.product Q.parts, (interedges r ab.1 ab.2).card :=
by simp_rw [card_interedges_finpartition_left P, card_interedges_finpartition_right _ Q,
  sum_product]

end rel
