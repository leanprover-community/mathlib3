/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.degree_sum

/-! # Things that belong to mathlib -/

open finset function sum
open_locale big_operators

variables {α 𝕜 ι : Type*}

namespace finset

lemma sum_mod (s : finset α) {m : ℕ} (f : α → ℕ) : (∑ i in s, f i) % m = (∑ i in s, f i % m) % m :=
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
  { rwa [nat.le_div_iff_mul_le hk, one_mul] },
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

lemma fin3_cases (i j : fin 3) : i = j ∨ i = j + 1 ∨ i = j + 2 :=by fin_cases i; fin_cases j; finish

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

lemma m_bound (hx : 0 < x) : (x + 1) * (1 - 1/x) / x ≤ 1 :=
by { rw [div_le_one hx, one_sub_div hx.ne', mul_div_assoc', div_le_iff hx], linarith }

end linear_ordered_field

section linear_ordered_field
variables [linear_ordered_field 𝕜] (r : α → α → Prop) [decidable_rel r] {s t : finset α} {x : 𝕜}

lemma sum_mul_sq_le_sq_mul_sq (s : finset α) (f g : α → 𝕜) :
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
  exact nonneg_of_mul_nonneg_left h h',
end

lemma chebyshev' (s : finset α) (f : α → 𝕜) :
  (∑ (i : α) in s, f i) ^ 2 ≤ (∑ (i : α) in s, f i ^ 2) * s.card :=
by simpa using sum_mul_sq_le_sq_mul_sq s f (λ _, 1)

lemma chebyshev (s : finset α) (f : α → 𝕜) :
  ((∑ i in s, f i) / s.card)^2 ≤ (∑ i in s, (f i)^2) / s.card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rw [←card_pos, ←@nat.cast_pos 𝕜] at hs,
  rw [div_pow, div_le_div_iff (sq_pos_of_ne_zero _ hs.ne') hs, sq (s.card : 𝕜), ←mul_assoc],
  exact mul_le_mul_of_nonneg_right (chebyshev' _ f) hs.le,
end

lemma lemma_B_ineq_zero (hst : s ⊆ t) (f : α → 𝕜) (hs : x^2 ≤ ((∑ x in s, f x)/s.card)^2)
  (hs' : (s.card : 𝕜) ≠ 0) :
  (s.card : 𝕜) * x^2 ≤ ∑ x in t, f x^2 :=
(mul_le_mul_of_nonneg_left (hs.trans (chebyshev s f)) (nat.cast_nonneg _)).trans $
  (mul_div_cancel' _ hs').le.trans $ sum_le_sum_of_subset_of_nonneg hst $ λ i _ _, sq_nonneg _

lemma lemma_B_ineq (hst : s ⊆ t) (f : α → 𝕜) (d : 𝕜) (hx : 0 ≤ x)
  (hs : x ≤ abs ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card))
  (ht : d ≤ ((∑ i in t, f i)/t.card)^2) :
  d + s.card/t.card * x^2 ≤ (∑ i in t, f i^2)/t.card :=
begin
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : 𝕜) ≤ s.card).eq_or_lt,
  { simpa [←hscard] using ht.trans (chebyshev t f) },
  have htcard : (0:𝕜) < t.card := hscard.trans_le (nat.cast_le.2 (card_le_of_subset hst)),
  have h₁ : x^2 ≤ ((∑ i in s, f i)/s.card - (∑ i in t, f i)/t.card)^2 :=
    sq_le_sq.2 (by rwa [abs_of_nonneg hx]),
  have h₂ : x^2 ≤ ((∑ i in s, (f i - (∑ j in t, f j)/t.card))/s.card)^2,
  { apply h₁.trans,
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left _ hscard.ne'] },
  apply (add_le_add_right ht _).trans,
  rw [←mul_div_right_comm, le_div_iff htcard, add_mul, div_mul_cancel _ htcard.ne'],
  have h₃ := lemma_B_ineq_zero hst (λ i, f i - (∑ j in t, f j) / t.card) h₂ hscard.ne',
  apply (add_le_add_left h₃ _).trans,
  simp [←mul_div_right_comm _ (t.card : 𝕜), sub_div' _ _ _ htcard.ne', ←sum_div, ←add_div, mul_pow,
    div_le_iff (sq_pos_of_ne_zero _ htcard.ne'), sub_sq, sum_add_distrib, ←sum_mul, ←mul_sum],
  ring_nf,
end

end linear_ordered_field

namespace simple_graph
variables {G G' : simple_graph α} {s : finset α}

instance {r : α → α → Prop} [h : decidable_rel r] : decidable_pred (uncurry r) := λ x, h x.1 x.2

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

end simple_graph
