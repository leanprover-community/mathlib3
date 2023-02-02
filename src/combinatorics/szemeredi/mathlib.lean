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

instance {r : α → α → Prop} [decidable_rel r] : decidable_pred (uncurry r) :=
λ x, ‹decidable_rel r› x.1 x.2

namespace tactic
open positivity
open_locale positivity

private lemma sub_ne_zero_of_ne' [subtraction_monoid α] {a b : α} (h : b ≠ a) : a - b ≠ 0 :=
sub_ne_zero_of_ne h.symm

/-- Extension for the `positivity` tactic: `a - b` is positive if `b < a` and nonnegative if
`b ≤ a`. Note, this only tries to find the appropriate assumption in context. -/
@[positivity]
meta def positivity_sub : expr → tactic strictness
| `(%%a - %%b) :=
  (do
    p ← to_expr ``(%%b < %%a) >>= find_assumption,
    positive <$> mk_app ``tsub_pos_of_lt [p] <|> positive <$> mk_app ``sub_pos_of_lt [p]) <|>
  (do
    p ← to_expr ``(%%b ≤ %%a) >>= find_assumption,
    nonnegative <$> mk_app ``sub_nonneg_of_le [p]) ≤|≥
  (do
    p ← to_expr ``(%%a ≠ %%b) >>= find_assumption,
    nonzero <$> to_expr ``(sub_ne_zero_of_ne %%p)) <|>
  do
    p ← to_expr ``(%%b ≠ %%a) >>= find_assumption,
    nonzero <$> to_expr ``(sub_ne_zero_of_ne' %%p)
| e := pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `a - b`"

example {a b : ℕ} (h : b < a) : 0 < a - b := by positivity
example {a b : ℤ} (h : b < a) : 0 < a - b := by positivity
example {a b : ℤ} (h : b ≤ a) : 0 ≤ a - b := by positivity

end tactic

local attribute [protected] nat.div_mul_div_comm

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

end linear_ordered_field

namespace simple_graph
variables {G G' : simple_graph α} {s : finset α}

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
