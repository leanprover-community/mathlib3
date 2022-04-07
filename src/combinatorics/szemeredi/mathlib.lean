/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.geom_sum
import combinatorics.simple_graph.density
import combinatorics.simple_graph.degree_sum
import combinatorics.pigeonhole
import data.real.basic

/-! # Things that belong to mathlib -/

open_locale big_operators nat
open finset fintype function

variables {α β γ ι ι' : Type*}

section sum₃
variables (α β γ)

/-- Ternary sum of types. This is equivalent to a nested binary sum (see `sum₃_equiv_sum`), but has
better pattern-matching properties. -/
inductive sum₃
| inl : α → sum₃
| inm : β → sum₃
| inr : γ → sum₃

open sum₃

instance [inhabited α] : inhabited (sum₃ α β γ) := ⟨inl default⟩

/-- A ternary sum is equivalent to a nested binary sum. -/
def sum₃_equiv_sum : sum₃ α β γ ≃ α ⊕ β ⊕ γ :=
{ to_fun := λ x, match x with
    | inl a := sum.inl a
    | inm b := sum.inr (sum.inl b)
    | inr c := sum.inr (sum.inr c)
  end,
  inv_fun := λ x, match x with
    | sum.inl a           := inl a
    | sum.inr (sum.inl b) := inm b
    | sum.inr (sum.inr c) := inr c
  end,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by obtain (_ | _ | _) := x; refl }

instance (α β γ : Type*) [fintype α] [fintype β] [fintype γ] : fintype (sum₃ α β γ) :=
fintype.of_equiv _ (sum₃_equiv_sum _ _ _).symm

end sum₃

namespace nat

lemma le_succ_mul_neg (n : ℕ) : ∀ d, d ≤ (n + 1) * d - n
| 0       := by simp
| (d + 1) := begin
    rw [mul_add, mul_one, add_tsub_assoc_of_le (n.le_add_right _), add_tsub_cancel_left],
    exact add_le_add_right (le_mul_of_one_le_left d.zero_le $ nat.le_add_left _ _) 1,
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

/-- The map that appears in Behrend's bound on Roth numbers. -/
def from_digits {n : ℕ} (d : ℕ) (a : fin n → ℕ) : ℕ := ∑ i, a i * d^(i : ℕ)

@[simp] lemma from_digits_zero (d : ℕ) (a : fin 0 → ℕ) : from_digits d a = 0 :=
by simp [from_digits]

lemma from_digits_succ {n d : ℕ} (a : fin (n+1) → ℕ) :
  from_digits d a = a 0 + (∑ (x : fin n), a x.succ * d ^ (x : ℕ)) * d :=
by simp [from_digits, fin.sum_univ_succ, pow_succ', ←mul_assoc, ←sum_mul]

lemma from_digits_succ' {n d : ℕ} (a : fin (n+1) → ℕ) :
  from_digits d a = a 0 + (from_digits d (a ∘ fin.succ)) * d :=
from_digits_succ _

lemma from_digits_monotone {n : ℕ} (d : ℕ) : monotone (from_digits d : (fin n → ℕ) → ℕ) :=
begin
  intros x₁ x₂ h,
  induction n with n ih,
  { simp },
  rw [from_digits_succ', from_digits_succ'],
  exact add_le_add (h 0) (nat.mul_le_mul_right d (ih (λ i, h i.succ))),
end

lemma from_digits_two_add {n d : ℕ} {x y : fin n → ℕ} (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) :
  from_digits (2 * d - 1) (x + y) = from_digits (2 * d - 1) x + from_digits (2 * d - 1) y :=
begin
  induction n with n ih,
  { simp [from_digits_zero] },
  simp only [from_digits_succ', pi.add_apply, add_add_add_comm, add_right_inj, ←add_mul,
    ←@ih (x ∘ fin.succ) (y ∘ fin.succ) (λ _, hx _) (λ _, hy _)],
  refl,
end

lemma sum_bound {n d : ℕ} {x y : fin n → ℕ} (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) (i : fin n) :
  (x + y) i < 2 * d - 1 :=
begin
  rw [←nat.pred_eq_sub_one, nat.lt_pred_iff, nat.lt_iff_add_one_le, nat.succ_eq_add_one,
    pi.add_apply, add_right_comm _ (y i), add_assoc, two_mul],
  apply add_le_add (nat.succ_le_of_lt (hx i)) (nat.succ_le_of_lt (hy i))
end

lemma sum_fin {β : Type*} [add_comm_monoid β] (n : ℕ) (f : ℕ → β) :
  ∑ (i : fin n), f i = ∑ i in range n, f i :=
(sum_subtype (range n) (by simp) f).symm

lemma digits_sum_eq {n d : ℕ} :
  ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) = ((2 * d - 1)^n - 1) / 2 :=
begin
  apply (nat.div_eq_of_eq_mul_left zero_lt_two _).symm,
  rcases nat.eq_zero_or_pos d with rfl | hd,
  { simp only [mul_zero, nat.zero_sub, zero_mul, sum_const_zero, tsub_eq_zero_iff_le, zero_pow_eq],
    split_ifs; simp },
  have : ((2 * d - 2) + 1) = 2 * d - 1,
  { rw ←tsub_tsub_assoc (nat.le_mul_of_pos_right hd) one_le_two },
  rw [sum_fin n (λ i, (d - 1) * (2 * d - 1)^(i : ℕ)), ←mul_sum, mul_right_comm,
    nat.mul_sub_right_distrib, mul_comm d, one_mul, ←this, ←geom_sum_def, ←geom_sum_mul_add,
    nat.add_sub_cancel, mul_comm],
end

lemma digits_sum_le {n d : ℕ} (hd : 0 < d) :
  ∑ (i : fin n), (d - 1) * (2 * d - 1)^(i : ℕ) < (2 * d - 1)^n :=
begin
  rw digits_sum_eq,
  exact (nat.div_le_self _ _).trans_lt
    (nat.pred_lt (pow_pos (hd.trans_le $ le_succ_mul_neg _ _) _).ne'),
end

end nat

-- Should *replace* the existing lemma with a similar name.
lemma exists_le_card_fiber_of_mul_le_card_of_maps_to'
  {α : Type*} {β : Type*} {M : Type*} [linear_ordered_comm_ring M] [decidable_eq β]
  {s : finset α} {t : finset β} {f : α → β} {b : M}
  (hf : ∀ a ∈ s, f a ∈ t) (ht : t.nonempty) (hn : t.card • b ≤ s.card) :
  ∃ y ∈ t, b ≤ (s.filter (λ x, f x = y)).card :=
begin
  simp only [finset.card_eq_sum_ones, nat.cast_sum],
  refine exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht _,
  simpa using hn,
end

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

lemma dumb_thing {α : Type*} [decidable_eq α]
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

lemma annoying_thing {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : n < 2 * k * (n / k) :=
begin
  rw [mul_assoc, two_mul, ←add_lt_add_iff_right (n % k), add_right_comm, add_assoc,
    nat.mod_add_div n k, add_comm, add_lt_add_iff_right],
  apply (nat.mod_lt n hk).trans_le,
  have : 1 ≤ n / k,
  { rwa [nat.le_div_iff_mul_le _ _ hk, one_mul] },
  simpa using nat.mul_le_mul_left k this,
end

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

lemma lt_of_not_le [linear_order α] {a b : α} (h : ¬ a ≤ b) : b < a := lt_of_not_ge' h

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

lemma disjoint.eq_bot_of_ge {α : Type*} [semilattice_inf α] [order_bot α] {a b : α}
  (hab : disjoint a b) (h : b ≤ a) :
  b = ⊥ :=
hab.symm.eq_bot_of_le h

lemma sum_mul_sq_le_sq_mul_sq {α : Type*}
  (s : finset α) (f g : α → ℝ) :
(∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
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
lemma rat.cast_sum {ι α : Type*} [division_ring α] [char_zero α] (s : finset ι) (f : ι → ℚ) :
  (↑(∑ i in s, f i) : α) = ∑ i in s, f i :=
map_sum (rat.cast_hom α) f s

@[simp, norm_cast]
lemma rat.cast_prod {ι α : Type*} [field α] [char_zero α] (s : finset ι) (f : ι → ℚ) :
  (↑(∏ i in s, f i) : α) = ∏ i in s, f i :=
map_prod (rat.cast_hom α) f s

lemma chebyshev' (s : finset α) (f : α → ℝ) :
  (∑ (i : α) in s, f i) ^ 2 ≤ (∑ (i : α) in s, f i ^ 2) * s.card :=
by simpa using sum_mul_sq_le_sq_mul_sq s f (λ _, 1)

lemma chebyshev (s : finset α) (f : α → ℝ) :
  ((∑ i in s, f i) / s.card)^2 ≤ (∑ i in s, (f i)^2) / s.card :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hs,
  { simp },
  rw div_pow,
  have hs' : 0 < (s.card : ℝ) := nat.cast_pos.2 hs.card_pos,
  rw [div_le_div_iff (sq_pos_of_ne_zero _ hs'.ne') hs', sq (s.card : ℝ), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right (chebyshev' _ _) hs'.le,
end

namespace simple_graph
variables {G G' : simple_graph α} {s : finset α}

/-- Abbreviation for a graph relation to be decidable. -/
protected abbreviation decidable {α : Type*} (G : simple_graph α) := decidable_rel G.adj

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

open finset

/-! ## interedges and pairs_density -/

namespace relation
variables (r : α → α → Prop) [decidable_rel r]

-- lemma interedges_bUnion_left [decidable_eq α] (A : finset β) (f : β → finset α) (B : finset α) :
--   interedges r (A.bUnion f) B = ∑ a in A, interedges r (f a) B :=
-- begin
--   rw [interedges, interedges_bUnion_left, card_bUnion],
--   { refl },
--   intros x hx y hy h,
--   apply interedges_disjoint_left,
--   -- simp only [interedges, interedges_bUnion],
--   -- rw card_bUnion,

-- end

-- lemma interedges_bUnion [decidable_eq α] (A B : finset β) (f g : β → finset α) :
--   interedges r (A.bUnion f) (B.bUnion g) =
--     ∑ ab in A.product B, interedges r (f ab.1) (g ab.2) :=
-- begin
--   simp only [interedges, interedges_bUnion],
--   rw card_bUnion,

-- end

end relation

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
