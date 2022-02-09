/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.special_functions.log
import combinatorics.simple_graph.degree_sum
import combinatorics.pigeonhole
import data.set.equitable
import .finpartition

/-! # Things that belong to mathlib -/

open_locale big_operators nat
open finset fintype function

variables {α β ι ι' : Type*}

namespace nat

lemma weird_thing : ∀ {d : ℕ}, d ≤ 2 * d - 1
| 0 := by simp
| (n+1) := by simp [mul_add, two_mul]

lemma thing2 (i j : ℕ) (hj : 0 < j) : j * (j - 1) * (i / j + 1) ^ 2 < (i + j) ^ 2 :=
begin
  have : j * (j-1) < j^2,
  { rw sq,
    exact nat.mul_lt_mul_of_pos_left (nat.sub_lt hj zero_lt_one) hj },
  apply (nat.mul_lt_mul_of_pos_right this $ pow_pos nat.succ_pos' _).trans_le,
  rw ←mul_pow,
  exact nat.pow_le_pow_of_le_left (add_le_add_right (nat.mul_div_le i j) _) _,
end

def from_digits {n : ℕ} (d : ℕ) (a : fin n → ℕ) : ℕ := ∑ i, a i * d^(i : ℕ)

@[simp] lemma from_digits_zero (d : ℕ) (a : fin 0 → ℕ) : from_digits d a = 0 :=
by simp [from_digits]

lemma from_digits_succ {n d : ℕ} (a : fin (n+1) → ℕ) :
  from_digits d a = a 0 + (∑ (x : fin n), a x.succ * d ^ (x : ℕ)) * d :=
by simp [from_digits, fin.sum_univ_succ, pow_succ', ←mul_assoc, ←sum_mul]

lemma from_digits_succ' {n d : ℕ} (a : fin (n+1) → ℕ) :
  from_digits d a = a 0 + (from_digits d (a ∘ fin.succ)) * d :=
from_digits_succ _

lemma from_digits_monotone {n : ℕ} (d : ℕ) :
  monotone (from_digits d : (fin n → ℕ) → ℕ) :=
begin
  intros x₁ x₂ h,
  induction n with n ih,
  { simp },
  rw [from_digits_succ', from_digits_succ'],
  exact add_le_add (h 0) (nat.mul_le_mul_right d (ih (λ i, h i.succ))),
end

lemma from_digits_two_add {n d : ℕ} {x y : fin n → ℕ}
  (hx : ∀ i, x i < d) (hy : ∀ i, y i < d) :
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
  apply (nat.div_le_self _ _).trans_lt (nat.pred_lt (pow_pos (hd.trans_le weird_thing) _).ne'),
end

end nat

section

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

end

namespace set
variables {s : set ι} {t : set ι'} {f : ι → set α} {g : ι' → set β}

lemma pairwise_disjoint.prod (hs : s.pairwise_disjoint f) (ht : t.pairwise_disjoint g) :
  (s ×ˢ t : set (ι × ι')).pairwise_disjoint (λ i, (f i.1) ×ˢ (g i.2)) :=
λ ⟨i, i'⟩ ⟨hi, hi'⟩ ⟨j, j'⟩ ⟨hj, hj'⟩ hij ⟨a, b⟩ ⟨⟨hai, hbi⟩, haj, hbj⟩,
  hij $ prod.ext (hs.elim_set hi hj _ hai haj) $ ht.elim_set hi' hj' _ hbi hbj

lemma pairwise_disjoint.product [decidable_eq α] [decidable_eq β] {f : ι → finset α}
  {g : ι' → finset β} (hs : s.pairwise_disjoint f) (ht : t.pairwise_disjoint g) :
  (s ×ˢ t : set (ι × ι')).pairwise_disjoint (λ i, (f i.1).product (g i.2)) :=
begin
  rintro ⟨i, i'⟩ ⟨hi, hi'⟩ ⟨j, j'⟩ ⟨hj, hj'⟩ hij ⟨a, b⟩ hab,
  simp_rw [finset.inf_eq_inter, finset.mem_inter, finset.mem_product] at hab,
  exact hij (prod.ext (hs.elim_finset hi hj _ hab.1.1 hab.2.1) $
    ht.elim_finset hi' hj' _ hab.1.2 hab.2.2),
end

-- lemma pairwise_disjoint.product' [decidable_eq α] [decidable_eq β] {s : finset ι} {t : finset ι'}
--   {f : ι → finset α} {g : ι' → finset β} (hs : s.pairwise_disjoint f)
--   (ht : t.pairwise_disjoint g) :
--   (s.product t).pairwise_disjoint (λ i, (f i.1).product (g i.2)) :=
-- begin
--   rintro ⟨i, i'⟩ ⟨hi, hi'⟩ ⟨j, j'⟩ ⟨hj, hj'⟩ hij ⟨a, b⟩ hab,
--   simp_rw [finset.inf_eq_inter, finset.mem_inter, finset.mem_product] at hab,
--   exact hij (prod.ext (hs.elim_finset hi hj _ hab.1.1 hab.2.1) $
--     ht.elim_finset hi' hj' _ hab.1.2 hab.2.2),
-- end

lemma pairwise_disjoint_pi {α : ι' → Type*} {ι : ι' → Type*} {s : Π i, set (ι i)}
  {f : Π i, ι i → set (α i)}
  (hs : ∀ i, (s i).pairwise_disjoint (f i)) :
  ((univ : set ι').pi s).pairwise_disjoint (λ I, (univ : set ι').pi (λ i, f _ (I i))) :=
λ I hI J hJ hIJ a ⟨haI, haJ⟩, hIJ $ funext $ λ i,
  (hs i).elim_set (hI i trivial) (hJ i trivial) (a i) (haI i trivial) (haJ i trivial)

lemma pairwise_disjoint.attach [semilattice_inf α] [order_bot α] {s : finset ι} {f : ι → α}
  (hs : (s : set ι).pairwise_disjoint f) :
  (s.attach : set {x // x ∈ s}).pairwise_disjoint (f ∘ subtype.val) :=
λ i _ j _ hij, hs i.2 j.2 $ mt subtype.ext_val hij

lemma subsingleton_of_subset_singleton {s : set α} {a : α} (h : s ⊆ {a}) : s.subsingleton :=
subsingleton_singleton.mono h

end set

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

-- lemma nonempty_diff [decidable_eq α] {s t : finset α} : (s \ t).nonempty ↔ ¬ s ⊆ t :=
-- sorry

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

section linear_ordered_field
variables [linear_ordered_field α]

lemma one_div_le_one_of_one_le {a : α} (ha : 1 ≤ a) : 1 / a ≤ 1 :=
(div_le_one $ zero_lt_one.trans_le ha).2 ha

lemma le_div_self {x y : α} (hx : 0 ≤ x) (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
  x ≤ x / y :=
by simpa using div_le_div_of_le_left hx hy₀ hy₁

lemma mul_le_of_nonneg_of_le_div {x y z : α} (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ≤ y / z) :
  x * z ≤ y :=
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

instance {r : α → α → Prop} [h : decidable_rel r] : decidable_pred (uncurry r) := λ x, h x.1 x.2

@[mono] lemma edge_set_mono (h : G ≤ G') : G.edge_set ⊆ G'.edge_set :=
begin
  refine sym2.ind _,
  intros x y h',
  exact h h',
end
variables [decidable_eq α] [fintype α] [decidable_rel G.adj] [decidable_rel G'.adj]

@[mono] lemma edge_finset_mono (h : G ≤ G') : G.edge_finset ⊆ G'.edge_finset :=
set.to_finset_mono.2 (edge_set_mono h)

variables (G G')

def edge_finset_on [decidable_eq α] [decidable_rel G.adj] (s : finset α) : finset (sym2 α) :=
((s.product s).filter $ function.uncurry G.adj).image quotient.mk

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

@[simp] lemma dart.adj (d : G.dart) : G.adj d.fst d.snd := d.3

variables [fintype α]

lemma double_edge_finset_card_eq [decidable_eq α] [decidable_rel G.adj] :
  2 * G.edge_finset.card = (univ.filter (λ (xy : α × α), G.adj xy.1 xy.2)).card :=
begin
  rw [←dart_card_eq_twice_card_edges, ←card_univ],
  refine card_congr (λ i _, (i.1, i.2)) (by simp) (by simp [dart.ext_iff, ←and_imp]) _,
  rintro ⟨x, y⟩ h,
  exact ⟨⟨x, y, (mem_filter.1 h).2⟩, mem_univ _, rfl⟩,
end

end simple_graph

open finset

/-! ## pairs_finset and pairs_density -/

namespace relation
variables (r : α → α → Prop) [decidable_rel r]

/-- Finset of edges between two finsets of vertices -/
def pairs_finset (U V : finset α) : finset (α × α) :=
(U.product V).filter (λ e, r e.1 e.2)

lemma mem_pairs_finset (U V : finset α) (x : α × α) :
  x ∈ pairs_finset r U V ↔ x.1 ∈ U ∧ x.2 ∈ V ∧ r x.1 x.2 :=
by simp only [pairs_finset, and_assoc, mem_filter, finset.mem_product]

lemma mem_pairs_finset' (U V : finset α) (x y : α) :
  (x, y) ∈ pairs_finset r U V ↔ x ∈ U ∧ y ∈ V ∧ r x y :=
mem_pairs_finset _ _ _ _

@[simp] lemma pairs_finset_empty_left (V : finset α) :
  pairs_finset r ∅ V = ∅ :=
by rw [pairs_finset, finset.empty_product, filter_empty]

lemma pairs_finset_mono {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_finset r A' B' ⊆ pairs_finset r A B :=
begin
  intro x,
  rw [mem_pairs_finset, mem_pairs_finset],
  exact λ h, ⟨hA h.1, hB h.2.1, h.2.2⟩,
end

lemma card_pairs_finset_compl (U V : finset α) :
  (pairs_finset r U V).card + (pairs_finset (λ x y, ¬r x y) U V).card = U.card * V.card :=
begin
  classical,
  rw [←card_product, pairs_finset, pairs_finset, ←card_union_eq, filter_union_filter_neg_eq],
  rw disjoint_filter,
  exact λ x _, not_not.2,
end

section decidable_eq
variable [decidable_eq α]

lemma pairs_finset_disjoint_left {U U' : finset α} (hU : disjoint U U') (V : finset α) :
  disjoint (pairs_finset r U V) (pairs_finset r U' V) :=
begin
  rw [disjoint_iff_inter_eq_empty, ←subset_empty] at ⊢ hU,
  rintro x hx,
  rw [mem_inter, mem_pairs_finset, mem_pairs_finset] at hx,
  exact hU (mem_inter.2 ⟨hx.1.1, hx.2.1⟩),
end

lemma pairs_finset_disjoint_right (U : finset α) {V V' : finset α} (hV : disjoint V V') :
  disjoint (pairs_finset r U V) (pairs_finset r U V') :=
begin
  rw [disjoint_iff_inter_eq_empty, ←subset_empty] at ⊢ hV,
  rintro x hx,
  rw [mem_inter, mem_pairs_finset, mem_pairs_finset] at hx,
  exact hV (mem_inter.2 ⟨hx.1.2.1, hx.2.2.1⟩),
end

lemma pairs_finset_bUnion_left (A : finset β) (V : finset α) (f : β → finset α) :
  pairs_finset r (A.bUnion f) V = A.bUnion (λ a, pairs_finset r (f a) V) :=
by { ext x, simp only [mem_pairs_finset, mem_bUnion, exists_and_distrib_right] }

lemma pairs_finset_bUnion_right (U : finset α) (B : finset β) (f : β → finset α) :
  pairs_finset r U (B.bUnion f) = B.bUnion (λ b, pairs_finset r U (f b)) :=
by { ext x, simp only [mem_pairs_finset, mem_bUnion], tauto }

lemma pairs_finset_bUnion (A B : finset β) (f g : β → finset α) :
  pairs_finset r (A.bUnion f) (B.bUnion g) =
    (A.product B).bUnion (λ ab, pairs_finset r (f ab.1) (g ab.2)) :=
by simp_rw [product_bUnion, pairs_finset_bUnion_left, pairs_finset_bUnion_right]

end decidable_eq

/-- Number of edges between two finsets of vertices -/
def pairs_count (U V : finset α) : ℕ := (pairs_finset r U V).card

lemma pairs_count_le_mul (U V : finset α) : pairs_count r U V ≤ U.card * V.card :=
begin
  rw [pairs_count, pairs_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

-- lemma pairs_count_bUnion_left [decidable_eq α] (A : finset β) (f : β → finset α) (B : finset α) :
--   pairs_count r (A.bUnion f) B = ∑ a in A, pairs_count r (f a) B :=
-- begin
--   rw [pairs_count, pairs_finset_bUnion_left, card_bUnion],
--   { refl },
--   intros x hx y hy h,
--   apply pairs_finset_disjoint_left,
--   -- simp only [pairs_count, pairs_finset_bUnion],
--   -- rw card_bUnion,

-- end

-- lemma pairs_count_bUnion [decidable_eq α] (A B : finset β) (f g : β → finset α) :
--   pairs_count r (A.bUnion f) (B.bUnion g) =
--     ∑ ab in A.product B, pairs_count r (f ab.1) (g ab.2) :=
-- begin
--   simp only [pairs_count, pairs_finset_bUnion],
--   rw card_bUnion,

-- end

/-- Edge density between two finsets of vertices -/
noncomputable def pairs_density (U V : finset α) : ℝ :=
pairs_count r U V / (U.card * V.card)

lemma pairs_density_nonneg (U V : finset α) : 0 ≤ pairs_density r U V :=
by { apply div_nonneg; exact_mod_cast nat.zero_le _ }

lemma pairs_density_le_one (U V : finset α) : pairs_density r U V ≤ 1 :=
div_le_one_of_le (by exact_mod_cast (pairs_count_le_mul _ _ _)) (by exact_mod_cast (nat.zero_le _))

lemma pairs_density_compl {U V : finset α} (hU : U.nonempty) (hV : V.nonempty) :
  pairs_density r U V + pairs_density (λ x y, ¬r x y) U V = 1 :=
begin
  rw [pairs_density, pairs_density, div_add_div_same, div_eq_one_iff_eq],
  { exact_mod_cast card_pairs_finset_compl r U V },
  { exact_mod_cast (mul_pos hU.card_pos hV.card_pos).ne' },
end

@[simp] lemma pairs_density_empty_left (V : finset α) : pairs_density r ∅ V = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, zero_mul, div_zero]

@[simp] lemma pairs_density_empty_right (U : finset α) : pairs_density r U ∅ = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, mul_zero, div_zero]

section symmetric
variables {r} (hr : symmetric r)
include hr

lemma mem_pairs_finset_comm (U V : finset α) (x y : α) :
  (x, y) ∈ pairs_finset r U V ↔ (y, x) ∈ pairs_finset r V U :=
begin
  rw [mem_pairs_finset', mem_pairs_finset'],
  split; exact λ h, ⟨h.2.1, h.1, hr h.2.2⟩,
end

lemma pairs_count_comm (U V : finset α) : pairs_count r U V = pairs_count r V U :=
begin
  apply finset.card_congr (λ (i : α × α) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    rwa mem_pairs_finset_comm hr },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ ⟨⟩,
    refl },
  rintro ⟨i, j⟩ h,
  refine ⟨⟨j, i⟩, _, rfl⟩,
  rwa mem_pairs_finset_comm hr,
end

lemma pairs_density_comm (U V : finset α) : pairs_density r U V = pairs_density r V U :=
by rw [pairs_density, mul_comm, pairs_count_comm hr, pairs_density]

end symmetric

end relation

/-! ## Specialization to `simple_graph` -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj]

open relation

def edge_count (U V : finset α) : ℝ := (pairs_finset G.adj U V).card

/- Remnants of what's now under `relation`. The only point for keeping it is to sometimes avoid
writing `G.adj` and `G.sym` sometimes. -/
/-- Edge density between two finsets of vertices -/
noncomputable def edge_density : finset α → finset α → ℝ := pairs_density G.adj

lemma edge_density_eq_edge_count_div_card (U V : finset α) :
  G.edge_density U V = G.edge_count U V/(U.card * V.card) :=
rfl

lemma edge_density_comm (U V : finset α) : G.edge_density U V = G.edge_density V U :=
pairs_density_comm G.symm U V

lemma edge_density_nonneg (U V : finset α) : 0 ≤ G.edge_density U V := pairs_density_nonneg _ U V

lemma edge_density_le_one (U V : finset α) : G.edge_density U V ≤ 1 := pairs_density_le_one _ U V

end simple_graph

/-! ## is_uniform for simple_graph -/

namespace simple_graph
variables (G : simple_graph α) (ε : ℝ) [decidable_rel G.adj]

/-- A pair of finsets of vertices is ε-uniform iff their edge density is close to the density of any
big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (U V : finset α) : Prop :=
∀ U', U' ⊆ U → ∀ V', V' ⊆ V → (U.card : ℝ) * ε ≤ U'.card → (V.card : ℝ) * ε ≤ V'.card →
  abs (edge_density G U' V' - edge_density G U V) < ε

/-- If the pair `(U, V)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform_mono {ε ε' : ℝ} {U V : finset α} (h : ε ≤ ε') (hε : is_uniform G ε U V) :
  is_uniform G ε' U V :=
λ U' hU' V' hV' hU hV,
begin
  refine (hε _ hU' _ hV' (le_trans _ hU) (le_trans _ hV)).trans_le h;
  exact mul_le_mul_of_nonneg_left h (nat.cast_nonneg _),
end

lemma is_uniform.symm {G : simple_graph α} [decidable_rel G.adj] {ε : ℝ} :
  symmetric (is_uniform G ε) :=
begin
  intros U V h V' hV' U' hU' hV hU,
  rw [edge_density_comm _ V', edge_density_comm _ V],
  apply h _ hU' _ hV' hU hV,
end

lemma is_uniform_comm {U V : finset α} : is_uniform G ε U V ↔ is_uniform G ε V U :=
⟨λ h, h.symm, λ h, h.symm⟩

lemma is_uniform_singleton {ε : ℝ} {x y : α} (hε : 0 < ε) : G.is_uniform ε {x} {y} :=
begin
  rintro U' hU' V' hV' hU hV,
  rw [card_singleton, nat.cast_one, one_mul] at hU hV,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty] at hU,
    exact (hε.not_le hU).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hV',
  { rw [finset.card_empty] at hV,
    exact (hε.not_le hV).elim },
  rwa [sub_self, abs_zero],
end

lemma not_is_uniform_zero {U V : finset α} : ¬ G.is_uniform 0 U V :=
λ h, not_le_of_lt (h ∅ (by simp) ∅ (by simp) (by simp) (by simp)) (abs_nonneg _)

variables {ε}

lemma is_uniform_of_one_le (hε : 1 ≤ ε) {U V : finset α} : G.is_uniform ε U V :=
begin
  intros U' hU' V' hV' hU hV,
  have hU'' := nat.cast_le.1 ((le_mul_of_one_le_right (nat.cast_nonneg _) hε).trans hU),
  have hV'' := nat.cast_le.1 ((le_mul_of_one_le_right (nat.cast_nonneg _) hε).trans hV),
  rw [eq_of_subset_of_card_le hU' hU'', eq_of_subset_of_card_le hV' hV'', sub_self, abs_zero],
  linarith
end

end simple_graph

/-! ## pairs_count with finpartition -/

namespace relation
variables [decidable_eq α] {r : α → α → Prop} [decidable_rel r]

lemma pairs_count_finpartition_left {U : finset α} (P : finpartition U) (V : finset α) :
  pairs_count r U V = ∑ a in P.parts, pairs_count r a V :=
begin
  simp_rw [pairs_count, ←P.bUnion_parts, pairs_finset_bUnion_left, id.def],
  rw card_bUnion,
  exact λ x hx y hy h, pairs_finset_disjoint_left r (P.disjoint hx hy h) _,
end

lemma pairs_count_finpartition_right (U : finset α) {V : finset α} (P : finpartition V) :
  pairs_count r U V = ∑ b in P.parts, pairs_count r U b :=
begin
  simp_rw [pairs_count, ←P.bUnion_parts, pairs_finset_bUnion_right, id],
  rw card_bUnion,
  exact λ x hx y hy h, pairs_finset_disjoint_right r _ (P.disjoint hx hy h),
end

lemma pairs_count_finpartition {U V : finset α} (P : finpartition U) (Q : finpartition V) :
  pairs_count r U V = ∑ ab in P.parts.product Q.parts, pairs_count r ab.1 ab.2 :=
by simp_rw [pairs_count_finpartition_left P, pairs_count_finpartition_right _ Q, sum_product]

end relation

/-! ## is_equipartition -/

namespace finpartition
variables [decidable_eq α] {s : finset α} (P : finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def is_equipartition : Prop := (P.parts : set (finset α)).equitable_on card

lemma is_equipartition_iff_card_parts_eq_average : P.is_equipartition ↔
  ∀ a : finset α, a ∈ P.parts → a.card = s.card/P.parts.card ∨ a.card = s.card/P.parts.card + 1 :=
by simp_rw [is_equipartition, finset.equitable_on_iff, P.sum_card_parts]

variables {P}

lemma _root_.set.subsingleton.is_equipartition (h : (P.parts : set (finset α)).subsingleton) :
  P.is_equipartition :=
h.equitable_on _

end finpartition

lemma finpartition.is_equipartition_iff_card_parts_eq_average' [decidable_eq α] [fintype α]
  {P : finpartition (univ : finset α)} :
  P.is_equipartition ↔
    ∀ a : finset α, a ∈ P.parts → a.card = card α/P.parts.card ∨ a.card = card α/P.parts.card + 1 :=
by rw [P.is_equipartition_iff_card_parts_eq_average, card_univ]

lemma finpartition.is_equipartition.average_le_card_part [decidable_eq α] [fintype α]
  {P : finpartition (univ : finset α)} (hP : P.is_equipartition) {a : finset α} (ha : a ∈ P.parts) :
  card α/P.parts.card ≤ a.card :=
(finpartition.is_equipartition_iff_card_parts_eq_average'.1 hP a ha).elim ge_of_eq
  (λ h, (nat.le_succ _).trans h.ge)

lemma finpartition.is_equipartition.card_part_le_average_add_one [decidable_eq α] [fintype α]
  {P : finpartition (univ : finset α)} (hP : P.is_equipartition) {a : finset α} (ha : a ∈ P.parts) :
  a.card ≤ card α/P.parts.card + 1 :=
(finpartition.is_equipartition_iff_card_parts_eq_average'.1 hP a ha).elim
  (λ i, by simp [i]) le_of_eq

/-! ### Discrete and indiscrete finpartition -/

namespace finpartition
variables [decidable_eq α] (s : finset α)

lemma bot_is_equipartition : (⊥ : finpartition s).is_equipartition :=
set.equitable_on_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩

lemma indiscrete_is_equipartition {hs : s ≠ ∅} : (indiscrete hs).is_equipartition :=
by { rw [is_equipartition, indiscrete_parts, coe_singleton], exact set.equitable_on_singleton s _ }

lemma parts_top_subset [lattice α] [order_bot α] (a : α) : (⊤ : finpartition a).parts ⊆ {a} :=
begin
  rintro b hb,
  change b ∈ finpartition.parts (dite _ _ _) at hb,
  split_ifs at hb,
  { simp only [copy_parts, empty_parts, not_mem_empty] at hb,
    exact hb.elim },
  { exact hb }
end

lemma parts_top_subsingleton [lattice α] [order_bot α] (a : α) :
  ((⊤ : finpartition a).parts : set α).subsingleton :=
set.subsingleton_of_subset_singleton $ λ b hb, mem_singleton.1 $ parts_top_subset _ hb

lemma top_is_equipartition : (⊤ : finpartition s).is_equipartition :=
(parts_top_subsingleton _).is_equipartition

end finpartition
