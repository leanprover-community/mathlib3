/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.special_functions.exp_log
import analysis.special_functions.pow
import combinatorics.simple_graph.basic
import ring_theory.polynomial.pochhammer

/-! # Things that belong to mathlib -/

universe u

open_locale big_operators nat
open finset fintype function

variable {α : Type u}

lemma between_nat_iff {a t : ℕ} :
  (a = t ∨ a = t+1) ↔ (t ≤ a ∧ a ≤ t+1) :=
begin
  split,
  { rintro (rfl | rfl);
    simp },
  rintro ⟨h₁, h₂⟩,
  obtain h | h := h₁.eq_or_lt,
  { exact or.inl h.symm },
  exact or.inr (le_antisymm h₂ (nat.succ_le_of_lt h)),
end

namespace real

lemma le_exp_iff_log_le {a b : ℝ} (ha : 0 < a) :
  log a ≤ b ↔ a ≤ exp b :=
by rw [←exp_le_exp, exp_log ha]

end real

lemma sum_mul_sq_le_sq_mul_sq (s : finset α) (f g : α → ℝ) :
  (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
begin
  have : 0 ≤ ∑ i in s, (g i)^2 := sum_nonneg (λ i hi, sq_nonneg _),
  cases eq_or_lt_of_le this with h h,
  { rw [eq_comm, sum_eq_zero_iff_of_nonneg] at h,
    { simp only [nat.succ_pos', pow_eq_zero_iff] at h,
      rw [finset.sum_congr rfl (show ∀ i ∈ s, f i * g i = 0, from λ i hi, by simp [h i hi]),
          finset.sum_congr rfl (show ∀ i ∈ s, g i ^ 2 = 0, from λ i hi, by simp [h i hi])],
      simp },
    { intros i hi,
      apply sq_nonneg } },
  let lambda := (∑ i in s, f i * g i) / (∑ i in s, (g i)^2),
  have : 0 ≤ ∑ i in s, (f i - lambda * g i)^2,
  { apply sum_nonneg,
    intros i hi,
    apply sq_nonneg },
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum,
    mul_left_comm _ lambda, ←mul_sum, div_pow, div_mul_eq_mul_div, ←sq, ←div_mul_eq_mul_div,
    div_mul_eq_mul_div_comm, sq (∑ i in s, g i ^ 2), div_self_mul_self', ←div_eq_mul_inv, two_mul,
    ←sub_sub, sub_add_cancel, sub_nonneg] at this,
  rw div_le_iff h at this,
  assumption
end

alias nat.desc_factorial_eq_zero_iff_lt ↔ _ nat.desc_factorial_of_lt

lemma pochhammer_nat_eq_desc_factorial (a b : ℕ) :
  (pochhammer ℕ b).eval a = (a + b - 1).desc_factorial b :=
begin
  cases b,
  { rw [nat.desc_factorial_zero, pochhammer_zero, polynomial.eval_one] },
  rw [nat.succ_sub_succ, nat.sub_zero],
  cases a,
  { rw [pochhammer_ne_zero_eval_zero _ b.succ_ne_zero, zero_add,
    nat.desc_factorial_of_lt b.lt_succ_self] },
  { rw [nat.succ_add, ←nat.add_succ, nat.add_desc_factorial_eq_asc_factorial,
      pochhammer_nat_eq_asc_factorial] }
end

lemma pochhammer_succ_eval (S : Type*) [comm_semiring S] (n : ℕ) (k : S) :
  (pochhammer S n.succ).eval k = (pochhammer S n).eval k * (k + ↑n) :=
by rw [pochhammer_succ_right, polynomial.eval_mul, polynomial.eval_add, polynomial.eval_X,
    polynomial.eval_nat_cast]

namespace nat

lemma lt_div_mul_add {a b : ℕ} (hb : 0 < b) : a < a/b*b + b :=
begin
  rw [←nat.succ_mul, ←nat.div_lt_iff_lt_mul _ _ hb],
  exact nat.lt_succ_self _,
end

lemma succ_sub_self : ∀ {n : ℕ}, n.succ - n = 1
| 0       := rfl
| (n + 1) := by rw [succ_sub_succ, succ_sub_self]

@[simp] theorem factorial_two : 2! = 2 := rfl

lemma cast_asc_factorial (S : Type*) [semiring S] (a b : ℕ) :
  (a.asc_factorial b : S) = (pochhammer S b).eval (a + 1) :=
by rw [←pochhammer_nat_eq_asc_factorial, pochhammer_eval_cast, nat.cast_add, nat.cast_one]

lemma cast_desc_factorial (S : Type*) [semiring S] (a b : ℕ) :
  (a.desc_factorial b : S) = (pochhammer S b).eval (a - (b - 1) : ℕ) :=
begin
  rw [←pochhammer_eval_cast, pochhammer_nat_eq_desc_factorial],
  cases b,
  { simp_rw desc_factorial_zero },
  simp_rw succ_sub_one,
  obtain h | h := le_total a b,
  { rw [desc_factorial_of_lt (lt_succ_of_le h), desc_factorial_of_lt (lt_succ_of_le _)],
    rw [sub_eq_zero_of_le h, zero_add] },
  { rw nat.sub_add_cancel h }
end

lemma cast_choose' (K : Type*) [division_ring K] [char_zero K] (a b : ℕ) :
  (a.choose b : K) = (pochhammer K b).eval (a - (b - 1) : ℕ) / b.factorial :=
by rw [eq_div_iff_mul_eq (nat.cast_ne_zero.2 b.factorial_ne_zero : (b.factorial : K) ≠ 0),
  ←nat.cast_mul, mul_comm, ←nat.desc_factorial_eq_factorial_mul_choose, ←cast_desc_factorial]

lemma cast_choose_two_right (K : Type*) [division_ring K] [char_zero K] (a : ℕ) :
  (a.choose 2 : K) = a * (a - 1) / 2 :=
begin
  rw [cast_choose', factorial_two, cast_two],
  cases a,
  { rw [nat.zero_sub, cast_zero, pochhammer_ne_zero_eval_zero _ (two_ne_zero), zero_mul] },
  { rw [succ_sub_succ, nat.sub_zero, cast_succ, add_sub_cancel, pochhammer_succ_right,
      pochhammer_one, polynomial.X_mul, polynomial.eval_mul_X, polynomial.eval_add,
      polynomial.eval_X, cast_one, polynomial.eval_one] }
end

end nat

open finset

/-! ## equitable_on -/

/-- A set is equitable if no element value is more than one bigger than another. -/
def equitable_on (s : set α) (f : α → ℕ) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ → f a₂ - f a₁ ≤ 1

@[simp]
lemma equitable_on_empty (f : α → ℕ) :
  equitable_on ∅ f :=
by simp [equitable_on]

lemma equitable_on_iff (s : set α) (f : α → ℕ) :
  equitable_on s f ↔ ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₂ - f a₁ ≤ 1 :=
begin
  split,
  { intros hf a₁ a₂ ha₁ ha₂,
    cases le_total (f a₁) (f a₂),
    { apply hf ha₁ ha₂ h },
    rw nat.sub_eq_zero_of_le h,
    exact zero_le_one },
  exact λ hf a₁ a₂ ha₁ ha₂ _, hf ha₁ ha₂,
end

lemma equitable_on_iff_almost_eq_constant {s : set α} {f : α → ℕ} :
  equitable_on s f ↔ ∃ b, ∀ a ∈ s, f a = b ∨ f a = b + 1 :=
begin
  classical,
  split,
  { rw equitable_on_iff,
    rcases s.eq_empty_or_nonempty with rfl | hs,
    { simp },
    { intros h,
      refine ⟨nat.find (set.nonempty.image f hs), _⟩,
      obtain ⟨w, hw₁, hw₂⟩ := nat.find_spec (set.nonempty.image f hs),
      intros a ha,
      have : nat.find (set.nonempty.image f hs) ≤ f a := nat.find_min' _ ⟨_, ha, rfl⟩,
      cases eq_or_lt_of_le this with q q,
      { exact or.inl q.symm },
      { refine or.inr (le_antisymm _ (nat.succ_le_of_lt q)),
        rw [←hw₂, ←nat.sub_le_left_iff_le_add],
        exact h hw₁ ha } } },
  { rintro ⟨b, hb⟩ x₁ x₂ hx₁ hx₂ h,
    rcases hb x₁ hx₁ with rfl | hx₁';
    cases hb x₂ hx₂ with hx₂' hx₂',
    { simp [hx₂'] },
    { simp [hx₂'] },
    { simpa [hx₁', hx₂'] using h },
    { simp [hx₁', hx₂'] } }
end

lemma equitable_on_finset_iff_eq_average {s : finset α} {f : α → ℕ} :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 :=
begin
  rw equitable_on_iff_almost_eq_constant,
  refine ⟨_, λ h, ⟨_, h⟩ ⟩,
  rintro ⟨b, hb⟩,
  by_cases h : ∀ a ∈ s, f a = b + 1,
  { clear hb,
    intros a ha,
    left,
    symmetry,
    apply nat.div_eq_of_eq_mul_left (finset.card_pos.2 ⟨_, ha⟩),
    rw [mul_comm, sum_const_nat],
    intros c hc,
    rw [h _ ha, h _ hc] },
  push_neg at h,
  obtain ⟨x, hx₁, hx₂⟩ := h,
  suffices : b = (∑ i in s, f i) / s.card,
  { simp_rw [←this],
    apply hb },
  simp_rw between_nat_iff at hb,
  symmetry,
  refine nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum (λ a ha, (hb a ha).1)))
    ((sum_lt_sum (λ a ha, (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le _),
  rw [mul_comm, sum_const_nat],
  exact λ _ _, rfl,
end

lemma equitable_on_finset_iff {s : finset α} {f : α → ℕ} :
  equitable_on (s : set α) f ↔
    ∀ a ∈ s, (∑ i in s, f i) / s.card ≤ f a ∧ f a ≤ (∑ i in s, f i) / s.card + 1 :=
by simp_rw [equitable_on_finset_iff_eq_average, between_nat_iff]

/-! ## pairs_finset and pairs_density -/

namespace relation
variables (r : α → α → Prop) [decidable_rel r]

/-- Finset of edges between two finsets of vertices -/
def pairs_finset (U W : finset α) : finset (α × α) :=
(U.product W).filter (λ e, r e.1 e.2)

lemma mem_pairs_finset (U W : finset α) (x : α × α) :
  x ∈ pairs_finset r U W ↔ x.1 ∈ U ∧ x.2 ∈ W ∧ r x.1 x.2 :=
by simp only [pairs_finset, and_assoc, mem_filter, finset.mem_product]

lemma mem_pairs_finset' (U W : finset α) (x y : α) :
  (x, y) ∈ pairs_finset r U W ↔ x ∈ U ∧ y ∈ W ∧ r x y :=
mem_pairs_finset _ _ _ _

lemma pairs_finset_empty_left (W : finset α) :
  pairs_finset r ∅ W = ∅ :=
by rw [pairs_finset, finset.empty_product, filter_empty]

lemma pairs_finset_mono {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_finset r A' B' ⊆ pairs_finset r A B :=
begin
  intro x,
  rw [mem_pairs_finset, mem_pairs_finset],
  exact λ h, ⟨hA h.1, hB h.2.1, h.2.2⟩,
end

section decidable_eq
variable [decidable_eq α]

lemma card_pairs_finset_compl (U W : finset α) :
  (pairs_finset r U W).card + (pairs_finset (λ x y, ¬r x y) U W).card = U.card * W.card :=
begin
  rw [←finset.card_product, pairs_finset, pairs_finset, ←finset.card_union_eq,
    finset.filter_union_filter_neg_eq],
  rw finset.disjoint_filter,
  exact λ x _, not_not.2,
end

lemma pairs_finset_disjoint_left {U U' : finset α} (hU : disjoint U U') (W : finset α) :
  disjoint (pairs_finset r U W) (pairs_finset r U' W) :=
begin
  rw [disjoint_iff_inter_eq_empty, ←subset_empty] at ⊢ hU,
  rintro x hx,
  rw [mem_inter, mem_pairs_finset, mem_pairs_finset] at hx,
  exact hU (mem_inter.2 ⟨hx.1.1, hx.2.1⟩),
end

lemma pairs_finset_disjoint_right (U : finset α) {W W' : finset α} (hW : disjoint W W') :
  disjoint (pairs_finset r U W) (pairs_finset r U W') :=
begin
  rw [disjoint_iff_inter_eq_empty, ←subset_empty] at ⊢ hW,
  rintro x hx,
  rw [mem_inter, mem_pairs_finset, mem_pairs_finset] at hx,
  exact hW (mem_inter.2 ⟨hx.1.2.1, hx.2.2.1⟩),
end

lemma pairs_finset_bUnion_left (A : finset (finset α)) (W : finset α)
  (f : finset α → finset α) :
  pairs_finset r (A.bUnion f) W = A.bUnion (λ a, pairs_finset r (f a) W) :=
by { ext x, simp only [mem_pairs_finset, mem_bUnion, exists_and_distrib_right] }

lemma pairs_finset_bUnion_right (U : finset α) (B : finset (finset α))
  (f : finset α → finset α) :
  pairs_finset r U (B.bUnion f) = B.bUnion (λ b, pairs_finset r U (f b)) :=
begin
  ext x,
  simp only [mem_pairs_finset, mem_bUnion, exists_prop],
  simp only [←and_assoc, exists_and_distrib_right, @and.right_comm _ (x.fst ∈ U)],
  rw [and_comm (x.fst ∈ U), and.right_comm],
end

lemma pairs_finset_bUnion (A B : finset (finset α)) (f g : finset α → finset α) :
  pairs_finset r (A.bUnion f) (B.bUnion g) =
  (A.product B).bUnion (λ ab, pairs_finset r (f ab.1) (g ab.2)) :=
by simp_rw [product_bUnion, pairs_finset_bUnion_left, pairs_finset_bUnion_right]

end decidable_eq

/-- Number of edges between two finsets of vertices -/
def pairs_count (U W : finset α) : ℕ :=
(pairs_finset r U W).card

lemma pairs_count_le_mul (U W : finset α) :
  pairs_count r U W ≤ U.card * W.card :=
begin
  rw [pairs_count, pairs_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

/-- Edge density between two finsets of vertices -/
noncomputable def pairs_density (U W : finset α) : ℝ :=
pairs_count r U W / (U.card * W.card)

lemma pairs_density_nonneg (U W : finset α) :
  0 ≤ pairs_density r U W :=
by { apply div_nonneg; exact_mod_cast nat.zero_le _ }

lemma pairs_density_le_one (U W : finset α) :
  pairs_density r U W ≤ 1 :=
begin
  refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
  norm_cast,
  exact pairs_count_le_mul r U W,
end

lemma pairs_density_compl [decidable_eq α] {U W : finset α} (hU : U.nonempty) (hW : W.nonempty) :
  pairs_density r U W + pairs_density (λ x y, ¬r x y) U W = 1 :=
begin
  have h : ((U.card * W.card : ℕ) : ℝ) ≠ 0 := nat.cast_ne_zero.2 (mul_pos (finset.card_pos.2 hU)
    (finset.card_pos.2 hW)).ne.symm,
  rw [pairs_density, pairs_density, div_add_div_same, ←nat.cast_mul, div_eq_iff h, one_mul],
  exact_mod_cast card_pairs_finset_compl r U W,
end

lemma pairs_density_empty_left (W : finset α) :
  pairs_density r ∅ W = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, zero_mul, div_zero]

lemma pairs_density_empty_right (U : finset α) :
  pairs_density r U ∅ = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, mul_zero, div_zero]

section symmetric
variables {r} (hr : symmetric r)
include hr

lemma mem_pairs_finset_comm (U W : finset α) (x y : α) :
  (x, y) ∈ pairs_finset r U W ↔ (y, x) ∈ pairs_finset r W U :=
begin
  rw [mem_pairs_finset', mem_pairs_finset'],
  split; exact λ h, ⟨h.2.1, h.1, hr h.2.2⟩,
end

lemma pairs_count_comm (U W : finset α) :
  pairs_count r U W = pairs_count r W U :=
begin
  apply finset.card_congr (λ (i : α × α) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    rw mem_pairs_finset_comm hr,
    exact h },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  rintro ⟨i, j⟩ h,
  refine ⟨⟨j, i⟩, _, rfl⟩,
  rw mem_pairs_finset_comm hr,
  exact h,
end

lemma pairs_density_comm (U W : finset α) : pairs_density r U W = pairs_density r W U :=
by rw [pairs_density, mul_comm, pairs_count_comm hr, pairs_density]

end symmetric

end relation

/-! ## Specialization to `simple_graph` -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj]

open relation

def edge_count (U W : finset α) : ℝ :=
(pairs_finset G.adj U W).card

/- Remnants of what's now under `relation`. The only point for keeping it is to sometimes avoid
writing `G.adj` and `G.sym` sometimes. -/
/-- Edge density between two finsets of vertices -/
noncomputable def edge_density : finset α → finset α → ℝ :=
pairs_density G.adj

lemma edge_density_eq_edge_count_div_card (U W : finset α) :
  G.edge_density U W = G.edge_count U W/(U.card * W.card) := rfl

lemma edge_density_comm (U W : finset α) : G.edge_density U W = G.edge_density W U :=
pairs_density_comm G.sym U W

lemma edge_density_nonneg (U W : finset α) :
  0 ≤ G.edge_density U W :=
pairs_density_nonneg _ U W

lemma edge_density_le_one (U W : finset α) :
  G.edge_density U W ≤ 1 :=
pairs_density_le_one _ U W

end simple_graph

/-! ## is_uniform for simple_graph -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj]

/-- A pair of finsets of vertices is ε-uniform iff their edge density is close to the density of any
big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (ε : ℝ) (U W : finset α) : Prop :=
∀ U', U' ⊆ U → ∀ W', W' ⊆ W → ε * U.card ≤ U'.card → ε * W.card ≤ W'.card →
abs (edge_density G U' W' - edge_density G U W) < ε

/-- If the pair `(U, W)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform_mono {ε ε' : ℝ} {U W : finset α} (h : ε ≤ ε') (hε : is_uniform G ε U W) :
  is_uniform G ε' U W :=
begin
  intros U' hU' W' hW' hU hW,
  refine (hε _ hU' _ hW' (le_trans _ hU) (le_trans _ hW)).trans_le h;
  exact mul_le_mul_of_nonneg_right h (nat.cast_nonneg _),
end

lemma is_uniform_symmetric (ε : ℝ) : symmetric (is_uniform G ε) :=
begin
  intros U W h W' hW' U' hU' hW hU,
  rw [edge_density_comm _ W', edge_density_comm _ W],
  apply h _ hU' _ hW' hU hW,
end

lemma is_uniform_comm (ε : ℝ) {U W : finset α} : is_uniform G ε U W ↔ is_uniform G ε W U :=
⟨λ h, G.is_uniform_symmetric ε h, λ h, G.is_uniform_symmetric ε h⟩

end simple_graph

/-! ## finpartition -/

/-- A finpartition of a finite set `S` is a collection of disjoint subsets of `S` which cover it. -/
@[ext] structure finpartition_on {α : Type u} (s : finset α) :=
(parts : finset (finset α))
(disjoint : ∀ (a₁ a₂ ∈ parts) x, x ∈ a₁ → x ∈ a₂ → a₁ = a₂)
(cover : ∀ ⦃x⦄, x ∈ s → ∃ (a ∈ parts), x ∈ a)
(subset : ∀ ⦃a⦄, a ∈ parts → a ⊆ s)
(not_empty_mem : ∅ ∉ parts)

/-- A `finpartition α` is a partition of the entire finite type `α` -/
abbreviation finpartition (α : Type u) [fintype α] := finpartition_on (univ : finset α)

namespace finpartition_on
variables {s : finset α} (P : finpartition_on s)

/-- The size of a finpartition is its number of parts. -/
protected def size : ℕ := P.parts.card

lemma size_eq_card_parts : P.size = P.parts.card := rfl

lemma disjoint' [decidable_eq α] (a₁ : finset α) (ha₁ : a₁ ∈ P.parts) (a₂ : finset α)
  (ha₂ : a₂ ∈ P.parts)
  (h : a₁ ≠ a₂) :
  _root_.disjoint a₁ a₂ :=
begin
  rintro x hx,
  rw [inf_eq_inter, mem_inter] at hx,
  exact h (P.disjoint a₁ a₂ ha₁ ha₂ x hx.1 hx.2),
end

lemma nonempty_of_mem_parts {a : finset α} (ha : a ∈ P.parts) : a.nonempty :=
begin
  rw nonempty_iff_ne_empty,
  rintro rfl,
  exact P.not_empty_mem ha,
end

lemma nonempty_parts_iff : P.parts.nonempty ↔ s.nonempty :=
begin
  refine ⟨λ ⟨a, ha⟩, (P.nonempty_of_mem_parts ha).mono (P.subset ha), _⟩,
  rintro ⟨x, hx⟩,
  obtain ⟨a, ha, -⟩ := P.cover hx,
  exact ⟨a, ha⟩,
end

lemma empty_parts_iff : P.parts = ∅ ↔ s = ∅ :=
by rw [←not_iff_not, ←ne.def, ←nonempty_iff_ne_empty, nonempty_parts_iff, nonempty_iff_ne_empty]

variable [decidable_eq α]

lemma bUnion_parts_eq : P.parts.bUnion id = s :=
(bUnion_subset_iff_forall_subset.2 (λ a ha, P.subset ha)).antisymm (λ x hx, mem_bUnion.2
  (P.cover hx))

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  rw ←card_bUnion P.disjoint',
  exact congr_arg finset.card P.bUnion_parts_eq,
end

/-- Given a finpartition `P` of `s` and finpartitions of each part of `P`, this yields the
finpartition that's obtained by -/
def bind (Q : Π i ∈ P.parts, finpartition_on i) : finpartition_on s :=
{ parts := P.parts.attach.bUnion (λ i, (Q i.1 i.2).parts),
  disjoint := λ a b ha hb x hxa hxb, begin
    rw finset.mem_bUnion at ha hb,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb,
    refine (Q A hA).disjoint a b ha _ x hxa hxb,
    have := P.disjoint A B hA hB x ((Q A hA).subset ha hxa) ((Q B hB).subset hb hxb),
    subst this,
    exact hb,
  end,
  cover := begin
    rintro x hx,
    obtain ⟨A, hA, hxA⟩ := P.cover hx,
    obtain ⟨a, ha, hxa⟩ := (Q A hA).cover hxA,
    refine ⟨a, _, hxa⟩,
    rw finset.mem_bUnion,
    exact ⟨⟨A, hA⟩, P.parts.mem_attach _, ha⟩,
  end,
  subset := begin
    rintro a ha,
    rw finset.mem_bUnion at ha,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    exact ((Q A hA).subset ha).trans (P.subset hA),
  end,
  not_empty_mem := λ h, begin
    rw finset.mem_bUnion at h,
    obtain ⟨⟨A, hA⟩, -, h⟩ := h,
    exact (Q A hA).not_empty_mem h,
  end }

lemma mem_bind_parts {Q : Π i ∈ P.parts, finpartition_on i} {a : finset α} :
  a ∈ (P.bind Q).parts ↔ ∃ A hA, a ∈ (Q A hA).parts :=
begin
  rw [bind, mem_bUnion],
  split,
  { rintro ⟨⟨A, hA⟩, -, h⟩,
    exact ⟨A, hA, h⟩ },
  rintro ⟨A, hA, h⟩,
  exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩,
end

lemma bind_size (Q : Π i ∈ P.parts, finpartition_on i) :
  (P.bind Q).size = ∑ A in P.parts.attach, (Q _ A.2).size :=
begin
  apply card_bUnion,
  rintro ⟨A, hA⟩ - ⟨B, hB⟩ - hAB c,
  rw [inf_eq_inter, mem_inter],
  rintro ⟨hcA, hcB⟩,
  apply hAB,
  rw subtype.mk_eq_mk,
  obtain ⟨x, hx⟩ := nonempty_of_mem_parts _ hcA,
  exact P.disjoint _ _ hA hB x (finpartition_on.subset _ hcA hx)
    (finpartition_on.subset _ hcB hx),
end

end finpartition_on

namespace finpartition
variables [fintype α] (P : finpartition α)

lemma parts_nonempty [nonempty α] : P.parts.nonempty :=
P.nonempty_parts_iff.2 univ_nonempty

end finpartition

/-! # pairs_count with finpartition -/

namespace relation
variables [decidable_eq α] {r : α → α → Prop} [decidable_rel r]

lemma pairs_count_finpartition_left {U : finset α} (P : finpartition_on U) (W : finset α) :
  pairs_count r U W = ∑ a in P.parts, pairs_count r a W :=
begin
  unfold pairs_count,
  simp_rw [←P.bUnion_parts_eq, pairs_finset_bUnion_left, id],
  rw card_bUnion,
  exact λ x hx y hy h, pairs_finset_disjoint_left r (P.disjoint' x hx y hy h) _,
end

lemma pairs_count_finpartition_right (U : finset α) {W : finset α} (P : finpartition_on W) :
  pairs_count r U W = ∑ b in P.parts, pairs_count r U b :=
begin
  unfold pairs_count,
  simp_rw [←P.bUnion_parts_eq, pairs_finset_bUnion_right, id],
  rw card_bUnion,
  exact λ x hx y hy h, pairs_finset_disjoint_right r _ (P.disjoint' x hx y hy h),
end

lemma pairs_count_finpartition {U W : finset α} (P : finpartition_on U) (Q : finpartition_on W) :
  pairs_count r U W = ∑ ab in P.parts.product Q.parts, pairs_count r ab.1 ab.2 :=
by simp_rw [pairs_count_finpartition_left P, pairs_count_finpartition_right _ Q, sum_product]

end relation

/-! ## finpartition_on.is_uniform -/

namespace finpartition_on
variables {s : finset α} (P : finpartition_on s) (G : simple_graph α)
open_locale classical

noncomputable def non_uniform_pairs (ε : ℝ) :
  finset (finset α × finset α) :=
(P.parts.product P.parts).filter (λ UW, UW.1 ≠ UW.2 ∧ ¬G.is_uniform ε UW.1 UW.2)

lemma mem_non_uniform_pairs (U W : finset α) (ε : ℝ) :
  (U, W) ∈ P.non_uniform_pairs G ε ↔ U ∈ P.parts ∧ W ∈ P.parts ∧ U ≠ W ∧
  ¬G.is_uniform ε U W :=
by rw [non_uniform_pairs, mem_filter, mem_product, and_assoc]

/-- An finpartition is `ε-uniform` iff at most a proportion of `ε` of its pairs of parts are not
`ε-uniform`. -/
def is_uniform (ε : ℝ) : Prop :=
((P.non_uniform_pairs G ε).card : ℝ) ≤ ε * (P.size * (P.size - 1) : ℕ)

lemma empty_is_uniform {P : finpartition_on s} (hP : P.parts = ∅) (G : simple_graph α) (ε : ℝ) :
  P.is_uniform G ε :=
by rw [finpartition_on.is_uniform, finpartition_on.non_uniform_pairs, finpartition_on.size, hP,
  empty_product, filter_empty, finset.card_empty, finset.card_empty, mul_zero, nat.cast_zero,
  mul_zero]

end finpartition_on

/-! ## is_equipartition -/

namespace finpartition_on
variables {s : finset α} (P : finpartition_on s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def is_equipartition : Prop :=
equitable_on (P.parts : set (finset α)) card

lemma is_equipartition_iff_card_parts_eq_average [decidable_eq α] :
  P.is_equipartition ↔
  ∀ a : finset α, a ∈ P.parts → a.card = s.card/P.size ∨ a.card = s.card/P.size + 1 :=
begin
  simp_rw [is_equipartition, equitable_on_finset_iff_eq_average, ←card_bUnion P.disjoint',
    ←P.bUnion_parts_eq],
  refl,
end

end finpartition_on

lemma finpartition.is_equipartition_iff_card_parts_eq_average [decidable_eq α] [fintype α]
  {P : finpartition α} :
  P.is_equipartition ↔
    ∀ a : finset α, a ∈ P.parts → a.card = card α/P.size ∨ a.card = card α/P.size + 1 :=
by rw [P.is_equipartition_iff_card_parts_eq_average, card_univ]

/-! ### Discrete and indiscrete finpartition -/

/-- The discrete equipartition of a fintype is the partition in singletons. -/
@[simps]
def discrete_finpartition_on [decidable_eq α] (s : finset α) : finpartition_on s :=
{ parts := s.image singleton,
  disjoint :=
  begin
    simp only [mem_image, exists_true_left, exists_imp_distrib],
    rintro a₁ a₂ i hi rfl j hj rfl k,
    simp only [mem_singleton],
    rintro rfl rfl,
    refl
  end,
  cover := λ v hv, ⟨{v}, mem_image.2 ⟨v, hv, rfl⟩, finset.mem_singleton_self v⟩,
  subset := by simp,
  not_empty_mem := λ h, begin
    obtain ⟨x, _, hx⟩ := mem_image.1 h,
    exact singleton_ne_empty _ hx,
  end }

@[simps]
def indiscrete_finpartition_on {s : finset α} (hs : s.nonempty) :
  finpartition_on s :=
{ parts := {s},
  disjoint :=
  begin
    simp only [mem_singleton],
    rintro _ _ rfl rfl _ _ _,
    refl
  end,
  cover := λ u hu, ⟨s, mem_singleton_self _, hu⟩,
  subset := by simp only [forall_eq, subset.refl, mem_singleton],
  not_empty_mem := λ h, hs.ne_empty (mem_singleton.1 h).symm }

namespace discrete_finpartition_on
variables [decidable_eq α] (s : finset α) (G : simple_graph α)

lemma is_equipartition : (discrete_finpartition_on s).is_equipartition :=
equitable_on_iff_almost_eq_constant.2 ⟨1, by simp⟩

protected lemma size : (discrete_finpartition_on s).size = s.card :=
begin
  change finset.card (s.image _) = _,
  rw [finset.card_image_of_injective],
  exact λ a b, singleton_inj.1,
end

lemma non_uniform_pairs {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition_on s).non_uniform_pairs G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨U, W⟩,
  simp only [finpartition_on.mem_non_uniform_pairs, discrete_finpartition_on_parts, mem_image,
    and_imp, exists_prop, not_and, not_not, ne.def, exists_imp_distrib],
  rintro x hx rfl y hy rfl h U' hU' W' hW' hU hW,
  rw [card_singleton, nat.cast_one, mul_one] at hU hW,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty] at hU,
    exact (hε.not_le hU).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hW',
  { rw [finset.card_empty] at hW,
    exact (hε.not_le hW).elim },
  rwa [sub_self, abs_zero],
end

lemma is_uniform {ε : ℝ} (hε : 0 < ε) :
  (discrete_finpartition_on s).is_uniform G ε :=
begin
  rw [finpartition_on.is_uniform, discrete_finpartition_on.size, non_uniform_pairs _ _ hε,
    finset.card_empty, nat.cast_zero],
  exact mul_nonneg hε.le (nat.cast_nonneg _),
end

end discrete_finpartition_on
