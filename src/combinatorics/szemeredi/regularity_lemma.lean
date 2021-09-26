/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import combinatorics.choose.bounds
import order.iterate

/-!
# Szemerédi's Regularity Lemma

In this file, we define edge density, equipartitions, and prove Szemerédi's Regularity Lemma.
-/

universe u

open_locale big_operators
open finset fintype function relation

variables {α : Type*}

/-! ### Prerequisites for SRL -/

namespace finset
variable [decidable_pred (λ (ab : α × α), well_ordering_rel ab.fst ab.snd)]

/-- Pairs of parts. We exclude the diagonal, as these do not make sense nor
behave well in the context of Szemerédi's Regularity Lemma. -/
def distinct_pairs (s : finset α) :
  finset (α × α) :=
(s.product s).filter (λ ab, well_ordering_rel ab.1 ab.2)

variable {s : finset α}

lemma mem_distinct_pairs (a b : α) :
  (a, b) ∈ s.distinct_pairs ↔ a ∈ s ∧ b ∈ s ∧ well_ordering_rel a b :=
by rw [distinct_pairs, mem_filter, mem_product, and_assoc]

lemma distinct_pairs_card [decidable_eq α] :
  s.distinct_pairs.card = s.card.choose 2 :=
begin
  rw ←prod_quotient_sym2_not_diag,
  refine card_congr (λ a ha, ⟦a⟧) _ _ _,
  { rintro ⟨a₁, a₂⟩ ha,
    rw [mem_distinct_pairs] at ha,
    simp only [mem_filter, sym2.is_diag_iff_proj_eq],
    refine ⟨mem_image_of_mem _ (by simp [ha.1, ha.2]), _⟩,
    apply ne_of_irrefl ha.2.2 },
  { rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
    simp only [mem_distinct_pairs, and_imp, prod.mk.inj_iff, sym2.eq_iff],
    rintro - - ha₁₂ hb₁ hb₂ hb₁₂ (i | ⟨rfl, rfl⟩),
    { exact i },
    { apply (asymm ha₁₂ hb₁₂).elim } },
  { refine quotient.ind _,
    simp only [prod.forall, mem_filter, sym2.is_diag_iff_proj_eq, exists_prop, and_imp,
      prod.exists, mem_distinct_pairs, and_assoc],
    intros a b h dif,
    obtain ⟨_, _⟩ : a ∈ s ∧ b ∈ s,
    { simp only [sym2.eq_iff, mem_image, exists_prop, mem_product, prod.exists, and_assoc] at h,
      rcases h with ⟨a, b, ha, hb, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩;
      exact ⟨‹_›, ‹_›⟩ },
    rcases trichotomous_of well_ordering_rel a b with lt | rfl | gt,
    { exact ⟨_, _, ‹a ∈ s›, ‹b ∈ s›, lt, rfl⟩ },
    { exact (dif rfl).elim },
    { exact ⟨_, _, ‹b ∈ s›, ‹a ∈ s›, gt, sym2.eq_swap⟩, } }
end

end finset

open finset

section relation
variables (r : α → α → Prop) [decidable_rel r]

lemma lemmaB {s t : finset α} (hst : s ⊆ t) (f : α → ℝ) {a b : ℝ}
  (hs : (∑ x in s, f x)/s.card = a + b) (ht : (∑ x in t, f x) / t.card = a) :
  a^2 + s.card/t.card * b^2 ≤ (∑ x in t, f x^2)/t.card :=
begin
  obtain htcard | htcard := (t.card.cast_nonneg : (0 : ℝ) ≤ t.card).eq_or_lt,
  { rw [←ht, ←htcard, div_zero, div_zero, div_zero, zero_mul, add_zero, pow_succ, zero_mul] },
  obtain hscard | hscard := (s.card.cast_nonneg : (0 : ℝ) ≤ s.card).eq_or_lt,
  { rw [←hscard, zero_div, zero_mul, add_zero, ←ht, le_div_iff htcard, div_pow, sq (t.card : ℝ),
      div_mul_eq_mul_div_comm, div_self_mul_self', mul_inv_le_iff htcard],
    simpa using sum_mul_sq_le_sq_mul_sq t (λ _, 1) f },
  have htzero : (t.card : ℝ) ≠ 0 := htcard.ne',
  have hszero : (s.card : ℝ) ≠ 0 := hscard.ne',
  rw div_eq_iff htzero at ht,
  rw div_eq_iff hszero at hs,
  suffices h : (∑ x in s, (f x - a))^2 ≤ s.card * (∑ x in t, (f x - a)^2),
  { apply le_of_mul_le_mul_left _ htcard,
    rw [mul_add, ←mul_assoc, mul_div_cancel' _ htzero, mul_div_cancel' _ htzero,
      ←le_sub_iff_add_le'],
    apply le_of_mul_le_mul_left _ hscard,
    rw [←mul_assoc, ←sq],
    simp_rw sub_sq at h,
    rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ←sum_mul, ←mul_sum, sum_const,
      sum_const, ht, hs, nsmul_eq_mul, nsmul_eq_mul, mul_comm (a + b), ←mul_sub, add_sub_cancel',
    mul_pow] at h,
    convert h,
    ring },
  have cs := sum_mul_sq_le_sq_mul_sq s (λ _, 1) (λ x, f x - a),
  simp only [one_pow, one_mul, nsmul_eq_mul, sum_const, nat.smul_one_eq_coe] at cs,
  apply cs.trans _,
  rw mul_le_mul_left hscard,
  exact sum_le_sum_of_subset_of_nonneg hst (λ i _ _, sq_nonneg _),
end

lemma aux₀ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
 (A'.card : ℝ)/A.card * (B'.card/B.card) * pairs_density r A' B' ≤ pairs_density r A B :=
begin
  obtain hA' | hA' := nat.eq_zero_or_pos A'.card,
  { rw [hA', nat.cast_zero, zero_div, zero_mul, zero_mul],
    exact pairs_density_nonneg r A B },
  obtain hB' | hB' := nat.eq_zero_or_pos B'.card,
  { rw [hB', nat.cast_zero, zero_div, mul_zero, zero_mul],
    exact pairs_density_nonneg r A B },
  have hAB' : (0 : ℝ) < A'.card * B'.card := by exact_mod_cast mul_pos hA' hB',
  have hAB : (0 : ℝ) < A.card * B.card := by exact_mod_cast mul_pos (hA'.trans_le
    (finset.card_le_of_subset hA)) (hB'.trans_le (finset.card_le_of_subset hB)),
  rw [pairs_density, pairs_density, div_mul_div, mul_comm, div_mul_div_cancel _ hAB'.ne',
    div_le_div_right hAB, nat.cast_le],
  exact finset.card_le_of_subset (pairs_finset_mono r hA hB),
end

lemma aux₁ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_density r A' B' - pairs_density r A B ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
calc
  pairs_density r A' B' - pairs_density r A B
      ≤ pairs_density r A' B' - A'.card/A.card * (B'.card/B.card) * pairs_density r A' B'
      : sub_le_sub_left (aux₀ r hA hB) _
  ... = (1 - A'.card/A.card * (B'.card/B.card)) * pairs_density r A' B'
      : by rw [sub_mul, one_mul]
  ... ≤ 1 - A'.card/A.card * (B'.card/B.card)
      : begin
          convert mul_le_mul_of_nonneg_left (pairs_density_le_one r _ _) _,
          { rw mul_one },
          apply sub_nonneg_of_le,
          apply mul_le_one, swap,
          apply div_nonneg,
          exact nat.cast_nonneg _,
          exact nat.cast_nonneg _,
          apply div_le_one_of_le,
          rw nat.cast_le,
          exact finset.card_le_of_subset hA,
          exact nat.cast_nonneg _,
          apply div_le_one_of_le,
          rw nat.cast_le,
          exact finset.card_le_of_subset hB,
          exact nat.cast_nonneg _,
        end

variable [decidable_eq α]

lemma aux₂ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 1 - (A'.card : ℝ)/A.card * (B'.card/B.card) :=
begin
  have habs : abs (pairs_density r A' B' - pairs_density r A B) ≤ 1,
  { rw [abs_sub_le_iff, ←sub_zero (1 : ℝ)],
    split; exact sub_le_sub (pairs_density_le_one r _ _) (pairs_density_nonneg r _ _) },
  obtain hA' | hA' := nat.eq_zero_or_pos A'.card,
  { rw [hA', nat.cast_zero, zero_div, zero_mul, sub_zero],
    exact habs },
  obtain hB' | hB' := nat.eq_zero_or_pos B'.card,
  { rw [hB', nat.cast_zero, zero_div, mul_zero, sub_zero],
    exact habs },
  rw finset.card_pos at hA' hB',
  refine abs_sub_le_iff.2 ⟨aux₁ r hA hB, _⟩,
  rw [←add_sub_cancel (pairs_density r A B) (pairs_density (λ x y, ¬r x y) A B),
    ←add_sub_cancel (pairs_density r A' B') (pairs_density (λ x y, ¬r x y) A' B'),
    pairs_density_compl _ (hA'.mono hA) (hB'.mono hB), pairs_density_compl _ hA' hB',
    sub_sub_sub_cancel_left],
  exact aux₁ _ hA hB,
end

lemma aux₃ {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2*δ - δ^2 :=
begin
  have hδ' : 0 ≤ 2 * δ - δ ^ 2,
  { rw [sub_nonneg, sq],
    refine mul_le_mul_of_nonneg_right (hδ₁.le.trans _) hδ₀,
    norm_num },
  rw ←sub_pos at hδ₁,
  obtain hA' | hA'pos := (nat.cast_nonneg A'.card).eq_or_lt,
  { rw ←hA' at hAcard,
    rwa [pairs_density, pairs_density, ←hA', (nonpos_of_mul_nonpos_left hAcard hδ₁).antisymm
      (nat.cast_nonneg _), zero_mul, zero_mul, div_zero, div_zero, sub_zero, abs_zero] },
  obtain hB' | hB'pos := (nat.cast_nonneg B'.card).eq_or_lt,
  { rw ←hB' at hBcard,
    rwa [pairs_density, pairs_density, ←hB', (nonpos_of_mul_nonpos_left hBcard hδ₁).antisymm
      (nat.cast_nonneg _), mul_zero, mul_zero, div_zero, div_zero, sub_zero, abs_zero] },
  have hApos : (0 : ℝ) < A.card := hA'pos.trans_le (nat.cast_le.2 (finset.card_le_of_subset hA)),
  have hBpos : (0 : ℝ) < B.card := hB'pos.trans_le (nat.cast_le.2 (finset.card_le_of_subset hB)),
  calc
    abs (pairs_density r A' B' - pairs_density r A B)
        ≤ 1 - A'.card/A.card * (B'.card/B.card)
        : aux₂ r hA hB
    ... ≤ 1 - (1 - δ) * (1 - δ)
        : sub_le_sub_left (mul_le_mul ((le_div_iff hApos).2 hAcard) ((le_div_iff hBpos).2
            hBcard) hδ₁.le (div_nonneg hA'pos.le hApos.le)) 1
    ... = 2*δ - δ^2
        : by ring,
end

lemma LemmaA {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) {δ : ℝ} (hδ : 0 ≤ δ)
  (hAcard : (1 - δ) * A.card ≤ A'.card) (hBcard : (1 - δ) * B.card ≤ B'.card) :
  abs (pairs_density r A' B' - pairs_density r A B) ≤ 2 * δ :=
begin
  cases le_or_lt 1 δ,
  { refine (abs_sub _ _).trans _,
    rw [abs_of_nonneg (pairs_density_nonneg r _ _), abs_of_nonneg (pairs_density_nonneg r A B),
      two_mul],
    exact add_le_add ((pairs_density_le_one r _ _).trans h)
      ((pairs_density_le_one r A B).trans h) },
  exact (aux₃ r hA hB hδ h hAcard hBcard).trans ((sub_le_self_iff _).2 (sq_nonneg δ)),
end

end relation

namespace simple_graph
variables (G : simple_graph α)
open_locale classical

/- Extracts a witness of the non-uniformity of `(U, W)`. Witnesses for `(U, W)` and `(W, U)` don't
necessarily match. Hence the motivation to define `witness`. -/
noncomputable def witness_aux (ε : ℝ) (U W : finset α) : finset α × finset α :=
dite (U = W ∨ G.is_uniform ε U W) (λ _, (U, W)) (λ h, begin
    unfold is_uniform at h,
    push_neg at h,
    exact (classical.some h.2, classical.some (classical.some_spec h.2).2),
  end)

/- Extracts a witness of the non-uniformity of `(U, W)`. It uses an arbitrary ordering of
`finset α` (`well_ordering_rel`) to ensure that the witnesses of `(U, W)` and `(W, U)` are related
(the existentials don't ensure we would take the same from `¬G.is_uniform ε U W` and
`¬G.is_uniform ε W U`). -/
noncomputable def witness (ε : ℝ) (U W : finset α) : finset α × finset α :=
ite (well_ordering_rel U W) (G.witness_aux ε U W) (G.witness_aux ε W U).swap

lemma witness_comm (ε : ℝ) (U W : finset α) :
  G.witness ε U W = (G.witness ε W U).swap :=
begin
  unfold witness,
  obtain h | rfl | h := trichotomous_of well_ordering_rel U W,
  { rw [if_pos h, if_neg (asymm h), prod.swap_swap] },
  { rw [witness_aux, if_neg, dif_pos (or.intro_left _ rfl), prod.swap],
    exact _root_.irrefl _ },
  rw [if_pos h, if_neg (asymm h)],
end

end simple_graph

open simple_graph

namespace finpartition_on
variables {s : finset α} (P : finpartition_on s) (G : simple_graph α)
open_locale classical

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_half` ensures this process only happens finitely many times. -/
noncomputable def index (P : finpartition_on s) : ℝ :=
(∑ UW in P.parts.distinct_pairs, G.edge_density UW.1 UW.2^2)/P.size^2

lemma index_nonneg (P : finpartition_on s) :
  0 ≤ P.index G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

lemma index_le_half (P : finpartition_on s) :
  P.index G ≤ 1/2 :=
begin
  rw finpartition_on.index,
  apply div_le_of_nonneg_of_le_mul (sq_nonneg _),
  { norm_num },
  suffices h : (∑ UW in P.parts.distinct_pairs, G.edge_density UW.1 UW.2^2) ≤
    P.parts.distinct_pairs.card,
  { apply h.trans,
    rw [distinct_pairs_card, div_mul_eq_mul_div, one_mul],
    convert choose_le_pow 2 _,
    norm_num },
  rw [finset.card_eq_sum_ones, nat.cast_sum, nat.cast_one],
  refine finset.sum_le_sum (λ s _, _),
  rw [sq, ←abs_le_one_iff_mul_self_le_one, abs_eq_self.2 (G.edge_density_nonneg _ _)],
  exact G.edge_density_le_one _ _,
end

end finpartition_on

def has_subset.subset.finpartition_on [decidable_eq α] {s : finset α}
  {P : finpartition_on s} {A : finset (finset α)} (h : A ⊆ P.parts) :
  finpartition_on (A.bUnion id) :=
{ parts := A,
  disjoint := λ a b ha hb, P.disjoint a b (h ha) (h hb),
  cover := λ x hx, mem_bUnion.1 hx,
  subset := λ a, subset_bUnion_of_mem _,
  not_empty_mem := λ hA, P.not_empty_mem (h hA) }

lemma has_subset.subset.finpartition_on_parts [decidable_eq α] {s : finset α}
  {P : finpartition_on s} {A : finset (finset α)} (h : A ⊆ P.parts) :
  h.finpartition_on.parts = A := rfl

open finpartition_on

section
variables [decidable_eq α] {s : finset α}

lemma mk_equitable_aux1 {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (subs : ∀ i ∈ A, i ⊆ s) (h : s = ∅) :
  ∃ (P : finset (finset α)),
    (∀ (x : finset α), x ∈ P → x.card = m ∨ x.card = m+1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    (∀ x ∈ s, ∃ y ∈ P, x ∈ y) ∧
    (∀ (x₁ x₂ ∈ P) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂) ∧
    (∀ x ∈ P, x ⊆ s) ∧
    ((P.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  subst h,
  simp only [finset.subset_empty] at subs,
  simp only [finset.card_empty, nat.mul_eq_zero, nat.succ_ne_zero, or_false,
    add_eq_zero_iff, and_false] at hs,
  refine ⟨∅, by simp, λ i hi, by simp [subs i hi], by simp [hs.2]⟩,
end

lemma mk_equitable_aux2 {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (subs : ∀ i ∈ A, i ⊆ s) (h : m = 0) :
  ∃ (P : finset (finset α)),
    (∀ (x : finset α), x ∈ P → x.card = m ∨ x.card = m+1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    (∀ x ∈ s, ∃ y ∈ P, x ∈ y) ∧
    (∀ (x₁ x₂ ∈ P) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂) ∧
    (∀ x ∈ P, x ⊆ s) ∧
    ((P.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  subst h,
  simp only [mul_one, zero_add, mul_zero] at hs,
  simp only [exists_prop, card_eq_zero, zero_add, le_zero_iff, sdiff_eq_empty_iff_subset],
  refine ⟨s.image singleton, by simp, _, by simp, _, by simp, _⟩,
  { intros x hx i hi,
    simp only [mem_bUnion, mem_image, exists_prop, mem_filter, id.def],
    refine ⟨{i}, ⟨⟨i, subs x hx hi, rfl⟩, by simpa⟩, by simp⟩ },
  { simp only [mem_image, and_imp, exists_prop, exists_imp_distrib],
    rintro _ _ x _ rfl y _ rfl,
    simp [singleton_inj] },
  { simp only [mem_image, and_imp, filter_true_of_mem, implies_true_iff, eq_self_iff_true,
      forall_apply_eq_imp_iff₂, exists_imp_distrib, card_singleton],
    rw [card_image_of_injective, hs],
    intros _ _ t,
    rwa singleton_inj at t }
end

lemma mk_equitable_aux {m a b : ℕ} (hs : a*m + b*(m+1) = s.card) (A : finset (finset α))
  (all : ∀ x ∈ s, ∃ y ∈ A, x ∈ y)
  (disj : ∀ (x₁ x₂ ∈ A) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂)
  (subs : ∀ i ∈ A, i ⊆ s) :
  ∃ (P : finset (finset α)),
    (∀ (x : finset α), x ∈ P → x.card = m ∨ x.card = m + 1) ∧
    (∀ x, x ∈ A → (x \ finset.bUnion (P.filter (λ y, y ⊆ x)) id).card ≤ m) ∧
    (∀ x ∈ s, ∃ y ∈ P, x ∈ y) ∧
    (∀ (x₁ x₂ ∈ P) i, i ∈ x₁ → i ∈ x₂ → x₁ = x₂) ∧
    (∀ x ∈ P, x ⊆ s) ∧
    ((P.filter (λ i, finset.card i = m+1)).card = b) :=
begin
  induction s using finset.strong_induction with s ih generalizing A a b,
  cases s.eq_empty_or_nonempty with h hs_ne,
  { exact mk_equitable_aux1 hs A subs h },
  cases (nat.eq_zero_or_pos m) with h m_pos,
  { exact mk_equitable_aux2 hs A subs h },
  have : 0 < a ∨ 0 < b,
  { by_contra,
    push_neg at h,
    simp only [le_zero_iff] at h,
    rw [h.1, h.2] at hs,
    simp only [add_zero, zero_mul, eq_comm, card_eq_zero] at hs,
    exact hs_ne.ne_empty hs },
  set p'_size := if 0 < a then m else m+1 with h',
  have : 0 < p'_size,
  { rw h',
    split_ifs,
    { apply m_pos },
    exact nat.succ_pos' },
  by_cases ∃ p ∈ A, m+1 ≤ finset.card p,
  { rcases h with ⟨p, hp₁, hp₂⟩,
    have : p'_size ≤ p.card,
    { apply le_trans _ hp₂,
      rw h',
      split_ifs,
      { apply nat.le_succ },
      refl },
    obtain ⟨p', hp'₁, hp'₂⟩ := exists_smaller_set _ _ this,
    have : p'.nonempty,
    { rwa [←card_pos, hp'₂] },
    obtain ⟨P', hP'₁, hP'₂, hP'₃, hP'₄, hP'₅, hP'₆⟩ :=
      @ih (s \ p')
      (sdiff_ssubset (finset.subset.trans hp'₁ (subs _ hp₁)) ‹p'.nonempty›)
      (insert (p \ p') (A.erase p))
      (if 0 < a then a-1 else a)
      (if 0 < a then b else b-1)
      _ _ _ _,
    rotate,
    { rw [card_sdiff (finset.subset.trans hp'₁ (subs _ hp₁)), ←hs, hp'₂, h'],
      split_ifs,
      { rw [nat.mul_sub_right_distrib, one_mul,
          nat.sub_add_eq_add_sub (nat.le_mul_of_pos_left h)] },
      { rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
        apply nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left h) } },
    { simp only [and_imp, exists_prop, mem_insert, mem_sdiff, mem_erase, ne.def],
      intros x hx₁ hx₂,
      by_cases x ∈ p,
      { refine ⟨p \ p', or.inl rfl, by simp only [hx₂, h, mem_sdiff, not_false_iff, and_self]⟩ },
    obtain ⟨y, hy₁, hy₂⟩ := all x hx₁,
      refine ⟨y, or.inr ⟨λ t, _, hy₁⟩, hy₂⟩,
      apply h,
      rw ←t,
      exact hy₂ },
    { simp only [mem_insert, mem_erase, ne.def],
      rintro x₁ x₂ (rfl | hx₁) (rfl | hx₂) i hi₁ hi₂,
      { refl },
      { apply (hx₂.1 (disj _ _ hx₂.2 hp₁ i hi₂ (sdiff_subset _ _ hi₁))).elim },
      { apply (hx₁.1 (disj _ _ hx₁.2 hp₁ i hi₁ (sdiff_subset _ _ hi₂))).elim },
      exact disj _ _ hx₁.2 hx₂.2 _ hi₁ hi₂ },
    { simp only [and_imp, mem_insert, forall_eq_or_imp, mem_erase, ne.def],
      split,
      { apply sdiff_subset_sdiff (subs _ hp₁) (refl _) },
      intros i hi₁ hi₂ x hx,
      simp only [mem_sdiff, subs i hi₂ hx, true_and],
      exact λ q, hi₁ (disj _ _ hi₂ hp₁ _ hx (hp'₁ q)) },
    refine ⟨insert p' P', _, _, _, _, _, _⟩,
    { simp only [mem_insert, forall_eq_or_imp, and_iff_left hP'₁, hp'₂, h'],
      split_ifs,
      { left, refl },
      { right, refl } },
    { conv in (_ ∈ _) {rw ←finset.insert_erase hp₁},
      simp only [and_imp, mem_insert, forall_eq_or_imp, ne.def],
      split,
      { simp only [filter_insert, if_pos hp'₁, bUnion_insert, mem_erase],
        apply le_trans (card_le_of_subset _) (hP'₂ (p \ p') (mem_insert_self _ _)),
        intros i,
        simp only [not_exists, mem_bUnion, and_imp, mem_union, mem_filter, mem_sdiff, id.def,
          not_or_distrib],
        intros hi₁ hi₂ hi₃,
        refine ⟨⟨hi₁, hi₂⟩, λ x hx hx', hi₃ _ hx (finset.subset.trans hx' (sdiff_subset _ _))⟩ },
      intros x hx,
      apply (card_le_of_subset _).trans (hP'₂ x (mem_insert_of_mem hx)),
      apply sdiff_subset_sdiff (finset.subset.refl _) (bUnion_subset_bUnion_of_subset_left _ _),
      refine filter_subset_filter _ (subset_insert _ _) },
    { simp only [and_imp, exists_prop, mem_sdiff] at hP'₃,
      simp only [exists_prop, mem_insert, or_and_distrib_right, exists_or_distrib],
      intros x hx,
      refine if h : x ∈ p' then or.inl ⟨_, rfl, h⟩ else or.inr (hP'₃ _ hx h) },
    { simp only [mem_insert, forall_eq_or_imp],
      rintro x₁ x₂ (rfl | hx₁) (rfl | hx₂),
      { simp },
      { intros i hi₁ hi₂,
        apply ((mem_sdiff.1 (hP'₅ _ hx₂ hi₂)).2 hi₁).elim },
      { intros i hi₁ hi₂,
        apply ((mem_sdiff.1 (hP'₅ _ hx₁ hi₁)).2 hi₂).elim },
      exact hP'₄ _ _ hx₁ hx₂ },
    { simp only [mem_insert, forall_eq_or_imp],
      refine ⟨finset.subset.trans hp'₁ (subs _ hp₁),
        λ x hx i hi, (mem_sdiff.1 (hP'₅ x hx hi)).1⟩ },
    rw [filter_insert, hp'₂, h'],
    by_cases 0 < a,
    { rw [if_pos h, if_neg, hP'₆, if_pos h],
      simp only [nat.one_ne_zero, self_eq_add_right, not_false_iff] },
    rw [if_neg h, if_pos rfl, card_insert_of_not_mem, hP'₆, if_neg h, nat.sub_add_cancel],
    apply ‹0 < a ∨ 0 < b›.resolve_left h,
    simp only [mem_filter, hp'₂, h', if_neg h, eq_self_iff_true, and_true],
    intro t,
    obtain ⟨i, hi⟩ := ‹p'.nonempty›,
    apply (mem_sdiff.1 (hP'₅ _ t hi)).2 hi },
  push_neg at h,
  have : p'_size ≤ s.card,
  { rw [←hs, h'],
    split_ifs,
    { apply le_add_right (nat.le_mul_of_pos_left ‹0 < a›) },
    exact le_add_left (nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›)) },
  obtain ⟨s', hs'₁, hs'₂⟩ := exists_smaller_set _ _ this,
  have : s'.nonempty,
  { rwa [←card_pos, hs'₂] },
  obtain ⟨P', hP'₁, hP'₂, hP'₃, hP'₄, hP'₅, hP'₆⟩ :=
    @ih (s \ s')
    (sdiff_ssubset hs'₁ ‹s'.nonempty›)
    (A.image (λ t, t \ s'))
    (if 0 < a then a-1 else a)
    (if 0 < a then b else b-1)
    _ _ _ _,
  rotate,
  { rw [card_sdiff ‹s' ⊆ s›, hs'₂, h', ←hs],
    split_ifs,
    { rw [nat.mul_sub_right_distrib, one_mul,
        nat.sub_add_eq_add_sub (nat.le_mul_of_pos_left ‹0 < a›)] },
    rw [nat.mul_sub_right_distrib, one_mul, ←nat.add_sub_assoc],
    exact nat.le_mul_of_pos_left (‹0 < a ∨ 0 < b›.resolve_left ‹¬0 < a›) },
  { intros x hx,
    simp only [mem_sdiff] at hx,
    obtain ⟨y, hy, hy'⟩ := all x hx.1,
    simp only [mem_image, exists_prop, mem_sdiff, exists_exists_and_eq_and],
    refine ⟨_, hy, hy', hx.2⟩ },
  { simp only [mem_image, and_imp, exists_prop, exists_imp_distrib],
    rintro x₁ x₂ x hx rfl x' hx' rfl i hi₁ hi₂,
    simp only [mem_sdiff] at hi₁ hi₂,
    rw disj _ _ hx hx' i hi₁.1 hi₂.1 },
  { simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp_distrib],
    intros a ha,
    apply sdiff_subset_sdiff (subs a ha) (refl _) },
  refine ⟨insert s' P', _, _, _, _, _, _⟩,
  { simp only [mem_insert, forall_eq_or_imp, and_iff_left hP'₁, hs'₂, h'],
    split_ifs,
    { left, refl },
    right, refl },
  { intros x hx,
    refine le_trans (card_le_of_subset (sdiff_subset _ _)) _,
    rw ←nat.lt_succ_iff,
    exact h _ hx },
  { intros x hx,
    by_cases x ∈ s',
    { refine ⟨_, by simp only [mem_insert, true_or, eq_self_iff_true], h⟩ },
    obtain ⟨w, hw, hw'⟩ := hP'₃ x (by simp only [hx, h, mem_sdiff, not_false_iff, and_self]),
    exact ⟨w, by simp only [hw, mem_insert, or_true], hw'⟩ },
  { simp only [mem_insert],
    rintro _ _ (rfl | hx₁) (rfl | hx₂) i hi₁ hi₂,
    { refl },
    { apply ((mem_sdiff.1 (hP'₅ _ hx₂ hi₂)).2 hi₁).elim },
    { apply ((mem_sdiff.1 (hP'₅ _ hx₁ hi₁)).2 hi₂).elim },
    exact hP'₄ _ _ hx₁ hx₂ _ hi₁ hi₂ },
  { simp only [hs'₁, true_and, mem_insert, forall_eq_or_imp],
    intros x hx,
    apply finset.subset.trans (hP'₅ x hx) (sdiff_subset _ _) },
  rw [filter_insert, hs'₂, h'],
  by_cases 0 < a,
  { rw [if_pos h, if_neg, hP'₆, if_pos h],
    simp only [nat.one_ne_zero, self_eq_add_right, not_false_iff] },
  rw [if_neg h, if_pos rfl, card_insert_of_not_mem, hP'₆, if_neg h, nat.sub_add_cancel],
  apply ‹0 < a ∨ 0 < b›.resolve_left h,
  simp only [mem_filter, hs'₂, h', if_neg h, eq_self_iff_true, and_true],
  intro t,
  obtain ⟨i, hi⟩ := ‹s'.nonempty›,
  exact (mem_sdiff.1 (hP'₅ _ t hi)).2 hi,
end.

namespace finpartition_on

/--
Given a partition `Q` of `s`, as well as a proof that `a*m + b*(m+1) = s.card`, build a new
partition `P` of `s` where each part has size `m` or `m+1`, every part of `Q` is the union of
parts of `P` plus at most `m` extra elements, there are `b` parts of size `m+1` and provided
`m > 0`, there are `a` parts of size `m` and hence `a+b` parts in total.
The `m > 0` condition is required since there may be zero or one parts of size `0`, while `a` could
be arbitrary.
-/
noncomputable def mk_equitable (Q : finpartition_on s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  finpartition_on s :=
begin
  let P := classical.some (mk_equitable_aux h Q.parts Q.cover Q.disjoint Q.subset),
  have hP := classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint Q.subset),
  refine ⟨P.erase ∅,
    λ a b ha hb x hxa hxb, hP.2.2.2.1 a b (erase_subset _ _ ha) (erase_subset _ _ hb) x hxa hxb,
    λ u hu, _, λ u hu, hP.2.2.2.2.1 _ (erase_subset _ _ hu), not_mem_erase _ _⟩,
  obtain ⟨a, ha, hua⟩ := hP.2.2.1 u hu,
  exact ⟨a, mem_erase.2 ⟨nonempty_iff_ne_empty.1 ⟨u, hua⟩, ha⟩, hua⟩,
end

lemma card_eq_of_mem_parts_mk_equitable {Q : finpartition_on s} {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) {u : finset α} (hu : u ∈ (Q.mk_equitable h).parts) :
  u.card = m ∨ u.card = m + 1 :=
(classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint Q.subset)).1
  u (mem_of_mem_erase hu)

lemma mk_equitable.is_equipartition (Q : finpartition_on s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  (Q.mk_equitable h).is_equipartition :=
begin
  rw [is_equipartition, equitable_on_iff_almost_eq_constant],
  exact ⟨m, λ u hu, card_eq_of_mem_parts_mk_equitable h hu⟩,
end

lemma card_filter_mk_equitable_big (Q : finpartition_on s) {m a b : ℕ}
  (h : a*m + b*(m+1) = s.card) :
  ((Q.mk_equitable h).parts.filter (λ u : finset α, u.card = m + 1)).card = b :=
begin
  convert (classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint
    Q.subset)).2.2.2.2.2 using 2,
  ext u,
  rw [mem_filter, mem_filter, finpartition_on.mk_equitable, mem_erase, and_assoc,
    and_iff_right_iff_imp],
  rintro hu rfl,
  rw finset.card_empty at hu,
  exact nat.succ_ne_zero _ hu.2.symm,
end

lemma card_filter_mk_equitable_small (Q : finpartition_on s) {m a b : ℕ} (hm : 0 < m)
  (h : a*m + b*(m+1) = s.card) :
  ((Q.mk_equitable h).parts.filter (λ u : finset α, u.card = m)).card = a :=
begin
  refine (mul_eq_mul_right_iff.1 $ (add_left_inj $ b * (m + 1)).1 _).resolve_right hm.ne',
  rw [h, ←(Q.mk_equitable h).sum_card_parts],
  have hunion : (Q.mk_equitable h).parts = (Q.mk_equitable h).parts.filter (λ u, u.card = m) ∪
    (Q.mk_equitable h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_mk_equitable h hx },
  nth_rewrite 1 hunion,
  rw [sum_union, sum_const_nat (λ x hx, (mem_filter.1 hx).2),
    sum_const_nat (λ x hx, (mem_filter.1 hx).2), Q.card_filter_mk_equitable_big],
  refine λ x hx, nat.succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [nat.succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma mk_equitable.size {Q : finpartition_on s} {m a b : ℕ} (hm : 0 < m)
  (h : a * m + b * (m + 1) = s.card) :
  (Q.mk_equitable h).size = a + b :=
begin
  have hunion : (Q.mk_equitable h).parts = (Q.mk_equitable h).parts.filter (λ u, u.card = m) ∪
    (Q.mk_equitable h).parts.filter (λ u, u.card = m + 1),
  { rw [←filter_or, filter_true_of_mem],
    exact λ x hx, card_eq_of_mem_parts_mk_equitable h hx },
  rw [finpartition_on.size, hunion, card_union_eq, Q.card_filter_mk_equitable_small hm,
    Q.card_filter_mk_equitable_big],
  refine λ x hx, nat.succ_ne_self m _,
  rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hx,
  rw [nat.succ_eq_add_one, ←hx.2.2, hx.1.2],
end

lemma almost_in_atoms_of_mem_parts_mk_equitable {Q : finpartition_on s} {m a b : ℕ}
  (h : a * m + b * (m + 1) = s.card) {u : finset α} (hu : u ∈ Q.parts) :
  (u \ finset.bUnion ((Q.mk_equitable h).parts.filter (λ x, x ⊆ u)) id).card ≤ m :=
begin
  have := (classical.some_spec (mk_equitable_aux h Q.parts Q.cover Q.disjoint
    Q.subset)).2.1,
  refine (card_le_of_subset _).trans ((classical.some_spec (mk_equitable_aux h Q.parts Q.cover
    Q.disjoint Q.subset)).2.1 u hu),
  intros x,
  simp only [not_exists, mem_bUnion, and_imp, mem_filter, mem_sdiff, id.def, ne.def],
  refine λ hxu hx, ⟨hxu, λ a ha hau, _⟩,
  obtain rfl | hanemp := eq_or_ne a ∅,
  { exact not_mem_empty _ },
  exact hx _ (mem_erase.2 ⟨hanemp, ha⟩) hau,
end

end finpartition_on

end

section atomise
variables [decidable_eq α] {s : finset α}

/-- Cuts `s` along the finsets in `Q`: Two elements of `s` will be in the same -/
def atomise (s : finset α) (Q : finset (finset α)) :
  finpartition_on s :=
{ parts := Q.powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ P ↔ i ∈ x)) \ {∅},
  disjoint := begin
    rintro x y hx hy i hi₁ hi₂,
    simp only [mem_sdiff, mem_powerset, mem_image, exists_prop] at hx hy,
    obtain ⟨P, hP, rfl⟩ := hx.1,
    obtain ⟨P', hP', rfl⟩ := hy.1,
    suffices h : P = P',
    { subst h },
    rw mem_filter at hi₁ hi₂,
    ext j,
    refine ⟨λ hj, _, λ hj, _⟩,
    { rwa [hi₂.2 _ (hP hj), ←hi₁.2 _ (hP hj)] },
    rwa [hi₁.2 _ (hP' hj), ←hi₂.2 _ (hP' hj)],
  end,
  cover := begin
    rintro x hx,
    simp only [mem_sdiff, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc],
    rw exists_exists_and_eq_and,
    have h : x ∈ s.filter (λ i, ∀ y ∈ Q, (y ∈ Q.filter (λ t, x ∈ t) ↔ i ∈ y)),
    { simp only [mem_filter, and_iff_right_iff_imp],
      exact ⟨hx, λ y hy _, hy⟩ },
    refine ⟨Q.filter (λ t, x ∈ t), filter_subset _ _, _, h⟩,
    rw [mem_singleton, ←ne.def, ←nonempty_iff_ne_empty],
    exact ⟨x, h⟩,
  end,
  subset := begin
    rintro x hx,
    simp only [mem_sdiff, mem_powerset, mem_image, exists_prop] at hx,
    obtain ⟨P, hP, rfl⟩ := hx.1,
    exact filter_subset _ s,
  end,
  not_empty_mem := λ h, (mem_sdiff.1 h).2 (mem_singleton_self _) }

lemma mem_atomise {s : finset α} {Q : finset (finset α)} {A : finset α} :
  A ∈ (atomise s Q).parts ↔ A.nonempty ∧ ∃ (P ⊆ Q), s.filter (λ i, ∀ x ∈ Q, x ∈ P ↔ i ∈ x) = A :=
by { simp only [atomise, mem_sdiff, nonempty_iff_ne_empty, mem_singleton, and_comm, mem_image,
  mem_powerset, exists_prop] }

lemma atomise_empty (hs : s.nonempty) : (atomise s ∅).parts = {s} :=
begin
  rw [atomise],
  simp,
  apply disjoint.sdiff_eq_left,
  rwa [disjoint_singleton, mem_singleton, ←ne.def, ne_comm, ←nonempty_iff_ne_empty],
end

lemma atomise_disjoint {s : finset α} {Q : finset (finset α)} {x y : finset α}
  (hx : x ∈ (atomise s Q).parts) (hy : y ∈ (atomise s Q).parts) : disjoint x y ∨ x = y :=
begin
  rw or_iff_not_imp_left,
  simp only [disjoint_left, not_forall, and_imp, exists_prop, not_not, exists_imp_distrib],
  intros i hi₁ hi₂,
  simp only [mem_atomise] at hx hy,
  obtain ⟨P, hP, rfl⟩ := hx.2,
  obtain ⟨P', hP', rfl⟩ := hy.2,
  simp only [mem_filter] at hi₁ hi₂,
  suffices h : P = P',
  { subst h },
  ext j,
  refine ⟨λ hj, _, λ hj, _⟩,
  { rwa [hi₂.2 _ (hP hj), ←hi₁.2 _ (hP hj)] },
  { rwa [hi₁.2 _ (hP' hj), ←hi₂.2 _ (hP' hj)] },
end

lemma atomise_covers {s : finset α} (Q : finset (finset α)) {x : α} (hx : x ∈ s) :
  ∃ Y ∈ (atomise s Q).parts, x ∈ Y :=
(atomise s Q).cover hx

lemma atomise_unique_covers {s : finset α} {Q : finset (finset α)} {x : α} (hx : x ∈ s) :
  ∃! Y ∈ (atomise s Q).parts, x ∈ Y :=
begin
  obtain ⟨Y, hY₁, hY₂⟩ := atomise_covers Q hx,
  refine exists_unique.intro2 Y hY₁ hY₂ (λ Y' hY'₁ hY'₂,
    or.resolve_left (atomise_disjoint ‹Y' ∈ _› ‹Y ∈ _›) _),
  simp only [disjoint_left, exists_prop, not_not, not_forall],
  exact ⟨_, hY'₂, hY₂⟩,
end

lemma card_atomise_le {s : finset α} {Q : finset (finset α)} :
  ((atomise s Q).parts).card ≤ 2^Q.card :=
begin
  apply (card_le_of_subset (sdiff_subset _ _)).trans,
  apply finset.card_image_le.trans,
  simp,
end

lemma union_of_atoms_aux {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) (i : α) :
  (∃ (B ∈ (atomise s Q).parts), B ⊆ A ∧ i ∈ B) ↔ i ∈ A :=
begin
  split,
  { rintro ⟨B, hB₁, hB₂, hB₃⟩,
    exact hB₂ hB₃ },
  intro hi,
  obtain ⟨B, hB₁, hB₂⟩ := atomise_covers Q (hs hi),
  refine ⟨B, hB₁, λ j hj, _, hB₂⟩,
  obtain ⟨P, hP, rfl⟩ := (mem_atomise.1 hB₁).2,
  simp only [mem_filter] at hB₂ hj,
  rwa [←hj.2 _ hA, hB₂.2 _ hA]
end

lemma union_of_atoms {s : finset α} {Q : finset (finset α)} {A : finset α}
  (hA : A ∈ Q) (hs : A ⊆ s) :
  s.filter (λ i, ∃ B ∈ (atomise s Q).parts, B ⊆ A ∧ i ∈ B) = A :=
begin
  ext i,
  simp only [mem_filter, union_of_atoms_aux hA hs],
  exact and_iff_right_iff_imp.2 (@hs i),
end

instance {B : finset α} : decidable B.nonempty :=
decidable_of_iff' _ finset.nonempty_iff_ne_empty

lemma union_of_atoms' {s : finset α} {Q : finset (finset α)} (A : finset α)
  (hx : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty)).bUnion id = A :=
begin
  ext x,
  rw mem_bUnion,
  simp only [exists_prop, mem_filter, id.def, and_assoc],
  rw ←union_of_atoms_aux hx hs,
  simp only [exists_prop],
  exact exists_congr (λ a, and_congr_right (λ b, and_congr_right (λ c,
    and_iff_right_of_imp (λ h, ⟨_, h⟩)))),
end

lemma partial_atomise {s : finset α} {Q : finset (finset α)} (A : finset α)
  (hA : A ∈ Q) (hs : A ⊆ s) :
  ((atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty)).card ≤ 2^(Q.card - 1) :=
begin
  suffices h :
    (atomise s Q).parts.filter (λ B, B ⊆ A ∧ B.nonempty) ⊆
      (Q.erase A).powerset.image (λ P, s.filter (λ i, ∀ x ∈ Q, x ∈ insert A P ↔ i ∈ x)),
  { apply (card_le_of_subset h).trans (card_image_le.trans _),
    rw [card_powerset, card_erase_of_mem hA],
    refl },
  rw subset_iff,
  simp only [mem_erase, mem_sdiff, mem_powerset, mem_image, exists_prop, mem_filter, and_assoc,
    finset.nonempty, exists_imp_distrib, and_imp, mem_atomise, forall_apply_eq_imp_iff₂],
  rintro P' i hi P PQ rfl hy₂ j hj,
  refine ⟨P.erase A, erase_subset_erase _ PQ, _⟩,
  have : A ∈ P,
  { rw mem_filter at hi,
    rw hi.2 _ hA,
    apply hy₂,
    exact mem_filter.2 hi },
  simp only [insert_erase this, filter_congr_decidable],
end

end atomise

/-- Arbitrary equipartition into `t` parts -/
lemma dummy_equipartition [decidable_eq α] (s : finset α) {t : ℕ}
  (ht : 0 < t) (hs : t ≤ s.card) :
  ∃ (P : finpartition_on s), P.is_equipartition ∧ P.size = t :=
begin
  have : (t - s.card % t) * (s.card / t) + (s.card % t) * (s.card / t + 1) = s.card,
  { rw [nat.mul_sub_right_distrib, mul_add, ←add_assoc, nat.sub_add_cancel, mul_one, add_comm,
      nat.mod_add_div],
    exact nat.mul_le_mul_right _ ((nat.mod_lt _ ht).le) },
  refine ⟨(indiscrete_finpartition_on $ finset.card_pos.1 (ht.trans_le hs)).mk_equitable this,
    finpartition_on.mk_equitable.is_equipartition _ _, _⟩,
  rw [finpartition_on.mk_equitable.size (nat.div_pos hs ht), nat.sub_add_cancel
    (nat.mod_lt _ ht).le],
end

/-! ### The actual proof -/

/-- Auxiliary function to explicit the bound on the size of the equipartition in the proof of
Szemerédi's Regularity Lemma -/
def exp_bound (n : ℕ) : ℕ := n * 4^n

lemma le_exp_bound :
 id ≤ exp_bound :=
λ n, nat.le_mul_of_pos_right (pow_pos (by norm_num) n)

lemma exp_bound_mono :
  monotone exp_bound :=
λ a b h, nat.mul_le_mul h (nat.pow_le_pow_of_le_right (by norm_num) h)

lemma exp_bound_pos {n : ℕ} : 0 < exp_bound n ↔ 0 < n :=
begin
  rw exp_bound,
  exact zero_lt_mul_right (pow_pos (by norm_num) _),
end

open_locale classical
variables [fintype α] {G : simple_graph α} {P : finpartition α} {ε : ℝ}

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

lemma m_pos [nonempty α] (hPα : P.size * 16^P.size ≤ card α) : 0 < m :=
begin
  refine nat.div_pos ((nat.mul_le_mul_left _ (nat.pow_le_pow_of_le_left (by norm_num) _)).trans hPα)
    _,
  rw [exp_bound_pos, size_eq_card_parts, card_pos],
  exact P.parts_nonempty,
end

private lemma hundred_div_ε_pow_five_le_m [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) :
  100/ε^5 ≤ m :=
begin
  calc
    100/ε^5
        ≤ 4^P.size : div_le_of_nonneg_of_le_mul (nonneg_of_mul_nonneg_left
          (le_trans (by norm_num) hPε) (pow_pos (by norm_num) _)) (pow_nonneg (by norm_num) _) hPε
    ... = ((P.size * 16^P.size)/exp_bound P.size : ℕ) : begin
      norm_cast,
      refine (nat.div_eq_of_eq_mul_left _ _).symm,
      { rw [exp_bound_pos, size_eq_card_parts, card_pos],
        exact P.parts_nonempty },
      rw [exp_bound, mul_comm (4^P.size), mul_assoc, ←mul_pow],
      norm_num,
    end
    ... ≤ m : nat.cast_le.2 (nat.div_le_div_right hPα)
end

private lemma a_add_one_le_four_pow_size :
  a + 1 ≤ 4^P.size :=
begin
  have h : 1 ≤ 4^P.size := one_le_pow_of_one_le (by norm_num) _,
  rw [exp_bound, ←nat.div_div_eq_div_mul, nat.add_le_to_le_sub _ h],
  apply nat.sub_le_left_of_le_add,
  rw ←nat.add_sub_assoc h,
  exact nat.le_pred_of_lt (nat.lt_div_mul_add h),
end

private lemma card_aux₁ :
  m * 4^P.size + a = (4^P.size - a) * m + a * (m + 1) :=
by rw [mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_size), mul_comm]

private lemma card_aux₂ {U : finset α} (hUcard : U.card = m * 4^P.size + a) :
  (4^P.size - a) * m + a * (m + 1) = U.card :=
by rw [hUcard, mul_add, mul_one, ←add_assoc, ←add_mul, nat.sub_add_cancel
  ((nat.le_succ _).trans a_add_one_le_four_pow_size), mul_comm]

private lemma card_aux₃ (hP : P.is_equipartition) {U : finset α} (hU : U ∈ P.parts)
  (hUcard : ¬U.card = m * 4^P.size + a) :
  (4^P.size - (a + 1)) * m + (a + 1) * (m + 1) = U.card :=
begin
  have aux :
    m * 4^finpartition_on.size P + a = card α/P.size,
  { apply nat.add_sub_cancel',
    rw [exp_bound, ←nat.div_div_eq_div_mul],
    exact nat.div_mul_le_self _ _ },
  rw aux at hUcard,
  rw finpartition.is_equipartition_iff_card_parts_eq_average at hP,
  rw [(hP U hU).resolve_left hUcard, mul_add, mul_one, ←add_assoc, ←add_mul,
    nat.sub_add_cancel a_add_one_le_four_pow_size, ←add_assoc, mul_comm, nat.add_sub_cancel', ←aux],
  rw ←aux,
  exact nat.le_add_right _ _,
end

/-- The part of `increment` that partitions `U`. -/
noncomputable def finpartition_on.is_equipartition.chunk_increment (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ) {U : finset α} (hU : U ∈ P.parts) :
  finpartition_on U :=
begin
  let R := atomise U (finset.image (λ W, (G.witness ε U W).1) (P.parts.filter (λ W,
    ¬G.is_uniform ε U W))),
  exact dite (U.card = m * 4^P.size + a)
    (λ hUcard, R.mk_equitable $ card_aux₂ hUcard)
    (λ hUcard, R.mk_equitable $ card_aux₃ hP hU hUcard),
end

section chunk_increment
variables {hP : P.is_equipartition} {U : finset α}
  {hU : U ∈ P.parts}

lemma card_eq_of_mem_parts_chunk_increment {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  A.card = card α / exp_bound P.size ∨ A.card = card α / exp_bound P.size + 1 :=
begin
  simp [finpartition_on.is_equipartition.chunk_increment] at hA,
  by_cases hUcard : U.card = m * 4^P.size + a,
  { rw dif_pos hUcard at hA,
    exact finpartition_on.card_eq_of_mem_parts_mk_equitable _ hA },
  rw dif_neg hUcard at hA,
  exact finpartition_on.card_eq_of_mem_parts_mk_equitable _ hA,
end

lemma m_le_card_of_mem_chunk_increment_parts {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  (m : ℝ) ≤ A.card :=
begin
  obtain h | h := card_eq_of_mem_parts_chunk_increment hA; rw h,
  exact nat.cast_le.2 (nat.le_succ _),
end

lemma card_le_m_add_one_of_mem_chunk_increment_parts {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  (A.card : ℝ) ≤ m + 1 :=
begin
  obtain h | h := card_eq_of_mem_parts_chunk_increment hA; rw h,
  { exact nat.cast_le.2 (nat.le_succ _) },
  { rw nat.cast_add_one }
end

lemma le_sum_card_subset_chunk_increment_parts (m_pos : 0 < m) {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  (A.card : ℝ) * u.card ≤ (∑ W in A, W.card)/(m/(m + 1)) :=
begin
  rw le_div_iff, swap,
  { exact div_pos (nat.cast_pos.2 m_pos) (nat.cast_add_one_pos _) },
  calc
    (A.card : ℝ) * u.card * (m/(m + 1))
        = A.card * m * (u.card/(m + 1))
        : by rw [←mul_div_assoc, mul_right_comm, mul_div_assoc]
    ... ≤ A.card * m
        : mul_le_of_le_one_right
          (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) ((div_le_one $ by exact
          nat.cast_add_one_pos _).2 $ card_le_m_add_one_of_mem_chunk_increment_parts $ hA hu)
    ... = ∑ W in A, (m : ℝ)
        : by rw [sum_const, nsmul_eq_mul]
    ... ≤ ∑ W in A, W.card
        : sum_le_sum (λ W hW, m_le_card_of_mem_chunk_increment_parts $ hA hW)
end

lemma sum_card_subset_chunk_increment_parts_le (m_pos : 0 < m) {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  (∑ W in A, (W.card : ℝ))/((m + 1)/m) ≤ A.card * u.card :=
begin
  rw div_le_iff, swap,
  { exact div_pos (nat.cast_add_one_pos _) (nat.cast_pos.2 m_pos) },
  calc
    ∑ W in A, (W.card : ℝ)
        ≤ ∑ W in A, (m + 1)
        : sum_le_sum (λ W hW, card_le_m_add_one_of_mem_chunk_increment_parts $ hA hW)
    ... = A.card * (m + 1) : by rw [sum_const, nsmul_eq_mul]
    ... ≤ A.card * (m + 1) * (u.card/m) : le_mul_of_one_le_right (mul_nonneg (nat.cast_nonneg _)
          (nat.cast_add_one_pos _).le) ((one_le_div (by exact nat.cast_pos.2 m_pos)).2
          (m_le_card_of_mem_chunk_increment_parts $ hA hu))
    ... = A.card * u.card * ((m + 1)/m)
        : by rw [←mul_div_assoc, mul_right_comm, mul_div_assoc]
end

lemma one_sub_le_m_div_m_add_one_sq [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) :
  1 - ε^5/50 ≤ (m/(m + 1))^2 :=
begin
  have hε : 0 < ε^5 := pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) hPε)
    (pow_nonneg (by norm_num) _),
  calc
    1 - ε^5/50
        = 1 - 2/(100/ε^5) : begin
          rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_eq_mul_one_div],
          norm_num,
         end
    ... ≤ 1 - 2/m : sub_le_sub_left (div_le_div_of_le_left zero_le_two
          (div_pos (by norm_num) hε) (hundred_div_ε_pow_five_le_m hPα hPε)) _
    ... ≤ 1 - 2/(m + 1) : sub_le_sub_left (div_le_div_of_le_left zero_le_two
          (nat.cast_pos.2 (m_pos hPα)) ((le_add_iff_nonneg_right _).2 zero_le_one)) _
    ... ≤ 1 - 2/(m + 1) + 1/(m + 1)^2
        : le_add_of_nonneg_right (div_nonneg zero_le_one (sq_nonneg _))
    ... = ((m + 1 - 1)/(m + 1))^2 : by rw [sub_div, div_self (nat.cast_add_one_ne_zero m :
            (m : ℝ) + 1 ≠ 0), sub_sq, div_pow, one_pow, mul_one, mul_one_div]
    ... = (m/(m + 1))^2 : by rw add_sub_cancel,
end

lemma m_add_one_div_m_le_one_add [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) (hm : 25 ≤ m) :
  ((m + 1 : ℝ)/m)^2 ≤ 1 + ε^5/49 :=
begin
  have m_pos : (0 : ℝ) < m,
  { rw ←nat.cast_zero,
    exact lt_of_lt_of_le (by norm_num) (nat.cast_le.2 hm) },
  rw [←sub_le_iff_le_add', add_comm],
  calc
    ((1 + m : ℝ)/m)^2 - 1
        = 1/m/m + 2/m : by rw [add_div, div_self m_pos.ne', add_sq, div_pow, one_pow, mul_one,
          mul_one_div, sq, ←div_div_eq_div_mul, add_sub_cancel]
    ... ≤ 1/25/m + 2/m : begin
      refine add_le_add_right (div_le_div_of_le_of_nonneg (div_le_div_of_le_left zero_le_one
        (by norm_num) _) (nat.cast_nonneg _)) _,
      rw (by norm_num : (25 : ℝ) = (25 : ℕ)),
      exact nat.cast_le.2 hm,
    end
    ... = (1/25 + 2)/m : (add_div _ _ _).symm
    ... ≤ 100/49/m : div_le_div_of_le_of_nonneg (by norm_num) (nat.cast_nonneg _)
    ... ≤ ε^5/49 : begin
      rw div_right_comm,
      refine div_le_div_of_le_of_nonneg _ (by norm_num),
      rw [div_le_iff m_pos, mul_comm, ←div_le_iff
        (pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) hPε) (pow_nonneg (by norm_num) _))],
      exact hundred_div_ε_pow_five_le_m hPα hPε,
    end
end

lemma density_sub_eps_le_sum_density_div_card [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) (m_pos : 0 < m)
  {U W : finset α} {hU : U ∈ P.parts} {hW : W ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hW).parts) :
  G.edge_density (A.bUnion id) (B.bUnion id) - ε^5/50 ≤
  (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) :=
begin
  have hε : 0 < ε^5 := pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 100).trans_le hPε)
    (pow_nonneg (by norm_num) _),
  calc
    G.edge_density (A.bUnion id) (B.bUnion id) - ε^5/50
        ≤ (1 - ε^5/50) * G.edge_density (A.bUnion id) (B.bUnion id)
        : begin
            rw [sub_mul, one_mul],
            exact sub_le_sub_left (mul_le_of_le_one_right (div_nonneg hε.le (by norm_num))
              (G.edge_density_le_one _ _)) _,
          end
    ... ≤ (m/(m + 1))^2 * G.edge_density (A.bUnion id) (B.bUnion id)
        : mul_le_mul_of_nonneg_right (one_sub_le_m_div_m_add_one_sq hPα hPε)
          (G.edge_density_nonneg _ _)
    ... = pairs_count G.adj (A.bUnion id) (B.bUnion id) /
          ((A.bUnion id).card/(m/(m + 1)) * ((B.bUnion id).card/(m/(m + 1))))
        : begin
            unfold simple_graph.edge_density pairs_density,
            simp only [←div_div_eq_div_mul],
            rw [div_div_eq_mul_div, div_div_eq_mul_div],
            ring,
          end
    ... = ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/((∑ aa in A, (aa.card : ℝ))/(m/(m + 1))
          * ((∑ b in B, (b.card : ℝ))/(m/(m + 1))))
        : begin
            rw [relation.pairs_count_finpartition hA.finpartition_on hB.finpartition_on,
              ←hA.finpartition_on.sum_card_parts, ←hB.finpartition_on.sum_card_parts],
            simp only [nat.cast_sum],
            rw [sum_div, hA.finpartition_on_parts, hB.finpartition_on_parts],
          end
    ... ≤ ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/(A.card * ab.1.card *
          (B.card * ab.2.card))
          : begin
            refine sum_le_sum (λ x hx, div_le_div_of_le_left (nat.cast_nonneg _) _ _);
            rw mem_product at hx,
            { norm_cast,
              refine mul_pos (mul_pos _ _) (mul_pos _ _); rw card_pos,
              exacts [⟨x.1, hx.1⟩, nonempty_of_mem_parts _ (hA hx.1), ⟨x.2, hx.2⟩,
                nonempty_of_mem_parts _ (hB hx.2)] },
            refine mul_le_mul (le_sum_card_subset_chunk_increment_parts m_pos hA hx.1)
              (le_sum_card_subset_chunk_increment_parts m_pos hB hx.2) _
              (div_nonneg _ (div_nonneg _ _));
            norm_cast; exact nat.zero_le _,
          end
    ... = (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card)
        : begin
            unfold simple_graph.edge_density pairs_density,
            rw sum_div,
            simp_rw div_div_eq_div_mul,
            refine finset.sum_congr rfl (λ x _, _),
            rw [mul_comm (B.card : ℝ), ←mul_assoc, ←mul_assoc, mul_comm _ (A.card : ℝ), ←mul_assoc],
          end
end

lemma sum_density_div_card_le_density_add_eps [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) (hm : 25 ≤ m)
  {U W : finset α} {hU : U ∈ P.parts} {hW : W ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hW).parts) :
  (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) ≤
  G.edge_density (A.bUnion id) (B.bUnion id) + ε^5/49 :=
begin
  have hε : 0 < ε^5 := pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 100).trans_le hPε)
    (pow_nonneg (by norm_num) _),
  have m_pos : 0 < m := (by norm_num : 0 < 25).trans_le hm,
  have m_add_one_div_m_pos : (0 : ℝ) < (m + 1)/m :=
    div_pos (nat.cast_add_one_pos _) (nat.cast_pos.2 m_pos),
  calc
    (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card)
        = ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/(A.card * ab.1.card *
          (B.card * ab.2.card))
        : begin
            unfold simple_graph.edge_density pairs_density,
            rw sum_div,
            simp_rw div_div_eq_div_mul,
            refine finset.sum_congr rfl (λ x _, _),
            rw [mul_comm (B.card : ℝ), ←mul_assoc, ←mul_assoc, mul_comm _ (A.card : ℝ), ←mul_assoc],
          end
    ... ≤ ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/((∑ aa in A, (aa.card : ℝ))/((m + 1)/m)
          * ((∑ b in B, (b.card : ℝ))/((m + 1)/m)))
        : begin
            refine sum_le_sum (λ x hx, div_le_div_of_le_left (nat.cast_nonneg _) _ _);
            rw mem_product at hx,
            { refine mul_pos (div_pos _ m_add_one_div_m_pos)
                (div_pos _ m_add_one_div_m_pos); norm_cast,
              { exact (card_pos.2 $ finpartition_on.nonempty_of_mem_parts _ $
                hA hx.1).trans_le (single_le_sum (λ _ _, nat.zero_le _) hx.1) },
              { refine (card_pos.2 $ finpartition_on.nonempty_of_mem_parts _ $
                hB hx.2).trans_le (single_le_sum (λ _ _, nat.zero_le _) hx.2) } },
            refine mul_le_mul (sum_card_subset_chunk_increment_parts_le m_pos hA hx.1)
              (sum_card_subset_chunk_increment_parts_le m_pos hB hx.2)
              (div_nonneg _ (div_nonneg _ _)) _; norm_cast; exact nat.zero_le _,
          end
    ... = pairs_count G.adj (A.bUnion id) (B.bUnion id) /
          ((A.bUnion id).card/((m + 1)/m) * ((B.bUnion id).card/((m + 1)/m)))
        : begin
            rw [relation.pairs_count_finpartition hA.finpartition_on hB.finpartition_on,
              ←hA.finpartition_on.sum_card_parts, ←hB.finpartition_on.sum_card_parts],
            simp only [nat.cast_sum],
            rw [eq_comm, sum_div, hA.finpartition_on_parts, hB.finpartition_on_parts],
          end
    ... = ((m + 1)/m)^2 * G.edge_density (A.bUnion id) (B.bUnion id)
        : begin
            unfold simple_graph.edge_density pairs_density,
            simp only [←div_div_eq_div_mul],
            rw [div_div_eq_mul_div, div_div_eq_mul_div],
            ring,
          end
    ... ≤ (1 + ε^5/49) * G.edge_density (A.bUnion id) (B.bUnion id)
        : mul_le_mul_of_nonneg_right (m_add_one_div_m_le_one_add hPα hPε hm)
          (G.edge_density_nonneg _ _)
    ... ≤ G.edge_density (A.bUnion id) (B.bUnion id) + ε^5/49
        : begin
            rw [add_mul, one_mul],
            exact add_le_add_left (mul_le_of_le_one_right (div_nonneg hε.le (by norm_num))
              (G.edge_density_le_one _ _)) _,
          end,
end

end chunk_increment

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_half`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
noncomputable def finpartition_on.is_equipartition.increment (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ) :
  finpartition α :=
 P.bind (λ U hU, hP.chunk_increment G ε hU)

open finpartition_on.is_equipartition

namespace increment

protected lemma size (hP : P.is_equipartition) (hPα : P.size * 16^P.size ≤ card α)
  (hPG : ¬P.is_uniform G ε) :
  (hP.increment G ε).size = exp_bound P.size :=
begin
  have hPα' : exp_bound P.size ≤ card α :=
    (nat.mul_le_mul_of_nonneg_left $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα,
  have hPpos : 0 < exp_bound P.size := exp_bound_pos.2 ((nat.eq_zero_or_pos _).resolve_left $ λ h,
    hPG $ finpartition_on.empty_is_uniform (by rw [←finset.card_eq_zero, ←finpartition_on.size, h])
    _ _),
  rw [is_equipartition, equitable_on_finset_iff_eq_average] at hP,
  rw [increment, bind_size],
  simp_rw [finpartition_on.is_equipartition.chunk_increment, apply_dite finpartition_on.size],
  rw [sum_dite, sum_const_nat, sum_const_nat, card_attach, card_attach], rotate,
  exact λ x hx, finpartition_on.mk_equitable.size (nat.div_pos hPα' hPpos) _,
  exact λ x hx, finpartition_on.mk_equitable.size (nat.div_pos hPα' hPpos) _,
  rw [nat.sub_add_cancel a_add_one_le_four_pow_size, nat.sub_add_cancel ((nat.le_succ _).trans
    a_add_one_le_four_pow_size), ←add_mul],
  congr,
  rw [filter_card_add_filter_neg_card_eq_card, card_attach, finpartition_on.size],
end

protected lemma is_equipartition (hP : P.is_equipartition) (G : simple_graph α) (ε : ℝ) :
  (hP.increment G ε).is_equipartition :=
begin
  rw [is_equipartition, equitable_on_iff_almost_eq_constant],
  refine ⟨m, λ A hA, _⟩,
  rw [mem_coe, increment, mem_bind_parts] at hA,
  obtain ⟨U, hU, hA⟩ := hA,
  exact card_eq_of_mem_parts_chunk_increment hA,
end

protected lemma index [nonempty α] (hP : P.is_equipartition) (hP₁₀₀ : 100 ≤ P.size)
  (hε : 100 < ε^5 * 4^P.size) (hPα : P.size * 16^P.size ≤ card α) (hPG : ¬P.is_uniform G ε) :
  P.index G + ε^5 / 8 ≤ (hP.increment G ε).index G :=
begin
  calc
    index G P + ε^5/8
        ≤ index G P - ε^5/25 + 1/P.size^2 * ε * (P.size.choose 2) * ε^4/3
        : begin
          have hP₀ : (0 : ℝ) < P.size := nat.cast_pos.2 ((nat.zero_lt_succ _).trans_le hP₁₀₀),
          rw [sub_eq_add_neg, add_assoc, ←neg_div, nat.cast_choose_two_right],
          refine add_le_add_left _ _,
          calc
            - ε^5/25 + 1/P.size^2 * ε * (P.size * (P.size - 1)/2) * ε^4/3
                = ε^5 * ((P.size * (P.size - 1))/P.size^2/6 - 1/25)
                : by ring
            ... = ε^5 * ((1 - 1/P.size)/6 - 1/25)
                : by rw [sq, mul_div_mul_left _ _ hP₀.ne', sub_div, div_self hP₀.ne']
            ... ≥ ε^5/8
                : begin
                  rw @div_eq_mul_inv ℝ _ _ 8,
                  refine mul_le_mul_of_nonneg_left _ _,
                  rw [le_sub_iff_add_le, le_div_iff (by norm_num : (0 : ℝ) < 6),
                    le_sub_iff_add_le, ←le_sub_iff_add_le', div_le_iff hP₀, ←div_le_iff'],
                  norm_num,
                  exact_mod_cast hP₁₀₀,
                  norm_num,
                  exact nonneg_of_mul_nonneg_right ((by norm_num : (0 : ℝ) ≤ 100).trans hε.le)
                    (pow_pos zero_lt_four _),
                end
        end
    ... ≤ index G (hP.increment G ε) : sorry,
end.

end increment

/-- The maximal number of times we need to blow up an equipartition to make it uniform -/
noncomputable def iteration_bound (ε : ℝ) (l : ℕ) : ℕ :=
max l (nat_floor (real.log (100/ε^5) / real.log 4) + 1)

lemma le_iteration_bound (ε : ℝ) (l : ℕ) : l ≤ iteration_bound ε l := le_max_left l _
lemma iteration_bound_pos (ε : ℝ) (l : ℕ) : 0 < iteration_bound ε l :=
nat.succ_pos'.trans_le (le_max_right _ _)

lemma const_lt_mul_pow_iteration_bound {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
  100 < ε^5 * 4^iteration_bound ε l :=
begin
  rw [←real.rpow_nat_cast 4, ←div_lt_iff' (pow_pos hε 5), real.lt_rpow_iff_log_lt, ←div_lt_iff,
    iteration_bound, nat.cast_max],
  { exact lt_max_of_lt_right (lt_nat_floor_add_one _) },
  { apply real.log_pos,
    norm_num },
  { exact div_pos (by norm_num) (pow_pos hε 5) },
  norm_num,
end

/-- An explicit bound on the size of the equipartition in the proof of Szemerédi's Regularity Lemma
-/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l)) *
  16^(exp_bound^[nat_floor (4/ε^5)] (iteration_bound ε l))

lemma iteration_bound_le_szemeredi_bound (ε l) :
  iteration_bound ε l ≤ szemeredi_bound ε l :=
(id_le_iterate_of_id_le le_exp_bound _ _).trans
  (nat.le_mul_of_pos_right (pow_pos (by norm_num) _))

/-- Effective Szemerédi's Regularity Lemma: For any sufficiently big graph, there is an ε-uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity [nonempty α] {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) (l : ℕ)
  (hG : l ≤ card α) :
  ∃ (P : finpartition α),
    P.is_equipartition ∧ l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  obtain hα | hα := le_total (card α) (szemeredi_bound ε l),
  { refine ⟨discrete_finpartition_on _, discrete_finpartition_on.is_equipartition _, _⟩,
    rw [discrete_finpartition_on.size, card_univ],
    exact ⟨hG, hα, discrete_finpartition_on.is_uniform _ G hε⟩ },
  let t := iteration_bound ε l,
  have ht : 0 < t := iteration_bound_pos _ _,
  suffices h : ∀ i, ∃ (P : finpartition α), P.is_equipartition ∧
    t ≤ P.size ∧ P.size ≤ (exp_bound^[i]) t ∧ (P.is_uniform G ε ∨ ε^5 / 8 * i ≤ P.index G),
  { obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := h (nat_floor (4/ε^5) + 1),
    refine ⟨P, hP₁, (le_iteration_bound _ _).trans hP₂, hP₃.trans _, _⟩,
    { rw function.iterate_succ_apply',
      exact mul_le_mul_left' (pow_le_pow_of_le_left (by norm_num) (by norm_num) _) _ },
    apply hP₄.resolve_right,
    rintro hPindex,
    apply lt_irrefl (1/2 : ℝ),
    calc
      1/2 = ε ^ 5 / 8 * (4 / ε ^ 5)
          : by { rw [mul_comm, div_mul_div_cancel 4 (pow_pos hε 5).ne'], norm_num }
      ... < ε ^ 5 / 8 * (nat_floor (4 / ε ^ 5) + 1)
          : (mul_lt_mul_left (div_pos (pow_pos hε 5) (by norm_num))).2 (lt_nat_floor_add_one _)
      ... ≤ P.index G : hPindex
      ... ≤ 1/2 : P.index_le_half G },
  intro i,
  induction i with i ih,
  { have : t ≤ (univ : finset α).card :=
      (iteration_bound_le_szemeredi_bound _ _).trans (by rwa finset.card_univ),
    obtain ⟨P, hP₁, hP₂⟩ := dummy_equipartition (univ : finset α) ht this,
    refine ⟨P, hP₁, hP₂.ge, hP₂.le, or.inr _⟩,
    rw [nat.cast_zero, mul_zero],
    exact index_nonneg _ _ },
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := ih,
  by_cases huniform : P.is_uniform G ε,
  { refine ⟨P, hP₁, hP₂, _, or.inl huniform⟩,
    rw function.iterate_succ_apply',
    exact hP₃.trans (le_exp_bound _) },
  replace hP₄ := hP₄.resolve_left huniform,
  have hεl' : 100 < ε ^ 5 * 4 ^ P.size,
  { apply lt_of_lt_of_le (const_lt_mul_pow_iteration_bound hε l),
    rw mul_le_mul_left (pow_pos hε 5),
    refine pow_le_pow (by norm_num) hP₂ },
  have hi : (i : ℝ) ≤ 4 / ε^5,
  { have hi := hP₄.trans (index_le_half G P),
    rw [div_mul_eq_mul_div, div_le_iff (show (0:ℝ) < 8, by norm_num)] at hi,
    norm_num at hi,
    rwa le_div_iff' (pow_pos hε _) },
  have hsize : P.size ≤ (exp_bound^[nat_floor (4/ε^5)] t) :=
    hP₃.trans (iterate_le_iterate_of_id_le le_exp_bound (le_nat_floor_of_le hi) _),
  have hPα : P.size * 16^P.size ≤ card α :=
    (nat.mul_le_mul hsize (nat.pow_le_pow_of_le_right (by norm_num) hsize)).trans hα,
  refine ⟨hP₁.increment G ε, increment.is_equipartition hP₁ G ε, _, _,
    or.inr (le_trans _ (increment.index hP₁ sorry hεl' hPα huniform))⟩,
  { rw increment.size hP₁ hPα huniform,
    exact hP₂.trans (le_exp_bound _) },
  { rw [increment.size hP₁ hPα huniform, function.iterate_succ_apply'],
    exact exp_bound_mono hP₃ },
  rw [nat.cast_succ, mul_add, mul_one],
  exact add_le_add_right hP₄ _,
end
