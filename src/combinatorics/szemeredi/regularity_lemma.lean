/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .bounds
import .finpartitions
import .witness
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

/-- Lemma A: if A' ⊆ A, B' ⊆ B each take up all but a δ-proportion, then the difference in edge
densities is `≤ 2 δ`. -/
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

open simple_graph
open_locale classical

variables [fintype α] (P : finpartition α)

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

/-! ### The actual proof -/

section chunk_increment
variables {P} (G : simple_graph α)
/-- The part of `increment` that partitions `U`. -/
noncomputable def finpartition_on.is_equipartition.chunk_increment (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ) {U : finset α} (hU : U ∈ P.parts) :
  finpartition_on U :=
dite (U.card = m * 4^P.size + a)
    (λ hUcard, (atomise U ((P.parts.filter $ λ V, ¬G.is_uniform ε U V).image $
      λ V, (G.witness ε U V).1)).equitabilise $ card_aux₂ hUcard)
    (λ hUcard, (atomise U ((P.parts.filter $ λ V, ¬G.is_uniform ε U V).image $
      λ V, (G.witness ε U V).1)).equitabilise $ card_aux₃ hP hU hUcard)

variables {hP : P.is_equipartition} {U : finset α} {hU : U ∈ P.parts}

lemma chunk_increment.size (m_pos : 0 < m) : (hP.chunk_increment G ε hU).size = 4^P.size :=
begin
  rw finpartition_on.is_equipartition.chunk_increment,
  split_ifs,
  { rw [finpartition_on.equitabilise.size m_pos, nat.sub_add_cancel],
    exact le_of_lt a_add_one_le_four_pow_size  },
  { rw [finpartition_on.equitabilise.size m_pos, nat.sub_add_cancel],
    exact a_add_one_le_four_pow_size }
end

lemma card_eq_of_mem_parts_chunk_increment {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  A.card = card α / exp_bound P.size ∨ A.card = card α / exp_bound P.size + 1 :=
begin
  simp [finpartition_on.is_equipartition.chunk_increment] at hA,
  by_cases hUcard : U.card = m * 4^P.size + a,
  { rw dif_pos hUcard at hA,
    exact finpartition_on.card_eq_of_mem_parts_equitabilise _ hA },
  rw dif_neg hUcard at hA,
  exact finpartition_on.card_eq_of_mem_parts_equitabilise _ hA,
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
  (A.card : ℝ) * u.card ≤ (∑ V in A, V.card)/(m/(m + 1)) :=
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
    ... = ∑ V in A, (m : ℝ)
        : by rw [sum_const, nsmul_eq_mul]
    ... ≤ ∑ V in A, V.card
        : sum_le_sum (λ V hV, m_le_card_of_mem_chunk_increment_parts $ hA hV)
end

lemma sum_card_subset_chunk_increment_parts_le (m_pos : 0 < m) {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  (∑ V in A, (V.card : ℝ))/((m + 1)/m) ≤ A.card * u.card :=
begin
  rw div_le_iff, swap,
  { exact div_pos (nat.cast_add_one_pos _) (nat.cast_pos.2 m_pos) },
  calc
    ∑ V in A, (V.card : ℝ)
        ≤ ∑ V in A, (m + 1)
        : sum_le_sum (λ V hV, card_le_m_add_one_of_mem_chunk_increment_parts $ hA hV)
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
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
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
            simp_rw [←div_div_eq_div_mul],
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
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
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
end.

lemma sq_density_sub_eps_le_sum_sq_density_div_card [nonempty α] (hPα : P.size * 16^P.size ≤ card α)
  (hPε : 100 ≤ 4^P.size * ε^5) (m_pos : 0 < m) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} :
  G.edge_density U V^2 - ε^5/25 ≤
  (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2^2)/16^P.size :=
begin
  have hε : 0 < ε^5 := pos_of_mul_pos_left ((by norm_num : (0 : ℝ) < 100).trans_le hPε)
    (pow_nonneg (by norm_num) _),
  have hε₀ : 0 < ε := sorry,
  obtain hGε | hGε := le_total (G.edge_density U V) (ε^5/50),
  { calc
      G.edge_density U V^2 - ε^5/25
          ≤ G.edge_density U V - ε^5/25
          : sub_le_sub_right (sq_le (G.edge_density_nonneg _ _) (G.edge_density_le_one _ _)) _
      ... ≤ ε^5/50 - ε^5/25
          : sub_le_sub_right hGε _
      ... ≤ 0
          : sub_nonpos_of_le (div_le_div_of_le_left hε.le (by norm_num) (by norm_num))
      ... ≤ (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
              G.edge_density ab.1 ab.2^2)/16^P.size
          : div_nonneg (sum_nonneg $ λ i _, sq_nonneg _) (pow_nonneg (by norm_num) _) },
  rw ←sub_nonneg at hGε,
  calc
    G.edge_density U V^2 - ε^5/25
        ≤ G.edge_density U V^2 - ε^5/25 * G.edge_density U V
        : sub_le_sub_left (mul_le_of_le_one_right (div_nonneg hε.le (by norm_num))
            (G.edge_density_le_one _ _)) _
    ... ≤ G.edge_density U V^2 - ε^5/25 * G.edge_density U V + (ε^5/50)^2
        : le_add_of_nonneg_right (sq_nonneg _)
    ... = (G.edge_density U V - ε^5/50)^2
        : by { rw [sub_sq, mul_right_comm, mul_div_comm, div_eq_mul_inv], norm_num }
    ... = (G.edge_density ((hP.chunk_increment G ε hU).parts.bUnion id)
            ((hP.chunk_increment G ε hV).parts.bUnion id) - ε^5/50)^2
        : by rw [finpartition_on.bUnion_parts_eq, finpartition_on.bUnion_parts_eq]
    ... ≤ ((∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
            G.edge_density ab.1 ab.2)/((hP.chunk_increment G ε hU).size
            * (hP.chunk_increment G ε hV).size))^2
        : pow_le_pow_of_le_left
            (by rwa [finpartition_on.bUnion_parts_eq, finpartition_on.bUnion_parts_eq])
            (density_sub_eps_le_sum_density_div_card hPα hPε m_pos set.subset.rfl set.subset.rfl) 2
    ... ≤ (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
            G.edge_density ab.1 ab.2^2)/((hP.chunk_increment G ε hU).size
            * (hP.chunk_increment G ε hV).size)
        : begin
          sorry
          -- exact (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),

        end
    ... = (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
            G.edge_density ab.1 ab.2^2)/16^P.size
        : begin
          rw [chunk_increment.size m_pos, chunk_increment.size m_pos, ←nat.cast_mul, ←mul_pow],
          norm_cast,
        end
end

lemma sq_density_sub_eps_le_sum_sq_density_div_card_of_nonuniform [nonempty α]
  (hPα : P.size * 16^P.size ≤ card α) (hPε : 100 ≤ 4^P.size * ε^5) (m_pos : 0 < m) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUV : ¬ G.is_uniform ε U V) :
  G.edge_density U V^2 - ε^5/25 + ε^4/3 ≤
  (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2^2)/16^P.size :=
begin
  calc
    G.edge_density U V^2 - ε^5/25 + ε^4/3
        ≤  G.edge_density U V^2 - ε^5/25 + 0/16^P.size * (9/16) * ε^4
        : sorry
    ... ≤ (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
            G.edge_density ab.1 ab.2^2)/16^P.size
        : sorry
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
  rw [is_equipartition, finset.equitable_on_iff] at hP,
  rw [increment, bind_size],
  simp_rw [finpartition_on.is_equipartition.chunk_increment, apply_dite finpartition_on.size],
  rw [sum_dite, sum_const_nat, sum_const_nat, card_attach, card_attach], rotate,
  exact λ x hx, finpartition_on.equitabilise.size (nat.div_pos hPα' hPpos) _,
  exact λ x hx, finpartition_on.equitabilise.size (nat.div_pos hPα' hPpos) _,
  rw [nat.sub_add_cancel a_add_one_le_four_pow_size, nat.sub_add_cancel ((nat.le_succ _).trans
    a_add_one_le_four_pow_size), ←add_mul],
  congr,
  rw [filter_card_add_filter_neg_card_eq_card, card_attach, finpartition_on.size],
end

protected lemma is_equipartition (hP : P.is_equipartition) (G : simple_graph α) (ε : ℝ) :
  (hP.increment G ε).is_equipartition :=
begin
  rw [is_equipartition, set.equitable_on_iff_exists_eq_eq_add_one],
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
          rw [sub_eq_add_neg, add_assoc, ←neg_div, nat.cast_choose_two],
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
