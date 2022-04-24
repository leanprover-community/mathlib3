/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.regularity.bound
import .atomise
import .equitabilise
import .prereqs
import .witness

/-!
# Chunk of `increment`
-/

open finpartition finset fintype rel szemeredi_regularity
open_locale big_operators classical

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ) {U : finset α} (hU : U ∈ P.parts) (V : finset α)

local notation `m` := (card α/step_bound P.parts.card : ℕ)

/-- The portion of `increment` that partitions `U`. -/
noncomputable def finpartition.is_equipartition.chunk_increment :
  finpartition U :=
dite (U.card = m * 4^P.parts.card + (card α/P.parts.card - m * 4^P.parts.card))
  (λ hUcard, (atomise U (P.witnesses G ε U)).equitabilise $ card_aux₁ hUcard)
  (λ hUcard, (atomise U (P.witnesses G ε U)).equitabilise $ card_aux₂ hP hU hUcard)
  -- hP and hU are used to get that U has size m * 4^P.parts.card + a or m * 4^P.parts.card + a + 1

/-- The portion of `chunk_increment` that's contained in the witness of non uniformity of `U` and
`V`. -/
noncomputable def finpartition.is_equipartition.star (V : finset α) : finset (finset α) :=
(hP.chunk_increment G ε hU).parts.filter (λ x, x ⊆ G.witness ε U V)

/-! # star -/

/-- Each thing in star is a subset of the witness. -/
lemma subset_witness_of_mem_star : ∀ A ∈ hP.star G ε hU V, A ⊆ G.witness ε U V :=
λ A hA, (mem_filter.1 hA).2

lemma bUnion_star_subset_witness : (hP.star G ε hU V).bUnion id ⊆ G.witness ε U V :=
bUnion_subset_iff_forall_subset.2 (subset_witness_of_mem_star hP G ε hU V)

variables {hP G ε hU V}

lemma star_subset_chunk_increment : hP.star G ε hU V ⊆ (hP.chunk_increment G ε hU).parts :=
filter_subset _ _

lemma star_pairwise_disjoint : (hP.star G ε hU V : set (finset α)).pairwise_disjoint id :=
(hP.chunk_increment G ε hU).disjoint.subset star_subset_chunk_increment

lemma witness_sdiff_bUnion_star_small (hV : V ∈ P.parts) (hUV : U ≠ V) (h₂ : ¬G.is_uniform ε U V) :
  (G.witness ε U V \ (hP.star G ε hU V).bUnion id).card ≤ 2^(P.parts.card - 1) * m :=
begin
  have hX : G.witness ε U V ∈ P.witnesses G ε U := mem_image_of_mem _ (by simp [hUV, hV, h₂]),
  have q : G.witness ε U V \ (hP.star G ε hU V).bUnion id ⊆
    ((atomise U (P.witnesses G ε U)).parts.filter
      (λ B, B ⊆ G.witness ε U V ∧ B.nonempty)).bUnion
      (λ B, B \ ((hP.chunk_increment G ε hU).parts.filter (λ x, x ⊆ B)).bUnion id),
  { intros x hx,
    rw [←union_of_atoms' (G.witness ε U V) hX (G.witness_subset h₂),
      finpartition.is_equipartition.star, mem_sdiff, mem_bUnion] at hx,
    simp only [not_exists, mem_bUnion, and_imp, filter_congr_decidable, exists_prop, mem_filter,
      not_and, mem_sdiff, id.def, mem_sdiff] at hx ⊢,
    obtain ⟨⟨B, hB₁, hB₂⟩, hx⟩ := hx,
    exact ⟨B, hB₁, hB₂, λ A hA AB, hx A hA $ AB.trans hB₁.2.1⟩ },
  apply (card_le_of_subset q).trans (card_bUnion_le.trans _),
  have :
    ∑ i in (atomise U (P.witnesses G ε U)).parts.filter (λ B, B ⊆ G.witness ε U V ∧ B.nonempty), m
      ≤ 2 ^ (P.parts.card - 1) * m,
  { rw sum_const_nat,
    { apply nat.mul_le_mul_right,
      have t := partial_atomise (G.witness ε U V) hX,
      rw filter_congr_decidable at t,
      apply t.trans (pow_le_pow (by norm_num) (nat.sub_le_sub_right _ _)),
      apply card_image_le.trans (card_le_of_subset (filter_subset _ _)) },
    { intros,
      refl } },
  refine le_trans _ this,
  suffices : ∀ B ∈ (atomise U (P.witnesses G ε U)).parts,
          (B \ ((hP.chunk_increment G ε hU).parts.filter (λ x, x ⊆ B)).bUnion id).card ≤ m,
  { exact sum_le_sum (λ B hB, this B $ filter_subset _ _ hB) },
  intros B hB,
  rw [finpartition.is_equipartition.chunk_increment],
  split_ifs with h₁,
  { convert card_parts_equitabilise_subset_le (card_aux₁ h₁) hB },
  { convert card_parts_equitabilise_subset_le (card_aux₂ hP hU h₁) hB }
end

lemma one_sub_eps_mul_card_witness_le_card_star (hV : V ∈ P.parts) (hUV : U ≠ V)
  (hunif : ¬G.is_uniform ε U V) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1) :
  (1 - ε/10) * (G.witness ε U V).card ≤ ((hP.star G ε hU V).bUnion id).card :=
begin
  have hP₁ : 0 < P.parts.card := finset.card_pos.2 ⟨_, hU⟩,
  have : (2^P.parts.card : ℝ) * m/(U.card * ε) ≤ ε/10,
  { rw [←div_div_eq_div_mul, div_le_iff' (eps_pos hPε)],
    refine le_of_mul_le_mul_left _ (pow_pos zero_lt_two P.parts.card),
    calc
      2^P.parts.card * ((2^P.parts.card * m : ℝ)/U.card)
          = (2 * 2)^P.parts.card * m/U.card : by rw [mul_pow, ←mul_div_assoc, mul_assoc]
      ... = 4^P.parts.card * m/U.card : by norm_num
      ... ≤ 1 : div_le_one_of_le (pow_mul_m_le_card_part hP hU) (nat.cast_nonneg _)
      ... ≤ 2^P.parts.card * ε^2 / 10 : begin
              refine (one_le_sq_iff (div_nonneg (mul_nonneg (pow_nonneg (@zero_le_two ℝ _) _) $
                sq_nonneg _) $ by norm_num)).1 _,
              rw [div_pow, mul_pow, pow_right_comm, ←pow_mul ε,
                one_le_div (sq_pos_of_ne_zero (10 : ℝ) $ by norm_num)],
              calc
                (10 ^ 2 : ℝ)
                = 100 : by norm_num
                ... ≤ 4^P.parts.card * ε^5 : hPε
                ... ≤ 4^P.parts.card * ε^4
                    : mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (eps_pos hPε).le hε₁
                        (nat.le_succ _)) (pow_nonneg zero_lt_four.le _)
                ... = (2^2)^P.parts.card * ε ^ (2 * 2) : by norm_num,
            end
      ... = 2^P.parts.card * (ε * (ε / 10)) : by rw [mul_div_assoc, sq, mul_div_assoc] },
  calc
    (1 - ε/10) * (G.witness ε U V).card
        ≤ (1 - 2^P.parts.card * m/(U.card * ε)) * (G.witness ε U V).card
        : mul_le_mul_of_nonneg_right (sub_le_sub_left this _) (nat.cast_nonneg _)
    ... = (G.witness ε U V).card - 2^P.parts.card * m/(U.card * ε) * (G.witness ε U V).card
        : by rw [sub_mul, one_mul]
    ... ≤ (G.witness ε U V).card - 2^(P.parts.card - 1) * m : begin
          refine sub_le_sub_left _ _,
          have : (2 : ℝ)^P.parts.card = 2^(P.parts.card - 1) * 2,
          { rw [←pow_succ', nat.sub_add_cancel hP₁] },
          rw [←mul_div_right_comm, this, mul_right_comm _ (2 : ℝ), mul_assoc, le_div_iff
            (mul_pos (nat.cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos) (eps_pos hPε))],
          refine mul_le_mul_of_nonneg_left _ _,
          exact (G.witness_card hunif).trans
            (le_mul_of_one_le_left (nat.cast_nonneg _) one_le_two),
          exact mul_nonneg (pow_nonneg zero_le_two _) (nat.cast_nonneg _),
        end
    ... ≤ ((hP.star G ε hU V).bUnion id).card
        : begin
          norm_cast,
          rw [sub_le, ←nat.cast_sub (finset.card_le_of_subset $ bUnion_star_subset_witness
            hP G ε hU V), ←card_sdiff (bUnion_star_subset_witness hP G ε hU V), nat.cast_le],
          exact witness_sdiff_bUnion_star_small hV hUV hunif,
        end
end

variables {hP G ε U hU V}

/-! # chunk_increment -/

lemma card_chunk_increment (hm : m ≠ 0) : (hP.chunk_increment G ε hU).parts.card = 4^P.parts.card :=
begin
  rw finpartition.is_equipartition.chunk_increment,
  split_ifs,
  { rw [card_parts_equitabilise hm, nat.sub_add_cancel],
    exact le_of_lt a_add_one_le_four_pow_parts_card },
  { rw [card_parts_equitabilise hm, nat.sub_add_cancel a_add_one_le_four_pow_parts_card] }
end

lemma card_eq_of_mem_parts_chunk_increment {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  A.card = m ∨ A.card = m + 1 :=
begin
  rw [finpartition.is_equipartition.chunk_increment] at hA,
  split_ifs at hA;
  apply card_eq_of_mem_parts_equitabilise _ hA,
end

lemma m_le_card_of_mem_chunk_increment_parts {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) : m ≤ A.card :=
(card_eq_of_mem_parts_chunk_increment hA).elim ge_of_eq (λ i, by simp [i])

lemma card_le_m_add_one_of_mem_chunk_increment_parts {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) : A.card ≤ m + 1 :=
(card_eq_of_mem_parts_chunk_increment hA).elim (λ i, by simp [i]) (λ i, i.le)

lemma card_bUnion_star_le_m_add_one_card_star_mul :
  (((hP.star G ε hU V).bUnion id).card : ℝ) ≤ (hP.star G ε hU V).card * (m + 1) :=
by exact_mod_cast (card_bUnion_le_card_mul _ _ _ $ λ s hs,
  card_le_m_add_one_of_mem_chunk_increment_parts $ star_subset_chunk_increment hs)

lemma le_sum_card_subset_chunk_increment_parts {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  (A.card : ℝ) * u.card * (m/(m+1)) ≤ (A.sup id).card :=
begin
  rw [mul_div_assoc', div_le_iff coe_m_add_one_pos, mul_right_comm],
  refine mul_le_mul _ _ (nat.cast_nonneg _) (nat.cast_nonneg _),
  { rw [←(of_subset _ hA rfl).sum_card_parts, of_subset_parts, ←nat.cast_mul, nat.cast_le],
    exact card_nsmul_le_sum _ _ _ (λ x hx, m_le_card_of_mem_chunk_increment_parts (hA hx)) },
  { exact_mod_cast card_le_m_add_one_of_mem_chunk_increment_parts (hA hu) }
end

lemma sum_card_subset_chunk_increment_parts_le (m_pos : (0 : ℝ) < m) {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  ((A.sup id).card : ℝ) ≤ (A.card * u.card) * ((m+1)/m) :=
begin
  rw [sup_eq_bUnion, mul_div_assoc', le_div_iff m_pos, mul_right_comm],
  refine mul_le_mul _ _ (nat.cast_nonneg _) (by exact_mod_cast nat.zero_le _),
  { norm_cast,
    refine card_bUnion_le_card_mul _ _ _ (λ x hx, _),
    apply card_le_m_add_one_of_mem_chunk_increment_parts (hA hx) },
  { exact_mod_cast m_le_card_of_mem_chunk_increment_parts (hA hu) }
end

lemma one_sub_le_m_div_m_add_one_sq [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) :
  1 - ε^5/50 ≤ (m/(m + 1))^2 :=
begin
  have : ((m:ℝ) / (m+1)) = 1 - 1/(m+1),
  { rw [one_sub_div coe_m_add_one_pos.ne', add_sub_cancel] },
  rw [this, sub_sq, one_pow, mul_one],
  refine le_trans _ (le_add_of_nonneg_right (sq_nonneg _)),
  rw [sub_le_sub_iff_left, ←le_div_iff' (show (0:ℝ) < 2, by norm_num), div_div_eq_div_mul,
    one_div_le coe_m_add_one_pos (div_pos (eps_pow_five_pos hPε) (show (0:ℝ) < 50*2, by norm_num)),
    one_div_div],
  refine le_trans _ (le_add_of_nonneg_right zero_le_one),
  norm_num,
  apply hundred_div_ε_pow_five_le_m hPα hPε,
end

lemma m_add_one_div_m_le_one_add [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1) :
  ((m + 1 : ℝ)/m)^2 ≤ 1 + ε^5/49 :=
begin
  rw same_add_div (m_coe_pos hPα).ne',
  have : 1 + 1/(m:ℝ) ≤ 1 + ε^5/100,
  { rw [add_le_add_iff_left, ←one_div_div (100:ℝ)],
    refine one_div_le_one_div_of_le (div_pos (by norm_num) (eps_pow_five_pos hPε)) _,
    apply hundred_div_ε_pow_five_le_m hPα hPε },
  refine (pow_le_pow_of_le_left _ this 2).trans _,
  { exact add_nonneg zero_le_one (one_div_nonneg.2 (nat.cast_nonneg _)) },
  rw [add_sq, one_pow, add_assoc, add_le_add_iff_left, mul_one, ←le_sub_iff_add_le',
    div_eq_mul_one_div _ (49:ℝ), mul_div_comm (2:ℝ), ←mul_sub_left_distrib, div_pow,
    div_le_iff (show (0:ℝ) < 100^2, by norm_num), mul_assoc, sq],
  refine mul_le_mul_of_nonneg_left _ (eps_pow_five_pos hPε).le,
  exact (pow_le_one 5 (eps_pos hPε).le hε₁).trans (by norm_num),
end

lemma density_sub_eps_le_sum_density_div_card [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
  ↑(G.edge_density (A.bUnion id) (B.bUnion id)) - ε^5/50 ≤
    (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) :=
begin
  have : ↑(G.edge_density (A.bUnion id) (B.bUnion id)) - ε^5/50
                                      ≤ (1 - ε^5/50) * G.edge_density (A.bUnion id) (B.bUnion id),
  { rw [sub_mul, one_mul, sub_le_sub_iff_left],
    refine mul_le_of_le_one_right (div_nonneg (eps_pow_five_pos hPε).le (by norm_num)) _,
    exact_mod_cast G.edge_density_le_one _ _ },
  refine this.trans _,
  simp only [simple_graph.edge_density_def, simple_graph.interedges, ←sup_eq_bUnion, nat.cast_sum,
    rel.card_interedges_finpartition (of_subset _ hA rfl) (of_subset _ hB rfl), of_subset_parts,
    sum_div, mul_sum, rat.cast_sum, rat.cast_div, rat.cast_mul, div_div_eq_div_mul,
    mul_div_comm ((1:ℝ) - _)],
  push_cast,
  apply sum_le_sum,
  simp only [and_imp, prod.forall, mem_product],
  rintro x y hx hy,
  rw [mul_mul_mul_comm, mul_comm (x.card : ℝ), mul_comm (y.card : ℝ), le_div_iff, mul_assoc],
  { apply mul_le_of_le_one_right (nat.cast_nonneg _),
    rw [div_mul_eq_mul_div, ←mul_assoc, mul_assoc],
    refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
    refine (mul_le_mul_of_nonneg_right (one_sub_le_m_div_m_add_one_sq hPα hPε) _).trans _,
    { exact_mod_cast (nat.zero_le _) },
    rw [sq, mul_mul_mul_comm, mul_comm ((m:ℝ)/_), mul_comm ((m:ℝ)/_)],
    refine mul_le_mul _ _ _ (nat.cast_nonneg _),
    apply le_sum_card_subset_chunk_increment_parts hA hx,
    apply le_sum_card_subset_chunk_increment_parts hB hy,
    apply mul_nonneg (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) _,
    refine div_nonneg (nat.cast_nonneg m) coe_m_add_one_pos.le },
  refine mul_pos (mul_pos _ _) (mul_pos _ _); rw [nat.cast_pos, finset.card_pos],
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]
end

lemma sum_density_div_card_le_density_add_eps [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
  (∑ ab in A.product B, (G.edge_density ab.1 ab.2 : ℝ))/(A.card * B.card) ≤
  G.edge_density (A.bUnion id) (B.bUnion id) + ε^5/49 :=
begin
  have : (1 + ε^5/49) * G.edge_density (A.bUnion id) (B.bUnion id) ≤
            G.edge_density (A.bUnion id) (B.bUnion id) + ε^5/49,
  { rw [add_mul, one_mul, add_le_add_iff_left],
    refine mul_le_of_le_one_right (div_nonneg (eps_pow_five_pos hPε).le (by norm_num)) _,
    exact_mod_cast G.edge_density_le_one _ _ },
  refine le_trans _ this,
  simp only [simple_graph.edge_density, edge_density, ←sup_eq_bUnion, nat.cast_sum, mul_sum,
    sum_div, rel.card_interedges_finpartition (of_subset _ hA rfl) (of_subset _ hB rfl),
    rat.cast_sum, rat.cast_div, rat.cast_mul,
    of_subset_parts, mul_div_comm ((1:ℝ) + _), div_div_eq_div_mul],
  push_cast,
  apply sum_le_sum,
  simp only [and_imp, prod.forall, mem_product],
  intros x y hx hy,
  rw [mul_mul_mul_comm, mul_comm (x.card : ℝ), mul_comm (y.card : ℝ), div_le_iff, mul_assoc],
  { refine le_mul_of_one_le_right (nat.cast_nonneg _) _,
    rw [div_mul_eq_mul_div, one_le_div],
    refine le_trans _ (mul_le_mul_of_nonneg_right (m_add_one_div_m_le_one_add hPα hPε hε₁) _),
    { rw [sq, mul_mul_mul_comm, mul_comm (_/(m:ℝ)), mul_comm (_/(m:ℝ))],
      refine mul_le_mul _ _ (nat.cast_nonneg _) _,
      apply sum_card_subset_chunk_increment_parts_le (m_coe_pos hPα) hA hx,
      apply sum_card_subset_chunk_increment_parts_le (m_coe_pos hPα) hB hy,
      apply mul_nonneg (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)) _,
      refine div_nonneg coe_m_add_one_pos.le (nat.cast_nonneg m) },
    { exact_mod_cast (nat.zero_le _) },
    rw [←nat.cast_mul, nat.cast_pos],
    apply nat.mul_pos;
    rw [finset.card_pos, sup_eq_bUnion, bUnion_nonempty],
    { exact ⟨_, hx, nonempty_of_mem_parts _ (hA hx)⟩ },
    { exact ⟨_, hy, nonempty_of_mem_parts _ (hB hy)⟩ } },
  refine mul_pos (mul_pos _ _) (mul_pos _ _); rw [nat.cast_pos, finset.card_pos],
  exacts [⟨_, hx⟩, nonempty_of_mem_parts _ (hA hx), ⟨_, hy⟩, nonempty_of_mem_parts _ (hB hy)]
end

lemma average_density_near_total_density [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
  |(∑ ab in A.product B, (G.edge_density ab.1 ab.2 : ℝ))/(A.card * B.card) -
    G.edge_density (A.bUnion id) (B.bUnion id)| ≤ ε^5/49 :=
begin
  rw abs_sub_le_iff,
  split,
  { rw sub_le_iff_le_add',
    exact sum_density_div_card_le_density_add_eps hPα hPε hε₁ hA hB },
  suffices : (G.edge_density (A.bUnion id) (B.bUnion id) : ℝ) -
    (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) ≤ ε^5/50,
  { apply this.trans,
    exact div_le_div_of_le_left (eps_pow_five_pos hPε).le (by norm_num) (by norm_num) },
  rw [sub_le_iff_le_add, ←sub_le_iff_le_add'],
  apply density_sub_eps_le_sum_density_div_card hPα hPε hA hB,
end

-- predagger inequality
lemma sq_density_sub_eps_le_sum_sq_density_div_card_aux [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  {U V : finset α} (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
  ↑(G.edge_density U V)^2 - ε^5/25 ≤
    ((∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
      G.edge_density ab.1 ab.2)/16^P.parts.card)^2 :=
begin
  obtain hGε | hGε := le_total ↑(G.edge_density U V) (ε^5/50),
  { refine (sub_nonpos_of_le $ (sq_le _ _).trans $ hGε.trans _).trans (sq_nonneg _),
    { exact_mod_cast G.edge_density_nonneg _ _ },
    { exact_mod_cast G.edge_density_le_one _ _ },
    { exact div_le_div_of_le_left (eps_pow_five_pos hPε).le (by norm_num) (by norm_num) } },
  rw ←sub_nonneg at hGε,
  have : ↑(G.edge_density U V) - ε ^ 5 / 50 ≤
    (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
      G.edge_density ab.1 ab.2) / (16 ^ P.parts.card),
  { apply (le_trans _ $ density_sub_eps_le_sum_density_div_card hPα hPε
      (set.subset.refl (hP.chunk_increment G ε hU).parts)
      (set.subset.refl (hP.chunk_increment G ε hV).parts)).trans _,
    { rw [bUnion_parts, bUnion_parts] },
    { rw [card_chunk_increment (m_pos hPα).ne', card_chunk_increment (m_pos hPα).ne', ←nat.cast_mul,
        ←mul_pow, nat.cast_pow],
      norm_cast } },
  apply le_trans _ (pow_le_pow_of_le_left hGε this 2),
  rw [sub_sq, sub_add, sub_le_sub_iff_left],
  apply (sub_le_self _ (sq_nonneg (ε^5/50))).trans,
  rw [mul_right_comm, mul_div_comm, div_eq_mul_one_div (ε^5), (show (2:ℝ)/50 = 1/25, by norm_num)],
  exact mul_le_of_le_one_right (mul_nonneg (eps_pow_five_pos hPε).le (by norm_num))
    (by exact_mod_cast G.edge_density_le_one _ _),
end

-- dagger inequality
lemma sq_density_sub_eps_le_sum_sq_density_div_card [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  {U V : finset α} (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
  (G.edge_density U V : ℝ)^2 - ε^5/25 ≤
  (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2^2)/16^P.parts.card :=
begin
  apply (sq_density_sub_eps_le_sum_sq_density_div_card_aux hPα hPε hU hV).trans,
  convert chebyshev _ _;
  rw [card_product, nat.cast_mul, card_chunk_increment (m_pos hPα).ne',
    card_chunk_increment (m_pos hPα).ne', ←nat.cast_mul, ←mul_pow];
  norm_cast,
end

lemma abs_density_star_sub_density_le_eps (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUV' : U ≠ V)
  (hUV : ¬ G.is_uniform ε U V) :
  |(G.edge_density ((hP.star G ε hU V).bUnion id) ((hP.star G ε hV U).bUnion id) : ℝ) -
    G.edge_density (G.witness ε U V) (G.witness ε V U)| ≤ ε/5 :=
begin
  convert lemma_A G.adj
    (bUnion_star_subset_witness hP G ε hU V)
    (bUnion_star_subset_witness hP G ε hV U)
    (div_nonneg (eps_pos hPε).le $ by norm_num)
    (one_sub_eps_mul_card_witness_le_card_star hV hUV' hUV hPε hε₁)
    (one_sub_eps_mul_card_witness_le_card_star hU hUV'.symm (λ hVU, hUV hVU.symm) hPε hε₁),
  linarith,
end

lemma m_bound {x : ℝ} (hx : 0 < x) : (x + 1) * (1 - 1/x) / x ≤ 1 :=
begin
  rw [div_le_one hx, one_sub_div hx.ne', mul_div_assoc', div_le_iff hx],
  linarith,
end

lemma eps_le_card_star_div [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1) {U V : finset α} (hU : U ∈ P.parts)
  (hV : V ∈ P.parts) (hUV : U ≠ V) (hunif : ¬ G.is_uniform ε U V) :
  4/5 * ε ≤ (hP.star G ε hU V).card / 4^P.parts.card :=
begin
  have hm : (0 : ℝ) ≤ 1 - 1/m :=
    sub_nonneg_of_le (one_div_le_one_of_one_le $ one_le_m_coe hPα),
  have hε : 0 ≤ 1 - ε / 10 :=
    sub_nonneg_of_le (div_le_one_of_le (hε₁.trans $ by norm_num) $ by norm_num),
  calc
    4/5 * ε
        = (1 - 1/10) * (1 - 1/9) * ε : by norm_num
    ... ≤ (1 - ε/10) * (1 - 1/m) * ((G.witness ε U V).card / U.card)
        : mul_le_mul
            (mul_le_mul (sub_le_sub_left (div_le_div_of_le_of_nonneg hε₁ $ by norm_num) _)
              (sub_le_sub_left (div_le_div_of_le_left zero_le_one (by norm_num)
                (by exact_mod_cast ((show 9 ≤ 100, by norm_num).trans
                $ hundred_le_m hPα hPε hε₁))) _)
              (by norm_num) hε)
            ((le_div_iff' $ (@nat.cast_pos ℝ _ _ _).2 (P.nonempty_of_mem_parts hU).card_pos).2
              (G.witness_card hunif))
            (eps_pos hPε).le
            (mul_nonneg hε hm)
    ... = (1 - ε/10) * (G.witness ε U V).card * ((1 - 1/m) / U.card)
        : by rw [mul_assoc, mul_assoc, mul_div_comm]
    ... ≤ ((hP.star G ε hU V).bUnion id).card * ((1 - 1/m) / U.card)
        : (mul_le_mul_of_nonneg_right
            (one_sub_eps_mul_card_witness_le_card_star hV hUV hunif hPε hε₁)
            (div_nonneg hm $ nat.cast_nonneg _))
    ... ≤ (hP.star G ε hU V).card * (m + 1) * ((1 - 1/m) / U.card) :
            mul_le_mul_of_nonneg_right card_bUnion_star_le_m_add_one_card_star_mul
              (div_nonneg hm $ nat.cast_nonneg _)
    ... ≤ (hP.star G ε hU V).card * (m + 1) * ((1 - 1/m) / (4^P.parts.card * m))
        : mul_le_mul_of_nonneg_left (div_le_div_of_le_left hm
            (mul_pos four_pow_pos $ m_coe_pos hPα) $ pow_mul_m_le_card_part hP hU)
            (mul_nonneg (nat.cast_nonneg _) $ add_nonneg (nat.cast_nonneg _) zero_le_one)
    ... ≤ (hP.star G ε hU V).card / 4^P.parts.card :
    begin
      rw [mul_assoc, mul_comm ((4:ℝ)^P.parts.card), ←div_div_eq_div_mul, ←mul_div_assoc,
        ←div_mul_eq_mul_div_comm],
      refine mul_le_of_le_one_right (div_nonneg (nat.cast_nonneg _) four_pow_pos.le) _,
      rw mul_div_assoc',
      exact m_bound (m_coe_pos hPα),
    end
end

lemma stuff [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (h_diff : U ≠ V)
  (hUV : ¬ G.is_uniform ε U V) :
  3/4 * ε ≤
    |(∑ ab in (hP.star G ε hU V).product (hP.star G ε hV U), G.edge_density ab.1 ab.2)
      / ((hP.star G ε hU V).card * (hP.star G ε hV U).card) -
        (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
          G.edge_density ab.1 ab.2)/16^P.parts.card| :=
begin
  rw [(show (16:ℝ) = 4^2, by norm_num), pow_right_comm, sq ((4:ℝ)^_)],
  set p : ℝ := (∑ ab in (hP.star G ε hU V).product (hP.star G ε hV U), G.edge_density ab.1 ab.2)
      / ((hP.star G ε hU V).card * (hP.star G ε hV U).card),
  set q : ℝ := (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
          G.edge_density ab.1 ab.2)/(4 ^ P.parts.card * 4 ^ P.parts.card),
  change _ ≤ |p - q|,
  set r : ℝ := G.edge_density ((hP.star G ε hU V).bUnion id) ((hP.star G ε hV U).bUnion id),
  set s : ℝ := G.edge_density (G.witness ε U V) (G.witness ε V U),
  set t : ℝ := G.edge_density U V,
  have hrs : |r - s| ≤ ε/5 := abs_density_star_sub_density_le_eps hPε hε₁ h_diff hUV,
  have hst : ε ≤ |s - t| := G.witness_pair_spec h_diff hUV,
  have hpr : |p - r| ≤ ε^5/49 := average_density_near_total_density hPα hPε hε₁
    star_subset_chunk_increment star_subset_chunk_increment,
  have hqt : |q - t| ≤ ε^5/49,
  { have := average_density_near_total_density hPα hPε hε₁
      (subset.refl (hP.chunk_increment G ε hU).parts)
      (subset.refl (hP.chunk_increment G ε hV).parts),
    simp_rw [←sup_eq_bUnion, sup_parts, card_chunk_increment (m_pos hPα).ne', nat.cast_pow] at this,
    norm_num at this,
    exact this },
  have hε : 0 < ε := eps_pos hPε,
  have hpr' : |p - r| ≤ ε/49,
  { refine hpr.trans (div_le_div_of_le_of_nonneg _ (by norm_num)),
    simpa using pow_le_pow_of_le_one hε.le hε₁ (show 1 ≤ 5, by norm_num) },
  have hqt' : |q - t| ≤ ε/49,
  { apply hqt.trans (div_le_div_of_le_of_nonneg _ (by norm_num)),
    simpa using pow_le_pow_of_le_one hε.le hε₁ (show 1 ≤ 5, by norm_num) },
  rw abs_sub_le_iff at hrs hpr' hqt',
  rw le_abs at hst ⊢,
  cases hst,
  left, linarith,
  right, linarith,
end

-- double dagger inequality
lemma sq_density_sub_eps_le_sum_sq_density_div_card_of_nonuniform [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (h_diff : U ≠ V)
  (hUV : ¬ G.is_uniform ε U V) :
  (G.edge_density U V : ℝ)^2 - ε^5/25 + ε^4/3 ≤
  (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2^2)/16^P.parts.card :=
calc
  ↑(G.edge_density U V)^2 - ε^5/25 + ε^4/3
      ≤ G.edge_density U V^2 - ε^5/25 +
          (hP.star G ε hU V).card * (hP.star G ε hV U).card/16^P.parts.card * (9/16) * ε^2 :
        begin
          apply add_le_add_left,
          have Ul : 4/5 * ε ≤ (hP.star G ε hU V).card / _ :=
            eps_le_card_star_div hPα hPε hε₁ hU hV h_diff hUV,
          have Vl : 4/5 * ε ≤ (hP.star G ε hV U).card / _ :=
            eps_le_card_star_div hPα hPε hε₁ hV hU h_diff.symm (λ h, hUV h.symm),
          rw [(show (16 : ℝ) = 4^2, by norm_num), pow_right_comm, sq ((4:ℝ)^_), ←div_mul_div_comm₀,
            mul_assoc],
          have UVl :=
            mul_le_mul Ul Vl
              (mul_nonneg (by norm_num) (eps_pos hPε).le)
              (div_nonneg (nat.cast_nonneg _) four_pow_pos.le),
          apply le_trans _ (mul_le_mul_of_nonneg_right UVl _),
          { field_simp,
            ring_nf,
            apply mul_le_mul_of_nonneg_right,
            norm_num,
            exact pow_nonneg (eps_pos hPε).le _ },
          { norm_num,
            exact pow_nonneg (eps_pos hPε).le _ }
        end
  ... ≤ (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
          G.edge_density ab.1 ab.2^2)/16^P.parts.card :
    begin
      have t : (hP.star G ε hU V).product (hP.star G ε hV U) ⊆
        (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts :=
          product_subset_product star_subset_chunk_increment star_subset_chunk_increment,
      have hε : 0 ≤ ε := (eps_pos hPε).le,
      have h₁ : 0 ≤ 3/4 * ε := by linarith,
      have := lemma_B_ineq t (λ x, G.edge_density x.1 x.2) (G.edge_density U V^2 - ε^5/25) h₁ _ _,
      { simp_rw [card_product, card_chunk_increment (m_pos hPα).ne', ←mul_pow, nat.cast_pow,
          mul_pow, div_pow, ←mul_assoc] at this,
        norm_num at this,
        exact this },
      { simp_rw [card_product, card_chunk_increment (m_pos hPα).ne', ←mul_pow],
        norm_num,
        exact stuff hPα hPε hε₁ h_diff hUV },
      { rw card_product,
        apply (sq_density_sub_eps_le_sum_sq_density_div_card_aux hPα hPε hU hV).trans,
        rw [card_chunk_increment (m_pos hPα).ne', card_chunk_increment (m_pos hPα).ne', ←mul_pow],
        norm_num,
        exact hP }
    end
