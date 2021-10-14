/-
Copyright (c) 2021 Yaël DIllies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël DIllies, Bhavik Mehta
-/
import .chunk
import .index

/-!
# Increment
-/

universes u v
def sym2_pair_bind {α : Type u} {β : Type v} [decidable_eq β] {s : finset α}
  (f : Π (i : α), i ∈ s → finset β) :
  sym2 {x // x ∈ s} → finset (sym2 β) :=
begin
  refine sym2.lift _,
  refine ⟨λ i j, finset.image quotient.mk ((f _ i.2).product (f _ j.2)), _⟩,
  rintro ⟨i, hi⟩ ⟨j, hj⟩,
  ext k,
  induction k using sym2.induction_on with x y,
  simp only [and_comm (_ ∈ f j _), finset.mem_image, exists_prop, prod.exists, finset.mem_product],
  rw exists_comm,
  apply exists₂_congr,
  intros p q,
  rw sym2.eq_swap,
end

lemma mem_sym2_pair_bind {α β : Type*} [decidable_eq β] {s : finset α}
  (f : Π i ∈ s, finset β) (i₁ i₂ : {x // x ∈ s}) (j₁ j₂ : β) :
  ⟦(j₁, j₂)⟧ ∈ sym2_pair_bind f ⟦(i₁, i₂)⟧ ↔
    (j₁ ∈ f _ i₁.2 ∧ j₂ ∈ f _ i₂.2) ∨ (j₂ ∈ f _ i₁.2 ∧ j₁ ∈ f _ i₂.2) :=
begin
  simp only [sym2_pair_bind, sym2.lift_mk, exists_prop, finset.mem_image, subtype.coe_mk,
    subtype.val_eq_coe, prod.exists, finset.mem_product, sym2.eq_iff],
  split,
  { rintro ⟨_, _, h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩,
    { apply or.inl h },
    { apply or.inr h } },
  tauto {closer := `[simp]},
end

lemma sym2.exists {α : Sort*} {f : sym2 α → Prop} : (∃ (x : sym2 α), f x) ↔ ∃ x y, f ⟦(x, y)⟧ :=
begin
  split,
  { rintro ⟨x, hx⟩,
    induction x using sym2.induction_on with x y,
    exact ⟨x, y, hx⟩ },
  { rintro ⟨x, y, h⟩,
    exact ⟨_, h⟩ }
end

open finset fintype simple_graph
open_locale big_operators classical

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_half`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
noncomputable def finpartition_on.is_equipartition.increment : finpartition (univ : finset α) :=
P.bind (λ U, hP.chunk_increment G ε)

open finpartition_on finpartition_on.is_equipartition

variables {G ε}

namespace increment

protected lemma size (hPα : P.size * 16^P.size ≤ card α) (hPG : ¬P.is_uniform G ε) :
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

-- def off_diag : finset (α × α) := (s.product s).filter (λ (a : α × α), a.fst ≠ a.snd)

-- def distinct_pairs (s : finset α) :
--   finset (sym2 α) :=
-- s.off_diag.image quotient.mk


lemma increment_distinct_pairs :
  (hP.increment G ε).parts.distinct_pairs =
    P.parts.attach.bUnion (λ i, (hP.chunk_increment G ε i.2).parts.distinct_pairs) ∪
    P.parts.attach.distinct_pairs.bUnion
      (sym2_pair_bind (λ i hi, (hP.chunk_increment G ε hi).parts)) :=
begin
  ext UiVj,
  apply UiVj.induction_on (λ Ui Vj, _),
  simp only [mem_distinct_pairs, mem_union, mem_bUnion, mem_product, exists_prop, mem_attach,
    exists_true_left, subtype.exists, prod.exists, true_and, sym2.exists, exists_and_distrib_left,
    finpartition_on.is_equipartition.increment, bind_parts, mem_sym2_pair_bind, ne.def],
  split,
  { rintro ⟨⟨U, hU, hUi⟩, ⟨V, hV, hVj⟩, h⟩,
    rcases eq_or_ne U V with rfl | hUV,
    { exact or.inl ⟨U, by simp [*]⟩ },
    right,
    refine ⟨U, hU, V, hUV, hV, _⟩,
    left,
    refine ⟨hUi, hVj⟩ },
  rintro (_ | ⟨U, hU, V, hUV, hV, (⟨h₁, h₂⟩ | ⟨h₂, h₁⟩)⟩),
  { tauto },
  { refine ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩, _⟩,
    rintro rfl,
    obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ h₁,
    exact hUV (P.disjoint.elim_finset hU hV _
      (finpartition_on.subset _ h₁ hi) (finpartition_on.subset _ h₂ hi)) },
  { refine ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩, _⟩,
    rintro rfl,
    obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ h₁,
    exact hUV (P.disjoint.elim_finset hU hV _
      (finpartition_on.subset _ h₂ hi) (finpartition_on.subset _ h₁ hi)) }
end.

-- -- dagger inequality
-- lemma sq_density_sub_eps_le_sum_sq_density_div_card [nonempty α]
-- (hPα : P.size * 16^P.size ≤ card α)
--   (hPε : 100 ≤ 4^P.size * ε^5) (m_pos : 0 < m) (hε₁ : ε ≤ 1)
--   {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} :
--   G.edge_density U V^2 - ε^5/25 ≤
--   (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
--     G.edge_density ab.1 ab.2^2)/16^P.size :=

lemma sum_sym2 [decidable_eq α] {β : Type*} [division_ring β] [char_zero β] (f : sym2 α → β)
  (s : finset (α × α)) {hs₁ : ∀ i j, (i,j) ∈ s → i ≠ j} (hs₂ : ∀ i j, (i,j) ∈ s → (j,i) ∈ s) :
  ∑ (i : sym2 _) in s.image quotient.mk, f i = (∑ i in s, f ⟦i⟧)/2 :=
begin
  rw sum_div,
  apply sum_image',
  rintro ⟨x, y⟩ h,
  suffices : s.filter (λ c', ⟦c'⟧ = ⟦(x,y)⟧) = {(x,y), (y,x)},
  { rw [this, sum_pair, sym2.eq_swap, add_halves'],
    rintro ⟨⟩,
    apply hs₁ _ _ h rfl, },
  ext ⟨i, j⟩,
  simp only [mem_filter, mem_insert, prod.mk.inj_iff, sym2.eq_iff, mem_singleton],
  tauto {closer := `[subst_vars; solve_by_elim]},
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
    ... ≤
      (∑ UV in P.parts.attach.distinct_pairs.bUnion (sym2_pair_bind (λ i hi, (hP.chunk_increment
        G ε hi).parts)), G.sym2_edge_density UV ^ 2) / (hP.increment G ε).size ^ 2 :
    begin
      rw sum_bUnion,
      rw distinct_pairs,
      rw sum_sym2 _ P.parts.attach.off_diag,
      -- rw sum_image,
    end
    ... ≤ index G (hP.increment G ε) :
    begin
      rw [index, increment_distinct_pairs],
      apply div_le_div_of_le_of_nonneg,
      { apply sum_le_sum_of_subset_of_nonneg,
        { apply subset_union_right },
        intros,
        apply sq_nonneg },
      apply sq_nonneg
    end
end.

end increment
