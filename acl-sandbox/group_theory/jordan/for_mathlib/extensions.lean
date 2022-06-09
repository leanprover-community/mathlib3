/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift
import .ulift

import set_theory.cardinal.finite

section Extensions

open function.embedding nat

open_locale classical

variable {α : Type*}

/-- Given a nat.card inequality, get an embedding from a fin _ -/
lemma gimme_some {m : ℕ} (hα : m ≤ nat.card α) : ∃ (x : fin m ↪ α), true :=
begin
  cases fintype_or_infinite α; resetI,
  { suffices : ∃ (x' : ulift (fin m) ↪ α), true,
    { obtain ⟨x'⟩ := this, use equiv.ulift.symm.to_embedding.trans x' },
    rw [exists_true_iff_nonempty, ← cardinal.le_def],
    simp only [cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin],
    simp only [cardinal.nat_cast_le, ← nat.card_eq_fintype_card],
    exact hα, },
  { rw [nat.card_eq_zero_of_infinite, nonpos_iff_eq_zero] at hα,
    rw hα,
    use function.embedding.of_is_empty }
end

/-- Given an embedding and a strict nat.card inequality, get another element  -/
lemma gimme_another {m : ℕ} (x : fin m → α) (hα : m < nat.card α) :
  ∃ (a : α), a ∉ set.range x :=
begin
  cases fintype_or_infinite α; resetI,
  { apply not_forall.mp,
    -- change ¬ (function.surjective x),
    intro h,
    apply (lt_iff_not_ge _ _).mp  hα,
    --   rw ge_iff_le,
    let hx := cardinal.mk_le_of_surjective (ulift.surjective_iff_surjective.mpr h),
    simp only [cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin, cardinal.nat_cast_le] at hx,
    rw nat.card_eq_fintype_card,
    exact hx },
  { exfalso,
    rw nat.card_eq_zero_of_infinite at hα,
    simpa using hα }
end

/-- Extend a fin embedding by another element -/
lemma may_extend_with {n : ℕ} (x : fin n ↪ α) (a : α) (ha : a ∉ set.range x.to_fun) :
  ∃ (x' : fin n.succ ↪ α),
  -- (∀ (i : fin n.succ) (hi : i.val < n), x' i = x ⟨i, hi⟩)
  (fin.cast_le n.le_succ).to_embedding.trans x' = x
  ∧ (x' ⟨n, n.lt_succ_self⟩ = a) :=
begin
  let p := λ i : fin n.succ, i.val < n,
  let f : { i : fin n.succ | i.val < n } → α := λ i, x.to_fun (fin.cast_lt i.val i.prop),
  let f' : { i : fin n.succ | ¬ (p i) } → α  := λ ⟨i, hi⟩, a,

  use (λ i, if hi : p i then f ⟨i, hi⟩ else f' ⟨i, hi⟩),
  { refine function.injective.dite p _ _ _,
    { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
      simp only [subtype.mk_eq_mk],
      let hij' := subtype.mk_eq_mk.mp (x.inj' hij),
      simp only [fin.val_eq_coe] at hij',
      exact fin.ext hij' },
  { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
    simp only [subtype.mk_eq_mk],
    rw [← subtype.coe_inj,
        nat.eq_of_lt_succ_of_not_lt i.prop hi,
        nat.eq_of_lt_succ_of_not_lt j.prop hj] },
  { intros _ _ _ _,
    change x.to_fun _ ≠ a,
    intro h, apply ha, use ⟨_,h⟩ } },
  split,
  { ext ⟨i, hi⟩,
    simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk, coe_fn_mk],
    rw dite_eq_iff,
    apply or.intro_left, use hi, refl },
  { simp only [not_lt, coe_fn_mk, dif_neg] }
end

/-- Extend an embedding from fin given a nat.card inequality -/
lemma may_extend {m n : ℕ} (hmn : m ≤ n) (hα : n ≤ nat.card α) (x : fin m ↪ α) :
  ∃ (x' : fin n ↪ α), (fin.cast_le hmn).to_embedding.trans x' = x :=
 -- ∀ (i : fin m), x' (⟨i.val, lt_of_lt_of_le i.prop hmn⟩ : fin n) = x i
begin
  induction n with n hrec,
  { simp only [nat.nat_zero_eq_zero, nonpos_iff_eq_zero] at hmn,
    let  w : fin 0 ↪ α :=  function.embedding.of_is_empty ,
    use w, ext ⟨i, hi⟩,
    exfalso, rw hmn at hi,
    exact nat.not_lt_zero i hi },
  { cases nat.eq_or_lt_of_le hmn,
    -- case where m = n.succ
    { use (equiv.to_embedding (fin.cast h.symm).to_equiv).trans x,
      ext ⟨i, hi⟩,
      simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk,
        equiv.to_embedding_apply, rel_iso.coe_fn_to_equiv, fin.cast_mk] },
    -- case where m < n.succ
    { obtain ⟨y, hy⟩ :=
      hrec (nat.le_of_lt_succ h) (le_trans (le_succ n) hα),
      obtain ⟨a,ha⟩ :=
      gimme_another y (lt_of_lt_of_le (nat.lt_succ_self n) hα),
      obtain ⟨x', hx', hx'a⟩ := may_extend_with y a ha,
      use x', rw ← hy, rw ← hx',
      ext ⟨i, hi⟩, refl } }
end

/-- Join two disjoint embeddings from fin _ types -/
lemma may_extend_with' {m n k : ℕ} {s : set α} (z : fin k ↪ ↥s) (h : n = m + k)
  (x : fin m ↪ ↥sᶜ) : -- let h' : n = k + m := eq.trans h (add_comm m k) in
  ∃ (x' : fin n ↪ α),
  (fin.cast_le (le_trans le_self_add (le_of_eq (eq.symm h)))).to_embedding.trans x'
    = x.trans  (subtype sᶜ)
  ∧
  (fin.nat_add m).to_embedding.trans ((fin.cast h.symm).to_equiv.to_embedding.trans x')
    = z.trans (subtype s) :=
begin
  let h' := eq.trans h (add_comm m k),
  let p := λ i : fin n, i.val < m,
  let f : { i : fin n | p i } → α := λ i, x.to_fun (fin.cast_lt i.val i.prop),
  let g : { i : fin n | ¬ (p i) } → α :=
    λ i, z.to_fun (fin.sub_nat m (fin.cast h' i.val)
      (by simpa [h] using not_lt.mp (subtype.mem i))),
  use (λ i, if hi : p i then f ⟨i, hi⟩ else g ⟨i, hi⟩),
  { refine function.injective.dite p _ _ _ ,
    { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
      let hij' := x.inj' (subtype.coe_injective  hij),
      simp only at hij', unfold fin.cast_lt at hij',
      simp only [subtype.mk_eq_mk] at hij' ⊢,
      apply fin.ext,
      simpa only using hij' },
    { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
      simp only [subtype.mk_eq_mk],
      apply (fin.cast h').injective,

      rw not_lt at hi hj,
      have  hi' : m ≤ (fin.cast h') i,
      { simp only [fin.coe_cast,fin.coe_eq_val], exact hi, },
      have  hj' : m ≤ (fin.cast h') j,
      { simp only [fin.coe_cast,fin.coe_eq_val], exact hj, },

      let hij' := z.inj' (subtype.coe_injective  hij),
      simp only at hij',
      rw [← fin.add_nat_sub_nat hi', ← fin.add_nat_sub_nat hj', hij'] },
    { intros i j hi hj hij,
      suffices : f ⟨i, hi⟩ ∉ s,
      { apply this, rw hij, simp only [subtype.coe_prop] },
      simp only [← set.mem_compl_eq, subtype.coe_prop] } },

  split,
  { ext ⟨i, hi⟩,
    simp only [trans_apply, rel_embedding.coe_fn_to_embedding,
      fin.cast_le_mk, coe_fn_mk],
    rw dite_eq_iff,
    apply or.intro_left, use hi, refl },
  { ext ⟨j, hj⟩,
    simp only [not_lt, le_add_iff_nonneg_right, zero_le, trans_apply,
      rel_embedding.coe_fn_to_embedding, fin.nat_add_mk, equiv.to_embedding_apply,
      rel_iso.coe_fn_to_equiv, fin.cast_mk, coe_fn_mk, dif_neg, function.embedding.coe_subtype],
    change ↑(z.to_fun _) = _,
    simp only [fin.cast_mk, add_tsub_cancel_left, fin.sub_nat_mk, to_fun_eq_coe]}
end

end Extensions
