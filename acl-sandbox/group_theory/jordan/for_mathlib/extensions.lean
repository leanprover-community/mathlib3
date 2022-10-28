/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift
import .ulift
import .cardinal
import data.finite.basic
import set_theory.cardinal.finite

section Extensions

open function.embedding nat

open_locale classical

variable {α : Type*}

example (h q : Prop) : h → ¬h → q := begin
exact absurd,
end

/-- Given a nat.card inequality, get an embedding from a fin _ -/
lemma gimme_some {m : ℕ} (hα : ↑m ≤ part_enat.card α) : ∃ (x : fin m ↪ α), true :=
begin
  suffices : ∃ (x' : ulift (fin m) ↪ α), true,
    { obtain ⟨x'⟩ := this, use equiv.ulift.symm.to_embedding.trans x' },
  rw [exists_true_iff_nonempty, ← cardinal.le_def],
  simp only [cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin],
  cases lt_or_ge (cardinal.mk α) (cardinal.aleph_0),
  { obtain ⟨n, hn⟩ := (cardinal.lt_aleph_0.1 h),
    rw hn, simp only [cardinal.nat_cast_le],
    unfold part_enat.card at hα, rw hn at hα,
    simpa only [cardinal.to_part_enat_cast, part_enat.coe_le_coe] using hα },
  { refine le_trans _ h,
    apply le_of_lt,
    exact cardinal.nat_lt_aleph_0 m }
end

lemma gimme_some_equiv {m : ℕ} [fintype α] (hα : m = fintype.card α) :
  nonempty (fin m ≃ α) :=
begin
  use (fintype.equiv_fin_of_card_eq hα.symm).symm,
end

lemma equiv_fin_of_part_enat_card_eq {m : ℕ} (hα : part_enat.card α = m) :
  nonempty (α ≃ fin m) :=
begin
  cases (fintype_or_infinite α) with h h; resetI,
  { simp only [part_enat.card_eq_coe_fintype_card, part_enat.coe_inj] at hα,
    use (fintype.equiv_fin_of_card_eq hα) },
  { rw part_enat.card_eq_top_of_infinite at hα,
    exfalso, apply part_enat.coe_ne_top m, rw hα },
end

/-- Given an embedding and a strict nat.card inequality, get another element  -/
lemma gimme_another {m : ℕ} (x : fin m → α) (hα : ↑m < part_enat.card α) :
  ∃ (a : α), a ∉ set.range x :=
begin
  rw ← not_forall,
  intro h,
  apply (lt_iff_not_ge _ _).mp  hα,
  let hx := cardinal.mk_range_le_lift,
  rw set.eq_univ_of_forall h at hx,
  simp only [cardinal.mk_univ, cardinal.lift_uzero, cardinal.mk_fin, cardinal.lift_nat_cast] at hx,

  cases lt_or_ge (cardinal.mk α) (cardinal.aleph_0) with hα' hα',
  { obtain ⟨n, hn⟩ := (cardinal.lt_aleph_0.1 hα'),
    unfold part_enat.card, rw hn,
    simp only [cardinal.to_part_enat_cast, ge_iff_le, part_enat.coe_le_coe],
    simpa only [hn, cardinal.lift_nat_cast, cardinal.nat_cast_le] using hx },
  { exfalso,
    apply (lt_iff_not_ge _ _).mp (cardinal.nat_lt_aleph_0 m),
    exact le_trans hα' hx }
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
      rw subtype.mk_eq_mk,
      apply fin.ext,
      rw ← fin.coe_cast_lt i _, rw ← fin.coe_cast_lt j _,
      rw x.inj' hij, },
  { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
    simp only [subtype.mk_eq_mk, fin.eq_iff_veq],
    rw [nat.eq_of_lt_succ_of_not_lt i.prop hi, nat.eq_of_lt_succ_of_not_lt j.prop hj], },
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

example (m n : ℕ) (h : m ≤ n): (m : part_enat) ≤ n :=
begin
exact part_enat.coe_le_coe.mpr h,
end


/-- Extend an embedding from fin given a nat.card inequality -/
lemma may_extend {m n : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ part_enat.card α) (x : fin m ↪ α) :
  ∃ (x' : fin n ↪ α), (fin.cast_le hmn).to_embedding.trans x' = x :=
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
      hrec (nat.le_of_lt_succ h) (le_trans (part_enat.coe_le_coe.mpr (le_succ n)) hα),
      obtain ⟨a,ha⟩ :=
      gimme_another y (lt_of_lt_of_le (part_enat.coe_lt_coe.mpr (nat.lt_succ_self n)) hα),
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
      simpa only [subtype.mk_eq_mk, fin.eq_iff_veq] using x.inj' (subtype.coe_injective  hij), },
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
      simp only [← set.mem_compl_iff, subtype.coe_prop] } },

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
