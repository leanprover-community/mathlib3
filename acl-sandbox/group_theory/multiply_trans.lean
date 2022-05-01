/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift


import set_theory.cardinal.basic

import group_theory.group_action.embedding
-- import group_theory.group_action.fixing_subgroup
-- import field_theory.galois

-- import group_theory.specific_groups.alternating

import .ad_to_ulift
import .ad_sub_mul_actions
import .mul_action_bihom
import .wielandt



-- import group_theory.subgroup.pointwise
-- import group_theory.coset
-- import group_theory.quotient_group
-- import group_theory.abelianization
-- import group_theory.group_action.defs
-- import group_theory.group_action.basic
-- import group_theory.group_action.group
-- import group_theory.group_action.conj_act
-- import group_theory.group_action.sub_mul_action

-- import order.partition.finpartition
-- import data.finset.lattice

-- import data.setoid.partition
-- import data.set.basic
-- import data.fintype.basic
-- import order.rel_classes
-- import algebra.big_operators.order

open_locale big_operators pointwise cardinal

open_locale classical

section Extensions

open function.embedding nat

variable {α : Type*}

lemma gimme_some {m : ℕ} (hα : ↑m ≤ #α) : ∃ (x : fin m ↪ α), true :=
begin
  suffices : ∃ (x' : ulift (fin m) ↪ α), true,
  { obtain ⟨x'⟩ := this, use equiv.ulift.symm.to_embedding.trans x' },
  rw [exists_true_iff_nonempty, ← cardinal.le_def],
  simp only [cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin],
  exact hα,
end

lemma gimme_another {m : ℕ} (x : fin m → α) (hα : ↑m < #α) :
  ∃ (a : α), a ∉ set.range x :=
begin
  apply not_forall.mp,
  -- change ¬ (function.surjective x),
  intro h,
  apply (lt_iff_not_ge _ _).mp  hα,
  --   rw ge_iff_le,
  let hx := cardinal.mk_le_of_surjective (ulift.surjective_iff_surjective.mpr h),
  simp only [cardinal.mk_ulift, cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin] at hx,
  rw  cardinal.lift_id at hx,
  exact hx,
end

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

lemma may_extend {m n : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ #α) (x : fin m ↪ α) :
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
      hrec (nat.le_of_lt_succ h) (le_trans (cardinal.nat_cast_le.mpr (nat.le_succ n)) hα),
      obtain ⟨a,ha⟩ :=
      gimme_another y (lt_of_lt_of_le (cardinal.nat_cast_lt.mpr (nat.lt_succ_self n)) hα),
      obtain ⟨x', hx', hx'a⟩ := may_extend_with y a ha,
      use x', rw ← hy, rw ← hx',
      ext ⟨i, hi⟩, refl } }
end

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

namespace mul_action

section multiple_transitivity

open function.embedding nat

variables (M α : Type*) [group M] [mul_action M α]

/--/
def is_multiply_pretransitive' (M α : Type*) [has_scalar M α] (n : ℕ) :=
∀ {x : list α} (hx : x.length = n) (ndx : x.nodup)
  {y : list α} (hy : y.length = n) (ndy : y.nodup),
∃ (g : M), g • x = y
-/

def is_multiply_pretransitive (n : ℕ) :=
  is_pretransitive M (fin n ↪ α)

lemma is_multiply_pretransitive_bihom (n : ℕ) (N β : Type*) [group N] [mul_action N β]
  (j : mul_action_bihom M α N β) (hj : function.surjective j.to_fun)
  (h : is_multiply_pretransitive M α n) : is_multiply_pretransitive N β n :=
begin
  let h_eq := h.exists_smul_eq,
  apply is_pretransitive.mk,
--  intros x y,
  have aux : ∀ (x : fin n ↪ β), ∃ (x' : fin n ↪ α),
    j.to_fun ∘ x'.to_fun = x.to_fun := λ x,
  begin
    let x' : fin n → α := λi, (hj (x i)).some,
    suffices hx' : function.injective x',
    { use ⟨x', hx'⟩,
      ext i,
      simp only [function.comp_app, to_fun_eq_coe],
      rw ← classical.some_spec (hj (x i)) },
    { intros i i' hi,
      let hi' := congr_arg j.to_fun hi,
      simp only [(classical.some_spec (hj (x _)))] at hi',
      exact x.inj' hi' }
  end,
  intros x y,
  obtain ⟨x', hx'⟩ := aux x,
  obtain ⟨y', hy'⟩ := aux y,
  obtain ⟨g, hg'⟩ := h_eq x' y',
  use j.to_monoid_hom g,
  ext i,
  change _ • x.to_fun i = y.to_fun i,
  rw [← hy', ← hx', j.map_smul'],
  apply congr_arg,
  rw ← hg',
  simp only [to_fun_eq_coe, smul_apply]
end

lemma is_zero_pretransitive : is_multiply_pretransitive M α 0 :=
begin
  apply is_pretransitive.mk,
  intros x y, use 1, rw one_smul,
  ext i, exfalso,
  exact is_empty.false i,
end

/-
lemma is_multiply_pretransitive_of_higher (M α : Type*) [has_scalar M α] {n : ℕ}
  (hn : is_multiply_pretransitive M α n) {m : ℕ} (hmn : m ≤ n) (hα : card_ge α n) :
  is_multiply_pretransitive M α m :=
begin
  intros x hx hxn y hy hyn,
  obtain ⟨x', hx', hx'n, hx'e⟩ := list.extend_nodup n hα x hxn _,
  swap, { rw hx, exact hmn },
  obtain ⟨y', hy', hy'n, hy'e⟩ := list.extend_nodup n hα y hyn _,
  swap, { rw hy, exact hmn },
  obtain ⟨g, hg⟩ := hn hx' hx'n hy' hy'n,
  use g,
  rw [← hx'e, ← hy'e, ← smul_take, hg, hx, hy],
end
-/

lemma is_multiply_pretransitive_of_higher  {n : ℕ}
  (hn : is_multiply_pretransitive M α n) {m : ℕ} (hmn : m ≤ n)
  (hα : ↑n ≤ #α) :
  is_multiply_pretransitive M α m :=
begin
  unfold is_multiply_pretransitive,
  let hn_eq := hn.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨x', hx'⟩ := may_extend hmn hα x,
  obtain ⟨y', hy'⟩ := may_extend hmn hα y,
  obtain ⟨g, hg⟩ := hn_eq  x' y',
  use g,
  ext, rw [← hy', ← hx', ← hg], refl
end

/-
lemma is_pretransitive_iff_is_one_pretransitive (M α : Type*) [has_scalar M α] :
  is_pretransitive M α ↔ is_multiply_pretransitive M α 1 :=
begin
  split,
  { intros h,  let heq := h.exists_smul_eq,
    intros x hx hxn y hy hyn,
    obtain ⟨a, rfl⟩ := list.length_eq_one.mp hx,
    obtain ⟨b, rfl⟩ := list.length_eq_one.mp hy,
    simp only [smul_cons, smul_nil, eq_self_iff_true, and_true],
    obtain ⟨g, hg⟩ := heq a b,
    exact ⟨g, hg⟩ },
  { intros heq,
    apply is_pretransitive.mk,
    intros a b,
    obtain ⟨g, hg⟩ := heq _ (_ : [a].nodup)  _ (_ : [b].nodup),
    simp only [smul_cons, smul_nil, eq_self_iff_true, and_true] at hg,
    exact ⟨g, hg⟩,
    any_goals
    { simp only [list.nodup_cons, list.not_mem_nil, not_false_iff, list.nodup_nil, and_self] },
    any_goals
    { simp only [list.length_singleton] } }
end
-/

lemma is_pretransitive_iff_is_one_pretransitive :
  is_pretransitive M α ↔ is_multiply_pretransitive M α 1 :=
begin
  split,
  { intros h, let h_eq := h.exists_smul_eq,
    unfold is_multiply_pretransitive,
    apply is_pretransitive.mk,
    intros x y,
    obtain ⟨g, hg⟩ := h_eq (x 0) (y 0),
    use g, ext i,
    rw smul_apply, rw fin.eq_zero i, exact hg },
  { intros h, let h_eq := h.exists_smul_eq,
    apply is_pretransitive.mk,
    intros a b,
    let x : fin 1 ↪ α := ⟨(λ _, a), function.injective_of_subsingleton _⟩,
    let y : fin 1 ↪ α := ⟨(λ _, b), function.injective_of_subsingleton _⟩,
    obtain ⟨g, hg⟩ := h_eq x y,
    use g,
    change g • (x 0) = (y 0),
    rw [← hg, smul_apply] }
end

/-
lemma nodup_aux3 {M α : Type*} [group M] [mul_action M α] {a : α}
  {l : list ↥(sub_mul_action_of_stabilizer M α a)} (hln : l.nodup) :
  let l' := a :: l.map coe  in
  l'.length = l.length.succ ∧ l'.nodup :=
--   (a :: l.map coe : list α).length = l.length.succ ∧ (a :: l.map coe).nodup :=
begin
  split,
  { rw list.length_cons, rw list.length_map },
  { rw list.nodup_cons, split,
    { intro h, obtain ⟨b, hbx, hba⟩ := list.mem_map.mp h,
      let hb' : ↑b ∈ (sub_mul_action_of_stabilizer M α a).carrier := set_like.coe_mem b,
      rw sub_mul_action_of_stabilizer_def at hb',
      rw hba at hb',
      simpa only [set.mem_compl_eq, set.mem_singleton, not_true] using hb' },
    exact (list.nodup_map_iff (subtype.coe_injective)).mpr hln },
end
-/

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.is_multiply_pretransitive
  (hα' : is_pretransitive M α)
  {n : ℕ} (a : α) :
  -- (hα0 : ↑n ≤ #α) /- (hα : card_ge α n.succ) -/  :
  is_multiply_pretransitive M α n.succ ↔
  is_multiply_pretransitive (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  let hα'eq := hα'.exists_smul_eq,
  split,
  { intro hn, let hn_eq := hn.exists_smul_eq,
    apply is_pretransitive.mk,
    intros x y,

    obtain ⟨x', hx', hx'a⟩ := may_extend_with (x.trans (subtype _)) a _,
    swap,
    { rintro ⟨u, hu⟩,
      simp only [to_fun_eq_coe, trans_apply, function.embedding.coe_subtype] at hu,
      exact (sub_mul_action_of_stabilizer_neq M α a (x u)) hu },

    obtain ⟨y', hy', hy'a⟩ := may_extend_with (y.trans (subtype _)) a _,
    swap,
    { rintro ⟨u, hu⟩,
      simp only [to_fun_eq_coe, trans_apply, function.embedding.coe_subtype] at hu,
      exact (sub_mul_action_of_stabilizer_neq M α a (y u)) hu },

    obtain ⟨g, hg'⟩ := hn_eq x' y',
    have hg : g ∈ stabilizer M a,
    { rw mem_stabilizer_iff,
      conv_lhs { rw ← hx'a },
      rw [← hy'a, ← hg', smul_apply] },

    use ⟨g, hg⟩,
    ext ⟨i, hi⟩,
    simp only [smul_apply, sub_mul_action.coe_smul_of_tower],
    rw ← function.embedding.ext_iff at hx' hy',
    specialize hx' ⟨i, hi⟩, specialize hy' ⟨i, hi⟩,
    simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk,
      function.embedding.coe_subtype] at hx' hy',
    rw [← hx', ← hy', ← hg'], refl, },
    --
  { intro hn, let hn_eq := hn.exists_smul_eq,
    apply is_pretransitive.mk,

    have aux_fun : ∀ (x : fin n.succ ↪ α),
      ∃ (g : M) (x1 : fin n ↪ ↥(sub_mul_action_of_stabilizer M α a)),
        (fin.cast_le (nat.le_succ n)).to_embedding.trans (g • x)
          = function.embedding.trans x1 (subtype _)
        ∧ g • (x ⟨n, nat.lt_succ_self n⟩) = a,
    { intro x,
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, nat.lt_succ_self n⟩) a,
      use g,
      have zgx : ∀ (i : fin n),
        g • (x i) ∈ sub_mul_action_of_stabilizer M α a,
      { rintros ⟨i, hi⟩,
        change _ ∈  (sub_mul_action_of_stabilizer M α a).carrier ,
        rw sub_mul_action_of_stabilizer_def,
        simp only [set.mem_compl_eq, set.mem_singleton_iff],
        rw ← hgx,
        simp only [← smul_apply],
        intro h, apply ne_of_lt hi,
        let h' := function.embedding.injective (g • x) h,
        simpa using h' },
      let x1 : fin n → sub_mul_action_of_stabilizer M α a :=
        λ i, ⟨g • (x i), zgx i⟩,
      use x1,
      { intros i j,
        simp only [subtype.mk_eq_mk, fin.coe_eq_cast_succ, smul_left_cancel_iff,
          embedding_like.apply_eq_iff_eq,
          order_embedding.eq_iff_eq, imp_self] },
      refine and.intro _ hgx,
      { ext i, simp, refl, } },

    intro x, -- gx • x = x1 :: a
    obtain ⟨gx, x1, hgx, hga⟩ := aux_fun x,
    intro y, -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := aux_fun y,
    -- g • x1 = y1,
    obtain ⟨g, hg⟩ := hn_eq x1 y1,

    use gy⁻¹ * g * gx,
    ext ⟨i, hi⟩,
    rw mul_smul, simp only [smul_apply],
    cases lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi',
    { rw ← function.embedding.ext_iff at hgx hgy hg,
      specialize hgx ⟨i, hi'⟩, specialize hgy ⟨i, hi'⟩, specialize hg ⟨i, hi'⟩,
      simp only [trans_apply, rel_embedding.coe_fn_to_embedding, fin.cast_le_mk, smul_apply,
        function.embedding.coe_subtype] at hgx hgy hg,
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg], refl },
    { simp only [hi'],
      rw [hga, mul_smul, inv_smul_eq_iff, hgb],
      rw ← mem_stabilizer_iff, exact set_like.coe_mem g } }
end

/-
theorem stabilizer.is_multiply_pretransitive (M α : Type*) [group M] [mul_action M α]
  (hα' : is_pretransitive M α)
  (n : ℕ) (hα : card_ge α n.succ) (a : α) :
  is_multiply_pretransitive M α n.succ ↔
  is_multiply_pretransitive (stabilizer M a) (sub_mul_action_of_stabilizer M α a) n :=
begin
  let hα'eq := hα'.exists_smul_eq,
  split,
  { intro hn,
    intros x hxl hxn y hyl hyn,
    let hx' := nodup_aux3 hxn, rw hxl at hx',
    let hy' := nodup_aux3 hyn, rw hyl at hy',
    obtain ⟨g,hgxy⟩ := hn hx'.left hx'.right hy'.left hy'.right,
    change g • (a :: list.map coe x) = (a :: list.map coe y) at hgxy,
    rw smul_cons at hgxy,
    have hg : g ∈ stabilizer M a,
    { rw mem_stabilizer_iff, exact list.head_eq_of_cons_eq hgxy },
    use ⟨g, hg⟩,
    change list.map (λ x, (⟨g, hg⟩ : ↥(stabilizer M a)) • x) x = y,
    apply (list.map_injective_iff.mpr (subtype.coe_injective)) ,
    rw ← list.tail_eq_of_cons_eq hgxy,
    change _ = list.map (λ x, g • x) (list.map coe x),
    simp only [list.map_map],
    apply list.map_congr,
    intros b hb,
    simp only [function.comp_app, sub_mul_action.coe_smul_of_tower], refl },
  { intro hn,
    -- Lemma to rewrite and coerce the data
    have : ∀ {x : list α} (hxl : x.length = n.succ) (hxn : x.nodup),
        ∃ (g : M) (x' : list ↥(sub_mul_action_of_stabilizer M α a)),
          x'.length = n ∧ x'.nodup ∧ g • x = a :: (x'.map coe),
      { intros x hxl hxn,
        obtain ⟨x0, x', rfl : x = x0 :: x'⟩ :=
          list.exists_cons_of_ne_nil (list.ne_nil_of_length_eq_succ hxl),
        obtain ⟨gx : M, hgx : gx • x0 = a⟩ := hα'eq _ _,
        lift (gx • x') to list ↥(sub_mul_action_of_stabilizer M α a) with g1x1 hx1,
        swap,
        { intros b hb,
          simp only [← sub_mul_action.mem_carrier, sub_mul_action_of_stabilizer_def],
          simp only [set.mem_compl_eq, set.mem_singleton_iff],
          rintro ⟨rfl⟩,
          refine (list.nodup_cons.mp _).left hb,
          rw ← hgx,
          rw ← smul_cons,
          change (list.map (λ x, gx • x) (x0 :: x')).nodup,
          exact list.nodup_map (mul_action.injective _) hxn },
        use gx, use g1x1,
        split,
        { rw ← list.length_map, rw hx1,
          change (x'.map _).length = _,
          rw list.length_map,
          simpa [list.length_cons, nat.add_one] using hxl },
        split,
        { apply list.nodup_of_nodup_map _,
          rw hx1,
          apply list.nodup_map (mul_action.injective _),
          exact (list.nodup_cons.mp hxn).right },
        { rw smul_cons, rw hgx, rw list.cons_inj,
          exact hx1.symm } },
      --
    intros x hxl hxn,
    obtain ⟨gx, x', hx'l, hx'n, hx'⟩ := this hxl hxn,
    -- gx • x = a : x',
    intros y hyl hyn,
    obtain ⟨gy, y', hy'l, hy'n, hy'⟩ := this hyl hyn,
    -- gy • y = a : y',
    obtain ⟨g, hg⟩ := hn hx'l hx'n hy'l hy'n,
    -- g • x' = y',

    use gy⁻¹ * g * gx,
    rw [mul_smul, hx', mul_smul, inv_smul_eq_iff, hy', smul_cons],
    simp only,
    split,
    { rw ← mem_stabilizer_iff, exact set_like.coe_mem g },
    { rw ← hg,
      change list.map _ _ = list.map coe (list.map _ x'),
      simp only [list.map_map],
      apply list.map_congr,
      intros b hb,
      refl } }
end
-/

/-
def example' {s : set α} : mul_action (fixing_subgroup M s) α :=
infer_instance

#print example'
#check example'

-/

/- {
one_smul := λ b, {by infer_instance }
mul_smul := begin sorry end


}
lemma example {s t : set α} : fixing_subgroup M (s ∪ t) =
  fixing_subgroup (fixing_subgroup M s) t :=
begin
sorry
end

-/


/-
lemma aux_nat : ∀ {d n i : ℕ} (h : d ≤ n) (hi : i < n) (hi' : ¬(i < n-d)),
  i - (n - d) < d :=
begin
  intros d n i h hi hi',
  simp only [not_lt] at hi',
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le h,
  simp only [add_tsub_cancel_left] at hi',
  obtain ⟨l, rfl⟩ := nat.exists_eq_add_of_le hi',
  rw add_comm at hi, simp only [add_lt_add_iff_right] at hi,
  simp only [add_tsub_cancel_left], exact hi,
end
-/

/-- The fixator of a subset of cardinal d in a k-transitive action
acts (k-d) transitively on the remaining -/
lemma remaining_transitivity (d : ℕ) (s : set α) (hs : ↑d = #s)
  (n : ℕ) -- (hα : ↑n ≤ #α)
  (h : is_multiply_pretransitive M α n) :
  is_multiply_pretransitive (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s) (n-d) :=
begin
  cases le_total d n with hdn hnd,
  { apply is_pretransitive.mk,
    intros x y,
    let h_eq := h.exists_smul_eq,

    have : ∃ (z : (fin d) ≃ ↥s), true,
    { suffices : ∃ (z' : ulift (fin d) ≃ ↥s), true,
      { obtain ⟨z'⟩ := this, use equiv.trans equiv.ulift.symm z' },
      rw exists_true_iff_nonempty ,
      rw ← cardinal.eq,
      simp only [cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin, hs] },
    obtain ⟨z⟩ := this,

    have hd' : n = (n - d) + d := (nat.sub_add_cancel hdn).symm,

    obtain ⟨x' : fin n ↪ α, hx'⟩ := may_extend_with' z.to_embedding hd' x,
    obtain ⟨y' : fin n ↪ α, hy'⟩ := may_extend_with' z.to_embedding hd' y,
    obtain ⟨g, hg⟩ := h_eq x' y',

    use g,
    { intro a,
      let i := z.symm a,
      have : z.to_embedding.trans (subtype s) i = a,
      by simp only [trans_apply, equiv.to_embedding_apply, equiv.apply_symm_apply,
          function.embedding.coe_subtype],
      rw ← this,
      conv_lhs { rw ← hx'.right },
      rw ← hy'.right,
      rw ← hg,
      simp only [trans_apply, smul_apply] },
    { ext i,
      simp only [smul_apply, sub_mul_action.coe_smul_of_tower],
      have : ((y i) : α) = (y.trans (subtype sᶜ) i : α),
      by simp only [trans_apply, function.embedding.coe_subtype],
      rw this,
      have : ((x i) : α) = (x.trans (subtype sᶜ) i : α),
      by simp only [trans_apply, function.embedding.coe_subtype],
      rw this,

      rw ← function.embedding.ext_iff at hx' hy',
      simp_rw [← hy'.left i, ← hx'.left i, ← hg],
      simp only [trans_apply, smul_apply, rel_embedding.coe_fn_to_embedding],
      refl } },
  { rw nat.sub_eq_zero_of_le hnd,
    apply is_zero_pretransitive }
end

open_locale classical

/-- A 2-transitive action is primitive -/
theorem is_preprimitive_of_two_pretransitive (M α : Type*) [group M] [mul_action M α]
  (h2 : is_multiply_pretransitive M α 2) : is_preprimitive M α :=
begin
  cases em (#α ≤ ↑1) with hα hα,
  -- Trivial case where subsingleton α
  { rw [cast_one, cardinal.le_one_iff_subsingleton] at hα,
    apply is_preprimitive.mk,
    { apply is_pretransitive.mk,
      intros x y, use 1, exact subsingleton_iff.mp hα _ _ },
    { intros B hB,
      apply or.intro_left,
      rw set.subsingleton_coe ,
      exact @set.subsingleton_of_subsingleton _ hα B} },
  -- Important case : 2 ≤ #α
  let hα' := id hα,
  rw [not_le, ← cardinal.succ_le, ← cardinal.nat_succ] at hα',
  change  ↑2 ≤ #α  at hα',
  apply is_preprimitive.mk,
  rw is_pretransitive_iff_is_one_pretransitive,
  apply is_multiply_pretransitive_of_higher M α h2 _ hα',
  norm_num,
  intros B hB,
  cases subsingleton_or_nontrivial B with h h,
  exact or.intro_left _ h,
  -- Cas top
  apply or.intro_right,
  rw [← cardinal.one_lt_iff_nontrivial, ← cast_one, ← cardinal.succ_le, ← cardinal.nat_succ] at h,
  change  ↑2 ≤ #↥B  at h,
  obtain ⟨x : fin 2 ↪ ↥B⟩ := gimme_some h,
  rw set.top_eq_univ,
  apply set.eq_univ_of_forall,
  intro a,

  cases em (a = x 0) with hca hca',
  rw hca, exact subtype.mem (x 0),
  cases em (a = x 1) with hcb hcb',
  rw hcb, exact subtype.mem (x 1),
  unfold is_multiply_pretransitive at h2, let h2_eq := h2.exists_smul_eq,

  let y : fin 2 → α := λ i, if i.val = 0 then x 0 else a,
  have hy0 : y 0 = x 0, by simp,
  have hy1 : y 1 = a, by simp,
  have : ∀ (i : fin 2), i = 0 ∨ i = 1,
  { rintro ⟨i, hi⟩,
    rw nat.lt_succ_iff at hi,
    cases nat.eq_zero_or_pos i with hi_zero hi_pos,
    { apply or.intro_left,
      change _ = (⟨0,_⟩ : fin 2),
      rw fin.mk.inj_iff , exact hi_zero, },
    { apply or.intro_right,
      change _ = (⟨1,_⟩ : fin 2),
      rw fin.mk.inj_iff, exact le_antisymm hi hi_pos } },
  have hy : function.injective y,
  { intros i j hij,
    cases this i with hi hi;
    cases this j with hj hj;
    simp only [hi, hj, hy0, hy1] at hij ⊢;
    exfalso,
    exact hca' hij.symm,
    exact hca' hij },

  obtain ⟨g : M, hg : g • (x.trans (subtype _))  = ⟨y, hy⟩ ⟩ := h2_eq _ _,
  rw ← function.embedding.ext_iff at hg,
  simp at hg,

  rw [← hy1, ← hg 1, ← inv_inv g,  ← mem_smul_set_iff_inv_smul_mem],
  rw is_block.def_mem M α hB (x 0) g⁻¹ _ _,
  exact subtype.mem (x 1),
  exact subtype.mem (x 0),
  rw [← hy0, ← hg 0, ← mul_smul, inv_mul_self, one_smul],
    exact subtype.mem (x 0),
end


end multiple_transitivity
end mul_action

.
