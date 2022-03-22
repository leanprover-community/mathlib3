/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift

import .ad_sub_mul_actions
import .wielandt
import group_theory.group_action.embedding
import set_theory.cardinal

import group_theory.subgroup.pointwise
import group_theory.coset
import group_theory.quotient_group
import group_theory.abelianization
import group_theory.group_action.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.conj_act
import group_theory.group_action.sub_mul_action

import order.partition.finpartition
import data.finset.lattice

import data.setoid.partition
import data.set.basic
import data.fintype.basic
import order.rel_classes
import algebra.big_operators.order



open_locale big_operators pointwise cardinal

open_locale classical



namespace mul_action

section multiple_transitivity

open function.embedding

variables (M α : Type) [group M] [mul_action M α]

/--/
def is_multiply_pretransitive' (M α : Type*) [has_scalar M α] (n : ℕ) :=
∀ {x : list α} (hx : x.length = n) (ndx : x.nodup)
  {y : list α} (hy : y.length = n) (ndy : y.nodup),
∃ (g : M), g • x = y
-/

def is_multiply_pretransitive (n : ℕ) :=
  is_pretransitive M (fin n ↪ α)


lemma gimme_more (m : ℕ) (x : fin m ↪ α) (hα : ↑m < #α) :
  ∃ (a : α), a ∉ set.range x := -- ∀ (i : fin m), x i ≠ a :=
begin
  suffices : ¬ (function.surjective x.to_fun ),
  exact not_forall.mp this,
  intro h,
  apply (lt_iff_not_ge _ _).mp  hα,
  rw ← cardinal.mk_fin,
  exact cardinal.mk_le_of_surjective h
end


lemma may_extend {m n : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ #α) (x : fin m ↪ α) :
  ∃ (x' : fin n ↪ α), ∀ (i : fin m),
    x' (⟨i.val, lt_of_lt_of_le i.prop hmn⟩ : fin n) = x i :=
begin
  induction n with n hrec,
  { simp only [nat.nat_zero_eq_zero, nonpos_iff_eq_zero] at hmn,
    let  w : fin 0 ↪ α :=  function.embedding.of_is_empty ,
    use w, intro i,
    exfalso,
    apply fin.is_empty.false,
    use (fin.cast hmn) i },
  { cases nat.eq_or_lt_of_le hmn,
    -- case where m = n.succ
    { use function.embedding.trans (equiv.to_embedding (fin.cast h.symm).to_equiv) x,
      simp only [fin.val_eq_coe, trans_apply, equiv.to_embedding_apply, rel_iso.coe_fn_to_equiv,
        fin.cast_mk, fin.eta,eq_self_iff_true, implies_true_iff] },
    -- case where m < n.succ
    { obtain ⟨y, hy⟩ := hrec (nat.le_of_lt_succ h) (le_trans (cardinal.nat_cast_le.mpr (nat.le_succ n)) hα),
      obtain ⟨a,ha⟩ := gimme_more α n y (lt_of_lt_of_le (cardinal.nat_cast_lt.mpr (nat.lt_succ_self n)) hα),
      /- use (λ i : fin n.succ,
      dite (i.val < n) (λ hi, y (fin.cast_lt i hi)) (λ _, a)),
      -/
      let p := λ i : fin n.succ, i.val < n,
      let f : { i : fin n.succ | i.val < n } → α := λ i, y.to_fun (fin.cast_lt i.val i.prop),
      let f' : { i : fin n.succ | ¬ (p i) } → α  := λ ⟨i, hi⟩, a,

      use (λ i, if hi : p i then f ⟨i, hi⟩ else f' ⟨i, hi⟩),
      { refine function.injective.dite p _ _ _,
        { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
          simp only [subtype.mk_eq_mk],
          let hij' := subtype.mk_eq_mk.mp (y.inj' hij),
          simp only [fin.val_eq_coe] at hij',
          exact fin.ext hij' },
        { rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
          simp only [subtype.mk_eq_mk],
          rw [← subtype.coe_inj,
            nat.eq_of_lt_succ_of_not_lt i.prop hi,
            nat.eq_of_lt_succ_of_not_lt j.prop hj] },
        { intros _ _ _ _,
          change y.to_fun _ ≠ a,
          intro h, apply ha, use ⟨_,h⟩ } },
      intro i,
      simp only [fin.val_eq_coe, coe_fn_mk],
      rw dite_eq_iff,
      apply or.intro_left,  -- i.val < n
      use (lt_of_lt_of_le  i.prop (nat.le_of_lt_succ h)),
      rw ← hy i, refl } }
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
  obtain ⟨x', hx'⟩ := may_extend α hmn hα x,
  obtain ⟨y', hy'⟩ := may_extend α hmn hα y,
  obtain ⟨g, hg⟩ := hn_eq  x' y',
  use g,
  ext i,
  rw [smul_apply, ← hy' i, ← hx' i, ← hg, smul_apply],
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

--- J'EN SUIS LÀ !
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

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
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

example : ∀ (α : Type*), (card_ge α 2) ↔ nontrivial α :=
begin
  intro α,
  split,
  { rintro ⟨x, hxl, hxn⟩,
    apply nontrivial.mk,
    let a := list.nth_le x 0 _ , let b := list.nth_le x 1 _,
    use a, use b, intro hab,
    rw list.nodup_iff_nth_le_inj at hxn,
    have : ¬(0 = 1), exact zero_ne_one, apply this,
    apply hxn 0 1 _ _ _,
    any_goals { rw hxl, norm_num },
    exact hab },
  { rintro ⟨a, b, hab⟩,
    unfold card_ge, use ([a, b]),
    simp [hab] }
end

open_locale classical

/-- A 2-transitive action is primitive -/
theorem is_preprimitive_of_two_pretransitive (M α : Type*) [group M] [mul_action M α]
  (h2 : is_multiply_pretransitive M α 2) : is_preprimitive M α :=
begin
  cases subsingleton_or_nontrivial α with hα hα,
  -- Trivial case where subsingleton α
  { apply is_preprimitive.mk,
    { apply is_pretransitive.mk,
      intros x y, use 1, exact subsingleton_iff.mp hα _ _ },
    { intros B hB,
      cases B.eq_empty_or_nonempty with h h',
      { exact or.intro_left _ h, },
      { apply or.intro_right, apply or.intro_right,
        rw @subsingleton.eq_univ_of_nonempty _ hα B h',
        exact set.top_eq_univ } } },
  -- Important case :
  have hα : card_ge α 2,
  { obtain ⟨a, b, hab⟩ := hα, use ([a,b]), simp [hab],  },
  apply is_preprimitive.mk,
  rw is_pretransitive_iff_is_one_pretransitive,
  refine @is_multiply_pretransitive_of_higher M α _ 2 _ _ _ hα,
  { intro x, apply h2 },
  { norm_num, },
  intros B hB,
  cases subsingleton_or_nontrivial B with h h,
  -- Cas qui devra être trivial avec la changement de définition
  sorry,
  -- Cas top
  apply or.intro_right,
  apply or.intro_right,
  obtain ⟨a, b, hab⟩ := h,
  rw set.top_eq_univ,
  apply set.eq_univ_of_forall,
  intro c,
  cases em (c = a) with hca hca',
  rw hca, exact subtype.mem a,
  cases em (c = b) with hcb hcb',
  rw hcb, exact subtype.mem b,
  unfold is_multiply_pretransitive at h2,
  obtain ⟨g : M, hg : g • ([↑a,↑b] : list α) = ([↑a,c])⟩ := h2 _ _ _ _,
  any_goals { simp [subtype.coe_injective, hab, hca', hcb'] },
  simp at hg,
  cases is_block.def_one _ _ hB g,
  { rw ← h, use ↑b,
    exact ⟨subtype.mem b, hg.right⟩ },
  { exfalso,
    suffices : ¬ (disjoint (g • B) B), exact this h,
    rw set.not_disjoint_iff, use ↑a,
    split,
    { rw ← hg.left, use ↑a, exact ⟨subtype.mem a, rfl⟩ },
    exact (subtype.mem a) },
  { intro hab', apply hab, exact subtype.coe_inj.mp hab' },
  exact ne_comm.mp hca'
end

example {α : Type*} (s : finset α) (x : ↥s) : ↑x ∈ s :=
finset.coe_mem x

example {α : Type*} (l : list α) (x : ↥l.to_finset) : ↑x ∈ l :=
list.mem_to_finset.mp (finset.coe_mem x)



example {α : Type*} (n : ℕ) (l : list α) :
  (list.take n l).length = min n l.length :=
begin
refine list.length_take n l,
end


example {α : Type*} (s : set α) (x y : list ↥s) :
   x = y ↔ (list.map coe x : list α) = (list.map coe y) :=
begin
  split,
  intro h, rw h,
  intro h, exact  (list.map_injective_iff.mpr (subtype.coe_injective)) h,
end



end multiple_transitivity
end mul_action

end FundamentalConcepts


 /- -- Now useless
    { obtain ⟨l', hl', hl'n, hl'e⟩ := list.extend_nodup n.succ hn.left [a] (list.nodup_singleton a) _,
      rw list.length_singleton at hl'e,
      swap,
      { simp only [list.length_singleton], exact nat.succ_le_succ (zero_le n) },
      unfold card_ge,
      lift l'.drop 1 to list ↥(sub_mul_action_of_stabilizer M α a) with l hl_coe,
      swap,
      { intros x hx,
        change x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
        rw sub_mul_action_of_stabilizer_def,
        simp only [set.mem_compl_eq, set.mem_singleton_iff],
        suffices : a ∉ list.drop 1 l',
        { intro h, apply this, rw ← h, exact hx, },
        rw ← list.singleton_disjoint,
        apply list.disjoint_of_nodup_append,
        rw [← hl'e,  list.take_append_drop],
        exact hl'n },
      use l,
      split,
      { rw [← list.length_map, hl_coe, list.length_drop, hl',
          ← nat.pred_eq_sub_one, nat.pred_succ] },
      { rw ← list.nodup_map_iff (subtype.coe_injective),
        rw hl_coe,
        rw ← list.take_append_drop 1 l' at hl'n,
        exact (list.nodup_append.mp hl'n).2.1 } },
-/
