

import tactic.lift

import field_theory.galois

import .ad_sub_mul_actions
import .wielandt
import .ad_to_ulift
import .multiply_trans

import group_theory.group_action.embedding
import group_theory.specific_groups.alternating

section finite_groups

open mul_action
open_locale classical

variables (α : Type*) [fintype α]

lemma unnamed :
  mul_action.is_multiply_pretransitive (equiv.perm α) α (fintype.card α):=
begin
  apply is_pretransitive.mk,
  intros x y,
  let x' := equiv.of_bijective x.to_fun _,
  let y' := equiv.of_bijective y.to_fun _,
  use x'.symm.trans y',
  ext i,
  simp only [function.embedding.smul_apply, equiv.perm.smul_def, equiv.coe_trans,
    function.comp_app, equiv.of_bijective_apply, function.embedding.to_fun_eq_coe,
    embedding_like.apply_eq_iff_eq],
  exact x'.left_inv i,
  all_goals { rw fintype.bijective_iff_injective_and_card, split },
  any_goals { try {exact fintype.card_fin (fintype.card α) } },
  exact embedding_like.injective y,
  exact embedding_like.injective x,
end

lemma aux_lt_eq {m n : ℕ} (hmn : m < n) : (m < n - 1) ∨ (m = n - 1) :=
begin
  rw nat.lt_iff_le_not_le,
  cases dec_em (m = n - 1) with h h',
  { exact or.intro_right _ h },
  { apply or.intro_left, apply and.intro,
    { exact nat.le_pred_of_lt hmn},
    { intro h, apply h',
      exact nat.le_antisymm (nat.le_pred_of_lt hmn) h } },
end

lemma unnamed_iff {G : Type*} [G : subgroup (equiv.perm α)]
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 1)) :
  G = ⊤ :=
begin
  let j : fin (fintype.card α - 1) ↪ fin (fintype.card α) :=
    (fin.cast_le ((fintype.card α).sub_le 1)).to_embedding,
  rw eq_top_iff, intros k _,
  obtain ⟨x⟩ := gimme_some (le_of_eq (cardinal.mk_fintype α).symm),
  let hmt_eq := hmt.exists_smul_eq,
  let x' := j.trans x,
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x'),
  suffices : k = g, { rw this, exact set_like.coe_mem g },

  have hx : ∀ (x : fin(fintype.card α) ↪ α), function.surjective x.to_fun,
  { intro x,
    suffices : function.bijective x.to_fun, exact this.right,
    rw fintype.bijective_iff_injective_and_card,
    exact ⟨embedding_like.injective x, fintype.card_fin (fintype.card α)⟩ },

  have hgk' : ∀ (i : fin (fintype.card α)) (hi : i.val < fintype.card α - 1), (g • x) i = (k • x) i,
  { intros i hi,
    simpa using congr_fun (congr_arg coe_fn hg') ⟨i.val, hi⟩ },
  have hgk : ∀ (i : fin (fintype.card α)), (g • x) i = (k • x) i,
  { intro i,
    cases aux_lt_eq i.prop with hi hi,
    { exact hgk' i hi },
    { obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i),
      cases aux_lt_eq j.prop with hj hj,
      { exfalso,
        suffices : i = j,
        { rw [← this, ← hi] at hj, refine lt_irrefl _ hj },
        apply embedding_like.injective (g • x),
        rw hgk' j hj, rw hxj },
      { rw ← hxj,
        apply congr_arg,
        apply fin.ext,
        rw [hi, hj] } } },

  apply equiv.perm.ext, intro a,
  obtain ⟨i, rfl⟩ := (hx x) a,
  let zi := hgk i,
  simp only [function.embedding.smul_apply, equiv.perm.smul_def] at zi,
  simp only [function.embedding.to_fun_eq_coe],
  rw ← zi,
  refl
end



lemma unnamed' :
  mul_action.is_multiply_pretransitive (alternating_group α) α (fintype.card α - 2) :=
begin
  cases lt_or_ge (fintype.card α) 2 with h2 h2,
  { rw nat.sub_eq_zero_of_le (le_of_lt h2),
    apply is_zero_pretransitive },
  -- fintype.card α ≥ 2
  obtain ⟨n,hn⟩ := nat.le.dest h2,
  have hn' : fintype.card α - 2 = n := norm_num.sub_nat_pos (fintype.card α) 2 n hn,
  rw add_comm at hn,
  have hn_le : n ≤ fintype.card α, { rw ← hn, exact le_self_add },

  apply is_pretransitive.mk,
  rw hn',
  intros x y,

  obtain ⟨x', hx'⟩ :=
    may_extend hn_le (le_of_eq (cardinal.mk_fintype α).symm) x,
  obtain ⟨y', hy'⟩ :=
    may_extend hn_le (le_of_eq (cardinal.mk_fintype α).symm) y,
  let heq := (unnamed α).exists_smul_eq,
  obtain ⟨g, hg⟩ := heq x' y',
  cases int.units_eq_one_or g.sign with h h,
  { use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩,
    ext i,
    simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    refl },
  { have hg'1 : n + 1 < fintype.card α,
    { rw ← hn, exact nat.lt.base (n + 1) },
    have hg'2 : n < fintype.card α,
    { apply lt_trans _ hg'1, exact lt_add_one n },

    let g' := equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩),

    have hg' : g'.sign = -1,
    { rw equiv.perm.is_swap.sign_eq,
      unfold equiv.perm.is_swap,
      use (y'.to_fun ⟨n+1, hg'1⟩), use (y'.to_fun ⟨n, hg'2⟩),
      split,
      { intro h,
        let h' := function.embedding.injective y' h,
        simp only [subtype.mk_eq_mk] at h',
        exact nat.succ_ne_self _ h' },
      refl },

    use g' * g,
    { rw equiv.perm.mem_alternating_group,
      simp only [equiv.perm.sign_mul, h, hg'],
      norm_num },
    ext i, simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],

      simp only [function.embedding.trans_apply, rel_embedding.coe_fn_to_embedding,
        function.embedding.smul_apply, equiv.perm.smul_def],

    change (g' * g) • _ = _,
    rw ← smul_smul,
    simp,
    change (equiv.swap (y'.to_fun ⟨n+1, hg'1⟩) (y'.to_fun ⟨n, hg'2⟩))  _ = _,

    refine equiv.swap_apply_of_ne_of_ne _ _,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      let h' := fin.veq_of_eq h,
      simp only [fin.val_eq_coe, fin.coe_cast_le] at h',
      let hi := i.prop,
      rw h' at hi,
      simpa only [add_lt_iff_neg_left, not_lt_zero'] using hi } ,
    { rw ← hg,
      intro h,
      simp only [function.embedding.to_fun_eq_coe, function.embedding.smul_apply,
        equiv.perm.smul_def, embedding_like.apply_eq_iff_eq] at h,
      let h' := fin.veq_of_eq h,
      simp only [fin.val_eq_coe, fin.coe_cast_le] at h',
      let hi := i.prop,
      rw h' at hi,
      simpa only [lt_self_iff_false] using hi} }
end


lemma unnamed'_iff {G : Type*} [G : subgroup (equiv.perm α)]
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 2)) :
  alternating_group α ≤ G :=
begin
  sorry
end

end finite_groups
