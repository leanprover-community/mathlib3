

import tactic.lift

import field_theory.galois

import .ad_sub_mul_actions
import .wielandt
import .ad_to_ulift
import .multiply_trans
import .multiple_prim

import group_theory.group_action.embedding
import group_theory.perm.support
import group_theory.specific_groups.alternating

section finite_groups

open mul_action
open_locale classical

variables (α : Type*) [fintype α] [decidable_eq α]

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


section Jordan

example (s : set α) : cardinal.mk s = ↑(fintype.card s) :=
begin
  exact cardinal.mk_fintype ↥s
end

variables (G : subgroup (equiv.perm α))

lemma normal_closure_of_stabilizer_eq_top
  (hsn' : 2 < fintype.card α) (hG' : is_multiply_pretransitive G α 2)
  {a : α} : subgroup.normal_closure (stabilizer G a).carrier = ⊤ :=
begin
  have hG : is_pretransitive G α,
  { rw is_pretransitive_iff_is_one_pretransitive,
    apply is_multiply_pretransitive_of_higher,
    exact hG',
    norm_num,
    rw cardinal.mk_fintype, apply le_of_lt, rw cardinal.nat_cast_lt, exact hsn' },
  let hG_eq := hG.exists_smul_eq,

  suffices : (stabilizer G a).is_maximal,
    rw subgroup.is_maximal_def at this,
    apply this.right,

  { --  unfold subgroup.normal_closure,
    split,
    { intros g hg, apply subgroup.closure_le_normal_closure,
      apply subgroup.subset_closure, exact hg },
    { intro hyp,

      -- prendre b, c ≠ a
      have : ∃ (b c : sub_mul_action_of_stabilizer G α a), b ≠ c,
      { rw ← nontrivial_iff ,
        rw ← cardinal.one_lt_iff_nontrivial,
        change 1 < cardinal.mk (sub_mul_action_of_stabilizer G α a).carrier,
        rw sub_mul_action_of_stabilizer_def,
        rw [← nat.cast_one, cardinal.mk_fintype, cardinal.nat_cast_lt],
        rw ← add_lt_add_iff_left 1,
        refine lt_of_lt_of_le hsn' (le_of_eq _),
        rw ← fintype.card_of_subsingleton _,
        apply cardinal.nat_cast_injective,

        rw [← cardinal.mk_fintype, nat.cast_add, ← cardinal.mk_fintype],
        simp only [← cardinal.mk_fintype],
        rw cardinal.mk_sum_compl ,
        { use a, exact set.mem_singleton a },
        exact unique.subsingleton },
      obtain ⟨⟨b, hb⟩, ⟨c, hc⟩, hbc⟩ := this,
      simp only [ne.def, subtype.mk_eq_mk] at hbc,

      have hatrans : is_pretransitive (stabilizer G a) (sub_mul_action_of_stabilizer G α a),
      { rw is_pretransitive_iff_is_one_pretransitive,
        exact (stabilizer.is_multiply_pretransitive G α hG).mp hG' },
      let hatrans_eq := hatrans.exists_smul_eq,

      -- trouver g ∈ stabilizer G a, g • b = c,
      obtain ⟨⟨g, hg⟩, hgbc⟩ := hatrans_eq ⟨b, hb⟩ ⟨c, hc⟩,
      have hgbc' : g • b = c,
      { rw ← set_like.coe_eq_coe at hgbc, exact hgbc },

      -- trouver h ∈ G, h⁻¹ • a = b,
      obtain ⟨h : G, hinvab : h • b = a⟩ := hG_eq b a,

      suffices : (h * g * h⁻¹) • a ≠ a,
      -- h * g * h⁻¹ ∈ subgroup.normal_closure (stabilizer G a)
      { apply this,
        rw ← mem_stabilizer_iff,
        apply hyp,
        refine (subgroup.normal_closure_normal).conj_mem _ _ _,
        apply subgroup.subset_normal_closure,
        exact hg },

      -- h * g * h⁻¹ • a = h • g • b = h • c ≠ h • b = a
      suffices : (h * g * h⁻¹) • a = h • c,
      { rw this, rw ← hinvab,
        intro z,
        apply hbc, apply mul_action.injective h, exact z.symm },

      simp only [← smul_smul],
      rw ← hgbc',
      refine congr_arg2 _ rfl _,
      refine congr_arg2 _ rfl _,
      rw inv_smul_eq_iff, exact hinvab.symm } },

    rw @maximal_stabilizer_iff_primitive G α _ _
      (begin
        rw [← cardinal.one_lt_iff_nontrivial,
          cardinal.mk_fintype, ← nat.cast_one, cardinal.nat_cast_lt],
        exact lt_trans (lt_add_one 1) hsn',
        end) hG a,
    apply is_preprimitive_of_two_pretransitive,
    exact hG'
end

theorem jordan0_init (hG : is_preprimitive G α)
  {a : α} (hsn' : 2 < fintype.card α)
  (hs_trans : is_pretransitive (stabilizer G a) (sub_mul_action_of_stabilizer G α a)) :
  is_multiply_pretransitive (subgroup.normal_closure (stabilizer G a).carrier) α 2 :=
begin
  let hG_eq := hG.exists_smul_eq,
  have hG' : is_multiply_pretransitive G α 2,
  { rw stabilizer.is_multiply_pretransitive,
    { rw ← is_pretransitive_iff_is_one_pretransitive,
      exact hs_trans, },
    exact hG.to_is_pretransitive },

  rw normal_closure_of_stabilizer_eq_top α G hsn' hG',
  let j : mul_action_bihom G α ↥(⊤ : subgroup G) α := {
  to_fun := id,
  to_monoid_hom := {
    to_fun := λ m, ⟨m, subgroup.mem_top m⟩,
    map_one' := rfl,
    map_mul' := λ m n, rfl },
  map_smul' := λ m x, rfl, },
  suffices : function.surjective j.to_fun,
  apply is_multiply_pretransitive_via_surjective_bihom this hG',
  exact function.surjective_id,
end

theorem card_eq_one_iff_is_singleton (s : set α) (hs : fintype.card s = 1) :
  ∃ (a : α), s = {a} :=
begin
  obtain ⟨⟨a,ha⟩, ha'⟩ := fintype.card_eq_one_iff.mp hs,
  use a,
  rw set.eq_singleton_iff_unique_mem,
  apply and.intro ha,
  intros x hx,
  exact subtype.mk_eq_mk.mp  (ha' ⟨x, hx⟩)
end

-- α = Ω, s = Δ, α \ s = Γ
theorem jordan0 (hG : is_preprimitive G α)
  {s : set α} {n : ℕ}  (hsn : fintype.card s = n.succ)
  (hsn' : 1 + n.succ < fintype.card α)
  (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 :=
begin
  let hG_eq := hG.to_is_pretransitive.exists_smul_eq,
  induction n with n hrec,
  -- Initialization : n = 0
  { -- s = {a}
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton α s hsn,
    rw hsa at *,

    have hG' : is_multiply_pretransitive G α 2,
    { rw stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive,
      rw ← is_pretransitive_iff_is_one_pretransitive,
      -- is_pretransitive (stabilizer G a) (sub_mul_action_of_stabilizer G α a),
      refine is_pretransitive_of_bihom
        (sub_mul_action_of_fixing_subgroup_of_singleton_bihom G a)
        (function.bijective.surjective
          (sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective G a))
        hs_trans, },

    suffices : stabilizer G a = fixing_subgroup G ({a} : set α),
    rw [← this],

    refine jordan0_init α G hG _ _,
    apply lt_of_eq_of_lt _ hsn', norm_num,
    rw is_pretransitive_iff_is_one_pretransitive,
    exact (stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive).mp hG',

    -- stabilizer G a = fixing_subgroup G ({a} : set α),
    { ext g,  split,
      intro hg, rw mem_fixing_subgroup_iff, intros x hx,
        rw (set.mem_singleton_iff.mp hx), exact hg,
      intro hg, exact (mem_fixing_subgroup_iff G).mp hg a (set.mem_singleton a) } },

  -- Induction step
  {



    sorry },
end

theorem jordan0' (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 := sorry

theorem jordan1 (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_pretransitive G α 2 :=
begin
 -- We can deduce it from jordan0
  apply is_pretransitive_of_subgroup,
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply jordan0 α G hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_trans,
end

theorem jordan1' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α 2 :=
begin
 -- We can deduce it from jordan0'
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply is_multiply_preprimitive_of_subgroup,
  norm_num,
  refine jordan0' α G hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_prim
end

-- Wielandt : s = Δ, n - m = #s, n = #α, m = #sᶜ, 1 < m < n
-- 1 + #s < n , #s ≥ 1

theorem jordan2 (hG : is_preprimitive G α)
  {s : set α} {m n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hprim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α (1 + n.succ) :=
begin
  let hG_eq := hG.exists_smul_eq,
  induction n with n hrec,
  { obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton α s hsn,
    rw hsa at *,
    split,
    { rw stabilizer.is_multiply_pretransitive,
      rw ← is_pretransitive_iff_is_one_pretransitive,
      refine is_pretransitive_of_bihom
        (sub_mul_action_of_fixing_subgroup_of_singleton_bihom G a)
        (function.bijective.surjective (sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective G a))
        hprim.to_is_pretransitive,
        exact hG.to_is_pretransitive, },
    { intros t h,
      suffices ht' : fintype.card t = 1,
      { obtain ⟨b, htb⟩ := card_eq_one_iff_is_singleton α t ht',
        rw htb at *,
        obtain ⟨g, hg⟩ := hG_eq a b,
        have hst : g • {a} = {b}, sorry,
        apply is_preprimitive_of_bihom _
          (function.bijective.surjective
            (sub_mul_action_of_fixing_subgroup_conj_bihom_bijective G hst))
          hprim },
      { rw [cardinal.mk_fintype, ← nat.cast_one, ← nat.cast_add,
          cardinal.nat_cast_inj, add_left_inj] at h,
        exact h } } },
  -- Induction step
  sorry
end

theorem jordan_perm (hG : is_preprimitive G α)
  {g : equiv.perm α} (h2g : equiv.perm.is_swap g) (hg : g ∈ G) : G = ⊤  :=
sorry

theorem jordan_alternating (hG : is_preprimitive G α)
  {g : equiv.perm α} (h3g : equiv.perm.is_three_cycle g) (hg : g ∈ G) :
  alternating_group α ≤ G = ⊤  :=
sorry

end Jordan



end finite_groups
