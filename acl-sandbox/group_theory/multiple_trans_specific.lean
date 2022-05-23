

import tactic.lift

import field_theory.galois

import .ad_sub_mul_actions
import .wielandt
import .ad_to_ulift
import .multiply_trans
import .multiple_prim

import group_theory.group_action.embedding
import group_theory.perm.support
import group_theory.index
import group_theory.specific_groups.alternating

section finite_groups

open mul_action
open_locale classical

variables {α : Type*} [fintype α] [decidable_eq α]

lemma equiv_perm_is_fully_pretransitive :
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

lemma is_fully_minus_one_pretransitive_iff [G : subgroup (equiv.perm α)]
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

lemma alternating_group_is_fully_minus_two_pretransitive :
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
  let heq := (equiv_perm_is_fully_pretransitive).exists_smul_eq,
  obtain ⟨g, hg⟩ := heq x' y',
  cases int.units_eq_one_or g.sign with h h,
  { use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩,
    ext i,
    simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    refl },
  swap, exact _inst_2,
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
      simpa only [lt_self_iff_false] using hi} },
end

lemma get_classes_of_index_two {G : Type*} [group G] (H : subgroup G) (hH2 : H.index = 2) :
  (∃ (k : G), k ∉ H) ∧  ∀ (k g : G), k ∉ H → (g ∉ H ↔ k * g ∈ H) :=
begin
 haveI hfinH : fintype (G⧸H),
  { refine fintype_of_not_infinite _,
    intro h,
    change nat.card (G⧸H) = 2 at hH2,
    rw @nat.card_eq_zero_of_infinite _ h at hH2,
    simpa using hH2 },

  have : H ≠ ⊤,
  { intro hH,
    rw [hH, subgroup.index_top] at hH2,
    simpa using hH2 },
  have : ∃ (g : G), g ∉ H,
  { simp only [ne.def, ← set_like.coe_set_eq]  at this,
    simp_rw ← set_like.mem_coe,
    rw ← set.ne_univ_iff_exists_not_mem ,
    exact this },
  apply and.intro this,

  obtain ⟨k, hk⟩ := this,
  have quot2k : ∀ (k : G) (hk : k ∉ H),
    ({ quotient_group.mk 1, quotient_group.mk k } : set (G ⧸H)) = ⊤,
  { intros k hk,
    simp only [← finset.coe_insert, ← finset.coe_singleton],
    simp only [set.top_eq_univ, ← finset.coe_univ],
    apply congr_arg,
    change nat.card (G ⧸ H) = 2 at hH2,
    rw [← finset.card_eq_iff_eq_univ, ← nat.card_eq_fintype_card, hH2],
    apply finset.card_doubleton,
    intro h1k, apply hk,
    simpa [quotient_group.eq', one_inv, one_mul] using h1k },

  intros k g hk,
  split,
  { intro hg',
    have : quotient_group.mk (k * g)  ∈ ({ quotient_group.mk 1, quotient_group.mk k } : set (G ⧸H)),
        rw [quot2k _ hk, set.top_eq_univ], apply set.mem_univ,
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at this,
    cases this with this this,
    { rw [eq_comm, quotient_group.eq', one_inv, one_mul] at this, exact this },
    { rw [eq_comm, quotient_group.eq', ← mul_assoc, mul_left_inv, one_mul] at this,
      exfalso,
      exact hg' this } },
  { intros hkg hg,
    apply hk,
    rw ← mul_mem_cancel_right hg,
    exact hkg }
end

theorem is_normal_of_index_two {G : Type*} [group G] (H : subgroup G) (hH2 : H.index = 2) :
  H.normal :=
begin
  obtain ⟨⟨k, hk⟩, hH⟩ := get_classes_of_index_two H hH2,
  apply subgroup.normal.mk,
  intros h hh g,
  cases dec_em (g ∈ H) with hg hg',
  { rw mul_mem_cancel_right (inv_mem hg),
    rw mul_mem_cancel_left hg,
    exact hh },
  { rw mul_assoc,
    rw ← (hH _ _ hg'),
    by_contra hz,
    rw ← inv_mem_iff at hz, simp only [mul_inv_rev, inv_inv] at hz,
    rw ← (hH _ _ hg') at hz,
    apply hz,
    simp only [inv_mem_iff],
    exact hh }
end

lemma alternating_group_of_subsingleton (hα : subsingleton α) : alternating_group α = ⊥ :=
begin
    rw eq_bot_iff,
    intros g hg,
    rw subgroup.mem_bot,
    let hα := @alternating_group.unique α _ _ hα,
    rw ← set_like.coe_mk g hg,
    rw ← subgroup.coe_one (alternating_group α),
    let hαq := hα.uniq,
    rw set_like.coe_eq_coe,
    rw hαq 1, rw hαq ⟨g, hg⟩
end

example {G : Type*} [fintype G] [group G] (H : subgroup G) {p : ℕ} (hp : p.prime) (hHp : H.index = p)
  (hp' : ∀ {l : ℕ} (hl : l.prime) (hl' : l ∣ fintype.card G), l ≥ p) : H.normal := sorry

lemma alternating_is_characteristic : (alternating_group α).characteristic :=
begin
  cases subsingleton_or_nontrivial α with hα hα,
  -- hα : subsingleton α
  { rw alternating_group_of_subsingleton hα,
    exact subgroup.bot_characteristic },

  -- hα : nontrivial α
  apply subgroup.characteristic.mk,
  intro φ,
  rw alternating_group_eq_sign_ker,
  rw monoid_hom.comap_ker,
  set s := equiv.perm.sign.comp φ.to_monoid_hom,

  have hs : function.surjective s,
  { change function.surjective (equiv.perm.sign ∘ φ),
    rw function.surjective.of_comp_iff _,
    exact @equiv.perm.sign_surjective α _ _ hα,
    exact mul_equiv.surjective φ },
  obtain ⟨g', hg'⟩ := hs (-1),
  have hg' : s g' ≠ 1,
  { rw hg',  intro h, rw ← units.eq_iff at h,
    simpa only using h, },

  apply congr_arg,

  ext g,
  apply congr_arg,
  refine equiv.perm.swap_induction_on g _ _,
  { rw [map_one, equiv.perm.sign.map_one] },
  { intros f x y hxy hf,

    rw [s.map_mul, equiv.perm.sign.map_mul, hf],
    apply congr_arg2 (*) _ (rfl),
    revert x y hxy,
    by_contra,
    push_neg at h,
    obtain ⟨a, b, hab, hk⟩ := h,
    rw equiv.perm.sign_swap hab at hk,
    let hk := or.resolve_right (int.units_eq_one_or (s _)) hk,

    apply hg',
    refine equiv.perm.swap_induction_on g' (s.map_one) _,
    intros f x y hxy hf,
    rw [s.map_mul, hf, mul_one],

    obtain ⟨u, hu⟩ := equiv.perm.is_conj_swap hxy hab,
    apply mul_left_cancel,
    swap, exact (s u),
    rw [← s.map_mul, semiconj_by.eq hu, s.map_mul, hk, mul_one, one_mul] }
end

lemma is_commutative_of_prime_order
{G : Type*} [group G] [fintype G] {p : ℕ} [hp : fact p.prime]
  (h : fintype.card G = p) : is_commutative G (*) :=
begin
  apply is_commutative.mk,
  exact (@is_cyclic.comm_group G _ (@is_cyclic_of_prime_card G _ _ p hp h)).mul_comm
end

theorem  equiv.perm.is_prod_swap_list (g : equiv.perm α)  :
  ∃ (l : list (equiv.perm α)), (∀ (s : equiv.perm α), s ∈ l → s.is_swap) ∧ g = l.prod :=
begin
  apply equiv.perm.swap_induction_on g,
  { use list.nil,
    split,
    { intros s hs, exfalso, exact list.not_mem_nil s hs },
    { simp only [list.prod_nil] } },
  { intros f x y hxy hf,
    obtain ⟨l, hl, hf⟩ := hf,
    use (equiv.swap x y) :: l,
    split,
    { intros s hs,
      rw list.mem_cons_iff at hs,
      cases hs with hs hs,
      rw hs, exact ⟨x,y, hxy, rfl⟩,
      exact hl s hs },
    rw list.prod_cons,
    rw hf }
end

lemma is_alternating_of_index_2 {G : subgroup (equiv.perm α)}
  (hG : G.index = 2) : alternating_group α = G :=
begin
  haveI hG' := is_normal_of_index_two G hG,
  let s : (equiv.perm α) →* (equiv.perm α ⧸ G) := quotient_group.mk' G,
  rw alternating_group_eq_sign_ker,
  rw ← quotient_group.ker_mk G,
  have hG'' : is_commutative (equiv.perm α ⧸ G) (*),
  { refine is_commutative_of_prime_order _,
    exact 2, exact nat.fact_prime_two,
    rw ← nat.card_eq_fintype_card,
    exact hG },

  have : ∃ (g : equiv.perm α), g.is_swap ∧ g ∉ G,
  { by_contra, push_neg at h,
    suffices : G = ⊤,
      rw this at hG, rw subgroup.index_top at hG,
      apply (1 : ℕ).one_ne_bit0, exact hG,
    rw eq_top_iff,
    rw ← equiv.perm.closure_is_swap,
    rw subgroup.closure_le G,
    intros g hg,
    simp only [set.mem_set_of_eq] at hg,
    simp only [set_like.mem_coe],
    exact h g hg },
  obtain ⟨k, hk, hk'⟩ := this,

  have this' : ∀ (g : equiv.perm α), g.is_swap → s g = s k,
  { intros g hg,
    obtain ⟨a, b, hab, habg⟩ := hg,
    obtain ⟨x, y, hxy, hxyk⟩ := hk,
    obtain ⟨u, hu⟩ := equiv.perm.is_conj_swap hab hxy,
    let hu' := congr_arg s (semiconj_by.eq hu),
    simp only [map_mul] at hu',
    apply mul_left_cancel,
    swap, exact s u,
    rw [habg, hxyk, hu'],
    apply hG''.comm },

  have hsk2 : (s k) ^ 2 = 1,
  { rw pow_two, rw ← map_mul,
    obtain ⟨x, y, hxy, hxyk⟩ := hk,
    rw hxyk,
    rw equiv.swap_mul_self,
    rw map_one },

  ext g,
  simp only [equiv.perm.sign.mem_ker, (quotient_group.mk' G).mem_ker],


  obtain ⟨l, hl, hg⟩ := g.is_prod_swap_list,
  let hsg := equiv.perm.sign_prod_list_swap hl,
  rw ← hg at hsg,
  have hsg' : s g = (s k) ^l.length,
  { rw hg,
    rw map_list_prod,
    rw list.prod_eq_pow_card (list.map s l) (s k) _,
    rw list.length_map,
    intros x hx,
    simp only [list.mem_map] at hx,
    obtain ⟨y, hyl, hxy⟩ := hx,
    rw ← hxy,
    apply this', exact hl y hyl, },
  obtain ⟨m, hm⟩ := nat.even_or_odd' (l.length),
  have neg_one_neq_one : (-1 : units ℤ) ≠ 1 :=
  begin
    intro h,
    rw ← units.eq_iff at h,
    simpa only using h,
  end,

  cases hm with hm hm,
  { rw [hm, pow_mul] at hsg hsg',
    rw hsk2 at hsg', rw int.units_sq at hsg,
    rw one_pow at hsg' hsg,
    simp only [hsg, hsg'],
    simp only [eq_self_iff_true] },
  { rw [hm, pow_add, pow_mul, pow_one] at hsg hsg',
    rw hsk2 at hsg', rw int.units_sq at hsg,
    rw [one_pow, one_mul] at hsg' hsg,
    rw [hsg, hsg'],
    simp only [quotient_group.mk'_apply, quotient_group.eq_one_iff],
    split,
    { intro h, exfalso, exact neg_one_neq_one h },
    { intro h, exfalso, exact hk' h } }
end

lemma large_subgroup_of_perm_contains_alternating {G : subgroup (equiv.perm α)}
  (hG : 2 * fintype.card G ≥ fintype.card (equiv.perm α)) :
  alternating_group α ≤ G :=
begin
  cases nat.eq_zero_or_pos G.index,
  { exfalso,
    exact subgroup.index_ne_zero_of_fintype h },
  cases eq_or_gt_of_le (nat.succ_le_iff.mpr h) with h h,
  { rw subgroup.index_eq_one at h, rw h, exact le_top },
  rw ← nat.succ_le_iff at h, norm_num at h,

  apply @le_of_eq _ _ (alternating_group α) G,
  apply is_alternating_of_index_2,
  refine le_antisymm _ h,

  refine nat.le_of_mul_le_mul_left _ _,
  swap,
  { rw [mul_comm, subgroup.index_mul_card, mul_comm],
    exact hG },
  exact fintype.card_pos
end



lemma nat.eq_minus_one_of_lt_of_ge {i n : ℕ} (hi : i < n) (hi' : n - 1 ≤ i) : i = n - 1 :=
begin
  refine nat.eq_of_le_of_lt_succ hi' _,
  rw nat.sub_add_cancel (nat.succ_le_of_lt (lt_of_le_of_lt (zero_le i) hi)),
  exact hi,
end


lemma nat.le_pred_succ_self (n : ℕ) : n ≤ n.pred.succ :=
begin
  cases nat.eq_zero_or_eq_succ_pred n,
  rw h, apply zero_le,
  exact le_of_eq h,
end

lemma nat.iff_eq_minus_one {n i : ℕ} (hni : n - 2 < i) (hin : i < n) :
  i = n - 1 :=
begin
    apply le_antisymm,
    rw ← nat.lt_succ_iff , rw nat.succ_eq_add_one,
    refine lt_of_lt_of_le hin _,
    swap,
    rw [← one_add_one_eq_two, ← nat.sub_sub, nat.lt_iff_add_one_le] at hni,
    refine le_trans _ hni,
    all_goals
    { simp only [← nat.succ_eq_add_one, ← nat.pred_eq_sub_one],
      apply nat.le_pred_succ_self },
end


lemma contains_alternating_of_index_le_2' {G : subgroup (equiv.perm α)}
  (hG : G.index ≤ 2) : alternating_group α ≤ G :=
begin
  apply large_subgroup_of_perm_contains_alternating,
  rw ← subgroup.index_mul_card G,
  apply nat.mul_le_mul_right _ hG,
end

-- Preuve très maladroite
-- Il vaudrait mieux prouver la divisibilité de Wielandt, 9.3
-- On verrait tout de suite que #G est multiple de n!/2,
-- donc l'indice de G est au plus 2.
lemma contains_alternating_iff_is_all_minus_two_pretransitive
  {G : Type*} [G : subgroup (equiv.perm α)]
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 2)) :
  alternating_group α ≤ G :=
begin
  cases nat.lt_or_ge (fintype.card α) 2 with hα1 hα,
  { -- fintype.card α  < 2
    rw nat.lt_succ_iff at hα1,
    suffices : alternating_group α = ⊥, rw this, exact bot_le,
    rw ← subgroup.card_le_one_iff_eq_bot,
    suffices : fintype.card ↥(alternating_group α) ≤ fintype.card (equiv.perm α),
    { apply le_trans this,
      rw fintype.card_perm,
      exact nat.factorial_le hα1 },
    apply fintype.card_subtype_le },

  apply large_subgroup_of_perm_contains_alternating,

  have hn : ∀ (n : ℕ) (hn : n >0), fintype.card α - n < fintype.card α,
  { intros n hn,
    conv_rhs { rw ← nat.sub_zero (fintype.card α)},
    refine nat.sub_lt _ hn,
    apply lt_of_lt_of_le _ hα, norm_num },
  let h1 := hn 1 (by norm_num),
  let h2 := hn 2 (by norm_num),

  let j : fin (fintype.card α - 2) ↪ fin (fintype.card α) :=
    (fin.cast_le ((fintype.card α).sub_le 2)).to_embedding,
  obtain ⟨x, hx⟩ := gimme_some (le_of_eq (cardinal.mk_fintype α).symm),
  have hx : function.surjective x.to_fun,
  { suffices : function.bijective x.to_fun, exact this.right,
    rw fintype.bijective_iff_injective_and_card,
    exact ⟨embedding_like.injective x, fintype.card_fin (fintype.card α)⟩ },

  let x1 := x (⟨fintype.card α - 1, h1⟩ : fin(fintype.card α)),
  let x2 := x (⟨fintype.card α - 2, h2⟩ : fin(fintype.card α)),
  let s := equiv.swap x1 x2,

  suffices : ∀ (k : equiv.perm α), k ∈ G ∨ k * s ∈ G,
  { let f : (({1, s} : finset (equiv.perm α)) × G) → (equiv.perm α) :=
      λ ⟨u, g⟩, ↑g * ↑u,
    have hf : function.surjective f,
    { intro k,
      cases this k,
      { let u : ({1, s} : finset (equiv.perm α)) := ⟨1, finset.mem_insert_self 1 _⟩,
        let g : ↥G := ⟨k, h⟩,
        use ⟨u, g⟩,
        change ↑g * ↑u = k,
        simp only [set_like.coe_mk, subtype.coe_mk, mul_one]},
      { let u : ({1, s} : finset (equiv.perm α)) := ⟨s, _⟩,
        let g : ↥G := ⟨k * s, h⟩,
        use ⟨u, g⟩,
        change ↑g * ↑u = k,
        simp only [subtype.coe_mk, equiv.mul_swap_mul_self],
        simp only [finset.mem_insert, finset.mem_singleton, eq_self_iff_true, or_true] } },
    apply le_trans (fintype.card_le_of_surjective f hf),
    rw fintype.card_prod,
    apply nat.mul_le_mul_right,
    simp only [fintype.card_coe],
    apply le_trans (finset.card_insert_le _ _),
    rw finset.card_singleton },

  intro k,
  let hmt_eq := hmt.exists_smul_eq,
  let x' := j.trans x,
  obtain ⟨g, hg'⟩ := hmt_eq x' (k • x'),

  have hgk' : ∀ (i : fin (fintype.card α)) (hi : i.val < fintype.card α - 2),
    g • (x i) = k • (x i),
  { intros i hi,
    simpa using congr_fun (congr_arg coe_fn hg') ⟨i.val, hi⟩ },

  have hgxkx : g • x2 = k • x2 ∨ g • x1 = k • x2,
  { obtain ⟨⟨i, hi⟩, hi'⟩ := hx (g⁻¹ • k • x2),
    rw eq_inv_smul_iff at hi',
    rw function.embedding.to_fun_eq_coe at hi',
    cases lt_or_ge i (fintype.card α - 2),
    { exfalso,
      rw hgk' ⟨i, hi⟩ h at hi',
      simp only [smul_left_cancel_iff, embedding_like.apply_eq_iff_eq] at hi',
      rw lt_iff_not_ge at h, apply h,
      rw hi',
      apply ge_of_eq, refl },
    rw ← hi',
    simp only [smul_left_cancel_iff, embedding_like.apply_eq_iff_eq],
    cases eq_or_gt_of_le h with h h',
    { apply or.intro_left, rw h },
    { apply or.intro_right,
      rw nat.iff_eq_minus_one h' hi } },

  let s1 := ite (g • x2 = k • x2) 1 s,
  suffices : k = g * s1⁻¹,
  { rw this,
    cases (ite_eq_or_eq (g • x2 = k • x2) 1 s : s1 = 1 ∨ s1 = s) with hs1 hs1,
    { change s1 = 1 at hs1,
      apply or.intro_left,
      rw hs1,
      simp only [one_inv, mul_one, set_like.coe_mem g] },
    { change s1 = s at hs1,
      apply or.intro_right,
      rw hs1,
      simp only [equiv.swap_inv, equiv.mul_swap_mul_self, set_like.coe_mem] } },

  suffices : ∀ (i : fin (fintype.card α)), i.val < fintype.card α - 1 →
    k • (x i) = g • s1⁻¹ • (x i),

  { ext a, obtain ⟨⟨i, hi⟩, rfl⟩ := hx a,
    cases nat.lt_or_ge i (fintype.card α - 1) with hi' hi',
    { simp only [function.embedding.to_fun_eq_coe, equiv.perm.coe_mul, function.comp_app],
      let hzi := this ⟨i, hi⟩ hi',
      simp only [function.embedding.smul_apply, equiv.perm.smul_def] at hzi,
      rw hzi,
      refl },
    -- i = fintype.card α - 1
    obtain ⟨⟨j, hj⟩, hij⟩ := hx (k⁻¹ • g • s1⁻¹ • (x ⟨i, hi⟩)),
    rw eq_inv_smul_iff at hij,
    cases nat.lt_or_ge j (fintype.card α - 1) with hj' hj',
    { let hzj := this ⟨j, hj⟩ hj',
      simp only [function.embedding.smul_apply, equiv.perm.smul_def, function.embedding.to_fun_eq_coe] at hij hzj,
      rw hij at hzj,
      simp only [smul_left_cancel_iff, embedding_like.apply_eq_iff_eq] at hzj,
      exfalso,
      apply lt_irrefl j,
      rw hzj at hi',
      exact lt_of_lt_of_le hj' hi' },
    { change _ = ↑g • _ at hij,
      simp only [function.embedding.to_fun_eq_coe, equiv.perm.smul_def,
        function.embedding.smul_apply] at hij,
      simp only [function.embedding.to_fun_eq_coe, equiv.perm.coe_mul, function.comp_app],
      rw ← hij,
      simp only [embedding_like.apply_eq_iff_eq],
      rw nat.eq_minus_one_of_lt_of_ge hi hi',
      rw nat.eq_minus_one_of_lt_of_ge hj hj' } },

    rintro ⟨i, hi⟩ hi',

    cases lt_or_ge i (fintype.card α - 2) with hi' hi'',
    { -- i < fintype.card α - 2
      let z := (hgk' ⟨i, hi⟩ hi').symm,
      /- simp only [function.embedding.smul_apply, equiv.perm.smul_def] at z,
      simp only [function.embedding.smul_apply, equiv.perm.smul_def],
       -/
      rw z,
      simp only [smul_left_cancel_iff],
      cases (ite_eq_or_eq (g • x2 = k • x2) 1 s : s1 = 1 ∨ s1 = s) with hs1 hs1,
      { change s1 = 1 at hs1, rw hs1,
        refl, },
      { change s1 = s at hs1, rw hs1,
        simp only [equiv.swap_inv, equiv.perm.smul_def],
        rw equiv.swap_apply_of_ne_of_ne _ _,
        all_goals
        { refine function.injective.ne x.inj' _,
          simp only [ne.def],
          intro hyp,  apply not_le.mpr hi', rw hyp },
        apply nat.sub_le_sub_left, norm_num } },

    { -- i ≥ fintype.card α - 2
      have hx : x ⟨i, hi⟩ = x2,
      { apply congr_arg,
        simp only,
        apply nat.eq_minus_one_of_lt_of_ge _ hi'',
        apply lt_of_lt_of_le hi',
        apply le_of_eq, refl },
      simp only [function.embedding.smul_apply, equiv.perm.smul_def],

      simp only [equiv.perm.smul_def] at hgxkx,
      cases hgxkx with gx2_eq_kx2 gx1_eq_kx2,
      { have hs' : s1 = 1,
        { rw ite_eq_left_iff, intro h, exfalso,
          apply h, rw gx2_eq_kx2,
          simp only [equiv.perm.smul_def] },
        simp only [hx, ← gx2_eq_kx2, smul_left_cancel_iff,
          hs', one_inv, equiv.perm.coe_one, id.def] },
      { have hs' : s1 = s,
        { rw ite_eq_right_iff, intro h, exfalso,
          simp only [equiv.perm.smul_def] at h,
          rw ← gx1_eq_kx2 at h,
          simp only [smul_left_cancel_iff, embedding_like.apply_eq_iff_eq] at h,
          rw [nat.sub_succ', ← nat.pred_eq_sub_one] at h,
          refine ne_of_lt (nat.pred_lt _) h,
          intro h', simp only [tsub_eq_zero_iff_le] at h',
          apply (lt_iff_not_ge _ _).mp (nat.lt_succ_self 1),
          exact le_trans hα h' },
        rw [hx, ← gx1_eq_kx2, hs', equiv.swap_inv, smul_left_cancel_iff, equiv.swap_apply_right] } }
end

lemma contains_alternating_iff_is_all_minus_two_pretransitive'
  {G : subgroup (equiv.perm α)}
  (hmt : is_multiply_pretransitive ↥G α (fintype.card α - 2)) :
  alternating_group α ≤ G :=
begin
  cases nat.lt_or_ge (fintype.card α) 2 with hα1 hα,
  { -- fintype.card α  < 2
    rw nat.lt_succ_iff at hα1,
    suffices : alternating_group α = ⊥, rw this, exact bot_le,
    rw ← subgroup.card_le_one_iff_eq_bot,
    suffices : fintype.card ↥(alternating_group α) ≤ fintype.card (equiv.perm α),
    { apply le_trans this,
      rw fintype.card_perm,
      exact nat.factorial_le hα1 },
    apply fintype.card_subtype_le },

  suffices : ∃ (s : set α), fintype.card s = fintype.card α - 2,
  obtain ⟨s, hs⟩ := this,
  rw ← hs at hmt,
  let hyp := index_of_fixing_subgroup_of_multiply_pretransitive G α s hmt,
  rw [hs, (nat.sub_sub_self hα), nat.factorial_two] at hyp,

  let hyp' := nat.mul_le_mul_right 2
    (nat.le_of_dvd (begin rw fintype.card_pos_iff, use 1, end)
      (subgroup.index_dvd_card  (fixing_subgroup G s))),
  rw [hyp, mul_comm] at hyp',

  apply large_subgroup_of_perm_contains_alternating,
  rw ge_iff_le, rw fintype.card_equiv (equiv.refl _) , exact hyp',

  obtain ⟨s, hs⟩ := finset.exists_smaller_set (⊤: finset α)
    (fintype.card α - 2) (nat.sub_le _ _),
  use s,
  simp only [finset.coe_sort_coe, fintype.card_coe],
  exact hs.right,
end



example (n : ℕ) (hn : n ≥ 2) : n - 2 ≠ n - 1 :=
begin
  intro h,
  rw [nat.sub_succ', ← nat.pred_eq_sub_one] at h,
  refine ne_of_lt (nat.pred_lt _) h,
  intro h', simp at h',
  apply (lt_iff_not_ge _ _).mp (nat.lt_succ_self 1),
  apply le_trans hn h',
end


example (n i : ℕ) (hin : i < n - 2) : i ≠ n - 1 :=
begin
  rw ← not_le at hin,
  intro hi, apply hin,
  rw hi,
  apply nat.sub_le_sub_left, norm_num,
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

  rw normal_closure_of_stabilizer_eq_top G hsn' hG',
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
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
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

    refine jordan0_init G hG _ _,
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
  apply jordan0 G hG hn
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
  refine jordan0' G hG hn
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
  { obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
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
      { obtain ⟨b, htb⟩ := card_eq_one_iff_is_singleton t ht',
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

example (s : set α) (hs : fintype.card s = fintype.card α) : s = ⊤ :=
begin
  have : s  ⊆ ⊤,
  intros x hx,
    rw set.top_eq_univ,
    exact set.mem_univ x,
  have : ∃  s' : finset α, s = s',
  refine set.exists_finite_iff_finset.mp _,
  exact ⟨s, set.finite.of_fintype s, rfl⟩,
  obtain ⟨s', rfl⟩ := this,
  have hs' : s' ≤ ⊤, sorry,
  suffices : s' = ⊤,
  { sorry, },
simp at hs,
  suffices : fintype.card α = (⊤ : finset α).card,
  rw this at hs,
  exact finset.eq_of_subset_of_card_le hs' (nat.le_of_eq hs.symm),
  refl
end

lemma eq_s2_of_nontrivial (hα : fintype.card α = 2) (hG : nontrivial G) :
  G = ⊤ :=
begin
  apply subgroup.eq_top_of_card_eq,
  apply le_antisymm,
  apply fintype.card_subtype_le ,
  rw [fintype.card_equiv (equiv.cast rfl), hα, nat.factorial_two],
  rw ← fintype.one_lt_card_iff_nontrivial at hG,
  exact hG,
end

theorem jordan_perm (hG : is_preprimitive G α)
  {g : equiv.perm α} (h2g : equiv.perm.is_swap g) (hg : g ∈ G) : G = ⊤  :=
begin
  cases nat.lt_or_ge (fintype.card α) 3 with hα3 hα3,
  { -- trivial case : fintype.card α ≤ 2
  sorry },
  suffices : ∃ (n : ℕ), fintype.card α = n + 3,
  obtain ⟨n, hn⟩ := this,

  let s := (g.support : set α),
  have hs2 : fintype.card s = 2,
  { obtain ⟨x, y, hxt, hxt'⟩ := h2g,
    simp only [finset.coe_sort_coe, fintype.card_coe, ← equiv.perm.card_support_swap hxt, hxt'] },
  have hsc : fintype.card (sᶜ : set α) = n.succ,
  { rw [fintype.card_compl_set, hs2, hn],
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one],  },
  apply is_fully_minus_one_pretransitive_iff,
  suffices : is_multiply_preprimitive G α (fintype.card α -1),
  apply this.left,

  suffices : fintype.card α - 1 = 1 + n.succ,
  rw this,
  refine jordan2 G hG _ _ _,
  exact ((g.support)ᶜ : set α),
  exact n,
  { rw ← hsc,
    simp only [fintype.card_of_finset, set.mem_compl_eq], },
  { rw hn,
    conv_lhs { rw add_comm },
    rw [← nat.add_one, add_assoc, add_lt_add_iff_left],
    norm_num },

  { rw ← is_multiply_preprimitive_one_iff,
    apply is_multiply_preprimitive_of_multiply_pretransitive_succ,
    apply le_of_eq,

  change ↑2 = cardinal.mk (sub_mul_action_of_fixing_subgroup G _).carrier,
  rw sub_mul_action_of_fixing_subgroup_def,
  rw ← hs2, simp only [compl_compl, cardinal.mk_fintype],

  let j : mul_action_bihom (fixing_subgroup G sᶜ) (sub_mul_action_of_fixing_subgroup G sᶜ)
    (equiv.perm s) s :=
    sub_mul_action_of_fixing_subgroup_bihom G,

  /-
  let j : mul_action_bihom (equiv.perm s) (s)
    (fixing_subgroup G sᶜ) (sub_mul_action_of_fixing_subgroup G sᶜ) := {
  to_fun := λ x, ⟨x,
  begin
    change ↑x ∈ (sub_mul_action_of_fixing_subgroup G sᶜ).carrier,
    rw sub_mul_action_of_fixing_subgroup_def,
    simp only [compl_compl, finset.mem_coe],
    exact x.prop
  end⟩,
  to_monoid_hom := sorry,
  map_smul' := sorry },
  have hj : function.surjective j.to_fun, sorry,
  -/
  apply is_multiply_pretransitive_via_surjective_bihom hj,
  norm_num, rw ← hs2,
  apply equiv_perm_is_fully_pretransitive },

  { rw hn, rw ← nat.add_one,
    conv_rhs {rw add_comm },
    simp only [nat.add_succ_sub_one] }
end


theorem jordan_alternating (hG : is_preprimitive G α)
  {g : equiv.perm α} (h3g : equiv.perm.is_three_cycle g) (hg : g ∈ G) :
  alternating_group α ≤ G :=
sorry

end Jordan



end finite_groups
