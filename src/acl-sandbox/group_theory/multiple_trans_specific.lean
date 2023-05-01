

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

open_locale pointwise classical

section ad_group_actions_defs

open mul_action

variables {G α : Type*} [group G] [mul_action G α]

lemma is_pretransitive.mk_base (a : α) (h : ∀ (x : α), ∃ (g : G), g • a = x) :
  is_pretransitive G α :=
begin
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨g, hg⟩ := h x,
  obtain ⟨k, hk⟩ := h y,
  use k * g⁻¹,
  rw [← smul_smul, ← hg, ← hk, inv_smul_smul],
end
/-
lemma smul_set_card_eq [fintype α] [decidable_eq α] (g : G) (s : set α) :
  fintype.card (g • s) = fintype.card s :=
begin
  change fintype.card ((λ x, g • x) '' s) = _,

  sorry
end -/

end ad_group_actions_defs

section finite_groups

open mul_action
open_locale classical

variables {α : Type*} [fintype α] [decidable_eq α]

variable (α)
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

variable {α}
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

lemma is_fully_minus_one_pretransitive_iff {G : subgroup (equiv.perm α)}
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

variable (α)
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
  let heq := (equiv_perm_is_fully_pretransitive α).exists_smul_eq,
  obtain ⟨g, hg⟩ := heq x' y',
  cases int.units_eq_one_or g.sign with h h,
  { use ⟨g, equiv.perm.mem_alternating_group.mpr h⟩,
    ext i,
    simp only [function.embedding.smul_apply],
    rw [← hx', ← hy', ← hg],
    refl },
--  swap, -- exact _inst_2,
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
    simpa [quotient_group.eq', inv_one, one_mul] using h1k },

  intros k g hk,
  split,
  { intro hg',
    have : quotient_group.mk (k * g)  ∈ ({ quotient_group.mk 1, quotient_group.mk k } : set (G ⧸H)),
        rw [quot2k _ hk, set.top_eq_univ], apply set.mem_univ,
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at this,
    cases this with this this,
    { rw [eq_comm, quotient_group.eq', inv_one, one_mul] at this, exact this },
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

variable {α}
lemma alternating_group_of_subsingleton (hα : subsingleton α) :
  alternating_group α = (⊥ : subgroup (equiv.perm α)) :=
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

variable (α)
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

variable {α}
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


example (a b : ℕ) (h : a = b) : 2 * a = 2 * b :=
begin
  exact congr_arg (has_mul.mul 2) h,
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

/-
-- Preuve très maladroite
-- Il vaudrait mieux prouver la divisibilité de Wielandt, 9.3
-- On verrait tout de suite que #G est multiple de n!/2,
-- donc l'indice de G est au plus 2.
lemma contains_alternating_iff_is_all_minus_two_pretransitive'
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
 -/

lemma is_full_minus_two_pretransitive_iff
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

variables {G : Type*} [group G] [mul_action G α]
-- variable (G : subgroup (equiv.perm α))

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

  rw normal_closure_of_stabilizer_eq_top hsn' hG',
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

open_locale pointwise


lemma is_pretransitive_of_fixing_subgroup_inter {G : Type*} [group G] [mul_action G α]
  {s : set α}
  (hs : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s))
  {g : G} {a : α} (ha : a ∉ s ∪ (g • s)) :
  is_pretransitive (fixing_subgroup G (s ∩ (g • s)))
    (sub_mul_action_of_fixing_subgroup G (s ∩ g • s)) :=
begin
  have ha' : a ∉ s ∩ (g • s),
  { intro ha', apply ha,
    apply set.mem_union_left,
    exact set.mem_of_mem_inter_left ha' },
  apply is_pretransitive.mk_base (⟨a, ha'⟩ : sub_mul_action_of_fixing_subgroup G (s ∩ (g • s))),
  let hs_trans_eq := hs.exists_smul_eq,
  rintros ⟨x, hx⟩,
  rw mem_sub_mul_action_of_fixing_subgroup_iff at hx,
  rw [set.mem_inter_iff, not_and_distrib] at hx,
  cases hx with hx hx,
  { -- x ∉ s
  obtain ⟨⟨k, hk⟩, hkax⟩ := hs_trans_eq ⟨a, _⟩ ⟨x, hx⟩,
  use k,
  { rintro ⟨z, hz⟩,
    simp only [subtype.coe_mk],
    simp only [← set_like.coe_eq_coe, subtype.coe_mk] at hkax,
    rw mem_fixing_subgroup_iff at hk,
    rw hk,
    apply set.mem_of_mem_inter_left hz },
  { simp only [← set_like.coe_eq_coe] at hkax ⊢,
    simp only [sub_mul_action.coe_smul_of_tower, sub_mul_action.coe_mk, subtype.coe_mk] at hkax ⊢,
    exact hkax },
  { intro ha', apply ha,
    apply set.mem_union_left,
    exact ha' } },
  { -- x ∉ g • s
  obtain ⟨⟨k, hk⟩, hkax⟩ := hs_trans_eq ⟨g⁻¹ • a, _⟩ ⟨g⁻¹ • x, _⟩,
  use g * k * g⁻¹,
  { rintro ⟨z, hz⟩,
    simp only [subtype.coe_mk],
    simp only [← set_like.coe_eq_coe, subtype.coe_mk] at hkax,
    simp only [← smul_smul],
    rw smul_eq_iff_eq_inv_smul,
    rw mem_fixing_subgroup_iff at hk,
    rw hk,
    rw ← mem_smul_set_iff_inv_smul_mem,
    apply set.mem_of_mem_inter_right hz },
  { simp only [← set_like.coe_eq_coe] at hkax ⊢,
    simp only [sub_mul_action.coe_smul_of_tower, sub_mul_action.coe_mk, subtype.coe_mk] at hkax ⊢,
    change k • g⁻¹ • a = g⁻¹ • x at hkax,
    change (g * k * g⁻¹) • a = x,
    rw ← smul_eq_iff_eq_inv_smul at hkax,
    simp only [← smul_smul],
    exact hkax },
  { rw mem_sub_mul_action_of_fixing_subgroup_iff,
    rw ← mem_smul_set_iff_inv_smul_mem,
    intro h, apply ha, apply set.mem_union_right, exact h },
  { rw mem_sub_mul_action_of_fixing_subgroup_iff,
    intro h, apply hx,
    rw mem_smul_set_iff_inv_smul_mem,
    exact h } }
end

lemma smul_set_card_eq {G : Type*} [group G] [mul_action G α]
  (g : G) (s : set α) :
  fintype.card (g • s : set α) = fintype.card s :=
begin
  conv_lhs { simp only [fintype.card_of_finset] },
  conv_rhs { simp only [← set.to_finset_card] },
  apply finset.card_image_of_injective,
  exact mul_action.injective g,
end

lemma is_preprimitive_of_fixing_subgroup_inter {G : Type*} [group G] [mul_action G α]
  {s : set α}
  (hs : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s))
  {g : G} {a : α} (ha : a ∉ s ∪ (g • s)) :
  is_preprimitive (fixing_subgroup G (s ∩ (g • s)))
    (sub_mul_action_of_fixing_subgroup G (s ∩ g • s)) :=
begin
  have : fixing_subgroup G s ≤ fixing_subgroup G (s ∩ g • s),
  { apply fixing_subgroup_antitone, apply set.inter_subset_left, },
  let t := s ∩ g • s,
  have hts : t ≤ s := set.inter_subset_left s _,
  let j : mul_action_bihom
    (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)
    (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t) := {
  to_fun := λ ⟨x, hx⟩, ⟨x, λ h, hx (hts h)⟩,
  to_monoid_hom := subgroup.inclusion (fixing_subgroup_antitone _ _ hts),
  map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩, rfl },
  have hj : function.injective j.to_fun,
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
    rw ← set_like.coe_eq_coe at hxy ⊢,
    simp only [set_like.coe_mk],
    exact hxy },
  apply is_primitive_of_bihom' (fixing_subgroup G (s ∩ (g • s)))
    (sub_mul_action_of_fixing_subgroup G (s ∩ g • s))
    (is_pretransitive_of_fixing_subgroup_inter hs.to_is_pretransitive ha) hs hj,
  { change _ > fintype.card (sub_mul_action_of_fixing_subgroup G (s ∩ g • s)).carrier,
    simp only [← set.to_finset_card],
    rw sub_mul_action_of_fixing_subgroup_def,
    rw [set.to_finset_compl, set.to_finset_inter, finset.compl_inter],
    rw gt_iff_lt,
    apply nat.lt_of_add_lt_add_right,
    rw finset.card_union_add_card_inter,

    suffices : (g • s).to_finsetᶜ.card = s.to_finsetᶜ.card,
    rw [this, ← two_mul],
    rw nat.lt_iff_add_one_le,
    apply nat.add_le_add,
    { apply le_of_eq,
      refine congr_arg _ _,
      rw ← set.to_finset_compl,
      simp only [set.to_finset_card],
      rw set.card_range_of_injective,
      change fintype.card (sᶜ : set α) = fintype.card (sub_mul_action_of_fixing_subgroup G s).carrier,
      rw sub_mul_action_of_fixing_subgroup_def,
      simp only [fintype.card_of_finset, set.mem_compl_eq],
      exact hj },
    { rw nat.succ_le_iff ,
      simp only [← set.to_finset_compl, ← set.to_finset_inter,
      ← set.compl_union],
      rw set.to_finset_card, --  (sᶜ ∩ (g • s)ᶜ),
      rw fintype.card_pos_iff ,
      use a },
    { simp only [finset.card_compl, set.to_finset_card],
      rw smul_set_card_eq, } },
end

example {s t : set α} (h : t ≤ s) : set s :=
begin
exact {x : ↥s | ↑x ∈ t}
end

example {G : Type*} [group G] {H K : subgroup G} (h : H ≤ K) : subgroup K :=
begin

  refine subgroup.subgroup_of H K,

end

-- α = Ω, s = Δ, α \ s = Γ
-- 1 ≤ #Δ < #Ω, 1 < #Γ < #Ω
--
theorem strong_jordan_of_pretransitive {n : ℕ} :
  ∀ {α : Type*} [decidable_eq α] [fintype α]
    -- {G : subgroup (equiv.perm α)},
    {G : Type*} [group G] [by exactI mul_action G α],
  by exactI ∀ (hG : is_preprimitive G α)
    {s : set α} (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)),
  is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 :=
sorry


lemma aux_pigeonhole {s t : set α} (h : fintype.card s + fintype.card t > fintype.card α) :
  (s ∩ t).nonempty :=
begin
  simp only [← set.to_finset_card] at h,
  rw ← set.ne_empty_iff_nonempty,
  intro hst,
  rw [← set.to_finset_inj, set.to_finset_inter, set.to_finset_empty, ← finset.not_nonempty_iff_eq_empty] at hst,
  apply hst,
  rw [← finset.card_compl_lt_iff_nonempty, finset.compl_inter],
  apply lt_of_le_of_lt (finset.card_union_le _ _),
  apply nat.lt_of_add_lt_add_left,
  rw ← add_assoc,
  simp only [finset.card_compl],
  rw nat.add_sub_of_le (finset.card_le_univ s.to_finset),
  conv_rhs { rw add_comm },
  apply nat.add_lt_add_left,
  apply nat.lt_of_add_lt_add_left,
  rw nat.add_sub_of_le (finset.card_le_univ t.to_finset),
  rw add_comm,
  exact h
end

/-
have : ((s.to_finset)ᶜ ∩ (g • s.to_finset)ᶜ).nonempty,
    { rw ← finset.card_compl_lt_iff_nonempty,
      simp only [finset.compl_inter, compl_compl],
      apply lt_of_le_of_lt (finset.card_union_le _ _),
      rw set.to_finset_card,
      suffices : (g • s.to_finset).card = fintype.card s,
      rw [this, hsn, ← two_mul],
      exact hn1,
      change (finset.image (λ x, g • x) s.to_finset).card = _,
      rw finset.card_image_of_injective _ (mul_action.injective g),
      rw set.to_finset_card },

end
 -/

theorem weak_jordan_of_pretransitive {n : ℕ} :
  ∀ {α : Type*} [decidable_eq α] [fintype α]
    -- {G : subgroup (equiv.perm α)},
    {G : Type*} [group G] [by exactI mul_action G α],
  by exactI ∀ (hG : is_preprimitive G α)
    {s : set α} (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)),
  is_multiply_pretransitive G α 2 :=
begin
  induction n using nat.strong_induction_on with n hrec,
  introsI α _ _ G _ _ hG s hsn hsn' hs_trans,

  let hs_trans_eq := hs_trans.exists_smul_eq,
  have hs_ne_top : s ≠ ⊤,
  { intro hs,
    rw [set.top_eq_univ, ← set_fintype_card_eq_univ_iff, hsn] at hs,
    rw hs at hsn',
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using hsn' },
  have hs_nonempty : s.nonempty,
  { rw ← set.nonempty_coe_sort , rw ← not_is_empty_iff ,
    intro hs,
    rw ← fintype.card_eq_zero_iff at hs,
    rw hs at hsn,
    simpa only using hsn },

  cases nat.lt_or_ge n.succ 2 with hn hn,
  { -- Initialization : n = 0
    have hn : n = 0,
    { rw ← nat.le_zero_iff,
      apply nat.le_of_succ_le_succ ,
      apply nat.le_of_lt_succ,
      exact hn },
    rw hn at *,
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq,

    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,

    rw stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive,

    rw ← is_pretransitive_iff_is_one_pretransitive,
      -- is_pretransitive (stabilizer G a) (sub_mul_action_of_stabilizer G α a),
    exact is_pretransitive_of_bihom
      (sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective G a).surjective
      hs_trans,

/-     suffices : fixing_subgroup G ({a} : set α) = stabilizer G a,
    rw this,
 -/
  /-   refine jordan0_init hG _ _,
    apply lt_of_eq_of_lt _ hsn', norm_num,
    rw is_pretransitive_iff_is_one_pretransitive,
    exact (stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive).mp hG',

    { -- stabilizer G a = fixing_subgroup G ({a} : set α),
      ext g,  split,
      intro hg, exact (mem_fixing_subgroup_iff G).mp hg a (set.mem_singleton a) ,
      intro hg, rw mem_fixing_subgroup_iff, intros x hx,
        rw (set.mem_singleton_iff.mp hx), exact hg } -/

    },

  -- Induction step : n ≥ 1

  cases nat.lt_or_ge (2 * n.succ) (fintype.card α) with hn1 hn2,
  { -- hn : 2 * s.card < fintype.card α

    -- get a, b ∈ s, a ≠ b
    obtain ⟨⟨a, ha : a ∈ s⟩, ⟨b, hb : b ∈ s⟩, hab⟩ :=
      fintype.one_lt_card_iff_nontrivial.mp (nat.succ_le_iff.mp (by { rw hsn, exact hn })),
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ :=
      @rudio G α _ _ hG s (set.finite.of_fintype s) hs_nonempty hs_ne_top a b hab,

    have : ((s.to_finset)ᶜ ∩ (g • s.to_finset)ᶜ).nonempty,
    { rw ← finset.card_compl_lt_iff_nonempty,
      simp only [finset.compl_inter, compl_compl],
      apply lt_of_le_of_lt (finset.card_union_le _ _),
      rw set.to_finset_card,
      suffices : (g • s.to_finset).card = fintype.card s,
      rw [this, hsn, ← two_mul],
      exact hn1,
      change (finset.image (λ x, g • x) s.to_finset).card = _,
      rw finset.card_image_of_injective _ (mul_action.injective g),
      rw set.to_finset_card },
    obtain ⟨c, hc⟩ := this.bex,
    simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset] at hc,
    let hcs := hc.left,
    have hcgs : g⁻¹ • c ∉ s,
    { intro h,
    -- rintro ⟨c', hc'⟩, apply hc.right,
      rw ← set.mem_to_finset at h,
      apply hc.right,
      rw finset.mem_smul_finset,
      use g⁻¹ • c, apply and.intro h,
      simp only [smul_inv_smul] },

    -- have : tᶜ = sᶜ ∪ (g • sᶜ) ≠ ∅
    -- let H := subgroup.closure ((fixing_subgroup G s).carrier ∪ (fixing_subgroup G (g • s)).carrier),
    -- H ≤ fixing_subgroup G t
    -- -- have : is_pretransitive H tᶜ
    -- have : is_pretransitive (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t),

    let t := s ∩ (g • s),

    have hct : c ∉ t, { intro h, apply hcs, apply set.mem_of_mem_inter_left h },
    have hct' : c ∉ s ∪ (g • s),
    { intro h, rw set.mem_union at h, cases h with h h,
      exact hc.left h,
      apply hcgs, rw ← mem_smul_set_iff_inv_smul_mem, exact h },
    let ht_trans : is_pretransitive (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t) :=
      is_pretransitive_of_fixing_subgroup_inter hs_trans hct',


    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { suffices : fintype.card t ≠ 0,
      obtain ⟨m, hm⟩ := nat.exists_eq_succ_of_ne_zero this,
      use m, apply and.intro hm,
      rw ← nat.succ_lt_succ_iff, rw ← hm, rw ← hsn,
      apply set.card_lt_card,
      split,
      rw set.le_eq_subset, apply set.inter_subset_left,
      intro hst, apply hgb, apply set.inter_subset_right s,
      apply hst, exact hb,

      intro ht,
      rw fintype.card_eq_zero_iff at ht,
      apply ht.false,
      use ⟨a, ha, hga⟩ },
    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec : is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    exact hrec m hmn hG (by
      { rw ← htm, simp only [fintype.card_of_finset],
        simp only [set.mem_inter_eq, finset.filter_congr_decidable],
        apply congr_arg,
        rw ← finset.filter_filter ,
        apply congr_arg,
        simp_rw ← set.mem_to_finset ,
        rw finset.filter_mem_eq_inter,
        rw finset.univ_inter  })
      htm' ht_trans,

     },
  { -- 2 * s.card ≥ fintype.card α

    have : nontrivial (sᶜ : set α),
    { rw ← fintype.one_lt_card_iff_nontrivial,
      rw ← set.to_finset_card ,
      rw set.to_finset_compl,
      rw finset.card_compl ,
      rw lt_tsub_iff_right ,
      rw [set.to_finset_card , hsn], exact hsn' },
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨⟨a, ha : a ∈ sᶜ⟩, ⟨b, hb : b ∈ sᶜ⟩, hab⟩ := this,
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    have hsc_ne : sᶜ.nonempty := set.nonempty_of_mem ha,
    have hsc_ne_top : sᶜ ≠ ⊤,
    { intro h,
      simp only [set.top_eq_univ, set.compl_univ_iff] at h,
      simpa only [h, set.not_nonempty_empty] using hs_nonempty },

    -- apply rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ :=
      @rudio G α _ _ hG sᶜ (set.finite.of_fintype sᶜ) hsc_ne hsc_ne_top a b hab,

    let t := s ∩ (g • s),
    have hbt : b ∉ t,
    { intro h, rw set.mem_compl_iff at hb, apply hb,
      apply set.mem_of_mem_inter_left h },
    have hat' : a ∉ s ∪ g • s,
    { intro h, rw set.mem_union at h,
      cases h with h h,
      rw set.mem_compl_iff at ha, exact ha h,
      rw mem_smul_set_iff_inv_smul_mem at hga h,
      rw set.mem_compl_iff at hga, exact hga h },
    let ht_trans : is_pretransitive (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t) :=
      is_pretransitive_of_fixing_subgroup_inter hs_trans hat',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { -- suffices : fintype.card t ≠ 0,
      suffices : t.nonempty,
      { rw [← set.nonempty_coe_sort,  ← fintype.card_pos_iff] at this,
        use (fintype.card t).pred,
        rw ← nat.succ_lt_succ_iff,
        rw nat.succ_pred_eq_of_pos this,
        rw ← hsn,
        apply and.intro rfl,
        apply set.card_lt_card,
        split,
        rw set.le_eq_subset, apply set.inter_subset_left,
        intro hst,
        rw set.mem_compl_iff at hb,
        simp only [set.smul_compl_set, set.mem_compl_eq, set.not_not_mem] at hgb,
        suffices : s = g • s,
        { apply hb, rw this, exact hgb },
        apply set.eq_of_subset_of_card_le,
        { rw [set.le_eq_subset] at hst,
          refine subset_trans hst _,
          apply set.inter_subset_right },
        { apply le_of_eq,
          apply smul_set_card_eq }  },

      { -- aux_pigeonhole ne marche pas !
        rw ← set.ne_empty_iff_nonempty,
        intro h,
        rw [← set.to_finset_inj, set.to_finset_inter, set.to_finset_empty,
          ← finset.not_nonempty_iff_eq_empty] at h,
        apply h,
        rw [← finset.card_compl_lt_iff_nonempty, finset.compl_inter],
        apply nat.lt_of_add_lt_add_right,
        rw finset.card_union_add_card_inter,
        apply nat.lt_of_add_lt_add_left,
        rw ← add_assoc,
        simp only [finset.card_compl],
        rw nat.add_sub_of_le (finset.card_le_univ s.to_finset),

        conv_rhs { rw add_comm, rw add_assoc },
        apply nat.add_lt_add_left,
        apply nat.lt_of_add_lt_add_left,
        rw nat.add_sub_of_le (finset.card_le_univ (g • s).to_finset),
        rw add_comm,
        suffices : (g • s).to_finset.card = s.to_finset.card,
        { rw this, conv_rhs { rw add_assoc },
          rw [← two_mul, set.to_finset_card, hsn],
          rw ← nat.one_add_le_iff,
          apply nat.add_le_add _ hn2,
          rw nat.succ_le_iff,
          rw finset.card_pos,
          use a,
          simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset],
          rw [← not_or_distrib, ← set.mem_union],
          exact hat' },
        { conv_lhs { simp only [set.to_finset_card, fintype.card_of_finset] },
          rw finset.card_image_of_injective _ (mul_action.injective g) } } },

    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec : is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    exact hrec m hmn hG
      (by { rw ← htm, simp only [fintype.card_of_finset],
            simp only [set.mem_inter_eq, finset.filter_congr_decidable],
            apply congr_arg,
            rw ← finset.filter_filter ,
            apply congr_arg,
            simp_rw ← set.mem_to_finset ,
            rw finset.filter_mem_eq_inter,
            rw finset.univ_inter  })
      htm'
      ht_trans }
end

example {s t : set α} (h : fintype.card s = fintype.card t) (h' : s ⊆ t) : s = t :=
begin
  apply set.eq_of_subset_of_card_le h',
  apply le_of_eq h.symm,
end

example {s : set α} {g : G} : g • (s.to_finset) = (g • s).to_finset :=
begin
  ext a,
  rw set.mem_to_finset,
  change a ∈ finset.image (λ x, g • x) s.to_finset ↔ a ∈ (λ x, g • x) '' s,
  generalize :  (λ x, g • x) = f,
  simp only [finset.mem_image, set.mem_to_finset, exists_prop, set.mem_image],
end

example {s : set α} {f : α → α} : fintype.card (f '' s) ≤ fintype.card s :=
begin
  rw ← set.coe_to_finset s,
  simp_rw ← finset.coe_image ,
  rw set.coe_to_finset s,
  simp only [← set.to_finset_card],

  have : ∀ (t : finset α), (t : set α).to_finset = t,
  { intro t,
ext a, simp,
    },
  rw this,
  exact finset.card_image_le,
end

example {f : α → α} {s : finset α} : (s.image f).card ≤ s.card :=
begin
  let h := (s.1.map f).to_finset_card_le,
exact finset.card_image_le,
end


example {α β : Type*} [fintype α] [fintype β] {f : α → β} {s : set α} :
  (f '' s).to_finset = finset.image f s.to_finset :=
begin
  ext b,
  simp only [set.mem_to_finset, set.mem_image, finset.mem_image, exists_prop],
end


lemma test {s : set α} {g : G} : let t := s ∩ (g • s) in
  subgroup.normal_closure (fixing_subgroup G t).carrier
  ≤ subgroup.normal_closure (fixing_subgroup G s).carrier :=
begin
/-   { apply subgroup.normal_closure_mono,
    intros k hk,
    simp only [subgroup.mem_carrier] at hk ⊢,
    rintro ⟨x, hx⟩,
    simp only [subtype.coe_mk],
    rw mem_fixing_subgroup_iff at hk,
    refine hk x (set.mem_of_mem_inter_left hx) },
 -/
 { refine subgroup.normal_closure_le_normal _,
    apply set.subset.trans _ (subgroup.conjugates_of_set_subset_normal_closure),
    intros k hk,
    simp only [subgroup.mem_carrier, mem_fixing_subgroup_iff] at hk,

  sorry }
end


example (s t : set α) :
  finset.filter (λ (x : α), x ∈ s ∧ x ∈ t) finset.univ = finset.filter t s.to_finset :=
begin
rw ← finset.filter_filter ,
apply congr_arg,
simp_rw ← set.mem_to_finset ,
rw finset.filter_mem_eq_inter,
rw finset.univ_inter
end


/-
theorem jordan0_old {n : ℕ} :
  ∀ {α : Type*} [decidable_eq α] [fintype α]
    -- {G : subgroup (equiv.perm α)},
    {G : Type*} [group G] [by exactI mul_action G α],
  by exactI ∀ (hG : is_preprimitive G α)
    {s : set α} (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)),
  is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 :=
begin
  induction n with n hrec,
  -- Initialization : n = 0
  { -- s = {a}
    intros α _ _ G _ _ hG s hsn hsn' hs_trans,
    resetI,
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq,

    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,

    have hG' : is_multiply_pretransitive G α 2,

      rw stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive,

      rw ← is_pretransitive_iff_is_one_pretransitive,
      -- is_pretransitive (stabilizer G a) (sub_mul_action_of_stabilizer G α a),
      refine is_pretransitive_of_bihom
        (sub_mul_action_of_fixing_subgroup_of_singleton_bihom G a)
        (function.bijective.surjective
          (sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective G a))
        hs_trans,


    suffices : fixing_subgroup G ({a} : set α) = stabilizer G a,
    rw this,

    refine jordan0_init hG _ _,
    apply lt_of_eq_of_lt _ hsn', norm_num,
    rw is_pretransitive_iff_is_one_pretransitive,
    exact (stabilizer.is_multiply_pretransitive G α hG.to_is_pretransitive).mp hG',

    { -- stabilizer G a = fixing_subgroup G ({a} : set α),
      ext g,  split,
      intro hg, exact (mem_fixing_subgroup_iff G).mp hg a (set.mem_singleton a) ,
      intro hg, rw mem_fixing_subgroup_iff, intros x hx,
        rw (set.mem_singleton_iff.mp hx), exact hg } },
{ -- Induction step
  intros α _ _ G _ _ hG s hsn hsn' hs_trans,
  resetI,

  suffices : s.to_finset.nonempty,
--  rw ← finset.nonempty.to_set at this,
  obtain ⟨a, has⟩ := finset.nonempty.bex this,
  simp only [set.mem_to_finset] at has,
  let t : set (sub_mul_action_of_stabilizer G α a) := coe ⁻¹' ((s.to_finset.erase a) : set α),
  have hat : (coe '' t : set α) = s.to_finset.erase a,
  { simp only [subtype.image_preimage_coe, finset.coe_erase, set_like.mem_coe,
    set.inter_eq_left_iff_subset, set.diff_singleton_subset_iff],
    simp_rw mem_sub_mul_action_of_stabilizer_iff,
    intros x _,
    simp only [set.mem_insert_iff],
    cases em (x = a) with hx hx,
    apply or.intro_left, exact hx,
    apply or.intro_right, exact hx },
  have hast : s = insert a (coe '' t),
  { rw hat,
    simp only [finset.coe_erase, set.coe_to_finset, set.insert_diff_singleton],
    rw set.insert_eq_of_mem has },

  -- suffices : is_multiply_pretransitive ↥(subgroup.normal_closure
  -- (fixing_subgroup (stabilizer G a) t).carrier) α 2,

  let k1 := sub_mul_action_of_fixing_subgroup_eq_bihom G hast.symm,
  let hk1 := sub_mul_action_of_fixing_subgroup_eq_bihom_bijective G hast.symm,

  let k2 := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom G a t,
  let hk2 := sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective G a t,

  -- let k3 := bihom_of_comap k2 (subgroup.normal_closure (fixing_subgroup G s).carrier),


  -- let hk := function.bijective.surjective (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective G a t),
  -- apply is_multiply_pretransitive_via_surjective_bihom hk,

  /-
  rw (subgroup'_is_multiply_pretransitive_via_bijective_bihom_iff
    (function.bijective.surjective (sub_mul_action_of_fixing_subgroup_of_stabilizer_bijective _ _ _))
    (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective _ _ _),
 -/
    sorry,

  { -- s.to_finset.nonempty
    rw ← finset.card_pos , rw set.to_finset_card, rw hsn, apply nat.succ_pos },
},
end
 -/

theorem strong_jordan_of_preprimitive (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 := sorry

theorem weak_jordan_of_preprimitive {n : ℕ} :
  ∀ {α : Type*} [decidable_eq α] [fintype α]
    {G : Type*} [group G] [by exactI mul_action G α],
  by exactI ∀ (hG : is_preprimitive G α)
    {s : set α} (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)),
  is_multiply_preprimitive G α 2 :=
 begin
  induction n using nat.strong_induction_on with n hrec,
  introsI α _ _ G _ _ hG s hsn hsn' hs_prim,

  let hs_trans_eq := hs_prim.to_is_pretransitive.exists_smul_eq,
  have hs_ne_top : s ≠ ⊤,
  { intro hs,
    rw [set.top_eq_univ, ← set_fintype_card_eq_univ_iff, hsn] at hs,
    rw hs at hsn',
    simpa only [add_lt_iff_neg_right, not_lt_zero'] using hsn' },
  have hs_nonempty : s.nonempty,
  { rw ← set.nonempty_coe_sort , rw ← not_is_empty_iff ,
    intro hs,
    rw ← fintype.card_eq_zero_iff at hs,
    rw hs at hsn,
    simpa only using hsn },

  cases nat.lt_or_ge n.succ 2 with hn hn,
  { -- Initialization : n = 0
    have hn : n = 0,
    { rw ← nat.le_zero_iff,
      apply nat.le_of_succ_le_succ ,
      apply nat.le_of_lt_succ,
      exact hn },
    rw hn at *,
    let hG_eq := hG.to_is_pretransitive.exists_smul_eq,

    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,

    rw is_multiply_preprimitive_of_stabilizer G α (by norm_num) hG.to_is_pretransitive,

    rw is_multiply_preprimitive_one_iff,

    refine is_preprimitive_via_surjective_bihom
      (function.bijective.surjective
        (sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective G a))
      hs_prim },

  -- Induction step : n ≥ 1

  cases nat.lt_or_ge (2 * n.succ) (fintype.card α) with hn1 hn2,
  { -- hn : 2 * s.card < fintype.card α

    -- get a, b ∈ s, a ≠ b
    obtain ⟨⟨a, ha : a ∈ s⟩, ⟨b, hb : b ∈ s⟩, hab⟩ :=
      fintype.one_lt_card_iff_nontrivial.mp (nat.succ_le_iff.mp (by { rw hsn, exact hn })),
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ :=
      @rudio G α _ _ hG s (set.finite.of_fintype s) hs_nonempty hs_ne_top a b hab,

    have : ((s.to_finset)ᶜ ∩ (g • s.to_finset)ᶜ).nonempty,
    { rw ← finset.card_compl_lt_iff_nonempty,
      simp only [finset.compl_inter, compl_compl],
      apply lt_of_le_of_lt (finset.card_union_le _ _),
      rw set.to_finset_card,
      suffices : (g • s.to_finset).card = fintype.card s,
      rw [this, hsn, ← two_mul],
      exact hn1,
      change (finset.image (λ x, g • x) s.to_finset).card = _,
      rw finset.card_image_of_injective _ (mul_action.injective g),
      rw set.to_finset_card },
    obtain ⟨c, hc⟩ := this.bex,
    simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset] at hc,
    let hcs := hc.left,
    have hcgs : g⁻¹ • c ∉ s,
    { intro h,
    -- rintro ⟨c', hc'⟩, apply hc.right,
      rw ← set.mem_to_finset at h,
      apply hc.right,
      rw finset.mem_smul_finset,
      use g⁻¹ • c, apply and.intro h,
      simp only [smul_inv_smul] },

    -- have : tᶜ = sᶜ ∪ (g • sᶜ) ≠ ∅
    -- let H := subgroup.closure ((fixing_subgroup G s).carrier ∪ (fixing_subgroup G (g • s)).carrier),
    -- H ≤ fixing_subgroup G t
    -- -- have : is_pretransitive H tᶜ
    -- have : is_pretransitive (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t),

    let t := s ∩ (g • s),

    have hct : c ∉ t, { intro h, apply hcs, apply set.mem_of_mem_inter_left h },
    have hct' : c ∉ s ∪ (g • s),
    { intro h, rw set.mem_union at h, cases h with h h,
      exact hc.left h,
      apply hcgs, rw ← mem_smul_set_iff_inv_smul_mem, exact h },
    let ht_prim : is_preprimitive (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t) :=
      is_preprimitive_of_fixing_subgroup_inter hs_prim hct',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { suffices : fintype.card t ≠ 0,
      obtain ⟨m, hm⟩ := nat.exists_eq_succ_of_ne_zero this,
      use m, apply and.intro hm,
      rw ← nat.succ_lt_succ_iff, rw ← hm, rw ← hsn,
      apply set.card_lt_card,
      split,
      rw set.le_eq_subset, apply set.inter_subset_left,
      intro hst, apply hgb, apply set.inter_subset_right s,
      apply hst, exact hb,

      intro ht,
      rw fintype.card_eq_zero_iff at ht,
      apply ht.false,
      use ⟨a, ha, hga⟩ },
    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec : is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    exact hrec m hmn hG (by
      { rw ← htm, simp only [fintype.card_of_finset],
        simp only [set.mem_inter_eq, finset.filter_congr_decidable],
        apply congr_arg,
        rw ← finset.filter_filter ,
        apply congr_arg,
        simp_rw ← set.mem_to_finset ,
        rw finset.filter_mem_eq_inter,
        rw finset.univ_inter  })
      htm' ht_prim,

     },
  { -- 2 * s.card ≥ fintype.card α

    have : nontrivial (sᶜ : set α),
    { rw ← fintype.one_lt_card_iff_nontrivial,
      rw ← set.to_finset_card ,
      rw set.to_finset_compl,
      rw finset.card_compl ,
      rw lt_tsub_iff_right ,
      rw [set.to_finset_card , hsn], exact hsn' },
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨⟨a, ha : a ∈ sᶜ⟩, ⟨b, hb : b ∈ sᶜ⟩, hab⟩ := this,
    simp only [ne.def, subtype.mk_eq_mk] at hab,

    have hsc_ne : sᶜ.nonempty := set.nonempty_of_mem ha,
    have hsc_ne_top : sᶜ ≠ ⊤,
    { intro h,
      simp only [set.top_eq_univ, set.compl_univ_iff] at h,
      simpa only [h, set.not_nonempty_empty] using hs_nonempty },

    -- apply rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ :=
      @rudio G α _ _ hG sᶜ (set.finite.of_fintype sᶜ) hsc_ne hsc_ne_top a b hab,

    let t := s ∩ (g • s),
    have hat' : a ∉ s ∪ g • s,
    { intro h, rw set.mem_union at h,
      cases h with h h,
      rw set.mem_compl_iff at ha, exact ha h,
      rw mem_smul_set_iff_inv_smul_mem at hga h,
      rw set.mem_compl_iff at hga, exact hga h },
    let ht_prim : is_preprimitive (fixing_subgroup G t) (sub_mul_action_of_fixing_subgroup G t) :=
      is_preprimitive_of_fixing_subgroup_inter hs_prim hat',

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ fintype.card t < fintype.card s
    have : ∃ (m : ℕ), fintype.card t = m.succ ∧ m < n,
    { -- suffices : fintype.card t ≠ 0,
      suffices : t.nonempty,
      { rw [← set.nonempty_coe_sort,  ← fintype.card_pos_iff] at this,
        use (fintype.card t).pred,
        rw ← nat.succ_lt_succ_iff,
        rw nat.succ_pred_eq_of_pos this,
        rw ← hsn,
        apply and.intro rfl,
        apply set.card_lt_card,
        split,
        rw set.le_eq_subset, apply set.inter_subset_left,
        intro hst,
        rw set.mem_compl_iff at hb,
        simp only [set.smul_compl_set, set.mem_compl_eq, set.not_not_mem] at hgb,
        suffices : s = g • s,
        { apply hb, rw this, exact hgb },
        apply set.eq_of_subset_of_card_le,
        { rw [set.le_eq_subset] at hst,
          refine subset_trans hst _,
          apply set.inter_subset_right },
        { apply le_of_eq,
          apply smul_set_card_eq }  },

      { -- aux_pigeonhole ne marche pas !
        rw ← set.ne_empty_iff_nonempty,
        intro h,
        rw [← set.to_finset_inj, set.to_finset_inter, set.to_finset_empty,
          ← finset.not_nonempty_iff_eq_empty] at h,
        apply h,
        rw [← finset.card_compl_lt_iff_nonempty, finset.compl_inter],
        apply nat.lt_of_add_lt_add_right,
        rw finset.card_union_add_card_inter,
        apply nat.lt_of_add_lt_add_left,
        rw ← add_assoc,
        simp only [finset.card_compl],
        rw nat.add_sub_of_le (finset.card_le_univ s.to_finset),

        conv_rhs { rw add_comm, rw add_assoc },
        apply nat.add_lt_add_left,
        apply nat.lt_of_add_lt_add_left,
        rw nat.add_sub_of_le (finset.card_le_univ (g • s).to_finset),
        rw add_comm,
        suffices : (g • s).to_finset.card = s.to_finset.card,
        { rw this, conv_rhs { rw add_assoc },
          rw [← two_mul, set.to_finset_card, hsn],
          rw ← nat.one_add_le_iff,
          apply nat.add_le_add _ hn2,
          rw nat.succ_le_iff,
          rw finset.card_pos,
          use a,
          simp only [finset.mem_inter, finset.mem_compl, set.mem_to_finset],
          rw [← not_or_distrib, ← set.mem_union],
          exact hat' },
        { conv_lhs { simp only [set.to_finset_card, fintype.card_of_finset] },
          rw finset.card_image_of_injective _ (mul_action.injective g) } } },

    obtain ⟨m, htm, hmn⟩ := this,

    have htm' : 1 + m.succ < fintype.card α,
    { apply lt_trans _ hsn',
      simp only [add_lt_add_iff_left],
      rw nat.succ_lt_succ_iff,
      exact hmn },

    -- apply hrec : is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup t).carrier) α 2
    exact hrec m hmn hG
      (by { rw ← htm, simp only [fintype.card_of_finset],
            simp only [set.mem_inter_eq, finset.filter_congr_decidable],
            apply congr_arg,
            rw ← finset.filter_filter ,
            apply congr_arg,
            simp_rw ← set.mem_to_finset ,
            rw finset.filter_mem_eq_inter,
            rw finset.univ_inter  })
      htm'
      ht_prim }
end


theorem weak_jordan_of_pretransitive' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_pretransitive G α 2 :=
begin
 -- We can deduce it from jordan0
  apply is_pretransitive_of_subgroup,
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply strong_jordan_of_pretransitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_trans,
end

theorem weak_jordan_of_preprimitive' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α 2 :=
begin
 -- We can deduce it from strong_jordan_of_preprimitive
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply is_multiply_preprimitive_of_subgroup,
  norm_num,
  refine strong_jordan_of_preprimitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_prim
end

-- Wielandt : s = Δ, n - m = #s, n = #α, m = #sᶜ, 1 < m < n
-- 1 + #s < n , #s ≥ 1
.

theorem jordan_of_preprimitive {n : ℕ} :
  ∀ {G α : Type*} [group G] [fintype α] [decidable_eq α],
  by exactI ∀ [mul_action G α], by exactI ∀ (hG : is_preprimitive G α)
  {s : set α} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hprim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)),
  is_multiply_preprimitive G α (1 + n.succ) :=
begin
  induction n with n hrec,
  { -- case n = 0
    introsI G α _ _ _ _ hG s hsn hα hGs,
    let hG_eq := hG.exists_smul_eq,
    obtain ⟨a, hsa⟩ := card_eq_one_iff_is_singleton s hsn,
    rw hsa at *,
    split,
    { rw stabilizer.is_multiply_pretransitive,
      rw ← is_pretransitive_iff_is_one_pretransitive,
      refine is_pretransitive_of_bihom
       -- (sub_mul_action_of_fixing_subgroup_of_singleton_bihom G a)
        (sub_mul_action_of_fixing_subgroup_of_singleton_bihom_bijective G a).surjective
        hGs.to_is_pretransitive,
        exact hG.to_is_pretransitive, },
    { intros t h,
      suffices ht' : fintype.card t = 1,
      { obtain ⟨b, htb⟩ := card_eq_one_iff_is_singleton t ht',
        rw htb at *,
        obtain ⟨g, hg⟩ := hG_eq a b,
        have hst : g • {a} = {b}, sorry,
        apply is_preprimitive_via_surjective_bihom
          (sub_mul_action_of_fixing_subgroup_conj_bihom_bijective G hst).surjective
          hGs },
      { rw [cardinal.mk_fintype, ← nat.cast_one, ← nat.cast_add,
          cardinal.nat_cast_inj, add_left_inj] at h,
        exact h } } },
  -- Induction step
  introsI G α _ _ _ _ hG s hsn hα hGs,
  suffices : ∃ (a : α) (t : set (sub_mul_action_of_stabilizer G α a)),
    a ∈ s ∧ s = insert a (coe '' t),
  obtain ⟨a, t, ha, hst⟩ := this,
  have ha' : a ∉ coe '' t,
  { intro h, rw set.mem_image at h, obtain ⟨x, hx⟩ := h,
    apply x.prop, rw hx.right, exact set.mem_singleton a },
  have ht_prim : is_preprimitive (stabilizer G a) (sub_mul_action_of_stabilizer G α a),
  { rw ← is_multiply_preprimitive_one_iff,
    rw ← is_multiply_preprimitive_of_stabilizer G α (by norm_num) hG.to_is_pretransitive,
    apply weak_jordan_of_preprimitive hG hsn hα hGs },

  have hGs' : is_preprimitive ↥(fixing_subgroup ↥(stabilizer G a) t) ↥(sub_mul_action_of_fixing_subgroup ↥(stabilizer G a) t),
  { apply is_preprimitive_via_surjective_bihom
        (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective G a t).surjective,
    apply is_preprimitive_via_surjective_bihom
        (sub_mul_action_of_fixing_subgroup_eq_bihom_bijective G hst).surjective,
    exact hGs },

  rw ← nat.succ_eq_one_add,
  rw is_multiply_preprimitive_of_stabilizer G α _ hG.to_is_pretransitive,
  rw nat.succ_eq_one_add,
  refine hrec ht_prim _ _ hGs',
  { -- fintype.card t = n.succ
    rw ← set.card_image_of_injective t (subtype.coe_injective),
    apply nat.add_right_cancel,
    rw ← set.card_insert (coe '' t) ha',
    simp_rw ← hst, rw ← nat.succ_eq_add_one, exact hsn,
    apply_instance },
  { -- 1 + n.succ < fintype.card ↥(sub_mul_action_of_stabilizer G α a)
    change _ < fintype.card ↥(sub_mul_action_of_stabilizer G α a).carrier,
    rw ← nat.succ_eq_one_add,
    apply nat.lt_of_add_lt_add_right,
    rw sub_mul_action_of_stabilizer_def,
    rw fintype.card_compl_set,
    rw nat.sub_add_cancel (set_fintype_card_le_univ _),
    simp only [set.card_singleton],
    rw add_comm,
    exact hα },
    { rw ge_iff_le, apply nat.succ_le_succ, apply nat.zero_le },


  -- ∃ (a : α), a ∈ s
  { suffices : s.nonempty,
    rw set.nonempty_def at this,
    obtain ⟨a, ha⟩ := this,
    use a,
    use coe ⁻¹' s,
    apply and.intro ha,
    rw set.insert_eq,
    rw set.image_preimage_eq_inter_range,
    simp only [subtype.range_coe_subtype, set.singleton_union],
    simp_rw mem_sub_mul_action_of_stabilizer_iff,
    simp only [ne.def],
    ext x,
--    apply subset_antisymm,
    { rw set.mem_insert_iff,
      simp,
      rw or_and_distrib_left,
      simp_rw or_not,
      rw and_true,
      split,
      intro hx, apply or.intro_right _ hx,
      intro hx, cases hx with hx hx,
      rw hx, exact ha,
      exact hx },
    rw ← set.ne_empty_iff_nonempty,

    intro h,
    simp only [h, set.empty_card'] at hsn,
    simpa using hsn },
end

#check nat.add_le_to_le_sub
#check nat.succ_eq_add_one
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

example ( m n : ℕ) (h : (m : cardinal) ≤ n ): m ≤ n :=
begin
  refine cardinal.nat_cast_le.mp h
end
end Jordan

end  finite_groups

section Jordan'

open mul_action
open_locale pointwise classical

variables {α : Type*} [fintype α] -- [decidable_eq α]
variable {G : subgroup (equiv.perm α)}

lemma eq_s2_of_nontrivial (hα : fintype.card α ≤ 2) (hG : nontrivial G) :
  G = (⊤ : subgroup (equiv.perm α)) :=
begin
  apply subgroup.eq_top_of_card_eq,
  apply le_antisymm,
  apply fintype.card_subtype_le ,
  rw [fintype.card_equiv (equiv.cast rfl)],
  refine le_trans _ _,
  exact (2 : ℕ).factorial,
  exact nat.factorial_le hα,
  rw [nat.factorial_two],
  rw ← fintype.one_lt_card_iff_nontrivial at hG,
  exact hG,
end

example (g f : equiv.perm α) (h : f = g) (a : α) : f a = g a :=
begin
  exact congr_fun (congr_arg coe_fn h) a
end

lemma nontrivial_on_equiv_perm_two {K : Type*} [group K] [mul_action K α]
  (hα : fintype.card α = 2) {g : K}
  {a : α} (hga : g • a ≠ a) : is_multiply_pretransitive K α 2 :=
begin
  suffices : function.surjective (canonical_bihom K α).to_monoid_hom.to_fun,
  { rw is_multiply_pretransitive_via_bijective_bihom_iff (canonical_bihom_bijective K α) this,
    rw ← hα,
    exact equiv_perm_is_fully_pretransitive α },
  rw monoid_hom.to_fun_eq_coe,
  rw ← monoid_hom.range_top_iff_surjective,

  apply subgroup.eq_top_of_card_eq,
  apply le_antisymm,
  change fintype.card ↥(set.range (canonical_bihom K α).to_monoid_hom.to_fun) ≤ _,
  apply fintype.card_subtype_le,
  suffices hg : to_perm g ∈ ((canonical_bihom K α).to_monoid_hom.range),
  { rw [fintype.card_perm, hα, nat.factorial_two, nat.succ_le_iff, subgroup.one_lt_card_iff_ne_bot],
    intro h, apply hga,
    rw [h, subgroup.mem_bot] at hg,
    simpa using congr_fun (congr_arg coe_fn hg) a },
  use g, refl
end

example [fintype α] (s : finset α) : (↑s : set α).to_finset = s :=
by rw [← finset.coe_inj, set.coe_to_finset]


lemma is_pretransitive_of_cycle {g : equiv.perm α} (hg : g ∈ G) (hgc : g.is_cycle) :
  is_pretransitive
    (fixing_subgroup G (↑g.support : set α)ᶜ)
    (sub_mul_action_of_fixing_subgroup G (↑g.support : set α)ᶜ) :=
begin
  obtain ⟨a, hga, hgc⟩ := hgc,

  have hs : ∀ (x : α), g • x ≠ x ↔ x ∈ sub_mul_action_of_fixing_subgroup G (↑g.support : set α)ᶜ,
  { intro x,
    rw mem_sub_mul_action_of_fixing_subgroup_iff,
    simp only [set.mem_compl_eq, finset.mem_coe, equiv.perm.not_mem_support],
    refl },
  let ha := (hs a).mp hga,
  suffices : ∀ x ∈ sub_mul_action_of_fixing_subgroup G (↑g.support : set α)ᶜ,
    ∃ (k : fixing_subgroup G (↑g.support : set α)ᶜ), x = k • a,
  { apply is_pretransitive.mk,
    rintros ⟨x, hx⟩ ⟨y, hy⟩,
    obtain ⟨k, hk⟩ := this x hx,
    obtain ⟨k', hk'⟩ := this y hy,
    use k' * k⁻¹,
    rw ← set_like.coe_eq_coe, rw set_like.coe_mk,
    simp only [sub_mul_action.coe_smul_of_tower, sub_mul_action.coe_mk],
    rw [hk, hk', smul_smul, inv_mul_cancel_right] },
  intros x hx,
  obtain ⟨i, hi⟩ := hgc x _,
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixing_subgroup G (↑g.support : set α)ᶜ,
  { simp_rw mem_fixing_subgroup_iff G,
    intros y hy,
    simpa only [set.mem_compl_eq, finset.mem_coe, equiv.perm.not_mem_support] using hy },

  let g' : fixing_subgroup ↥G (↑g.support : set α)ᶜ := ⟨(⟨g, hg⟩ : ↥G), hg'⟩,
  use g' ^ i,
  rw ← hi,
  refl,

  exact (hs x).mpr hx,
end

lemma equiv.perm.is_swap.cycle_type {α : Type u_1} [fintype α] [decidable_eq α]
  {σ : equiv.perm α} (h : σ.is_swap) : σ.cycle_type = {2} :=
begin
  simp only [equiv.perm.is_cycle.cycle_type h.is_cycle, equiv.perm.card_support_eq_two.mpr h],
  refl,
end

lemma equiv.perm.is_swap.order_of {α : Type u_1} [fintype α] [decidable_eq α]
  {σ : equiv.perm α} (h : σ.is_swap) : order_of σ = 2 :=
by rw [← equiv.perm.lcm_cycle_type, h.cycle_type, multiset.lcm_singleton, normalize_eq]

theorem jordan_perm (hG : is_preprimitive G α)
  {g : equiv.perm α} (h2g : equiv.perm.is_swap g) (hg : g ∈ G) : G = ⊤  :=
begin
  cases nat.lt_or_ge (fintype.card α) 3 with hα3 hα3,
  { -- trivial case : fintype.card α ≤ 2
    rw nat.lt_succ_iff at hα3,
    apply subgroup.eq_top_of_card_eq,
    apply le_antisymm,
    apply fintype.card_subtype_le ,
    rw [fintype.card_equiv (equiv.cast rfl)],
    refine le_trans (nat.factorial_le hα3) _,
    rw [nat.factorial_two],
    apply nat.le_of_dvd,
    exact fintype.card_pos,
    suffices : 2 = order_of g,
    { rw [← set_like.coe_mk g hg, order_of_subgroup] at this,
      rw this, exact order_of_dvd_card_univ },
    rw h2g.order_of },
  obtain ⟨n, hn⟩ := nat.exists_eq_add_of_le hα3, rw add_comm at hn,

  let s := (g.support : set α),
  have hs2 : fintype.card s = 2,
  { simp only [finset.coe_sort_coe, fintype.card_coe, equiv.perm.card_support_eq_two],
    exact h2g },
  have hsc : fintype.card (sᶜ : set α) = n.succ,
  { rw [fintype.card_compl_set, hs2, hn],
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one],  },
  apply is_fully_minus_one_pretransitive_iff,
  suffices : is_multiply_preprimitive G α (fintype.card α - 1),
  apply this.left,

  have hn' : fintype.card α - 1 = 1 + n.succ,
  { rw hn,
    conv_rhs {rw [add_comm, nat.succ_eq_add_one] },
    simp only [nat.add_succ_sub_one]},
  rw hn',

  refine jordan_of_preprimitive hG _ _ _,
  exact ((g.support)ᶜ : set α),
  exact n,
  { rw ← hsc,
    simp only [fintype.card_of_finset, set.mem_compl_eq], },
  { rw hn,
    rw [nat.one_add, ← nat.add_one, ← nat.add_one, add_assoc, add_lt_add_iff_left],
    norm_num },

  apply is_preprimitive_of_prime,
  swap,
  change nat.prime(fintype.card (sub_mul_action_of_fixing_subgroup G (g.support : set α)ᶜ).carrier),
  rw sub_mul_action_of_fixing_subgroup_def,
  simp only [compl_compl, finset.coe_sort_coe, fintype.card_coe],
  rw equiv.perm.card_support_eq_two.mpr h2g,
  norm_num,

  apply is_pretransitive_of_cycle hg,
  exact equiv.perm.is_swap.is_cycle h2g,
end

theorem jordan_alternating (hG : is_preprimitive G α)
  {g : equiv.perm α} (h3g : equiv.perm.is_three_cycle g) (hg : g ∈ G) :
  alternating_group α ≤ G :=
begin
  cases nat.lt_or_ge (fintype.card α) 4 with hα4 hα4,
  { -- trivial case : fintype.card α ≤ 3
    rw nat.lt_succ_iff at hα4,
    apply large_subgroup_of_perm_contains_alternating,
    rw ge_iff_le,
    rw fintype.card_perm,
    apply le_trans (nat.factorial_le hα4),
    norm_num,
    change 2 * 3 ≤ _,
    simp only [mul_le_mul_left, nat.succ_pos'],
    apply nat.le_of_dvd (fintype.card_pos),
    suffices : 3 = order_of (⟨g, hg⟩ : G),
    rw this, exact order_of_dvd_card_univ,

    rw ← equiv.perm.is_three_cycle.order_of h3g,
    conv_lhs { rw ← set_like.coe_mk g hg },
    apply order_of_subgroup,
    exact has_one.nonempty, },

  obtain ⟨n, hn⟩ := nat.exists_eq_add_of_le hα4, rw add_comm at hn,

  apply is_full_minus_two_pretransitive_iff,
  suffices : is_multiply_preprimitive G α (fintype.card α - 2),
  apply this.left,

  have hn' : fintype.card α - 2 = 1 + n.succ,
  { rw hn,
    conv_rhs {rw [add_comm, nat.succ_eq_add_one]  },
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one] },
  rw hn',

  have hs3 : fintype.card (g.support) = 3,
  { simp only [fintype.card_coe],
    exact equiv.perm.is_three_cycle.card_support h3g },
  refine jordan_of_preprimitive hG _ _ _,

  exact ((g.support)ᶜ : set α),
  exact n,
  { simp only [fintype.card_compl_set, finset.coe_sort_coe, fintype.card_coe],
    rw equiv.perm.is_three_cycle.card_support h3g,
    rw hn,
    simp only [nat.succ_sub_succ_eq_sub, nat.add_succ_sub_one] },
  { rw hn,
    rw [nat.one_add, ← nat.add_one, ← nat.add_one, add_assoc,  add_lt_add_iff_left],
    norm_num },

  apply is_preprimitive_of_prime,
  swap,
  change nat.prime(fintype.card (sub_mul_action_of_fixing_subgroup G (g.support : set α)ᶜ).carrier),
  rw sub_mul_action_of_fixing_subgroup_def,
  simp only [compl_compl, finset.coe_sort_coe, fintype.card_coe],
  rw equiv.perm.is_three_cycle.card_support h3g,
  norm_num,

  apply is_pretransitive_of_cycle hg,
  exact equiv.perm.is_three_cycle.is_cycle h3g
end

end Jordan'


#exit

lemma is_pretransitive_of_full_cycle {G : Type*} [group G] [mul_action G α]
  (g : G) (hgc : (mul_action.to_perm g : equiv.perm α).is_cycle)
  (hgs : (mul_action.to_perm g : equiv.perm α).support.card = fintype.card α) : is_pretransitive G α :=
begin
  rw finset.card_eq_iff_eq_univ at hgs,
  obtain ⟨a, hga, hgc⟩ := hgc,
  suffices : ∀ (x : α), ∃ (k : G), x = k • a,
  { apply is_pretransitive.mk,
    intros x y,
    obtain ⟨k, hk⟩ := this x,
    obtain ⟨k', hk'⟩ := this y,
    use k' * k⁻¹,
    rw [hk, hk', smul_smul, inv_mul_cancel_right] },
  intro x,
  obtain ⟨i, hi⟩ := hgc x _,
  use g ^ i,
  swap,
  rw ← equiv.perm.mem_support, rw hgs, apply finset.mem_univ,

  suffices : (to_perm g : equiv.perm α) ^ i = to_perm (g ^i),
  simp only [← hi, this, to_perm_apply],
  simpa using (monoid_hom.map_zpow (mul_action.to_perm_hom G α) g i).symm
end
