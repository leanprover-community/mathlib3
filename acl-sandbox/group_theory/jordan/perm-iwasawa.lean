/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.basic tactic.group
import group_theory.solvable
import group_theory.group_action.sub_mul_action
-- import group_theory.perm.concrete_cycle
import order.minimal
import .primitive
import .jordan

open_locale pointwise

open mul_action


section action_on_finsets

variables (α : Type*) [decidable_eq α] (G : Type*) [group G] [mul_action G α]
variable (n : ℕ)

def nat.finset := { s : finset α | s.card = n}

/- -- `sub_mul_action is not a class`
@[instance] def nat.finset.mul_action.finset' :
  sub_mul_action G (finset α) := {
carrier := n.finset α,
smul_mem' :=  λ g s hs,
begin
  change (finset.image (λ x, g • x) s).card = n,
  rw finset.card_image_of_injective,
  exact hs, exact mul_action.injective g,
end }
-/

@[instance] def nat.finset.mul_action.finset :
  mul_action G (n.finset α) := {
to_has_scalar := {
  smul := λ g ⟨s, hs⟩, ⟨g • s,
  begin
    change (finset.image (λ x, g • x) s).card = n,
    rw finset.card_image_of_injective,
    exact hs, exact mul_action.injective g,
  end⟩ },
one_smul := λ ⟨s, hs⟩,
begin
  rw ← subtype.coe_inj, exact mul_action.one_smul s,
end,
mul_smul := λ g h ⟨s, hs⟩,
begin
  rw ← subtype.coe_inj, exact mul_action.mul_smul g h s,
end }

lemma nat.finset.mul_action.finset_apply (g : G) (f : finset α) (hf : f ∈ n.finset α) :
  ↑(g • (⟨f, hf⟩ : n.finset α)) = g • f := rfl

variable [fintype α]

def embedding_to_finset.map : (fin n ↪ α) →[equiv.perm α] n.finset α := {
  to_fun := λ (f : fin n ↪ α), ⟨finset.univ.map f,
  begin
    change (finset.univ.map f).card = n,
    rw finset.card_map,
    exact finset.card_fin n,
  end⟩,
  map_smul' := λ g f,
  begin
    simp only [id.def],
    rw [← subtype.coe_inj, subtype.coe_mk,
      nat.finset.mul_action.finset_apply],
    rw function.embedding.smul_def, rw finset.smul_finset_def,
    rw ← finset.map_map,
    rw finset.map_eq_image,
    refl
  end }

lemma embedding_to_finset.map_def (f : fin n ↪ α) :
  ↑(embedding_to_finset.map α n f) = finset.univ.map f := rfl

lemma embedding_to_finset.map_surjective : function.surjective (embedding_to_finset.map α n) :=
begin
  rintro ⟨s, hs⟩,
  have slc : s.to_list.length = n,
  { change s.card = n at hs, rw ← hs, exact finset.length_to_list s, },
  use  λ i, s.to_list.nth_le ↑i (begin rw slc, exact i.prop, end),
  -- function.injective
  rintros ⟨i, hi⟩ ⟨j, hj⟩ hij,
  simp only [subtype.mk_eq_mk],
  apply list.nodup_iff_nth_le_inj.mp (s.nodup_to_list),
  exact hij,
  -- image of map = given finset set
  ext,
  rw embedding_to_finset.map_def,
  simp only [subtype.coe_mk, equivariant_map.coe_mk, finset.mem_map, finset.mem_univ,
    function.embedding.coe_fn_mk, exists_true_left],
  rw [← finset.mem_to_list, list.mem_iff_nth_le, fin.exists_iff],
  simp_rw ← slc,
  refl,
end



theorem nat.finset_is_pretransitive : is_pretransitive (equiv.perm α) (n.finset α) :=
begin
  apply is_pretransitive_of_surjective_map (embedding_to_finset.map_surjective α n),
  apply is_pretransitive.mk,
  intros f f',
  have hα : n ≤ fintype.card α,
  { rw ← fintype.card_fin n, exact fintype.card_le_of_embedding f },
  obtain ⟨f1, hf1⟩ := may_extend hα _ f,
  obtain ⟨f'1, hf'1⟩ := may_extend hα _ f',
  obtain ⟨g1, hgf, hfg⟩ := function.bijective_iff_has_inverse.mp
    ((fintype.bijective_iff_injective_and_card _).mpr
      ⟨f1.inj', fintype.card_fin _⟩),
  rw function.embedding.to_fun_eq_coe at hgf hfg,
  obtain ⟨g'1, hgf', hfg'⟩ := function.bijective_iff_has_inverse.mp
    ((fintype.bijective_iff_injective_and_card _).mpr
      ⟨f'1.inj', fintype.card_fin _⟩),
  rw function.embedding.to_fun_eq_coe at hgf' hfg',
  use f'1 ∘ g1, use f1 ∘ g'1,
  exact function.left_inverse.comp hgf' hfg,
  exact function.right_inverse.comp hfg' hgf,
  { ext a, simp, rw [← hf1, ← hf'1], simp, rw hgf },
  all_goals { simp only [enat.card_eq_coe_fintype_card] },
end

lemma exists_covby_le {α : Type*} [partial_order α] [fintype α] (a b : α) (hab : a < b):
  ∃ (c : α),  a ⋖ c ∧ c ≤ b :=
begin
  let Hwf := fintype.preorder.well_founded_lt,
  let sab := { x : α | a < x ∧ x ≤ b },
  have sab_ne : sab.nonempty,
  { rw set.nonempty_def,
    use b, exact ⟨hab, le_refl b⟩ },
  let c := well_founded.min (Hwf) sab sab_ne,
  use c,
  have hc : a < c ∧ c ≤ b := well_founded.min_mem Hwf sab sab_ne,
  split,
  { -- a ⋖ c
    split,
    apply (well_founded.min_mem Hwf sab sab_ne).left,
    intros x hax hxc,
    apply well_founded.not_lt_min Hwf sab sab_ne,
    exact ⟨hax, le_trans (le_of_lt hxc) hc.right⟩,
    exact hxc },
  { -- c ≤ b
    exact hc.right,
  },
  apply_instance,
end

lemma exa (s t : n.finset α) :
  s = t ↔ s ≤ t :=
begin
split,
  { intro h, rw h, exact le_refl t, },
  { intro h,
    rw ← subtype.coe_eta s s.prop, rw ← subtype.coe_eta t t.prop,
    rw ← subtype.coe_inj,
    simp only [subtype.coe_mk],
    apply finset.eq_of_subset_of_card_le h,
    suffices : ∀ (s : n.finset α), (s : finset α).card = n,
    simp only [this],
    intro s, exact s.prop },
end

example (s t : set α) (g : G) : g • s ⊆ t ↔ s ⊆ g⁻¹ • t :=
begin
exact set.set_smul_subset_iff,
end


lemma exb (s : n.finset α) (g : equiv.perm α) :
  g • s ≠ s ↔
  ∃ (a : α) (ha : a ∈ (s : set α)), a ∉ g⁻¹ • (s : set α) :=
begin
  rw not_iff_comm, rw exa,
  rw ← not_iff_comm,
  rw ← set.not_subset,
  rw not_iff_comm, rw not_not,
  rw ← set.set_smul_subset_iff,
  simp,
end

example (s : n.finset α) (g : equiv.perm α) :
  g • s ≠ s ↔
  ∃ (a : α) (ha : a ∈ (s : set α)), a ∉ g⁻¹ • (s : set α) :=
begin
  rw ← set.not_subset,
  split,
  { intros h h', apply h,
    let hs := s.prop, rw set.mem_def at hs,
    change finset.card ↑s = n at hs,
    rw ← subtype.coe_eta s s.prop,
    rw ← subtype.coe_inj,
    rw nat.finset.mul_action.finset_apply,
    rw subtype.coe_mk,
    apply finset.eq_of_subset_of_card_le,
    intros x hx,
    change x ∈ finset.image (λ u, g • u) (s : finset α) at hx,
    rw finset.mem_image at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    rw ← finset.mem_coe,
    rw ← set.mem_inv_smul_set_iff,  apply h', exact hy,
    apply le_of_eq, apply symm,
    rw ← nat.finset.mul_action.finset_apply α (equiv.perm α) n
        g s hs,
    rw hs,
    rw subtype.coe_eta,
    exact subtype.mem (g • s) },
  { intros h h', apply h,
    intros x hx, rw set.mem_inv_smul_set_iff,
    rw ← h',
    rw ← subtype.coe_eta s s.prop,
    rw [coe_coe, finset.mem_coe],
    rw nat.finset.mul_action.finset_apply,
    -- simp only [equiv.perm.smul_def, coe_coe, finset.mem_coe],
    change g • x ∈ finset.image (λ u, g • u) (s : finset α),
    rw finset.mem_image,
    use x, use hx }
end

lemma nat.finset_is_preprimitive_of (h_one_lt : 1 < n) (hn : n < fintype.card α)
  (hα : fintype.card α ≠ 2 * n) : is_preprimitive (equiv.perm α) (n.finset α) :=
begin
  letI ht : is_pretransitive (equiv.perm α) (n.finset α) :=
    n.finset_is_pretransitive α,
  haveI : nontrivial (n.finset α), sorry,
  obtain ⟨s, _, hs⟩ := finset.exists_smaller_set finset.univ n (le_of_lt hn),
  rw ← maximal_stabilizer_iff_preprimitive,
  swap, exact ⟨s,hs⟩,
  split,
  have stab_lt_top : stabilizer (equiv.perm α) (⟨s, hs⟩ : n.finset α) < ⊤,
  { obtain ⟨a, ha : a ∈ s⟩ := finset.nonempty.bex
  (begin rw [← finset.card_pos, hs], exact lt_trans (nat.lt_succ_self 0) h_one_lt, end),
    obtain ⟨b : α, hb : b ∈ sᶜ⟩ := finset.nonempty.bex (begin
      rw [← finset.card_compl_lt_iff_nonempty sᶜ, compl_compl, hs], exact hn, end),
    rw lt_top_iff_ne_top,
    intro h,
    rw finset.mem_compl at hb, apply hb,
    have hg : equiv.swap a b ∈ stabilizer (equiv.perm α) (⟨s, hs⟩ : n.finset α),
    rw h, apply subgroup.mem_top,
    rw mem_stabilizer_iff at hg,
    rw [← subtype.coe_inj, subtype.coe_mk,
        nat.finset.mul_action.finset_apply] at hg,
    rw ← hg,
    change b ∈ finset.image (equiv.swap a b) s,
    rw finset.mem_image,
    use a, use ha, apply equiv.swap_apply_left },
  split, exact ne_of_lt stab_lt_top,
  intros b hb,
  obtain ⟨c, hc, hc'⟩ := exists_covby_le _ b hb,
  rw eq_top_iff, apply le_trans _ hc', rw ← eq_top_iff,

  suffices : is_preprimitive ↥c α,
  rw [← hs, finset.one_lt_card_iff] at h_one_lt,
  obtain ⟨a, b, has, hbs, hab⟩ := h_one_lt,
  have hg : equiv.swap a b ∈ c,
  { apply le_of_lt hc.left,
    rw mem_stabilizer_iff,
    rw [← subtype.coe_inj, nat.finset.mul_action.finset_apply, subtype.coe_mk],

    apply finset.eq_of_subset_of_card_le,
    -- Prove : equiv.swap a b • s ⊆ s
    intros x hx, change x ∈ finset.image (λ x , equiv.swap a b • x) s at hx,
    rw finset.mem_image at hx, obtain ⟨y, hy, rfl⟩ := hx,
    simp only [equiv.perm.smul_def],
    cases em (y = a) with hya hya,
    rw [hya, equiv.swap_apply_left], exact hbs,
    cases em (y = b) with hyb hyb,
    rw [hyb, equiv.swap_apply_right], exact has,
    rw equiv.swap_apply_of_ne_of_ne hya hyb, exact hy,
    -- Prove : s.card ≤ (equiv.swap a b • s).card
    apply le_of_eq,
    apply symm,
    rw ← nat.finset.mul_action.finset_apply α (equiv.perm α) n
      (equiv.swap a b) s hs, rw hs,
    exact subtype.mem (equiv.swap a b • ⟨s, hs⟩) },
  apply jordan_swap this _ _ hg,
  { use a, use b, apply and.intro hab, refl },

  apply is_preprimitive.mk,
  apply is_pretransitive.mk,
  -- Prove : pretransitivity
  have : ¬(c ≤ stabilizer (equiv.perm α) (⟨s, hs⟩ : n.finset α)),
  exact not_le_of_lt hc.left,
  rw ← set_like.coe_subset_coe at this,
  rw set.not_subset at this,
  obtain ⟨g, hg, hg'⟩ := this,

  have : ∃ (a : α), a ∈ s ∧ g • a ∉ s,

  simp at hg',


  intros x y,

  sorry,
  -- Prove : trivial blocks
  sorry
end



#exit

end action_on_finsets

open equiv.perm equiv mul_action
variables (α : Type*) [decidable_eq α] (G : Type*) [group G] [mul_action G α]

variables {G α}

section Permutations

/-- The symmetric group is generated by permutations of the form (a x), for any fixed a -/
-- → group_theory.perm.sign
theorem equiv.perm.closure_is_based_swap (a : α) : subgroup.closure { f : perm α | ∃ (x : α), f = swap a x } = ⊤ :=
begin
  apply top_unique,
  rw ← closure_is_swap,
  let H := subgroup.closure { f : perm α | ∃ (x : α), f = swap a x },
  have h_swaps : ∀ (x : α), swap a x ∈ H ,
  { intro x,
    apply subgroup.subset_closure,
    simp only [exists_apply_eq_apply', set.mem_set_of_eq] },
  apply (subgroup.closure_le H).mpr,
  intros f hf,
  rw set.mem_set_of_eq at hf,
  obtain ⟨x, y, hxy, rfl⟩ := hf,
    -- (a x) (a y) (a x) = (x y)
    cases dec_em (x = a) with hxa hxa',
    { -- hxa : x = a
      rw hxa, exact h_swaps y, },
    -- hxa' : x ≠ a'
    cases dec_em (y = a) with hya hya',
    { -- hya : y = a
      rw hya, rw equiv.swap_comm, exact h_swaps x },

    rw ← swap_mul_swap_mul_swap hya' hxy.symm,
    apply subgroup.mul_mem H _ (h_swaps x),
    apply subgroup.mul_mem H (h_swaps x) _,
    rw equiv.swap_comm,
    exact h_swaps y,
end

/- now unused, is replaced by action on lists
/-- The standard action of perm α on α is multi-transitive -/
-- The proof is awfully long, maybe I should learn about finset
theorem standard_is_multi_transitive (n : ℕ) (hn : n ≤ fintype.card α) :
  mul_action.is_pretransitive (perm α) (func.inj_pow (perm α) α n) :=
begin
  induction n with n hrec,
  { apply mul_action.is_pretransitive.mk,
    intros x y,
    use (1 : perm α), rw one_smul,
    ext i, apply fin.elim0 i },
  { apply mul_action.is_pretransitive.mk,
    intros x y,
    -- définir x' et y' comme les restrictions de x et y à fin n
    let j := fin.cast_succ,
    let hj : function.injective j := fin.cast_succ_injective n,

    let x' := func.inj_map.comp j hj x,
    let y' := func.inj_map.comp j hj y,
    let this := (hrec (nat.le_of_succ_le hn)).exists_smul_eq,
    obtain ⟨g, hg⟩ := this x' y',

    have : g • (func.inj_map.comp j hj x) = func.inj_map.comp j hj (g • x),
    { simp only [mul_action_hom.map_smul] },

    have h_upto_n': ∀ (i : fin n.succ) (hi : i < fin.last n), (g • x).val i = y.val i,
    { intros i hi,
      let i' := fin.cast_lt i hi,
      simp only [perm.smul_def, func.smul_def, subtype.val_eq_coe, sub_mul_action.coe_smul_of_tower],
      have tx : x.val i = x'.val i',
      { let z:= func.inj_map.comp_eval j hj x i',
        simp only [fin.cast_succ_cast_lt, subtype.val_eq_coe] at z,
        exact z.symm, },
      have ty : y.val i = y'.val i',
      { let z:= func.inj_map.comp_eval j hj y i',
        simp only [fin.cast_succ_cast_lt, subtype.val_eq_coe] at z,
        exact z.symm, },
      have t' : g • x'.val i' = y'.val i',
      { let hg2 := congr_arg (λ x : func.inj_map _ _ _, x.val) hg ,
        exact congr_fun hg2 i',
      },
      simp only [perm.smul_def, subtype.val_eq_coe] at t' tx ty,
      rw ty, rw tx, exact t' },

    let g' := equiv.swap ((g • x).val (fin.last n)) (y.val (fin.last n)),
    have h_inj_n : ∀ (f : func.inj_pow (perm α) α n.succ) (i : fin n.succ) (hi : i < fin.last n), f.val i ≠ f.val (fin.last n),
    { intros f i hi hx,
      rw f.prop hx at hi,
      exact lt_irrefl (fin.last n) hi  },

    use g'*g,

    ext i,
    cases le_iff_lt_or_eq.mp (fin.le_last i) with hi hn,
    { have ht : g' • ((g • x).val i) = y.val i,
      { rw ← h_upto_n' i hi,
        refine equiv.swap_apply_of_ne_of_ne _ _ ,
        exact h_inj_n (g • x) i hi,
        rw h_upto_n' i hi,
        exact h_inj_n y i hi },
      simpa only using ht},
    { rw hn,
      have ht : g' • ((g • x).val (fin.last n)) = y.val (fin.last n),
      { apply equiv.swap_apply_left _ _ },
      simpa only using ht } }
end
-/

/- unused : is done by general case of finsets
/-- The square of an action minus the diagonal, has a sub_mul_action -/
def square' (G : Type*) [group G] (X : Type*) [mul_action G X] :
 sub_mul_action G (X × X) :=
{ carrier := { x : X × X | x.1 ≠ x.2 },
  smul_mem' := λ g x hx,
  begin
    rw set.mem_set_of_eq at hx ⊢,
    simp only [hx, prod.smul_snd, prod.smul_fst, ne.def, smul_left_cancel_iff, not_false_iff],
  end, }

lemma standard_is_two_transitive (α : Type*) [decidable_eq α] [fintype α] :
  mul_action.is_pretransitive (perm α) (square' (perm α) α) :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y,

  let g := equiv.swap x.val.1 y.val.1,
  let x' := g • x,
  have t1 : x'.val.1 = y.val.1,
  { simp only [perm.smul_def, prod.smul_fst, subtype.val_eq_coe, sub_mul_action.coe_smul_of_tower],
    refine equiv.swap_apply_left _ _,  },

  let h := equiv.swap x'.val.2 y.val.2,

  use h*g,

  apply subtype.ext_iff_val.mpr,
  apply prod.ext_iff.mpr,
  split,
  have : h • (x'.val.1) = y.val.1,
  { rw ← t1,
    refine equiv.swap_apply_of_ne_of_ne _ _ ,
    exact x'.prop,
    rw t1, exact y.prop  },
  exact this,
  refine equiv.swap_apply_left _ _,
end


theorem transitive_on_pairs {α : Type*} [decidable_eq α] [fintype α] :
 --  ∀ (x y : action_on_pairs_of (perm α) α) , ∃ (g : perm α), g • x = y :=
  mul_action.is_pretransitive (perm α) (action_on_pairs_of (perm α) α) :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y,
  let px : square' (perm α) α := ⟨pair.lift x, pair.lift.ne x⟩,
  let py : square' (perm α) α := ⟨pair.lift y, pair.lift.ne y⟩,
  have h := (standard_is_two_transitive α).exists_smul_eq,
  obtain ⟨g, hg⟩ := h px py,
  use g,
  apply set_like.coe_eq_coe.mp,
  rw sub_mul_action.coe_smul,
  rw pair.lift.spec x, rw pair.lift.spec y,
  change (λ a, g • a) '' {(pair.lift x).fst, (pair.lift x).snd} = {(pair.lift y).fst, (pair.lift y).snd},
  rw set.image_pair,
  let hg' := set_like.coe_eq_coe.mpr hg,
  simp only [sub_mul_action.coe_smul, subtype.coe_mk] at hg',
  rw ← hg',
  simp only [prod.smul_snd, prod.smul_fst],
end
-/

theorem transitive_on_nodup_list.exists_smul_eq
  (s t : list α) (hs : s.nodup) (ht : t.nodup) (hst : s.length = t.length) :
  ∃ (g : perm α), g • s = t :=
begin
  revert t,
  induction s,
  case nil { -- s = list.nil
    intros t ht hst,
    use 1,
    change list.map ⇑(1 : perm α) list.nil = t,
    rw list.map_nil,
    simp only [list.length] at hst,
    apply symm,
    apply list.length_eq_zero.mp,
    exact hst.symm, } ,
  case cons  :  a  s' ih { -- s = a :: s'
    specialize ih (list.nodup_of_nodup_cons hs),
    have has' : a ∉ s' := list.not_mem_of_nodup_cons hs,
    intros t ht hst,
    cases t with b t' ,
    case nil {  -- t = list.nil, absurd
      simp only [list.length, nat.succ_ne_zero] at hst,
      exfalso, assumption, },
    case cons {  -- t = b :: t'
    have hbt' : b ∉ t' := list.not_mem_of_nodup_cons ht,
    simp only [add_left_inj, list.length] at hst,
    obtain ⟨g' : perm α, hg' : g' • s' = t'⟩ := ih t' (list.nodup_of_nodup_cons ht) hst,
    use (equiv.swap b (g' • a)) * g',
    simp only [mul_smul, perm.smul_def],
    have hg'' : g' • (a :: s') = (g' • a) :: t',
    { change list.map ⇑g' (a :: s') = (g' • a) :: t',
      change list.map ⇑g' s' = t' at hg',
      rw list.map_cons _ _ _,
      rw hg',
      refl, },
    rw hg'',
    change list.map (swap b (g' • a)) (g' • a :: t')  = b :: t',
    rw list.map_cons _ _ _ ,
    simp only [true_and, perm.smul_def, eq_self_iff_true,swap_apply_right], -- only [perm.smul_def] at this ⊢,
    conv_rhs { rw ← list.map_id t', },
    apply list.map_congr ,
    intros x hx,
    simp only [id.def],
    apply equiv.swap_apply_of_ne_of_ne,
    -- b ∉ t'
    rintro ⟨rfl⟩, exact (list.nodup_cons.mp ht).left hx,
    -- g' • a ∉ t'
    rintro ⟨rfl⟩, rw ← hg' at hx,
    apply (list.nodup_cons.mp hs).left,
    exact (list.mem_map_of_injective (mul_action.injective g')).mp hx } }
end

example (s : finset α) : s.to_list.to_finset = s :=
begin
simp only [finset.to_list_to_finset],
end

lemma finset.map_to_list [decidable_eq β] (f : α → β) (s : finset α) :
  (list.map f s.to_list).to_finset = finset.image f s :=
begin
ext x,
split,
  { intro hx,
    rw list.mem_to_finset at hx,
    obtain ⟨a, ha, rfl⟩ := list.mem_map.mp hx,
    rw finset.mem_image,
    use a,
    split,
    rw finset.mem_to_list at ha, exact ha,
    refl },
  { intro hx,
    rw finset.mem_image at hx,
    obtain ⟨a, ha, rfl⟩ := hx,
    apply list.mem_to_finset.mpr,
    apply list.mem_map.mpr,
    use a, split,
    rw finset.mem_to_list, exact ha,
    refl, }
end

theorem transitive_on_fin_subsets.exists_smul_eq
  (s t : finset α) (hst : s.card = t.card) :
  ∃ (g : perm α), g • (s : set α) = t :=
begin
  rw ← finset.length_to_list s at hst,
  rw ← finset.length_to_list t at hst,
  obtain ⟨g : perm α, hg : list.map ⇑g s.to_list = t.to_list⟩ :=
    transitive_on_nodup_list.exists_smul_eq s.to_list t.to_list (finset.nodup_to_list s) (finset.nodup_to_list t) hst,
  use g,
  change (λx, g • x) '' (s : set α) = t,
  rw [← finset.coe_image, finset.coe_inj],

  rw ← finset.to_list_to_finset t,
  rw ← hg,
  rw ← finset.map_to_list (λ x, g • x) s,
  apply congr_arg,
  refl,
end

/- Direct proof for finsets, useless

theorem transitive_on_fin_subsets.exists_smul_eq' {α : Type*} [decidable_eq α]
  (s t : finset α) (hst : s.card = t.card) :
  ∃ (g : perm α), g • (s : set α) = t :=
begin
  /- Two possible approaches :
    1. enumerate s, t ; extend to enumerations of α ; and compose
    2. induction on cardinals.
        0 : g = 1
        n → n + 1 :
          - choose a ∈ s, b ∈ t
          - set s' = s \ {a}, t' = t \ {b}
          - choose g' such that g • s' = t'
          - set g = (swap b g' • a) * g'
          - g • s = g • (a ∪ s') = (swap b g'•a)  • g' • (a ∪ s')
              = (swap b g'•a) • (g'•a ∪ g'•s')
              = (swap b g'•a) • (g'•a ∪ t')
              = (swap b g'•a) • g'•a ∪ (swap b g'•a) • t'
              = b ∪ (swap b g'•a) • t'
          - b ∉  t',
          - g' • a ∉ t' = g' • s', sinon a ∈ s'
      I follow 2.
    -/
  suffices : ∀ (n : ℕ) (s t : finset α) (hs : s.card = n) (ht : t.card = n),
    ∃ (g : perm α), g • (s : set α) = t ,
    exact this (s.card) s t rfl hst.symm,
  intro n,
  induction n with n hrec,
  -- n = 0
  { intros s t hs ht,
    rw finset.card_eq_zero at hs ht,
    use 1,
    simp only [one_smul, finset.coe_inj],
    rw [ht, hs] },
  -- n → n.succ
  { intros s t hs ht,

    have hs' : 0 < s.card,  { rw hs, exact nat.succ_pos n,  },
    obtain ⟨a, ha⟩ := finset.card_pos.mp hs',
    let s' := s.erase a,
    have hs' : s'.card = n,
    { rw [← nat.pred_succ n, ← hs],
      apply finset.card_erase_of_mem ha, },

    have ht' : 0 < t.card, { rw ht, exact nat.succ_pos n, },
    obtain ⟨b, hb⟩ := finset.card_pos.mp ht',
    let t' := t.erase b,
    have ht' : t'.card = n,
    { rw [← nat.pred_succ n, ← ht],
      apply finset.card_erase_of_mem hb, },

    obtain ⟨g', hg'⟩ := hrec s' t' hs' ht',

    have finset.map_coe : ∀ (g : perm α) (s t : finset α),
      g • (s : set α) = t ↔ finset.image (λ x, g • x) s = t ,
    { intros g s t,
      split,
      { intro h,
        apply finset.coe_inj.mp,
        rw finset.coe_image,
        exact h },
      { intro h,
        change (λ x, g • x) '' ↑s = ↑t,
        rw ← finset.coe_image,
        exact finset.coe_inj.mpr h } },

    let hg' := (finset.map_coe _ _ _).mp hg',

    have hg₁ : g' • (s : set α) = insert (g' • a) t',
    { rw ← finset.coe_insert,
      apply (finset.map_coe g' s _).mpr,
      rw ← finset.insert_erase ha,
      rw finset.image_insert,
      apply congr_arg, exact hg', },

    let g := (equiv.swap b (g' • a)) * g',
    use g,
    rw mul_smul,
    rw hg₁,

    rw ← finset.coe_insert,
    rw (finset.map_coe (swap b (g' • a)) _ t).mpr,

    rw finset.image_insert,
    rw [perm.smul_def,  equiv.swap_apply_right],
    rw ← finset.insert_erase hb,
    apply congr_arg,

    have this : t.erase b = finset.image (λ x, (1 : perm α) • x) (t.erase b),
    { have this' : (λ (x : α), (1 : perm α) • x) = id,
        { funext, rw one_smul, refl,  },
      rw this',
      rw finset.image_id,  },
    rw this,
    apply (finset.map_coe _ _ _).mp,
    rw finset.coe_image,
    apply set.image_congr,
    intros x hx,
    rw perm.smul_def, apply equiv.swap_apply_of_ne_of_ne ,
      -- x ≠ b
      intro h, rw h at hx,
      exact (finset.not_mem_erase b t) hx,
      -- x ≠ g ' • a,
      intro h, rw h at hx, rw ← hg' at hx,
      simp only [perm.smul_def, set.mem_image, finset.coe_erase, set.mem_diff, set.mem_singleton_iff, eq_self_iff_true, not_true,
  exists_eq_right, apply_eq_iff_eq, and_false, finset.coe_image] at hx,
      exact hx },
end
-/

theorem transitive_on_pairs {α : Type*} [decidable_eq α] [fintype α] :
 --  ∀ (x y : action_on_pairs_of (perm α) α) , ∃ (g : perm α), g • x = y :=
  mul_action.is_pretransitive (perm α) (action_on_pairs_of (perm α) α) :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y,
  let fx := (pair.is_finite x).to_finset,
  let fy := (pair.is_finite y).to_finset,
  obtain ⟨g, hg⟩ := transitive_on_fin_subsets.exists_smul_eq fx fy _,
  swap,
    rw  (pair.card_eq_two x), rw (pair.card_eq_two y),
  use g,
    apply set_like.coe_eq_coe.mp,
    rw sub_mul_action.coe_smul,
    simp only [set.finite.coe_to_finset, set.coe_to_finset] at hg,
    exact hg,
end


end Permutations

section Subgroups

/--!
## Subgroups

Two lemmas to simplify stuff in presence of conjugation
-/

lemma subgroup.conj_of_mem_is_mem {G : Type*} [group G] (H : subgroup G) {g h : G} (hh : h ∈ H) :
    g ∈ H → h * g * h⁻¹ ∈ H  :=
begin
    intro hg,
    exact H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh),
end

lemma subgroup.mem_conj_of_mem_iff {G : Type*} [group G] (H : subgroup G) {g h : G} (hh : h ∈ H) :
    h * g * h⁻¹ ∈ H ↔ g ∈ H :=
begin
  split,
  { intro hg,
    have hg' : g = h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹,
      by group,
    rw hg',
    exact subgroup.conj_of_mem_is_mem H (H.inv_mem hh) hg,
  /-
    rw ← mul_one g, rw ← inv_mul_self h,  rw ← mul_assoc,
    rw ← one_mul (g * h⁻¹ * h),
    rw ← inv_mul_self h,  rw  mul_assoc,
    apply H.mul_mem (H.inv_mem hh),
    rw ← mul_assoc,  apply H.mul_mem _ hh, rw ← mul_assoc,
    exact hg,  -/
  },
  exact  subgroup.conj_of_mem_is_mem H hh,
end

end Subgroups

section Gimme_Some

/-- Get a third element distinct from any two given -/
lemma out_of_three (α : Type*) [decidable_eq α] [fintype α] (hα: 3 ≤ fintype.card α) (x y : α) :
  ∃ (z : α), z ≠ x ∧ z ≠ y :=
begin
  let s := ({ y, x}: finset α),
  have : s.card < fintype.card α,
  exact calc s.card ≤ ({x} : finset α).card + 1 :
        by exact finset.card_insert_le y {x}
    ... ≤ 1 + 1 : by rw finset.card_singleton x
    ... ≤ 2 : by simp only [le_refl]
    ... < fintype.card α : by exact nat.succ_le_iff.mp hα,

  have : sᶜ.card > 0,
  exact calc sᶜ.card = (finset.univ).card - s.card :
        finset.card_univ_diff s
    ... > 0 : by refine lt_tsub_comm.mp this,

  obtain ⟨z, h⟩ := finset.card_pos.mp (gt_iff_lt.mp this),
  have h' : ¬(z ∈ s) := finset.mem_compl.mp h,
  use z,
  split,
  have hxs : x ∈ s,
  { apply finset.mem_insert.mpr ,
    apply or.intro_right,
    refine finset.mem_singleton.mpr rfl , },
  intro hx, rw hx at h', exact h' hxs,
  have hys : y ∈ s, by refine finset.mem_insert_self y {x},
  intro hy, rw hy at h', exact h' hys,
end

/-- Get an element distinct from those of a given list -/
lemma out_of_list (α : Type*) [decidable_eq α] [fintype α]
  (l : list α) (hα: l.length < fintype.card α) :
  ∃ (z : α), ∀ (x : α), x ∈ l → z ≠ x :=
begin
  let s := list.to_finset l,
  have : s.card < fintype.card α :=
    lt_of_le_of_lt (list.to_finset_card_le l) hα,

  have : sᶜ.card > 0,
  exact calc sᶜ.card = (finset.univ).card - s.card :
        finset.card_univ_diff s
    ... > 0 : by refine lt_tsub_comm.mp this,

  obtain ⟨z, h⟩ := finset.card_pos.mp (gt_iff_lt.mp this),
  simp only [finset.mem_compl, list.mem_to_finset] at h,
  use z,
  intros x hx,
  intro hz, rw ← hz at hx,
  exact h hx,
end

end Gimme_Some

section Iwasawa

/-!
## Iwasawa Criterion

We construct an Iwasawa structure for perm α acting on pairs of α.

TODO : Construct an Iwasawa structure for perm α acting on triples of α.

-/

open_locale pointwise
open classical

theorem faithful_on_pairs' (α : Type*) [decidable_eq α] [fintype α]
  (hα : 3 ≤ fintype.card α) (g : perm α) (hg : g ≠ 1) :
  ∃ (x : action_on_pairs_of (perm α) α), g • x ≠ x :=
  --  mul_action.fixed_by (perm α) (action_on_pairs_of (perm α) α) g ≠ ⊤ :=
begin
  have : ∃ (a : α), g • a ≠ a,
    by_contradiction,
    simp at h hg,
    apply hg,
    ext a,
    simp only [perm.coe_one, id.def],
    exact h a,
  obtain ⟨a, ha⟩ := this,
  obtain ⟨c, hc⟩ := out_of_list  α [a, g • a] _,
  swap,
    refine lt_of_lt_of_le _ hα,
    simp only [list.length, list.length_singleton, nat.lt.base],
  have hc : c ≠ a ∧ c ≠ g • a,
  split,
    refine hc _ _, simp,
    refine hc _ _, simp,
  simp only [perm.smul_def] at hc,
  let x : action_on_pairs_of (perm α) α := pair.mk hc.left,
  use x,

 --  intro htop,
 -- rw set.top_eq_univ at htop,
 -- let hx' := set.eq_univ_iff_forall.mp htop x,
 -- simp at hx',
  intro hx',
  let h' := set_like.coe_eq_coe.mpr hx',
  simp only [has_scalar.subpair_apply, pair.is_def, sub_mul_action.coe_smul_of_tower] at h',
  have hc1 : g • a ∈ {g • c, g • a} := is_in_subpair_right ,
  rw h' at hc1, simp only [perm.smul_def] at hc1 ha,
  cases is_in_subpair_iff.mp hc1 with hh1 hh2,
    exact hc.right hh1.symm,
    exact ha hh2,
end


/- Now useless

/-- The stabilizer of a pair is not ⊤ -/
theorem pairs_stabilizers_is_not_top (α : Type*) [decidable_eq α] [fintype α]
  (hα : 3 ≤ fintype.card α) (x : action_on_pairs_of (perm α) α) :
  (stabilizer (perm α) x) ≠ ⊤ :=
begin
  revert x,
  rintro ⟨x,a, b, h_a_ne_b, rfl⟩,
  obtain ⟨c, hc⟩ := out_of_list α [a,b] (lt_of_lt_of_le (nat.lt.base 2) hα),
  let g := equiv.swap a c,
  have g_ab_ne_ab : g • { a, b} ≠ { a, b} ,
  { intro h,
    rw has_scalar.subpair_apply g a b at h,
    have : c = g • a ,
      simp only  [swap_apply_left, perm.smul_def],
    have : c = a ∨ c = b,
    { apply is_in_subpair_iff.mp,
      rw this, rw ←h,
      apply is_in_subpair_left  },
    cases this with ha' hb',
    specialize hc a,
    refine (hc _) ha' ,
    simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
    specialize hc b, refine (hc _) hb',
    simp only [list.mem_cons_iff, eq_self_iff_true, or_true, list.mem_singleton],     },

    have g_ne_stab : ¬(g ∈ (stabilizer (perm α)  ({a,b} : set α))),
    { intro h,
      exact g_ab_ne_ab (mem_stabilizer_iff.mp h), },

    intro h,
    let w := (stabilizer_of_sub_mul (perm α) (action_on_pairs_of (perm α) α)) ⟨{a,b},_⟩,
    rw set_like.coe_mk {a,b} _ at w,
    rw w at h,

    let hg := subgroup.mem_top g,
    rw ← h at hg,

    exact g_ab_ne_ab hg
end

/-- The stabilizer of a pair {a,b} contains the transposition (a b) -/
lemma pairs_stabilizers_maximal.has_swap' (α : Type*) [decidable_eq α] [fintype α]
  (a b : α) :
  equiv.swap a b ∈ stabilizer (perm α) ({a, b} : set α) :=
begin
  rw mem_stabilizer_iff,
  /- change swap a b ∈ { x : perm α | x • ({a, b} : set α) = {a, b} },
  rw set.mem_set_of_eq, -/
  rw has_scalar.subpair_apply,
  simp only [swap_apply_left, perm.smul_def, swap_apply_right],
  exact subpair_symm  , -- b a
end

/-- The stabilizer of a pair {a, b} contains a transposition of the form (a c),
 for some c ∉ {a, b} -/
theorem pairs_stabilizers_maximal.has_swaps (α : Type*) [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α)
  (a b : α) (h_a_ne_b : a ≠ b)
  (H : subgroup (perm α))
  (hH : stabilizer (perm α) ({a,b} : set α) < H) :
  ∃ (c : α), c ≠ a ∧ c ≠ b ∧ swap a c ∈ H :=
begin
  let hH' := le_of_lt hH,
  obtain ⟨h, h_in_H, h_not_in_stab⟩ :=
    (set.ssubset_iff_of_subset hH').mp hH,

  have h_ab : h • ({a, b} : set α) = {h • a, h • b} :=
    has_scalar.subpair_apply h a b,

  have h_ab_ne_ab : h • ({a, b} : set α) ≠ {a, b},
  { intro _,
    apply h_not_in_stab,
    apply mem_stabilizer_iff.mpr,
    assumption },

  have h_ab_H : equiv.swap a b ∈ H,
  { apply  hH',
    apply pairs_stabilizers_maximal.has_swap' },

  cases classical.em (h • a = a) with ha ha',
  { -- h • a = a; then h • b ≠ b
    rw ha at h_ab,
    use h • b,
    split, -- h • b ≠ a
    { intro hba,  apply h_a_ne_b,
      apply smul_left_cancel h,  rw [ha, hba] },
    split, -- h • b ≠ b
    { intro hb, rw hb at h_ab, exact h_ab_ne_ab h_ab, },
    -- swap a (h • b) ∈ H
    rw ← ha,
    simp only [perm.smul_def],
    rw equiv.swap_apply_apply h a b ,
    exact (subgroup.mem_conj_of_mem_iff H h_in_H).mpr h_ab_H },

  -- cas restants : h • a ≠ a
  cases classical.em (h • a = b) with hab hab',
  { -- h • a = b, donc h • b ≠ a,
    rw hab at h_ab,
    use h • b,
    have hb_ne_a : h • b ≠ a,
    { intro hba, rw hba at h_ab, rw h_ab at h_ab_ne_ab,
      apply  h_ab_ne_ab, exact subpair_symm, },
    have hb_ne_b : h • b ≠ b,
    { intro hb, rw ← hb at hab,
      exact h_a_ne_b (smul_left_cancel h hab),  },
    split, exact hb_ne_a,
    split, exact hb_ne_b,
    have : swap a (h • b) = (swap a b) * h * (swap a b) * h⁻¹ * (swap a b),
    { simp only [perm.smul_def],
      -- conjugation with (swap a b)
      apply (mul_right_inj (swap a b)).mp,
      apply (mul_left_inj (swap a b)⁻¹).mp,
      -- simplification of the LHS
      rw ← equiv.swap_apply_apply (swap a b) _ _ ,
      simp only [swap_apply_left, swap_inv],
      have : (swap a b) • (h • b) = h • b :=
        equiv.swap_apply_of_ne_of_ne hb_ne_a hb_ne_b,
      simp only [perm.smul_def] at this,
      rw this,
      -- simplification of the RHS
      simp  [mul_assoc, equiv.mul_swap_mul_self, equiv.swap_mul_self_mul],
      rw ← mul_assoc,
      rw ← equiv.swap_apply_apply h a b,

      simp only [perm.smul_def] at hab,
      rw hab, },
    rw this,

    -- ⊢ swap a b * h * swap a b * h⁻¹ * swap a b ∈ H
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H _ (subgroup.inv_mem H h_in_H),
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H h_ab_H h_in_H },

    -- cas restants : ha', hab' : h • a ≠ a, b
  cases classical.em (h • b = a) with hba hba',
  { -- hba : h • b = a
    use h • a,
    split, exact ha', split, exact hab',
    have : swap a (h • a) = h * (swap a b) * h⁻¹,
    { simp only [perm.smul_def],
      rw ← equiv.swap_apply_apply h _ _ ,
      simp only [perm.smul_def] at hba,
      rw hba,
      rw equiv.swap_comm },
    rw this,

    exact (subgroup.mem_conj_of_mem_iff H h_in_H).mpr h_ab_H  },

  -- cas restants : h • a ≠ a, b ; h • b ≠ a,
  cases classical.em (h • b = b) with hb hb',
  { -- h • b = b
    use h • a,
    split, exact ha',
    split, exact hab',
    have : swap a (h • a) = (swap a b) * h * (swap a b) * h⁻¹ * (swap a b),
    { simp only [perm.smul_def],
      -- conjugation with (swap a b)
      apply (mul_right_inj (swap a b)).mp,
      apply (mul_left_inj (swap a b)⁻¹).mp,
      -- simplification of the LHS
      rw ← equiv.swap_apply_apply (swap a b) _ _ ,
      simp only [swap_apply_left, swap_inv],
      have : (swap a b) • (h • a) = h • a :=
        equiv.swap_apply_of_ne_of_ne ha' hab',
      simp only [perm.smul_def] at this,
      rw this,
      -- simplification of the RHS
      simp  [mul_assoc, equiv.mul_swap_mul_self, equiv.swap_mul_self_mul],
      rw ← mul_assoc,
      rw ← equiv.swap_apply_apply h a b,

      simp only [perm.smul_def] at hb,
      rw hb,
      rw equiv.swap_comm },
    rw this,

    -- ⊢ swap a b * h * swap a b * h⁻¹ * swap a b ∈ H
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H _ (subgroup.inv_mem H h_in_H),
    apply subgroup.mul_mem H _ h_ab_H,
    apply subgroup.mul_mem H h_ab_H h_in_H },

  -- cas restants : a, b, h • a, h • b  are pairwise distinct
  obtain ⟨c, hc⟩ := out_of_list α [a, b, h⁻¹ • a, h⁻¹ • b] _,
  swap,

  exact calc [h⁻¹ • a, h⁻¹ • b, a, b].length = 4 : by simp
    ... < 5 : nat.lt.base 4
    ... ≤ fintype.card α : hα,

  use c,

  split, -- c ≠ a
  { refine hc a _, apply list.mem_cons_self , },
  split, -- c ≠ b
  { refine hc b _, simp only [list.mem_cons_of_mem, list.mem_cons_self] },


  have ta : swap (h • a) (h • c) • a = a,
  { apply equiv.swap_apply_of_ne_of_ne,
    exact ne.symm ha',
    intro hca, specialize hc (h⁻¹ • a), rw hca at hc,
    simp only [perm.smul_def, perm.inv_apply_self, list.mem_cons_iff, true_or, eq_self_iff_true, not_true, ne.def, forall_true_left,
or_true] at hc,
    exact hc },

  have tb : swap (h • a) (h • c) • b = b,
  { apply equiv.swap_apply_of_ne_of_ne, exact ne.symm hab',
    intro hcb,
    have chb : c = h⁻¹ • b,
    { rw hcb , simp, },
    -- specialize hc (h⁻¹ • b), rw chb at hc,
    specialize hc ([a, b, h⁻¹ • a, h⁻¹ • b].last _),
    apply list.cons_ne_nil,
    simp only [perm.smul_def, list.mem_cons_iff, eq_self_iff_true, list.last, ne.def, forall_true_left, or_true, list.mem_singleton,
apply_eq_iff_eq] at hc,
    trivial,  },

  have tH : swap (h • a) (h • c) ∈ H,
  { apply  hH',
    simp only [mem_stabilizer_iff],
    rw has_scalar.subpair_apply,
    rw ta, rw tb },

  have tconj : h * (swap a c) * h⁻¹ = swap (h • a) (h • c),
  { simp only [perm.smul_def],
    rw equiv.swap_apply_apply h _ _, },

  -- subgroup.mul_mem H x y : x ∈ H → y ∈ H → x * y ∈ H
  have tconj' : (swap a c) = h⁻¹ * swap (h • a) (h • c) * h,
  { rw ← tconj,
    rw mul_assoc,
    simp only [inv_mul_cancel_left, inv_mul_cancel_right] },

  rw tconj',
  apply subgroup.mul_mem H _ h_in_H,
  exact subgroup.mul_mem H (subgroup.inv_mem H h_in_H) tH
end


/-- The stabilizers of pairs of elements of α are maximal subgroups -/
theorem pairs_stabilizers_maximal (α : Type*) [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (x : action_on_pairs_of (perm α) α) :
  (stabilizer (perm α) x).is_maximal :=
begin
  apply subgroup.is_maximal_iff.mpr,
  split,
  -- stabilizer is not ⊤
  refine pairs_stabilizers_is_not_top α _ x,
  exact le_trans (le_trans (nat.le_succ 3) (nat.le_succ 4)) hα,

  -- no larger subgroup than stabilizer except ⊤
  { intros H h hH hh hhH,
    let w := stabilizer_of_sub_mul (perm α) (action_on_pairs_of (perm α) α) x,
    obtain ⟨a, b, hab, hx⟩ := x.prop,
    rw hx at w,
    rw w at hH hh,

    have hH' : stabilizer (perm α) {a,b} < H,
    { apply (set.ssubset_iff_of_subset hH).mpr,
      exact ⟨h, hhH, hh⟩ },

    obtain ⟨c, hca, hcb, hc⟩ :=
      pairs_stabilizers_maximal.has_swaps α hα
        a b hab
        H hH',

    apply top_unique,
    rw ← equiv.perm.closure_is_based_swap a,
    apply (subgroup.closure_le H).mpr,
    rintros f ⟨x, rfl⟩ ,
    rw set_like.mem_coe,
    cases classical.em (x = a) with ha ha,
    { -- x = a, swap a a = one,
      rw ha, simp only [swap_self, set_like.mem_coe],
      rw ← equiv.perm.one_def, exact subgroup.one_mem H },
    change x ≠ a at ha,
    cases classical.em (x = b) with hb hb,
    { -- x = b,
      rw hb,
      apply hH,
      exact pairs_stabilizers_maximal.has_swap' α a b },
    change x ≠ b at hb,
    -- x ≠ a, x ≠ b, using (c x) (a c) (c x) = (x a)
    rw swap_comm,
    rw ← swap_mul_swap_mul_swap hca.symm ha.symm,
    have hcx : swap c x ∈ H,
    { apply  hH,
      simp only [mem_stabilizer_iff, has_scalar.subpair_apply,perm.smul_def],
      rw equiv.swap_apply_of_ne_of_ne hca.symm ha.symm,
      rw equiv.swap_apply_of_ne_of_ne hcb.symm hb.symm },
    apply subgroup.mul_mem H _ hcx,
    exact subgroup.mul_mem H hcx hc  }
end

-/



lemma simp_2m_n {m n : ℕ} (h : 2*m < n) : m < n-m :=
begin
  have h' : m ≤ n,
    apply le_of_lt,
    exact calc m ≤ m + m : by simp
          ...    ≤ 2 * m : by rw ← two_mul
          ...    < n : h ,

  refine lt_of_add_lt_add_right _,
  use m, rw ← two_mul,
  rw [add_comm, nat.add_sub_of_le h'],
  exact h,
end


-- variables {α : Type*} [decidable_eq α] [decidable_mem α] [fintype α]

-- TODO
lemma swaps_in_stabilizer {s : set α} {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
  swap a b ∈ stabilizer (perm α) s :=
begin
  simp only [mem_stabilizer_iff],
  suffices : swap a b • s ⊆ s,
    apply set.subset.antisymm_iff.mpr,
    split, exact this,
    intros x hx,
    have this' : x = (swap a b) • ((swap a b) • x),
      rw ← mul_smul,
      simp only [perm.smul_def, perm.coe_one, id.def, swap_mul_self],
    have hx' : (swap a b) • x ∈ s,
      apply this,
      use x, exact ⟨hx, rfl⟩,
      rw this',
      use (swap a b) • x, exact ⟨hx', rfl⟩,
  rintros _ ⟨x, hx, rfl⟩,
  cases classical.em (x = a) with hxa hxa',
    rw hxa, simp only [swap_apply_left, perm.smul_def], exact hb,
    cases classical.em (x = b) with hxb hxb',
    rw hxb, simp only [swap_apply_right, perm.smul_def], exact ha,
    rw [perm.smul_def, equiv.swap_apply_of_ne_of_ne hxa' hxb'], exact hx,
end


theorem subset_stabilizer_ne_top (α : Type*) [decidable_eq α] [fintype α]
  (s : set α) (hs : s.nonempty) (hs' : sᶜ.nonempty) :
  (stabilizer (perm α) s) ≠ ⊤ :=
begin
  obtain ⟨a : α, ha : a ∈ s⟩ := hs,
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := hs',
  intro h,
  let g := equiv.swap a b,
  have h' : g ∈ ⊤ :=  subgroup.mem_top g,
  rw [← h , mem_stabilizer_iff] at h',
  rw set.mem_compl_eq at hb,
  apply hb,
  rw ← h',
  use a,
  exact and.intro ha (equiv.swap_apply_left a b)
end


lemma ne_stabilizer_of_finite_ne_incl (α : Type*)  -- [decidable_eq α] [fintype α]
  (s : set α) (hfs : s.finite)
  (h : perm α) (hH : h ∉ stabilizer (perm α) s):
  ∃ x, (x ∈ s) ∧ (h • x ∉ s) :=
begin
  have hfhs : (h • s).finite,
    change ((λ x, h • x) '' s).finite,
    exact set.finite.image (λ (x : α), h • x) hfs,

  rw mem_stabilizer_iff at hH,

  by_contradiction hK,
  simp only [not_exists, perm.smul_def, not_and, set.not_not_mem] at hK,
  apply hH,
  apply set.subset.antisymm,

  rintros _ ⟨x, hx, rfl⟩, rw perm.smul_def, exact hK x hx,

  intros x hx,

  obtain ⟨a, ha, rfl⟩ :=
  let f : Π (a : α), a ∈ hfs.to_finset → α := λ x hx, h • x
  in
  let hf : ∀ (a : α) (ha : a ∈ hfs.to_finset), f a ha ∈ hfs.to_finset := λ x hx,
  begin
    simp only [set.finite.mem_to_finset] at hx ⊢,
    exact hK x hx
  end
  in
  let hinj : ∀ (a₁ a₂ : α)  (ha₁ : a₁ ∈ hfs.to_finset) (ha₂ : a₂ ∈ hfs.to_finset),  f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂ :=
    λ a₁ a₂ ha₁ ha₂ heq, mul_action.injective h heq
  in
  let hst : hfs.to_finset.card ≤ hfs.to_finset.card := rfl.le
  in
  finset.surj_on_of_inj_on_of_card_le f hf hinj hst
    x ((set.finite.mem_to_finset hfs).mpr hx),

  use a,
  exact ⟨(set.finite.mem_to_finset hfs).mp ha, rfl⟩,
end

lemma set.ne_mem_compl_eq (s : set α) (x : α) : x ∉ sᶜ = (x ∈ s) :=
begin
  conv_rhs {rw ← compl_compl s},
  apply symm,
  exact set.mem_compl_eq sᶜ _,
end


/-- Stabilizers of nontrivial subsets s of α are maximal subgroups of perm α
provided 2 * s.to_finset.card < fintype.card α -/
theorem  subset_stabilizer_maximal (α : Type*) [decidable_eq α] [fintype α]
  (s : set α) (hs0 : s.nonempty) (h_2s_lt_top : 2 * s.to_finset.card < fintype.card α) :
  (stabilizer (perm α) s).is_maximal :=
begin
  have hs_le_sc : s.to_finset.card < (s.to_finset)ᶜ.card,
    rw finset.card_compl ,
    exact simp_2m_n  h_2s_lt_top,

  rw subgroup.is_maximal_iff,
  split,
    apply subset_stabilizer_ne_top α s hs0,
    suffices : (s.to_finset)ᶜ.nonempty,
      obtain ⟨x, hx⟩ := this,
      simp only [finset.mem_compl, set.mem_to_finset] at hx,
      use x,
    apply finset.card_pos.mp,
    apply lt_of_le_of_lt (zero_le s.to_finset.card),
    exact hs_le_sc,

  intros H h hSH hhS hhH,
  apply top_unique,
  rw ← equiv.perm.closure_is_swap,
  apply (subgroup.closure_le H).mpr,
  rintros σ ⟨a, b, ha_ne_b, rfl⟩,
  suffices : ∀(a b : α), ((a ∈ s ∧ b ∈ s) ∨ (a ∈ s ∧ b ∉ s) ∨ (a ∉ s ∧ b ∉ s))
      → swap a b ∈ H,
    cases classical.em (a ∈ s) with ha ha',
    cases classical.em (b ∈ s) with hb hb',
      apply this a b,
      apply or.intro_left, exact ⟨ha, hb⟩,
      apply this a b,
      apply or.intro_right, apply or.intro_left,  exact ⟨ha, hb'⟩,

    cases classical.em (b ∈ s) with hb hb',
      rw equiv.swap_comm ,
      apply this b a,
      apply or.intro_right, apply or.intro_left, exact ⟨hb, ha'⟩,
      apply this a b,
      apply or.intro_right, apply or.intro_right, exact ⟨ha', hb'⟩,

  intros a b hab,
  cases hab with hab hab',
  -- a ∈ s ∧ b ∈ s
    apply hSH,
    exact swaps_in_stabilizer hab.left hab.right,
  cases hab' with hab hab,
  swap,
  -- a ∉ s ∧ b ∉ s
    apply hSH,
    rw stabilizer_compl,
    exact swaps_in_stabilizer hab.left hab.right,

  -- a ∈ s ∧ b ∉ s
  have hhSc : h ∉ stabilizer (perm α) sᶜ,
    rw stabilizer_compl at hhS, exact hhS,

  -- we construct a transposition (a b) in H
  -- that maps some a ∈ s to some b ∉ s
   have : ∃(a b : α) (ha : a ∈ s) (hb : b ∉ s), swap a b ∈ H,
   { -- there is an element of sᶜ that is mapped to s
    -- this uses the hypothesis on h
    have this_x : ∃ x, x ∈ sᶜ ∧ h • x ∉ sᶜ,
    { apply ne_stabilizer_of_finite_ne_incl,
      exact set.finite.of_fintype sᶜ,
      rw stabilizer_compl at hhS,
      exact hhS },

    -- there is some element of sᶜ that is mapped to sᶜ
    -- only uses that s.card < sᶜ.card
    have this_y : ∃ y, y ∈ sᶜ ∧ h • y ∈ sᶜ,
    { by_contradiction hyp_H,
      simp only [not_and, not_exists] at hyp_H,
        apply not_le.mpr hs_le_sc,
        refine finset.card_le_card_of_inj_on _ _ _,
          exact λ x, h • x,
          { intros x hx,
            simp only [set.mem_to_finset],
            rw ← compl_compl s,
            apply set.mem_compl,
            apply hyp_H x,
            simpa using hx },
          { intros a₁ ha₁ a₂ ha₂ hf,
            exact mul_action.injective h hf } },

    -- h (x y) h⁻¹ = (hx hy) = (a b)
    obtain ⟨x, hx⟩ := this_x,
    obtain ⟨y, hy⟩ := this_y,
    use h • x, use h • y,
    simp only [exists_prop, perm.smul_def, set.not_not_mem, set.mem_compl_eq] at hx hy ⊢,
    apply and.intro hx.right,
    apply and.intro hy.right,

    rw equiv.swap_apply_apply,
    rw (subgroup.mem_conj_of_mem_iff H hhH),

    apply hSH,    rw stabilizer_compl,
    apply swaps_in_stabilizer,
    exact hx.left, exact hy.left },

  obtain ⟨a', b', ha', hb', this⟩ := this,

  have haa' : swap a a' ∈ H := hSH (swaps_in_stabilizer hab.left ha'),
  apply (subgroup.mem_conj_of_mem_iff H haa').mp,
  rw equiv.swap_inv,
  rw equiv.swap_comm a b,
  rw equiv.swap_mul_swap_mul_swap _ _,
   swap, -- b ≠ a
  { intro h, rw h at hab, exact hab.right hab.left, },
  swap, -- b ≠ a'
  { intro h, rw ← h at ha', exact hab.right ha', },

  have hbb' : swap b b' ∈ H,
  { rw stabilizer_compl at hSH,
    exact hSH (swaps_in_stabilizer (hab.right) hb') },
  apply (subgroup.mem_conj_of_mem_iff H hbb').mp,
  rw equiv.swap_inv,
  rw equiv.swap_mul_swap_mul_swap _ _,
  rw equiv.swap_comm, exact this,
  -- a' ≠ b,  bis repetita
  { intro h, rw h at ha', exact hab.right ha', },
  -- a' ≠ b',
  { intro h, rw h at ha', exact hb' ha', },
end

/-- If α has at least 5 elements, then
the stabilizers of pairs of elements of α are maximal subgroups -/
theorem pairs_stabilizers_maximal (α : Type*) [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) (x : action_on_pairs_of (perm α) α) :
  (stabilizer (perm α) x).is_maximal :=
begin
  rw stabilizer_of_sub_mul,
  apply subset_stabilizer_maximal,

  apply (set.finite.to_finset.nonempty _).mp,
  apply finset.card_pos.mp,
  rw pair.card_eq_two x,
  simp only [nat.succ_pos'],

  have : (x : set α).to_finset = (pair.is_finite x).to_finset,
  { apply finset.coe_inj.mp,
    rw [set.finite.coe_to_finset, set.coe_to_finset], },
  rw [this, pair.card_eq_two x],
  exact le_trans (le_refl _) hα,
end

/-- If α has at least 5 elements, then
the action of the symmetric groups on pairs is primitive -/
def perm.action_on_pairs.primitive {α : Type*} [decidable_eq α] [fintype α] (hα : 5 ≤ fintype.card α) :
  is_primitive (perm α) (action_on_pairs_of (perm α) α) :=
{
is_nonempty :=
  begin
  have h1 : ∀ (a : α), [a].length < fintype.card α,
  { intro a,
    rw list.length_singleton _,
    refine lt_of_lt_of_le _ hα,
    simp only [nat.one_lt_succ_succ] },
  have h0 : ([] : list α).length < fintype.card α,
  { simp, refine lt_of_lt_of_le _ hα, refine nat.succ_pos',  },
  obtain ⟨a, ha⟩ := out_of_list α ([] : list α) h0,
  obtain ⟨b, hb⟩ := out_of_list α [a] (h1 a),
  have hab : b ≠ a,
    apply (hb a),
    simp only [list.mem_singleton],
  use (pair.mk hab),
end,
exists_smul_eq := transitive_on_pairs.exists_smul_eq ,
has_maximal_stabilizers := λ x,
begin
  refine pairs_stabilizers_maximal α hα x,
end
}

noncomputable
def pair.swap (x : action_on_pairs_of (perm α) α) : perm α :=
  swap (pair.lift x).1 (pair.lift x).2

def pair.swap.is_swap (x : action_on_pairs_of (perm α) α) :
  equiv.perm.is_swap (pair.swap x)  :=
begin
  use (pair.lift x).1, use (pair.lift x).2,
  split,
  exact pair.lift.ne x,
  refl,
end

def pair.apply_eq (g : perm α) (x : action_on_pairs_of (perm α) α) :
  (g • x : set α) = { g • ((pair.lift x).1) , g • ((pair.lift x).2) } :=
begin
  rw ← has_scalar.subpair_apply,
  rw pair.lift.spec x,
 end

def pair.swap.swap_eq (x : action_on_pairs_of (perm α) α) {a b : α}
  (h : (x : set α) = {a, b}) : pair.swap x = swap a b :=
begin
  have : ({(pair.lift x).1, (pair.lift x).2 } : set α) = {a, b},
  { rw pair.lift.spec x at h, exact h,  },
  unfold pair.swap,
  cases subpair_eq_iff.mp this with H H,
  rw [H.left, H.right],
  rw [H.left, H.right, equiv.swap_comm]
end

def pair.swap.conj_swap (g : perm α) (x : action_on_pairs_of (perm α) α) :
  pair.swap (g • x) = (mul_aut.conj g).to_monoid_hom (pair.swap x) :=
begin
  unfold pair.swap,
  simp only [perm.smul_def, mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply],
  rw ← equiv.swap_apply_apply,
  apply pair.swap.swap_eq, apply pair.apply_eq,
end


/- Useless
/-- An Iwasawa structure on the product α × α -/
def perm.iwasawa (α : Type*) [decidable_eq α] [fintype α]:
Iwasawa_Criterion.has_iwasawa_structure (perm α) (α × α) :=
{ T := λ x, subgroup.closure { equiv.swap x.1 x.2 },
  is_comm := λ x, subgroup.closure.of_singleton_is_commutative (equiv.swap x.1 x.2),
  is_conj := λ g x,
  begin
    have : (mul_aut.conj g).to_monoid_hom '' ({swap x.1 x.2} : set (perm α))
      = { swap ((g • x).1) ((g • x).2) },
    { simp only [set.image_singleton, perm.smul_def, mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply, set.singleton_eq_singleton_iff],
      apply symm,
      apply equiv.swap_apply_apply,  },
    rw ← this,
    rw ← monoid_hom.map_closure (mul_aut.conj g).to_monoid_hom ({ swap x.1 x.2} : set (perm α)),
    simp only [subgroup.pointwise_smul_def,
    mul_distrib_mul_action.to_monoid_End_apply],
    refl,
  end,
  is_generator :=
  begin
    apply top_unique,
    rw ← closure_is_swap,
    let H := ⨆ (x : α × α), subgroup.closure {swap x.fst x.snd},
    -- refine w _,
    refine (subgroup.closure_le H).mpr _,
    intros σ hσ,
    obtain ⟨a,b, hab, rfl⟩ := hσ,
    refine subgroup.mem_supr_of_mem _ _,
    use ⟨a,b⟩,
    simp only,
    generalize : swap a b = σ,
    exact subgroup.subset_closure (set.mem_singleton σ),
  end,
}
-/

/-- An Iwasawa structure for (perm α) acting on pairs -/
def perm.iwasawa' (α : Type*) [decidable_eq α] [fintype α]:
Iwasawa_Criterion.has_iwasawa_structure (perm α) (action_on_pairs_of (perm α) α) :=
{ T := λ x, subgroup.closure ({ pair.swap x } : set (perm α)),
  is_comm := λ x, subgroup.closure.of_singleton_is_commutative _ ,
  is_conj := λ g x,
  begin
    have : { pair.swap (g • x) } = (mul_aut.conj g).to_monoid_hom '' ({ pair.swap x } : set (perm α)),
    { rw pair.swap.conj_swap g x,
      simp only [set.image_singleton],
    },
    rw this,
    rw ← monoid_hom.map_closure (mul_aut.conj g).to_monoid_hom ({ pair.swap x } : set (perm α)),
    simp only [subgroup.pointwise_smul_def,
    mul_distrib_mul_action.to_monoid_End_apply],
    refl
  end,
  is_generator :=
  begin
    apply top_unique,
    rw ← closure_is_swap,
    let H := ⨆ x, subgroup.closure {pair.swap x},
    refine (subgroup.closure_le H).mpr _,
    intros σ hσ,
    obtain ⟨a,b, hab, rfl⟩ := hσ,
    let x : action_on_pairs_of (perm α) α := ⟨({a,b} : set α), _ ⟩,
      swap,
      split, swap, use a, use b, split, exact hab, exact rfl,
    suffices : pair.swap x = swap a b,
      rw ← this,
      refine subgroup.mem_supr_of_mem x _,
      apply subgroup.subset_closure,
      apply set.mem_singleton,

    apply pair.swap.swap_eq x,
    simp only [subtype.coe_mk],
  end,
}

-- The main theorem, unfortunately weaker than expected
/-- If α has at least 5 elements, then
the only nontrivial normal sugroup of (perm α) is the alternating_group. -/
theorem perm.normal_subgroup {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α)
  {N : subgroup (perm α)} (hnN : N.normal) (ntN : nontrivial N) : alternating_group α  ≤ N :=
begin
  rw ← alternating_group.is_commutator hα,
  refine Iwasawa_Criterion.Iwasawa_mk (perm α) (action_on_pairs_of (perm α) α) _ _ N hnN _,
  exact perm.action_on_pairs.primitive hα,
  exact perm.iwasawa' α ,

  intro h,
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN,
  obtain ⟨x, hx⟩ := faithful_on_pairs' α _ g hg_ne,
  swap,
    refine le_trans _ hα,
    simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
  apply hx,
  let hx' := set.eq_univ_iff_forall.mp h x,
  simp at hx',

  change (subtype.mk g hgN) • x = x,
  apply hx' ,
end


/-
subtype.coe_mk : ∀ (a : ?M_1) (h : ?M_2 a), ↑⟨a, h⟩ = a
set_like.coe_mk : ∀ (x : ?M_2) (hx : x ∈ ?M_4), ↑⟨x, hx⟩ = x

set_like.mem_coe : ?M_5 ∈ ↑?M_4 ↔ ?M_5 ∈ ?M_4
set_like.coe_mem : ∀ (x : ↥?M_4), ↑x ∈ ?M_4

set_like.eta : ∀ (x : ↥?M_4) (hx : ↑x ∈ ?M_4), ⟨↑x, hx⟩ = x
-/

open list

lemma list.cycle_type_form_perm' (l : list α) (hl : l.nodup) (hn : 2 ≤ l.length) :
  l.form_perm.cycle_type = {l.length} :=
begin
  rw cycle_type_eq [l.form_perm],
  { simp only [map, function.comp_app],
    rw [support_form_perm_of_nodup _ hl, card_to_finset, erase_dup_eq_self.mpr hl],
    { simpa },
    { intros x h,
      simpa [h, nat.succ_le_succ_iff] using hn } },
  { simp },
  { simpa using is_cycle_form_perm hl hn },
  { simp }
end

namespace alternating_group

theorem subset_stabilizer_ne_top (α : Type*) [decidable_eq α] [fintype α]
  (s : finset α) (hs : s.nonempty) (hs' : sᶜ.card ≥ 2) :
  (stabilizer (alternating_group α) s) ≠ ⊤ :=
begin
  obtain ⟨a : α, ha : a ∈ s⟩ := hs,
  have : sᶜ.nonempty,
  { rw ← finset.card_pos, apply lt_of_lt_of_le _ hs', norm_num,},
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := this,
  have : ∃ (c : α), c ≠ b ∧ c ∈ sᶜ,
  { suffices : (sᶜ.erase b).nonempty,
      obtain ⟨c, hc⟩ := this,
      use c, rw ← finset.mem_erase, exact hc,
    rw ← finset.card_pos,
    apply lt_of_lt_of_le _ finset.pred_card_le_card_erase ,
    simp only [tsub_pos_iff_lt],
    apply lt_of_lt_of_le _ hs', norm_num },
  obtain ⟨c, hc', hc⟩ := this,
  rw finset.mem_compl at hb hc,
  let l := [a,b,c],
  have hl : l.nodup,
  -- g.is_cycle,
  { -- apply list.is_cycle_form_perm _, norm_num,
    rw list.nodup_cons, split,
    { intro habc,
      simp only [list.mem_cons_iff, list.mem_singleton] at habc,
      cases habc with h h,
        rw h at ha, exact hb ha,
        rw h at ha, exact hc ha,  },
    simp only [list.not_mem_nil, and_true, not_false_iff, list.nodup_cons, list.mem_singleton, list.nodup_nil],
    exact hc'.symm },
  let g := l.form_perm,
  have hg : g ∈ alternating_group α,
  { apply equiv.perm.is_three_cycle.mem_alternating_group ,
    rw equiv.perm.is_three_cycle,
    apply list.cycle_type_form_perm',
    exact hl, norm_num, },

  intro h,
  let hg' := subgroup.mem_top (⟨g,hg⟩ : alternating_group α),
  rw ← h at hg',
  rw @mem_stabilizer_iff (alternating_group α) _ _ _ _ _ at hg',
  unfold has_scalar.smul at hg',
  simp only [perm.smul_def, submonoid.coe_subtype, has_scalar.comp.smul, subgroup.coe_mk] at hg',
  apply hb, rw ← hg',
  rw finset.mem_image,
  use a, apply and.intro ha,
  rw list.form_perm_apply_mem_eq_next hl,
  norm_num,
  apply list.mem_cons_self
end

/-- Stabilizers of nontrivial subsets s of α are maximal subgroups of perm α
provided 2 * s.to_finset.card < fintype.card α -/
theorem  subset_stabilizer_maximal (α : Type*) [decidable_eq α] [fintype α]
  (s : finset α) (hs0 : s.nonempty) (h_2s_lt_top : 2 * s.card < fintype.card α) :
  (stabilizer (alternating_group α) s).is_maximal :=
begin
  have hs_le_sc : s.card < sᶜ.card,
    { rw finset.card_compl ,  exact simp_2m_n  h_2s_lt_top },
  rw subgroup.is_maximal_iff,
  split,
  { apply subset_stabilizer_ne_top,
    exact hs0,
    apply lt_of_le_of_lt _ hs_le_sc ,
    rw nat.succ_le_iff, exact finset.card_pos.mpr hs0 },

  sorry
end


theorem is_simple
  (hα : 5 ≤ fintype.card α) : is_simple_group (alternating_group α) :=
{exists_pair_ne :=
begin
  apply (alternating_group.nontrivial_of_three_le_card _).exists_pair_ne,
  apply le_trans _ hα,
  simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
end,
  eq_bot_or_eq_top_of_normal := λ N nN,
begin
  sorry,
end}


/- Apparently, one cannot conclude by this method -/
theorem is_simple' {α : Type*} [decidable_eq α] [fintype α]
  (hα : 5 ≤ fintype.card α) : is_simple_group (alternating_group α) :=
{ exists_pair_ne :=
begin
  apply (alternating_group.nontrivial_of_three_le_card _).exists_pair_ne,
  apply le_trans _ hα,
  simp only [bit1_le_bit1, nat.lt_one_iff, nat.one_le_bit0_iff],
end,
  eq_bot_or_eq_top_of_normal := λ N nN,
begin
  cases classical.em (N = ⊥) with htN hntN,
    exact or.intro_left _ htN,
  apply or.intro_right _,
  let j := subgroup.subtype (alternating_group α),
  let N' := subgroup.map j N,
  have hnN' : N'.normal,


  sorry,
end
}



end Iwasawa
