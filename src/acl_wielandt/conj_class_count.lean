/-
Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL
-/

import tactic
import logic.equiv.basic
import tactic.basic tactic.group
import group_theory.subgroup.basic
import group_theory.group_action.sub_mul_action
import group_theory.group_action.embedding
import group_theory.perm.cycle.type
import group_theory.perm.list
import group_theory.perm.cycle.basic
import group_theory.perm.cycle.concrete

import group_theory.group_action.quotient
import group_theory.specific_groups.alternating
-- import group_theory.abelianization

-- import group_theory.sylow

-- import .sub_mul_actions
-- import .multiple_transitivity
-- import .for_mathlib.extensions

import .equivariant_map

open_locale pointwise

/- instance pi.mul_one_class' {I : Type*} {f : I → Type*} {p : I → Prop}
[Π (i : I) (pi : p i), mul_one_class (f i)] :
mul_one_class (Π (i : I) (pi : p i), f i) :=
begin
  refine {
  one := λ i hi, _,
  mul := λ u v i hi,
  begin
    haveI : mul_one_class (f i) := _inst_1 i hi,
    exact (u i hi) * (v i hi),
  end,
  one_mul := λ u, begin
    ext i hi,
    dsimp, convert (_inst_1 i hi).one_mul (u i hi),
    end,
  mul_one := λ u, begin
    ext i hi,
    dsimp, convert (_inst_1 i hi).mul_one (u i hi),
    end, },
end

instance pi.group' {I : Type*} {f : I → Type*} {p : I → Prop}
[Π (i : I) (pi : p i), group (f i)] :
group (Π (i : I) (pi : p i), f i) :=
begin
  refine_struct {
  mul_assoc := λ u v w,
  begin
    ext i hi,
    haveI : group (f i) := _inst_1 i hi,
    dsimp,

    exact u i hi * v i hi * w i hi = u i hi * (v i hi * w i hi),
  end,
  inv := sorry,
  mul_left_inv := sorry,
.. },
end

 -/

/-
lemma function.extend_apply_first {α β γ : Type*}
  (f : α → β) (g : α → γ) (e' : β → γ)
  (hf : ∀ (a b : α), f a = f b → g a = g b) (a : α) :
  function.extend f g e' (f a) = g a :=
begin
  classical,
  simp only [function.extend_def, dif_pos, exists_apply_eq_apply],
  apply hf,
  exact (classical.some_spec (exists_apply_eq_apply f a)),
end

lemma function.extend_apply_first {α β γ : Type*}
  (f : α → β) (g : α → γ) (e' : β → γ)
  (hf : ∀ (a b : α), f a = f b → g a = g b) (a : α) :
  function.extend f g e' (f a) = g a := function.factors_through.extend_apply hf e' a


-/


/-
def subgroup.mul_equiv {α β : Type*} [group α] [group β] (e : mul_equiv α β)
  {G : subgroup α} {H : subgroup β} (h : ∀ g, g ∈ G ↔ e g ∈ H) :
  mul_equiv G H :=
{ to_fun := subtype.map e.to_fun (λ g hg, (h g).mp hg), -- λ ⟨g, hg⟩, ⟨e g, h.mp hg⟩,
  inv_fun := subtype.map e.inv_fun (λ k hk,
    by simp only [h, mul_equiv.inv_fun_eq_symm, mul_equiv.apply_symm_apply, hk]),
  left_inv := λ ⟨g, hg⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [subtype.map_coe],
    simp only [mul_equiv.to_fun_eq_coe, mul_equiv.inv_fun_eq_symm, mul_equiv.symm_apply_apply],
  end,
  right_inv := λ ⟨k, hk⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [subtype.map_coe],
    simp only [mul_equiv.inv_fun_eq_symm, mul_equiv.to_fun_eq_coe, mul_equiv.apply_symm_apply],
  end,
  map_mul' := λ ⟨g, hg⟩ ⟨k, hk⟩,
  begin
    simp only [← subtype.coe_inj],
    rw subgroup.coe_mul,
    simp only [subtype.map_coe],
    simp only [mul_mem_class.mk_mul_mk, subgroup.coe_mk, mul_equiv.to_fun_eq_coe, map_mul],
  end, }
-/

section lists

variables {α β : Type*}

lemma list.disjoint_map (f : α → β) (s t : list α)
  (hf : function.injective f) (h : list.disjoint s t) :
  list.disjoint (s.map f) (t.map f) :=
begin
  simp only [list.disjoint],
  intros b hbs hbt,
  rw list.mem_map at hbs hbt,
  obtain ⟨a, ha, rfl⟩ := hbs,
  apply h ha,
  obtain ⟨a', ha', ha''⟩ := hbt,
  rw hf ha''.symm, exact ha',
end

lemma list.disjoint_pmap {p : α → Prop} (f : Π (a : α), p a → β) (s t : list α)
  (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
  (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
  (h : list.disjoint s t) : list.disjoint (list.pmap f s hs) (list.pmap f t ht) :=
begin
  simp only [list.disjoint],
  intros b hbs hbt,
  rw list.mem_pmap at hbs hbt,
  obtain ⟨a, ha, rfl⟩ := hbs,
  apply h ha,
  obtain ⟨a', ha', ha''⟩ := hbt,
  rw hf a a' (hs a ha) (ht a' ha') ha''.symm,
  exact ha',
end

def list.mk_subtype {p : α → Prop} :
  Π (l : list α) (hl : ∀ a ∈ l, p a), list (subtype p)
| [] := λ _, list.nil
| (a :: l) := λ hl, (⟨a, hl a (list.mem_cons_self a l)⟩ ::
  list.mk_subtype l (λ b hb, hl b (list.mem_cons_of_mem a hb)))

lemma list.coe_mk {p :α → Prop} (l : list α) (hl : ∀ a ∈ l, p a) :
  list.map coe (list.mk_subtype l hl) = l :=
begin
  induction l with a l' hl',
  -- nil
  simp only [list.mk_subtype, list.map_nil],
  -- (a :: l)
  simp only [list.mk_subtype, list.map_cons],
  split,
  simp only [subtype.coe_mk],
  apply hl',
end

def list.mk_subtype' {p : α → Prop} (l : list α) (hl : ∀ a ∈ l, p a) :
  list (subtype p) :=
  list.pmap (λ (a : α) (ha : p a), (⟨a, ha⟩ : subtype p)) l hl

lemma list.coe_mk' {p :α → Prop} (l : list α) (hl : ∀ a ∈ l, p a) :
  list.map coe (list.mk_subtype' l hl) = l :=
begin
  simp only [list.mk_subtype'],
  rw list.map_pmap,
  rw list.pmap_congr,
  rw list.pmap_eq_map,
  rw list.map_id,
  exact hl,
  intros a ha hpa _,
  simp only [subtype.coe_mk, id.def],
end

example [decidable_eq α] (p : α → Prop) [decidable_pred p] (s : finset α) (hs : ∀ a ∈ s, p a) :
  finset.image coe (finset.subtype p s) = s :=
begin
  ext,
  simp only [finset.mem_image, finset.mem_subtype, exists_prop, subtype.exists,
    subtype.coe_mk, exists_eq_right_right, and_iff_right_iff_imp],
  exact hs a,
end

example (f : α → β) (hf : function.injective f) (l : list (set α))
  (hl : list.pairwise disjoint l) :
  list.pairwise disjoint (list.map (set.image f) l) :=
begin
  rw list.pairwise_map,
  simp_rw set.disjoint_image_iff hf,
  exact hl,
end

end lists


lemma equiv.perm.disjoint_iff_support_disjoint
  {α : Type*} [fintype α] [decidable_eq α] {f g : equiv.perm α} :
  f.disjoint g ↔ disjoint f.support g.support :=
by simp only [equiv.perm.disjoint_iff_eq_or_eq, finset.disjoint_iff_inter_eq_empty , ← equiv.perm.not_mem_support, ← finset.mem_compl, ← finset.mem_union, ← finset.compl_inter, ← finset.compl_eq_univ_iff, ← finset.eq_univ_iff_forall]

/-
section stabilizers

variables {G : Type*} [group G] {X : Type*} [mul_action G X] (s : set X)

open_locale pointwise

variables (G s)
def sub_mul_action_of_stabilizer : sub_mul_action (mul_action.stabilizer G s) X :=
{ carrier := s,
  smul_mem' := λ g x hx,
  begin
    have h : g • x ∈ g • s := ⟨x, hx, rfl⟩,
    let hg := g.prop, rw mul_action.mem_stabilizer_iff at hg,
    change g • s = s at hg,
    rw hg at h, exact h,
  end}

instance mul_action_of_stabilizer : mul_action (mul_action.stabilizer G s) s :=
  (sub_mul_action_of_stabilizer G s).mul_action

variables {G s}
def sub_mul_action_of_stabilizer_hom : mul_action.stabilizer G s →* equiv.perm s :=
  mul_action.to_perm_hom (mul_action.stabilizer G s) s

lemma sub_mul_action_of_stabilizer_hom_def
  (g : G) (hg : g ∈ mul_action.stabilizer G s) (x : X) (hx : x ∈ s) :
  ↑(sub_mul_action_of_stabilizer_hom (⟨g, hg⟩ : mul_action.stabilizer G s) (⟨x, hx⟩ : s)) = g • x :=
begin
  simp only [sub_mul_action_of_stabilizer_hom],
  simp only [mul_action.to_perm_hom_apply, mul_action.to_perm_apply],
  refl,
end

end stabilizers -/



section ranges

def list.ranges : list ℕ → list (list ℕ)
  | [] := list.nil
  | (a :: l) := (list.range(a) :: list.map (list.map (nat.add a)) (list.ranges l))

-- #eval list.ranges [2,5,4]

lemma list.ranges_disjoint (l : list ℕ) : list.pairwise list.disjoint (list.ranges l) :=
begin
  induction l with a l hl,
  -- nil
  exact list.pairwise.nil,
  -- (a :: l)
  simp only [list.ranges, list.pairwise_cons],
  split,
  { intros s hs,
    obtain ⟨s', hs', rfl⟩ := list.mem_map.mp hs,
    intros u hu,
    rw list.mem_map, rintro ⟨v, hv, rfl⟩,
    rw list.mem_range at hu,
    exact lt_iff_not_le.mp hu (le_self_add), },
  { rw list.pairwise_map,
    apply list.pairwise.imp _ hl,
    intros u v, apply list.disjoint_map _ u v _,
    exact λ u v, nat.add_left_cancel, },
end

lemma list.ranges_nodup (l : list ℕ) : ∀ s ∈ list.ranges l, list.nodup s :=
begin
  induction l with a l hl,
  { -- nil
    intros s hs, exfalso,
    simpa only [list.ranges, list.not_mem_nil] using hs, },
  { -- (a :: l)
    intros s hs,
    simp only [list.ranges, list.mem_cons_iff] at hs,
    cases hs with hs hs,
      -- s = a
      rw hs, exact list.nodup_range a,
      -- s ∈ l
      rw list.mem_map at hs, obtain ⟨t, ht, rfl⟩ := hs,
      refine list.nodup.map (λ u v, nat.add_left_cancel) (hl t ht), }
end

lemma list.ranges_length (l : list ℕ) :
  list.map (list.length) l.ranges = l :=
begin
  induction l with a l hl,
  -- nil
  simp only [list.ranges, list.map_nil],
  -- (a :: l)
  simp only [list.ranges, list.map_cons],
  split,
  exact finset.card_range a,
  simp only [list.map_map],
  conv_rhs { rw ← hl },
  apply list.map_congr,
  intros s hs,
  simp only [function.comp_app],
  rw list.length_map,
end

lemma list.ranges_lt (l : list ℕ) {s : list ℕ} {n : ℕ} (hs : s ∈ list.ranges l)
  (hn : n ∈ s) : n < l.sum :=
begin
  revert s n,
  induction l with a l hl,
  { -- nil
    intros s n hs hn,
    exfalso,
    simp only [list.ranges] at hs,
    exact list.not_mem_nil s hs, },
  { -- (a :: l)
    intros s n hs hn,
    simp only [list.ranges, list.mem_cons_iff] at hs,
    cases hs with hs hs,
    { rw [hs, list.mem_range] at hn,
      apply lt_of_lt_of_le hn,
      rw list.sum_cons,
      exact le_self_add, },
    { rw list.mem_map at hs, obtain ⟨t, ht, rfl⟩ := hs,
      rw list.mem_map at hn, obtain ⟨m, hm, rfl⟩ := hn,
      simp only [list.sum_cons, nat.add_def, add_lt_add_iff_left],
      exact hl ht hm, }, },
end

end ranges

section cycle_types

variables (α : Type*) [decidable_eq α] [fintype α]

def equiv.perm_with_cycle_type (c : multiset ℕ) :=
  finset.filter (λ (g : equiv.perm α), equiv.perm.cycle_type g = c) finset.univ

variable {α}
lemma equiv.perm_with_cycle_type_empty {c : multiset ℕ} (hc : fintype.card α < c.sum) :
  equiv.perm_with_cycle_type α c = ∅ :=
begin
  apply finset.eq_empty_of_forall_not_mem,
  intro g,
  unfold equiv.perm_with_cycle_type,
  simp only [set.to_finset_univ, finset.mem_filter, finset.mem_univ, true_and],
  intro hg, apply lt_iff_not_le.mp hc, rw ← hg,
  rw equiv.perm.sum_cycle_type,
  refine (equiv.perm.support g).card_le_univ,
end

lemma list.exists_pw_disjoint_with_card {c : list ℕ} (hc : c.sum ≤ fintype.card α) :
  ∃ (o : list (list α)),
  (list.map (list.length) o = c) ∧ (∀ s ∈ o, list.nodup s) ∧ list.pairwise list.disjoint o :=
begin
  have : nonempty (fin (fintype.card α) ≃ α) := by simp only [← fintype.card_eq, fintype.card_fin],
  have e := this.some,

  let klift : Π (n : ℕ), (n < fintype.card α) → fin (fintype.card α) :=
    λ n hn, (⟨n, hn⟩ : fin(fintype.card α)),

  let klift' : Π (l : list ℕ), (∀ a ∈ l, a < fintype.card α) → list (fin (fintype.card α)) :=
  list.pmap klift,

  have hc'_lt : ∀ (a : list ℕ), a ∈ c.ranges → ∀ (a_1 : ℕ), a_1 ∈ a → a_1 < fintype.card α,
  { intros s u a ha,
    apply lt_of_lt_of_le _ hc,
    apply list.ranges_lt c u ha, },

  let l := list.pmap klift' (list.ranges c) hc'_lt,
  have hl : ∀ (a : list ℕ) (ha : a ∈ c.ranges),
    list.map (fin.coe_embedding) (klift' a (hc'_lt a ha)) = a,
  { intros a ha,
    simp only [klift', klift],
    conv_rhs { rw ← list.map_id a}, rw list.map_pmap,
    simp only [fin.coe_embedding_apply, fin.coe_mk, list.pmap_eq_map, list.map_id'', list.map_id], },

  have hl' : list.map (list.map (fin.coe_embedding)) l = list.ranges c,
  { conv_rhs { rw ← list.map_id (list.ranges c) },
    rw ← list.pmap_eq_map _ id (list.ranges c) (hc'_lt),
    simp only [l],
    rw list.map_pmap,
    apply list.pmap_congr,
    intros a ha ha' ha'',
    simp only [hl a ha, id.def], },

  use list.map (list.map e) l,

  split,
  {  -- length
    rw ← list.ranges_length c,
    simp only [list.map_map, l, list.map_pmap, function.comp_app, list.length_map,
      list.length_pmap, list.pmap_eq_map], },
  split,
  { -- nodup
    intro s,
    rw list.mem_map,
    rintro ⟨t, ht, rfl⟩,
    apply list.nodup.map (equiv.injective e),
    simp only [l, list.mem_pmap] at ht,
    obtain ⟨u, hu, rfl⟩ := ht,
    apply list.nodup.of_map,
    rw hl u hu, apply list.ranges_nodup c u hu, },
  { -- pairwise disjoint
    suffices : list.pairwise list.disjoint l,
    refine list.pairwise.map _ _ this ,
    { intros s t hst,
      apply list.disjoint_map,
      exact equiv.injective e, exact hst, },
    { -- list.pairwise list.disjoint l,
      simp only [l],
      apply list.pairwise.pmap (list.ranges_disjoint c),
      intros u hu v hv huv,
      simp only [klift'],
      apply list.disjoint_pmap,
      { simp only [klift],
        intros a a' ha ha' h,
        simpa only [fin.mk_eq_mk] using h, },
      exact huv,
      }, },
end

lemma equiv.perm_with_cycle_type_nonempty_iff {m : multiset ℕ} :
  (m.sum ≤ fintype.card α ∧ (∀ a ∈ m, 2 ≤ a)) ↔ (equiv.perm_with_cycle_type α m).nonempty :=
begin
  split,
  { rintro ⟨hc, h2c⟩,
    have hc' : m.to_list.sum ≤ fintype.card α, simp only [multiset.sum_to_list], exact hc,
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := list.exists_pw_disjoint_with_card hc',
    use list.prod (list.map (λ l, list.form_perm l) p),
    simp only [equiv.perm_with_cycle_type, finset.mem_filter, set.to_finset_univ,
      finset.mem_univ, true_and],
    have hp2 : ∀ (x : list α) (hx : x ∈ p), 2 ≤ x.length,
    { intros x hx,
      apply h2c x.length,
      rw [← multiset.mem_to_list, ← hp_length, list.mem_map],
      exact ⟨x, hx, rfl⟩, },
    rw equiv.perm.cycle_type_eq _ rfl,
    { -- lengths
      rw ← multiset.coe_to_list m,
      apply congr_arg,
      rw list.map_map, rw ← hp_length,
      apply list.map_congr,
      intros x hx, simp only [function.comp_app],
      have hx_nodup : x.nodup := hp_nodup x hx,
      rw list.support_form_perm_of_nodup x hx_nodup,
      { -- length
        rw list.to_finset_card_of_nodup hx_nodup, },
      { -- length >= 1
        intros a h,
        apply nat.not_succ_le_self 1,
        conv_rhs { rw ← list.length_singleton a, }, rw ← h,
        exact hp2 x hx, }, },
    { -- cycles
      intro g,
      rw list.mem_map,
      rintro ⟨x, hx, rfl⟩,
      have hx_nodup : x.nodup := hp_nodup x hx,
      rw ← cycle.form_perm_coe x hx_nodup,
      apply cycle.is_cycle_form_perm ,
      rw cycle.nontrivial_coe_nodup_iff hx_nodup,
      exact hp2 x hx, },
    { -- disjoint
      rw list.pairwise_map,
      apply list.pairwise.imp_of_mem _ hp_disj,
      intros a b ha hb hab,
      rw list.form_perm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb),
      exact hab, }, },
  { -- empty case
    intro h,
    obtain ⟨g, hg⟩ := h,
    simp only [equiv.perm_with_cycle_type, set.to_finset_univ, finset.mem_filter,
      finset.mem_univ, true_and] at hg,
    split,
    rw [← hg, equiv.perm.sum_cycle_type ],
    exact (equiv.perm.support g).card_le_univ,
    intro a,
    rw [← hg],
    exact equiv.perm.two_le_of_mem_cycle_type, },
end

lemma equiv.perm.mem_cycle_factors_conj (g k c : equiv.perm α) :
  c ∈ g.cycle_factors_finset ↔ (k * c * k⁻¹) ∈ (k * g * k⁻¹).cycle_factors_finset :=
begin
  suffices imp_lemma : ∀ (g k c : equiv.perm α),
    c ∈ g.cycle_factors_finset → (k * c * k⁻¹) ∈ (k * g * k⁻¹).cycle_factors_finset,
  { split,
    apply imp_lemma g k c,
    intro h,
    suffices : ∀ (h : equiv.perm α), h = k⁻¹ * (k * h * k⁻¹) * k,
    { rw [this g, this c], apply imp_lemma, exact h, },
    intro h,
    simp only [← mul_assoc],
    simp only [mul_left_inv, one_mul, inv_mul_cancel_right], },
  { intros g k c,
    simp only [equiv.perm.mem_cycle_factors_finset_iff],
    rintro ⟨hc, hc'⟩,
    split,
    exact equiv.perm.is_cycle.is_cycle_conj hc,
    intros a ha,
    simp only [equiv.perm.coe_mul, embedding_like.apply_eq_iff_eq],
    apply hc',
    rw equiv.perm.mem_support at ha ⊢,
    intro ha', apply ha,
    simp only [mul_smul, ← equiv.perm.smul_def] at ha' ⊢,
    rw ha',
    simp only [equiv.perm.smul_def, equiv.perm.apply_inv_self], },
end

example {β : Type*} (e : equiv α β) (a : α) (b : β) :
  e a = b ↔ a = e.symm b :=
begin
  refine equiv.apply_eq_iff_eq_symm_apply e
end

lemma equiv.perm.conj_support_eq (k : conj_act(equiv.perm α)) (g : equiv.perm α) (a : α) :
  a ∈ (k • g).support ↔ k⁻¹.of_conj_act a ∈ g.support :=
begin
  simp only [equiv.perm.mem_support, conj_act.smul_def],
  rw not_iff_not ,
  simp only [equiv.perm.coe_mul, function.comp_app, conj_act.of_conj_act_inv],
  exact equiv.apply_eq_iff_eq_symm_apply (k.of_conj_act),
end

lemma equiv.perm.mem_cycle_factors_conj' (k : conj_act(equiv.perm α)) (g c : equiv.perm α) :
  c ∈ g.cycle_factors_finset ↔ k • c ∈ (k • g).cycle_factors_finset :=
begin
  suffices imp_lemma : ∀ (k : conj_act(equiv.perm α)) (g c : equiv.perm α),
    c ∈ g.cycle_factors_finset → k • c ∈ (k • g).cycle_factors_finset,
  { split,
    { apply imp_lemma k g c, },
    { intro h,
      rw ← inv_smul_smul k c, rw ← inv_smul_smul k g,
      apply imp_lemma,  exact h, } },
  { intros k g c,
    simp only [equiv.perm.mem_cycle_factors_finset_iff],
    rintro ⟨hc, hc'⟩,
    split,
    { exact equiv.perm.is_cycle.is_cycle_conj hc, },
    { intro a,
      rw equiv.perm.conj_support_eq,
      intro ha,
      simp only [conj_act.smul_def],
      simpa using hc' _ ha, }, },
end

-- open_locale classical

example (g : equiv.perm α) (x : α) (hx : x ∈ g.support) :
  (∃ (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset), x ∈ c.support)  :=
begin
  use g.cycle_of x,
  rw equiv.perm.cycle_of_mem_cycle_factors_finset_iff ,
  apply and.intro hx,
  rw [equiv.perm.mem_support, equiv.perm.cycle_of_apply_self, ← equiv.perm.mem_support],
  exact hx,
end

lemma equiv.perm.mem_cycle_factors_conj_eq (k : conj_act (equiv.perm α)) (g : equiv.perm α) :
  equiv.perm.cycle_factors_finset (k • g) = k • (equiv.perm.cycle_factors_finset g) :=
begin
  ext c,
  rw equiv.perm.mem_cycle_factors_conj' k⁻¹ (k • g) c,
  simp only [inv_smul_smul],
  exact finset.inv_smul_mem_iff,
end

example {α : Type*} (s : finset α) (a b : α) (h : a = b) : a ∈ s ↔ b ∈ s :=
begin
  refine iff_of_eq (congr_fun (congr_arg has_mem.mem h) s),
end

example (k: equiv.perm α) : mul_equiv.symm (mul_aut.conj k)
 = mul_aut.conj k⁻¹ := begin
-- simp only [map_inv],
ext g x,
rw [map_inv, mul_aut.conj_symm_apply, mul_aut.conj_inv_apply],
 end

lemma is_conj_iff_inv_is_conj {G : Type*} [group G] (a b k : G) :
  k * a * k⁻¹ = b  ↔ a = k⁻¹ * b * k :=
by rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq , mul_assoc]

lemma equiv.perm.cycle_factors_conj (g k : equiv.perm α) :
  finset.map (mul_aut.conj k).to_equiv.to_embedding g.cycle_factors_finset
  = (k * g * k⁻¹).cycle_factors_finset :=
begin
  ext c,
  rw finset.mem_map_equiv,
  rw equiv.perm.mem_cycle_factors_conj g k,
  apply iff_of_eq,
  apply congr_arg2 _ _,
  refl,
  rw is_conj_iff_inv_is_conj,
  rw [← mul_equiv.to_equiv_symm, mul_equiv.to_equiv_eq_coe, mul_equiv.coe_to_equiv,
    mul_aut.conj_symm_apply],
end


lemma mul_action.conj_act.mem_stabilizer_iff {G : Type*} [group G] (k : conj_act G)
  (g : G) : k ∈ mul_action.stabilizer (conj_act G) g ↔ k * g * k⁻¹ = g :=
begin
  simp only [mul_action.mem_stabilizer_iff, has_smul.smul],
  refl,
end

lemma mul_action.conj_act.mem_stabilizer_iff' {G : Type*} [group G] (k : conj_act G)
  (g : G) : k ∈ mul_action.stabilizer (conj_act G) g ↔ commute k g :=
begin
  rw mul_action.conj_act.mem_stabilizer_iff,
  rw [commute, semiconj_by, mul_inv_eq_iff_eq_mul],
end

open_locale pointwise
/-
def equiv.perm.mul_action_conj_cycle_factors' (g : equiv.perm α) :=
  sub_mul_action_of_stabilizer (conj_act (equiv.perm α)) (equiv.perm α) (g.cycle_factors_finset)

def equiv.perm.mul_action_conj_cycle_factors (g : equiv.perm α) :
  sub_mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (equiv.perm α) :=
{ carrier := g.cycle_factors_finset,
  smul_mem' :=
  begin
    rintro ⟨k, hk⟩, intros c hc,
    simp only [finset.mem_coe] at ⊢ hc,
    change k • c ∈ _,
    rw conj_act.smul_def k c,
    rw [mul_action.mem_stabilizer_iff, conj_act.smul_def k g] at hk,
    rw [← hk, ← equiv.perm.mem_cycle_factors_conj],
    exact hc,
  end }
-/
/-
instance equiv.perm.cycle_factors_smul' {g : equiv.perm α} :
  has_smul (mul_action.stabilizer (conj_act (equiv.perm α)) g) (g.cycle_factors_finset) :=
{ smul := λ ⟨k, hk⟩ ⟨c, hc⟩, ⟨k • c,
  begin
    simp only [has_smul.smul],
    convert (equiv.perm.mem_cycle_factors_conj g k c).mp hc,
    apply symm,
    exact (mul_action.conj_act.mem_stabilizer_iff k g).mp hk,
  end⟩}
-/


lemma equiv.perm.cycle_factors_conj_smul_eq {g : equiv.perm α}
 (k : mul_action.stabilizer (conj_act (equiv.perm α)) g) (c : g.cycle_factors_finset) :
  ((k • c) : equiv.perm α) = (conj_act.of_conj_act ↑k) * ↑c * (conj_act.of_conj_act ↑k⁻¹) := rfl

/-
instance equiv.perm.cycle_factors_mul_action' (g : equiv.perm α) :
  mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (g.cycle_factors_finset) :=
{ one_smul := λ c, sorry,
  mul_smul := λ ⟨h, hh⟩ ⟨k, hk⟩ ⟨c, hc⟩,
  begin
    rw ← subtype.coe_inj,
    simp only [submonoid.mk_mul_mk],

    let hzz := equiv.perm.cycle_factors_smul'_eq ⟨k, hk⟩ ⟨c, hc⟩,


      sorry,

  end, },

def equiv.perm.cycle_factors_smul' (g : equiv.perm α) :
  mul_action (subgroup.zpowers g).centralizer (g.cycle_factors_finset) :=
{ one_smul := λ c, by simp only [one_mul, finset.mk_coe, subgroup.coe_one, inv_one, mul_one,
      equiv.coe_fn_mk, equiv.perm.coe_one, id.def],
  mul_smul := λ h k c, by simp only [subtype.coe_mk,
      subgroup.coe_mul, mul_inv_rev, equiv.coe_fn_mk,
      equiv.perm.coe_mul, subtype.mk_eq_mk, ← mul_assoc],
  to_has_smul := { smul :=  λ k c, ⟨k * c * k⁻¹,
    begin
      convert (equiv.perm.mem_cycle_factors_conj g k c).mp c.prop,
      simp only [← (subgroup.mem_centralizer_iff.mp k.prop) g (subgroup.mem_zpowers g),
    mul_inv_cancel_right],
    end⟩ } } -/


-- open_locale classical


example {G : Type*} [group G] (g k : G) : g ⁻¹ * k = k * g⁻¹ ↔ k * g = g * k :=
begin
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_inv_eq_iff_eq_mul, inv_inv],
end

lemma group.commute_iff_mem_centralizer_zpowers {G : Type*} [group G] (g k : G) :
  commute g k ↔ k ∈ subgroup.centralizer (subgroup.zpowers g) :=
begin
  rw subgroup.mem_centralizer_iff,
  split,
  { intros H h,
    rw subgroup.mem_zpowers_iff,
    rintro ⟨n, rfl⟩,
    apply commute.zpow_left,
    exact H },
  { intro H,
    simp only [commute, semiconj_by],
    rw H g (subgroup.mem_zpowers g), },
end

/-
example (g : equiv.perm α) : mul_action.stabilizer (conj_act (equiv.perm α)) g
≃* subgroup.centralizer (subgroup.zpowers g) :=
  subgroup.mul_equiv (conj_act.of_conj_act)
  (begin
    intro k,
    rw mul_action.mem_stabilizer_iff,
    simp only [has_smul.smul],
    rw mul_inv_eq_iff_eq_mul,
    rw ← group.commute_iff_mem_centralizer_zpowers,
    simp only [commute, semiconj_by],
    conv_lhs { rw eq_comm, },
  end)

example {α β : Type*} [decidable_eq α] [decidable_eq β] [group α] [mul_action α β]
  (s : finset β) (g : α) : coe (g • s)  = g • (s : set β) :=
finset.coe_smul_finset g s
-/


-- open_locale classical


lemma equiv.perm.commute_of_mem_cycles_factors_commute (k g : equiv.perm α)
  (hk : ∀ (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset), commute k c) :
  commute k g :=
begin
  rw ← equiv.perm.cycle_factors_finset_noncomm_prod g
    (equiv.perm.cycle_factors_finset_mem_commute g),
  apply finset.noncomm_prod_commute ,
  simp only [id.def],
  exact hk,
end

lemma equiv.perm.self_mem_cycle_factors_commute
  (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) : commute c g :=
begin
  apply equiv.perm.commute_of_mem_cycles_factors_commute,
  intros c' hc',
  by_cases hcc' : c = c',
  rw hcc',
  apply g.cycle_factors_finset_mem_commute hc hc', exact hcc',
end

lemma equiv.perm.mem_cycle_factors_finset_support
  (g c: equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (a : α) :
  a ∈ c.support ↔ g a ∈ c.support :=
begin
  let hc' := equiv.perm.mem_cycle_factors_finset_iff.mp hc,
  split,
  { intro ha,
    rw ← hc'.2 a ha,
    exact equiv.perm.apply_mem_support.mpr ha, },
  { intro ha,
    rw ← equiv.perm.apply_mem_support,
    suffices : c a = g a,
    rw this, exact ha,
    apply equiv.injective g,
    rw ←  hc'.2 (g a) ha,
    simp only [← equiv.perm.mul_apply],
    have this := equiv.perm.self_mem_cycle_factors_commute g c hc,
    simp only [commute, semiconj_by] at this,
    rw this, },
end

lemma equiv.perm.subtype_perm_apply_pow_of_mem (g : equiv.perm α)
  (s : finset α) (hs : ∀ (x : α), x ∈ s ↔ g x ∈ s)
  (n : ℕ) (x : α) (hx : x ∈ s) :
    (((g.subtype_perm hs) ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x :=
begin
  revert x,
  induction n with n hrec,
  { -- zero case
    intros x hx,
    simp only [pow_zero, equiv.perm.coe_one, id.def, subtype.coe_mk], },
  { -- induction case
    intros x hx,
    simp only [pow_succ', equiv.perm.coe_mul, function.comp_app],
    apply hrec, },
end

lemma equiv.perm.subtype_perm_apply_zpow_of_mem (g : equiv.perm α)
  (s : finset α) (hs : ∀ (x : α), x ∈ s ↔ g x ∈ s) (i : ℤ)
  (x : α) (hx : x ∈ s) :
    (((g.subtype_perm hs) ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x :=
begin
  induction i,
  -- nat case
  apply equiv.perm.subtype_perm_apply_pow_of_mem,
  -- neg_succ case
  simp only [zpow_neg_succ_of_nat],
  apply equiv.injective (g ^ (i+1)),
  simp only [equiv.perm.apply_inv_self],
  rw ← equiv.perm.subtype_perm_apply_pow_of_mem g s hs,
  simp only [finset.mk_coe, equiv.perm.apply_inv_self, subtype.coe_mk],
  apply finset.coe_mem,
end

/-- Restrict a permutation to its support -/
def equiv.perm.subtype_perm_of_support (c : equiv.perm α) : equiv.perm c.support :=
  equiv.perm.subtype_perm c (λ (x : α), equiv.perm.apply_mem_support.symm)

/-- Restrict a permutation to a finset containing its support -/
def equiv.perm.subtype_perm_of_support_le (c : equiv.perm α)
(s : finset α) (hcs : c.support ≤ s) : equiv.perm s :=
  equiv.perm.subtype_perm c
(begin
  intro x,
  by_cases hx' : x ∈ c.support,
  { simp only [hcs hx', true_iff],
    apply hcs, rw equiv.perm.apply_mem_support, exact hx', },
  rw equiv.perm.not_mem_support at hx', rw hx', end)

lemma equiv.perm.le_support_is_invariant {c : equiv.perm α} {s : finset α}
(hcs : c.support ≤ s) (x : α) : x ∈ s ↔ c x ∈ s :=
begin
  by_cases hx' : x ∈ c.support,
  { simp only [hcs hx', true_iff],
    exact hcs (equiv.perm.apply_mem_support.mpr hx'), },
  rw equiv.perm.not_mem_support.mp hx',
end

/-- Support of a cycle is nonempty -/
lemma equiv.perm.support_of_cycle_nonempty {g : equiv.perm α} (hg : g.is_cycle) :
  g.support.nonempty :=
begin
  rw [finset.nonempty_iff_ne_empty, ne.def, equiv.perm.support_eq_empty_iff],
  exact equiv.perm.is_cycle.ne_one hg,
  /- rw ←  finset.card_pos,
  apply lt_of_lt_of_le _ (equiv.perm.is_cycle.two_le_card_support hg),
  norm_num, -/
end


example (g : equiv.perm α) :
∃ (a : g.cycle_factors_finset → α), ∀ c : g.cycle_factors_finset, a c ∈ (c : equiv.perm α).support :=
begin
  have : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.nonempty,
  { intro c,
    exact equiv.perm.support_of_cycle_nonempty
      (equiv.perm.mem_cycle_factors_finset_iff.mp c.prop).1, },
   exact ⟨λ c, (this c).some, λ c, (this c).some_spec⟩,
end

/-- If g and c commute, then g stabilizes the support of c -/
lemma equiv.perm.mem_support_of_commute {g c : equiv.perm α} (hgc : g * c = c * g) :
  ∀ (x : α), x ∈ c.support ↔ g x ∈ c.support :=
begin
  intro x,
  simp only [equiv.perm.mem_support, not_iff_not, ← equiv.perm.mul_apply],
  rw [← hgc, equiv.perm.mul_apply],
  exact (equiv.apply_eq_iff_eq g).symm,
end


/-- Centralizer of a cycle is a power of that cycle on the cycle -/
lemma equiv.perm.centralizer_of_cycle_on' (g c : equiv.perm α) (hc : c.is_cycle) :
  (g * c = c * g) ↔  ∃ (hc' : ∀ (x : α), x ∈ c.support ↔ g x ∈ c.support),
      equiv.perm.subtype_perm g hc' ∈ subgroup.zpowers (c.subtype_perm_of_support) :=
begin
  split,
  { intro hgc,
    let hgc' := equiv.perm.mem_support_of_commute hgc,
    use hgc',
    obtain ⟨a, ha⟩ := equiv.perm.support_of_cycle_nonempty hc,
    suffices : c.same_cycle a (g a),
    simp only [equiv.perm.same_cycle] at this,
    obtain ⟨i, hi⟩ := this, use i,
    ext ⟨x, hx⟩,
    simp only [equiv.perm.subtype_perm_of_support, subtype.coe_mk, equiv.perm.subtype_perm_apply],
    rw equiv.perm.subtype_perm_apply_zpow_of_mem,
    suffices : c.same_cycle a x,
    { obtain ⟨j, rfl⟩ := this,
      { simp only [← equiv.perm.mul_apply, commute.eq (commute.zpow_right hgc j)],
        rw [← zpow_add, add_comm i j, zpow_add],
        simp only [equiv.perm.mul_apply],
        simp only [embedding_like.apply_eq_iff_eq],
        exact hi, }, },
    -- c.same_cycle a x,
    exact equiv.perm.is_cycle.same_cycle hc
      (equiv.perm.mem_support.mp ha) (equiv.perm.mem_support.mp hx),
    -- c.same_cycle a (g a),
    apply equiv.perm.is_cycle.same_cycle hc (equiv.perm.mem_support.mp ha),
    exact equiv.perm.mem_support.mp ((hgc' a).mp ha), },
  { -- converse
    rintro ⟨hc', h⟩,
    obtain ⟨i, hi⟩ := h,
    suffices hi' : ∀ (x : α) (hx : x ∈ c.support), g x = (c ^ i) x,
    { ext x,
      simp only [equiv.perm.coe_mul, function.comp_app],
      by_cases hx : x ∈ c.support,
      { -- hx : x ∈ c.support
        rw hi' x hx,
        rw hi' (c x) (equiv.perm.apply_mem_support.mpr hx),
        simp only [← equiv.perm.mul_apply, ← zpow_add_one, ← zpow_one_add],
        rw int.add_comm 1 i, },
      { -- hx : x ∉ c.support
        rw equiv.perm.not_mem_support.mp hx, apply symm,
        rw ← equiv.perm.not_mem_support,
        intro hx', apply hx,
        exact (hc' x).mpr hx', }, },
    { -- proof of hi'
      intros x hx,
      let hix := equiv.perm.congr_fun hi ⟨x, hx⟩,
      simp only [← subtype.coe_inj, equiv.perm.subtype_perm_of_support] at hix,
      simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply,
        equiv.perm.subtype_perm_apply_zpow_of_mem] at hix,
      exact hix.symm, } },
end

example  (g c : equiv.perm α) (hc : c.is_cycle) (hc' : ∀ (x : α), x ∈ c.support ↔ g x ∈ c.support) :
      (equiv.perm.subtype_perm g hc').of_subtype ∈ subgroup.zpowers c
      ↔  equiv.perm.subtype_perm g hc' ∈ subgroup.zpowers (c.subtype_perm_of_support) :=
begin
  simp only [subgroup.mem_zpowers_iff],
  apply exists_congr,
  intro n,

  split,
  { intro h, ext ⟨x, hx⟩, let h' := equiv.perm.congr_fun h x,
    simp only [h', equiv.perm.subtype_perm_of_support, equiv.perm.subtype_perm_apply_zpow_of_mem, subtype.coe_mk,
  equiv.perm.subtype_perm_apply],
    rw equiv.perm.of_subtype_apply_of_mem,
    simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
    exact hx, },
  { intro h, ext x,
    rw ← h,
    by_cases hx : x ∈ c.support,
    { rw equiv.perm.of_subtype_apply_of_mem,
      simp only [equiv.perm.subtype_perm_of_support, equiv.perm.subtype_perm_apply_zpow_of_mem], exact hx, },
    { rw equiv.perm.of_subtype_apply_of_not_mem,
      rw ← equiv.perm.not_mem_support,
      intro hx', apply hx,
      apply equiv.perm.support_zpow_le, exact hx',
      exact hx, }, },
end

lemma equiv.perm.zpow_eq_of_subtype_subtype_perm_iff' (g c : equiv.perm α)
  (hc' : ∀ x, x ∈ c.support ↔ g x ∈ c.support) (n : ℤ) :
  c ^ n = equiv.perm.of_subtype (g.subtype_perm hc')
  ↔ c.subtype_perm_of_support ^ n = g.subtype_perm hc'
:=
begin
  split,
  { intro h, ext ⟨x, hx⟩, let h' := equiv.perm.congr_fun h x,
    simp only [h', equiv.perm.subtype_perm_of_support, equiv.perm.subtype_perm_apply_zpow_of_mem, subtype.coe_mk,
  equiv.perm.subtype_perm_apply],
    rw equiv.perm.of_subtype_apply_of_mem,
    simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
    exact hx, },
  { intro h, ext x,
    rw ← h,
    by_cases hx : x ∈ c.support,
    { rw equiv.perm.of_subtype_apply_of_mem,
      simp only [equiv.perm.subtype_perm_of_support, equiv.perm.subtype_perm_apply_zpow_of_mem], exact hx, },
    { rw equiv.perm.of_subtype_apply_of_not_mem,
      rw ← equiv.perm.not_mem_support,
      intro hx', apply hx,
      apply equiv.perm.support_zpow_le, exact hx',
      exact hx, }, },
end

lemma equiv.perm.zpow_eq_of_subtype_subtype_perm_iff (g c : equiv.perm α)
  (s : finset α) (hg : ∀ x, x ∈ s ↔ g x ∈ s) (hc : c.support ⊆ s) (n : ℤ) :
  c ^ n = equiv.perm.of_subtype (g.subtype_perm hg)
  ↔ c.subtype_perm (equiv.perm.le_support_is_invariant hc) ^ n = g.subtype_perm hg :=
begin
  split,
  { intro h, ext ⟨x, hx⟩, let h' := equiv.perm.congr_fun h x,
    simp only [h', equiv.perm.subtype_perm_apply_zpow_of_mem, subtype.coe_mk,
  equiv.perm.subtype_perm_apply],
    rw equiv.perm.of_subtype_apply_of_mem,
    simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
    exact hx, },
  { intro h, ext x,
    rw ← h,
    by_cases hx : x ∈ s,
    { rw equiv.perm.of_subtype_apply_of_mem,
      simp only [equiv.perm.subtype_perm_apply_zpow_of_mem], exact hx, },
    { rw equiv.perm.of_subtype_apply_of_not_mem,
      rw ← equiv.perm.not_mem_support,
      intro hx',
      apply hx,
      apply hc, apply equiv.perm.support_zpow_le, exact hx',
      exact hx, }, },
end

lemma equiv.perm.centralizer_of_cycle_on (g c : equiv.perm α) (hc : c.is_cycle) :
  (g * c = c * g)
  ↔  ∃ (hc' : ∀ (x : α), x ∈ c.support ↔ g x ∈ c.support),
      (equiv.perm.subtype_perm g hc').of_subtype ∈ subgroup.zpowers c :=
begin
  split,
  { intro hgc,
    let hgc' := equiv.perm.mem_support_of_commute hgc,
    use hgc',
    obtain ⟨a, ha⟩ := equiv.perm.support_of_cycle_nonempty hc,
    suffices : c.same_cycle a (g a),
    simp only [equiv.perm.same_cycle] at this,
    obtain ⟨i, hi⟩ := this, use i,
    ext x,
    by_cases hx : x ∈ c.support,
    { rw equiv.perm.of_subtype_apply_of_mem,
      simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
      obtain ⟨j, rfl⟩ := equiv.perm.is_cycle.same_cycle hc
        (equiv.perm.mem_support.mp ha) (equiv.perm.mem_support.mp hx),
      simp only [← equiv.perm.mul_apply],
      rw commute.eq (commute.zpow_right hgc j),
      rw commute.eq (commute.zpow_zpow_self c i j),
      simp only [equiv.perm.mul_apply, hi],
      exact hx, },
    { rw equiv.perm.of_subtype_apply_of_not_mem,
      rw ← equiv.perm.not_mem_support,
      intro hx', apply hx,
      apply equiv.perm.support_zpow_le,
      exact hx',
      exact hx, },
    -- c.same_cycle a (g a)
      apply equiv.perm.is_cycle.same_cycle hc (equiv.perm.mem_support.mp ha),
      exact equiv.perm.mem_support.mp ((hgc' a).mp ha),
    },
  { -- converse
    rintro ⟨hc', h⟩,
    obtain ⟨i, hi⟩ := h,
    suffices hi' : ∀ (x : α) (hx : x ∈ c.support), g x = (c ^ i) x,
    { ext x,
      simp only [equiv.perm.coe_mul, function.comp_app],
      by_cases hx : x ∈ c.support,
      { -- hx : x ∈ c.support
        rw hi' x hx,
        rw hi' (c x) (equiv.perm.apply_mem_support.mpr hx),
        simp only [← equiv.perm.mul_apply, ← zpow_add_one, ← zpow_one_add],
        rw int.add_comm 1 i, },
      { -- hx : x ∉ c.support
        rw equiv.perm.not_mem_support.mp hx, apply symm,
        rw ← equiv.perm.not_mem_support,
        intro hx', apply hx,
        exact (hc' x).mpr hx', }, },
    { -- proof of hi'
      intros x hx,
      rw hi,
      rw equiv.perm.of_subtype_apply_of_mem,
      simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
      exact hx, } },
end

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
lemma equiv.perm.subtype_perm_on_cycle_factor (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) :
  (g.subtype_perm ((equiv.perm.mem_cycle_factors_finset_support g c hc)))
  = (c.subtype_perm_of_support) :=
begin
  ext ⟨x, hx⟩,
  simp only [equiv.perm.subtype_perm_of_support, subtype.coe_mk, equiv.perm.subtype_perm_apply],
  exact ((equiv.perm.mem_cycle_factors_finset_iff.mp hc).2 x hx).symm,
end

lemma equiv.perm.centralizer_mem_cycle_factors_iff' (g k : equiv.perm α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) :
  k * c = c * k ↔
  ∃ (hc' : ∀ (x : α), x ∈ c.support ↔ k x ∈ c.support),
      k.subtype_perm hc' ∈ subgroup.zpowers (g.subtype_perm
        ((equiv.perm.mem_cycle_factors_finset_support g c hc))) :=
begin
  split,
  { intro H,
    obtain ⟨hc', H'⟩ := (equiv.perm.centralizer_of_cycle_on' k c
      (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1).mp H,
    rw ← equiv.perm.subtype_perm_on_cycle_factor g c hc at H',
    exact ⟨hc', H'⟩, },
  { rintro ⟨hc', H'⟩,
    rw equiv.perm.subtype_perm_on_cycle_factor g c hc at H',
    rw equiv.perm.centralizer_of_cycle_on' k c (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1,
    exact ⟨hc', H'⟩, },
end

lemma equiv.perm.centralizer_mem_cycle_factors_iff (g k : equiv.perm α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) :
  k * c = c * k ↔
  ∃ (hc' : ∀ (x : α), x ∈ c.support ↔ k x ∈ c.support),
      (k.subtype_perm hc').of_subtype ∈ subgroup.zpowers c :=
begin
  rw equiv.perm.centralizer_of_cycle_on,
  rw equiv.perm.mem_cycle_factors_finset_iff at hc,
  exact hc.1,
end

/- -- The axiom of choice…
example (ι : Type*) (α : Π (i : ι), Type*) (f : Π i, set (α i))
  (h :∀ i, (f i).nonempty)  : ∃ (a : Π i, α i), (∀ i, a i ∈ f i) :=
begin
  suffices : nonempty (Π i, (f i)),
  obtain a := this.some,
  use λ i, ↑(a i),
  intro i, refine subtype.mem (a i),
  rw ← not_is_empty_iff ,
  intro h',
  rw is_empty_pi at h',
  obtain ⟨i, hi⟩ := h',
  rw ← not_nonempty_iff  at hi,
  apply hi,
  simp only [set.nonempty_coe_sort],
  exact h i,
end

-- Finite choices
example (ι : Type*) (α : Π (i : ι), Type*) (f : Π (i : ι), finset (α i))
  (h :∀  i, (f i).nonempty) (s : finset ι) : ∃ (a : Π (i : s), α i), (∀ i : s, a i ∈ f i) :=
begin
  apply finset.induction_on s,
  { -- empty s
    apply exists.intro,
    intro i, exfalso, exact finset.not_mem_empty _ i.prop,
    intro i, exfalso, exact finset.not_mem_empty _ i.prop, },
  { -- insert
    intros k s hks hrec,
    obtain ⟨a, ha⟩ := hrec,
    apply exists.intro,
    rintro ⟨i,hi⟩,
    rw finset.mem_insert at hi,
    cases hi with hi hi,



    sorry, },
end
 -/



lemma equiv.perm.zpow_mod_card_support_cycle_of_self_apply [fintype α] (f : equiv.perm α) (n : ℤ) (x : α) :
  (f ^ (n % (f.cycle_of x).support.card)) x = (f ^ n) x :=
begin
  by_cases hx : f x = x,
  { rw [equiv.perm.zpow_apply_eq_self_of_apply_eq_self hx, equiv.perm.zpow_apply_eq_self_of_apply_eq_self hx] },
  { rw [←equiv.perm.cycle_of_zpow_apply_self, ←equiv.perm.cycle_of_zpow_apply_self f,
        ←equiv.perm.order_of_is_cycle (equiv.perm.is_cycle_cycle_of f hx)],
    rw [←zpow_eq_mod_order_of] },
end

example (n : ℤ) (hn : 0 ≤ n) : ∃ (nn : ℕ), n = nn :=
begin
exact int.eq_coe_of_zero_le hn,
end


lemma equiv.perm.cycle_zpow_mem_support_iff {g : equiv.perm α} (hg : g.is_cycle)
  {n : ℤ} {x : α} (hx : g x ≠ x) : (g ^ n) x = x ↔ n % g.support.card = 0 :=
begin
  let q := n / g.support.card, let r := n % g.support.card,
  change _ ↔ r = 0,
  have div_euc : r + (g.support.card)* q = n ∧ 0 ≤ r ∧ r < g.support.card,
  { rw ← int.div_mod_unique _,
    split, refl, refl,
    simp only [int.coe_nat_pos],
    apply lt_of_lt_of_le _ (equiv.perm.is_cycle.two_le_card_support hg), norm_num, },
  simp only [← equiv.perm.order_of_is_cycle hg] at div_euc,

  obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le div_euc.2.1,
  simp only [hm, nat.cast_nonneg, nat.cast_lt, true_and] at div_euc,
  simp only [hm, nat.cast_eq_zero],
  rw [← div_euc.1, zpow_add g, zpow_mul, zpow_coe_nat],
  simp only [pow_order_of_eq_one, zpow_coe_nat, one_zpow, mul_one],
  have : (g ^ m) x = x ↔ g ^ m = 1,
  { split,
    { intro hgm,
      simp [equiv.perm.is_cycle.pow_eq_one_iff hg],
      use x,
      exact ⟨hx, hgm⟩, },
    { intro hgm, rw hgm, simp only [equiv.perm.coe_one, id.def], }, },
  rw this,
  cases dec_em (m = 0) with hm hm,
  simp only [hm, pow_zero, eq_self_iff_true],
  simp only [hm, iff_false],
    exact pow_ne_one_of_lt_order_of' hm div_euc.2,
end

lemma equiv.perm.zpow_eq_zpow_on_iff (g : equiv.perm α) (m n : ℤ) (x : α) (hx : g x ≠ x):
   (g ^ m) x = (g ^ n) x ↔ m % (g.cycle_of x).support.card = n % (g.cycle_of x).support.card  :=
begin
  rw int.mod_eq_mod_iff_mod_sub_eq_zero,
  conv_lhs { rw [← int.sub_add_cancel m n, int.add_comm, zpow_add], },
  simp only [equiv.perm.coe_mul, embedding_like.apply_eq_iff_eq],
  rw ← equiv.perm.cycle_of_zpow_apply_self g x,
  rw ← equiv.perm.cycle_zpow_mem_support_iff,
  { exact g.is_cycle_cycle_of hx, },
  { simp only [equiv.perm.mem_support, equiv.perm.cycle_of_apply_self], exact hx, },
end

example (p q : Prop) : p ∧ q → p := and.left

example (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset)
  (x y : α) (hx : x ∈ c.support) :
  g.same_cycle x y ↔ y ∈ c.support :=
begin

  have hx' : g.cycle_of x = c := (equiv.perm.cycle_is_cycle_of hx hc).symm,
  have hx'' : x ∈ g.support,
  { apply (equiv.perm.support_cycle_of_le g x),
    rw hx', exact hx, },
  split,
  { intro hxy,
    rw ← hx',
    rw equiv.perm.mem_support_cycle_of_iff,
    exact ⟨hxy, hx''⟩, },
  {
    intro hy,

    apply and.left,
    rw ← equiv.perm.mem_support_cycle_of_iff,
    rw hx', exact hy, },
end

/-  -- SUPPRIMÉ AU PROFIT DE DÉFINITIONS PLUS GÉNÉRALES QUI PROUVENT LE PRODUIT SEMI DIRECT
/- Ici, on utilise a, k, et les propriétés 2 et 3
 - dans conj_class2, on utilise tout -/
lemma is_surjective_aux (g : equiv.perm α) (τ: equiv.perm (g.cycle_factors_finset))
  (H : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.card = ((τ c) : equiv.perm α).support.card) :
  ∃ (a : g.cycle_factors_finset → α) (k : equiv.perm α),
    (∀ (c : g.cycle_factors_finset), a c ∈ (c : equiv.perm α).support)
    ∧ (g * k = k * g)
    ∧ (∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act k) • (c : equiv.perm α) = τ c)
    ∧ k ∘ a = a ∘ τ
    ∧ k.support ⊆ g.support :=
begin
  have hsupp_ne : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.nonempty,
  { intro c,
    exact equiv.perm.support_of_cycle_nonempty
      (equiv.perm.mem_cycle_factors_finset_iff.mp c.prop).1, },
  let a : g.cycle_factors_finset → α := λc, (hsupp_ne c).some,
  use a,
  let ha' : ∀ (c : g.cycle_factors_finset), g.cycle_of (a c) = (c : equiv.perm α) :=
  λ c,  (equiv.perm.cycle_is_cycle_of (hsupp_ne c).some_spec c.prop).symm,
  have ha : ∀ c : g.cycle_factors_finset, g (a c) ≠ (a c),
  { intro c,
    rw ← equiv.perm.mem_support,
    rw ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff ,
    rw ha' c, exact c.prop, },
  have ha'': ∀ (c : g.cycle_factors_finset) (i : ℤ), g.cycle_of ((g ^ i) (a c)) = c,
  { intros c i, rw equiv.perm.cycle_of_self_apply_zpow, rw ha', },

  let Kf : equiv.perm (g.cycle_factors_finset) → (g.cycle_factors_finset) × ℤ → α :=
    λ e ⟨c, i⟩, (g ^ i) (a (e c)),
  have Kf_apply : ∀ {e : equiv.perm (g.cycle_factors_finset)} {c : g.cycle_factors_finset} {i : ℤ},
    Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) := λ e c i, rfl,
  let k := function.extend (Kf 1) (Kf τ) id,

  have haK : ∀ (e : equiv.perm (g.cycle_factors_finset)) (c : g.cycle_factors_finset) (i : ℤ),
  g.cycle_of (Kf e ⟨c, i⟩) = (e c : equiv.perm α),
  { intros e c i, rw Kf_apply,
    rw equiv.perm.cycle_of_self_apply_zpow, rw ha', },
  have ha2 : ∀ (e : equiv.perm (g.cycle_factors_finset)) (c : g.cycle_factors_finset) (i : ℤ),
   g (Kf e ⟨c,i⟩) = Kf e ⟨c, i + 1⟩,
  { intros e c i,
    simp only [Kf_apply],
    rw ← equiv.perm.mul_apply, rw ← zpow_one_add, rw add_comm 1 i, },
  have ha3 :  ∀ (e : equiv.perm (g.cycle_factors_finset)) (c d : g.cycle_factors_finset) (i : ℤ),
   (d = e c) → (d : equiv.perm α) (Kf e ⟨c,i⟩) = Kf e ⟨c, i + 1⟩,
-- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  { intros e c d i h,
    rw h,
    rw ← haK e c i,
    rw equiv.perm.cycle_of_apply_self,
    apply ha2, },
  have ha4 : ∀ (e : equiv.perm (g.cycle_factors_finset)) (c d : g.cycle_factors_finset) (i : ℤ),
   (d ≠ e c) → (d : equiv.perm α) (Kf e ⟨c,i⟩) = Kf e ⟨c, i⟩,
  { intros e c d i h,
    suffices hdc : (d : equiv.perm α).disjoint (e c : equiv.perm α),
    { apply or.resolve_right (equiv.perm.disjoint_iff_eq_or_eq.mp hdc (Kf e ⟨c, i⟩)),
      -- intro hd,
      rw ← haK e c i,
      rw equiv.perm.cycle_of_apply_self ,
      rw ← equiv.perm.cycle_of_eq_one_iff,
      rw haK e c i,
      apply equiv.perm.is_cycle.ne_one ,
      refine (equiv.perm.mem_cycle_factors_finset_iff.mp _).1,
      exact g,
      exact (e c).prop, },
    apply g.cycle_factors_finset_pairwise_disjoint d.prop (e c).prop,
    rw function.injective.ne_iff (subtype.coe_injective), exact h, },
  have ha5 : ∀ (x : α) (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf 1 cj = x)),
    k x = x,
  { intros x hx,
    simp only [k, function.extend_apply' _ _ _ hx, id.def], },
  have ha6 : ∀ (x : α) (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf 1 cj = x))
    (c : g.cycle_factors_finset), (c : equiv.perm α) x = x,
  { intros x hx c,
    by_contradiction, apply hx,
    rw [← ne.def, ← equiv.perm.mem_support] at h,
    suffices : g.same_cycle (a c) x,
    { obtain ⟨i, hi⟩ := this,
      use ⟨c, i⟩,
      rw [Kf_apply, ← hi, equiv.perm.coe_one, id.def], },

    apply and.left,
    rw ← equiv.perm.mem_support_cycle_of_iff,
    rw ha' c, exact h, },
  have hkfg : ∀ (e e' : equiv.perm (g.cycle_factors_finset))
    (hee' : ∀ (c : g.cycle_factors_finset), (e c : equiv.perm α).support.card = (e' c : equiv.perm α).support.card),
    (Kf e').factors_through (Kf e), --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
  { rintros e e' Hee' ⟨c, i⟩ ⟨d, j⟩ He,
    change (g ^ i) (a (e c)) = (g ^ j) (a (e d)) at He,
    change (g ^ i) (a (e' c)) = (g ^ j) (a (e' d)),
    suffices hcd : c = d,
    { rw hcd at He ⊢,
      rw [g.zpow_eq_zpow_on_iff i j, ha'] at He,
      rw [g.zpow_eq_zpow_on_iff, ha', ← Hee' d],
      exact He,
      { exact ha (e' d), },
      { exact ha (e d), }, },
    { -- d = c
        apply equiv.injective e,
        rw [← subtype.coe_inj, ← ha'' (e c) i, ← ha'' (e d) j, He], }, },

  have k_apply : ∀ (c : g.cycle_factors_finset) (i : ℤ), k (Kf 1 ⟨c,i⟩) = Kf τ ⟨c,i⟩,
  { intros c i,
    simp only [k],
    rw function.factors_through.extend_apply (hkfg 1 τ _) id ⟨c,i⟩,
    -- rw function.extend_apply_first (Kf 1) (Kf τ) id _ ⟨c,i⟩,
    { intro c, simp only [← H c, equiv.perm.coe_one, id.def], }, },
  have k_apply' : ∀ (x : α), x ∉ g.support → k x = x,
  { intros x hx,
    simp only [k],
    rw function.extend_apply',
    simp only [id.def],
    intro hyp,
    obtain ⟨⟨c, i⟩, rfl⟩ := hyp,
    apply hx,
    change (g ^ i) (a c) ∈ g.support,
    rw equiv.perm.zpow_apply_mem_support ,
    rw equiv.perm.mem_support,
    exact ha c, },
  have hk_bij : function.bijective k,
  { rw fintype.bijective_iff_injective_and_card,
    refine and.intro _ rfl,
    intros x y hxy,
    by_cases hx : ∃ (a : (g.cycle_factors_finset) × ℤ), Kf 1 a = x,
    { obtain ⟨⟨c, i⟩, rfl⟩ := hx,
      simp only [k_apply] at hxy,
      by_cases hy : ∃ (b : (g.cycle_factors_finset) × ℤ), Kf 1 b = y,
      { -- x = Kf 1 a, y = Kf 1 b
        obtain ⟨⟨d, j⟩, rfl⟩ := hy,
        simp only [k_apply] at hxy,
        refine @hkfg τ 1 _ ⟨c,i⟩ ⟨d,j⟩ hxy,
        { intros c, simp only [equiv.perm.coe_one, id.def, H c], }, },
      { -- x = kf a, y non
        exfalso, apply hy,
        rw ha5 y hy at hxy,
        use (⟨τ c, i⟩ : g.cycle_factors_finset × ℤ),
        rw ← hxy, refl, }, },
    { rw ha5 x hx at hxy,
      by_cases hy : ∃ (b : (g.cycle_factors_finset) × ℤ), Kf 1 b = y,
      { -- x pas kfa, -- y = kf b,
        obtain ⟨⟨d, j⟩, rfl⟩ := hy,
        exfalso, apply hx,
        simp only [k_apply] at hxy,
        use ⟨τ d, j⟩, rw hxy, refl, },
      { -- x pas kf a, y non plus
        rw ha5 y hy at hxy,
        exact hxy, }, }, },
    use equiv.of_bijective k hk_bij,
    split,
    { exact λ c, (hsupp_ne c).some_spec, },
    split,
    { -- commutation
      ext x,
      simp only [equiv.perm.coe_mul, function.comp_app, equiv.of_bijective_apply],
      by_cases hx : ∃ (a : (g.cycle_factors_finset) × ℤ), Kf 1 a = x,
      { obtain ⟨⟨c, i⟩, rfl⟩ := hx,
        simp only [ha2, k_apply], },
      { have hx' : ¬ (∃ dj : (g.cycle_factors_finset) × ℤ, Kf 1 dj = g x),
        { intro hx', apply hx,
          obtain ⟨⟨d, j⟩, hx'⟩ := hx',
          use ⟨d, j-1⟩,
          apply equiv.injective g,
          simp only [← hx', ha2, sub_add_cancel], },
        rw ha5 x hx, rw ha5 _ hx', }, },
    split,
    { -- action on g.cycle_factors_finset
      intro c,
      rw conj_act.smul_def,
      rw mul_inv_eq_iff_eq_mul,
      simp only [conj_act.of_conj_act_to_conj_act],
      ext x,
      simp,
      by_cases hx : ∃ (a : (g.cycle_factors_finset) × ℤ), Kf 1 a = x,
      { obtain ⟨⟨d, j⟩, rfl⟩ := hx,
        by_cases hcd : d = c,
        { -- d = c
          rw hcd,
          rw ha3, simp only [k_apply],
          rw ha3,
          exact rfl,
          simp only [equiv.perm.coe_one, id.def], },
        { -- d ≠ c
          rw ha4, simp only [k_apply], rw ha4,
          rw function.injective.ne_iff (equiv.injective τ), exact ne.symm hcd,
          simp only [equiv.perm.coe_one, id.def, ne.def], exact ne.symm hcd, }, },
      { simp only [ha5 x hx, ha6 x hx], }, },
    split,
    { -- k ∘ a = a ∘ τ
      ext c,
      simp only [function.comp_app, equiv.of_bijective_apply],
      suffices : a c = Kf 1 (c, 0),
      rw [this, k_apply],
      all_goals { simp only [Kf_apply, zpow_zero, equiv.perm.coe_one, id.def], }, },
    { -- k.support ⊆ g.support
      intro x,
      simp only [equiv.perm.mem_support, ne.def],
      intros hxk hxg, apply hxk,
      apply k_apply',
      rw equiv.perm.not_mem_support, exact hxg, },
end
 -/


example (j : ℤ) : j = 1 + (j - 1) :=
begin
exact eq_add_of_sub_eq' rfl
end

example (g : equiv.perm α) (i j : ℤ) (x : α) : (g ^ i) x = (g ^ j) x ↔ (g ^ (j - i)) x = x :=
begin
conv_lhs { rw [← sub_add_cancel j i, add_comm, zpow_add, equiv.perm.mul_apply], },
simp only [embedding_like.apply_eq_iff_eq],
exact comm,
end

instance mul_action.decidable_mem_fixed_by {α β: Type*} [monoid α] [decidable_eq β] [mul_action α β] (a : α) : decidable_pred (λ (b : β), b ∈ mul_action.fixed_by α β   a) :=
begin
  intro b,
  simp only [mul_action.mem_fixed_by, equiv.perm.smul_def],
  apply_instance,
end

instance mul_action.decidable_mem_stabilizer {α β: Type*} [group α] [decidable_eq β] [mul_action α β] (b : β) : decidable_pred (λ (g : α), g ∈ mul_action.stabilizer α b) :=
begin
  simp only [decidable_pred, mul_action.mem_stabilizer_iff],
  intro g, apply_instance,
end

def equiv.perm_conj_stabilizer_fun (g : equiv.perm α) :
(equiv.perm ((mul_action.fixed_by (equiv.perm α) α g)) × Π (c ∈ g.cycle_factors_finset), subgroup.zpowers (c : equiv.perm α)) → equiv.perm α :=
λ (uv : equiv.perm (mul_action.fixed_by (equiv.perm α) α g)
      × Π (c ∈ g.cycle_factors_finset), subgroup.zpowers (c : equiv.perm α)),
begin
  exact uv.fst.of_subtype
    * finset.noncomm_prod (g.cycle_factors_finset)
        (λ c, dite (c ∈ g.cycle_factors_finset) (λ hc, uv.snd c hc) (λ hc, 1))
    (λ c hc d hd h,
    begin
      simp only [finset.mem_coe] at hc hd,
      rw dif_pos hc, rw dif_pos hd,
      obtain ⟨m, hc'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop,
      obtain ⟨n, hd'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd d hd).prop,
      rw [← hc', ← hd'],
      apply commute.zpow_zpow,
      exact g.cycle_factors_finset_mem_commute hc hd h,
    end),
end

example (g : equiv.perm α) (u : equiv.perm (mul_action.fixed_by (equiv.perm α) α g))
  (v : Π (c ∈ g.cycle_factors_finset), subgroup.zpowers (c : equiv.perm α)) :
conj_act.to_conj_act (equiv.perm_conj_stabilizer_fun g ⟨u, v⟩) ∈
mul_action.stabilizer (conj_act (equiv.perm α)) g :=
begin
  simp only [equiv.perm_conj_stabilizer_fun, map_mul],
  apply subgroup.mul_mem,
  { rw mul_action.mem_stabilizer_iff,
    rw conj_act.smul_def,
    rw mul_inv_eq_iff_eq_mul,
    ext x,
    simp only [equiv.perm.coe_mul, function.comp_app, conj_act.of_conj_act_to_conj_act],
    by_cases hx : x ∈ mul_action.fixed_by _ α g,
    { simp only [mul_action.mem_fixed_by, equiv.perm.smul_def] at hx,
      rw hx,
      apply symm,
      rw [← equiv.perm.smul_def, ← mul_action.mem_fixed_by],
      exact (equiv.perm.mem_iff_of_subtype_apply_mem u x).mp hx, },
    { rw equiv.perm.of_subtype_apply_of_not_mem u hx,
      apply equiv.perm.of_subtype_apply_of_not_mem u,
      intro hx', apply hx,
      simp only [mul_action.mem_fixed_by, equiv.perm.smul_def] at hx' ⊢,
      simp only [embedding_like.apply_eq_iff_eq] at hx', exact hx', } },
  { rw mul_action.mem_stabilizer_iff,
    rw conj_act.smul_def,
    rw mul_inv_eq_iff_eq_mul,
    simp only [conj_act.of_conj_act_to_conj_act],
    change commute _ _ ,
    rw commute.symm_iff,
    apply finset.noncomm_prod_commute,
    intros c hc,
    rw dif_pos hc,
    obtain ⟨m, hm⟩ := subgroup.mem_zpowers_iff.mp (v c hc).prop,
    rw ← hm,
    change commute g (c ^ m),
    apply commute.zpow_right,
    rw commute.symm_iff,
    exact equiv.perm.self_mem_cycle_factors_commute g c hc, },
end

example {G : Type*} [group G] (x : G) (hx : x ∈ (⊥ : subgroup G)) : x = 1 :=
begin
refine subgroup.mem_bot.mp hx,
end

lemma commute_of_subtype_disjoint {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  (hpq : ∀ a, ¬ (p a ∧ q a))
  (x : equiv.perm (subtype p)) (y : equiv.perm (subtype q)) :
  commute x.of_subtype y.of_subtype :=
begin
  apply equiv.perm.disjoint.commute,
  intro a,
  by_cases hx : p a,
  { rw equiv.perm.of_subtype_apply_of_not_mem y,
    apply or.intro_right, refl,
    exact not_and.mp (hpq a) hx, },
  { rw equiv.perm.of_subtype_apply_of_not_mem x hx,
    apply or.intro_left, refl, }
end

example {ι : Type*} (p : ι → Prop) (f : Π i, p i → Type*)
  (i j : ι) (hi : p i) (hj : p j) (h : i = j) : f i hi = f j hj :=
begin
simp_rw h,
end


example {ι : Type*} [decidable_eq ι] (p : α → ι) (s : finset ι)
  (f : Π (i : ι), i ∈ s → equiv.perm ↥{a : α | p a = i})
  (i j : ι) (hi : i ∈ s) (hj : j ∈ s) (h : i = j) :
  equiv.perm.of_subtype (f j hj) = equiv.perm.of_subtype (f i hi) :=
begin
subst h,
end

def equiv.perm.of_partition_fun {ι : Type*} [decidable_eq ι] (p : α → ι) (s : finset ι) : (Π i ∈ s, equiv.perm {a | p a = i}) → equiv.perm α :=
λ f, s.noncomm_prod (λ i, dite (i ∈ s) (λ hi, (f i hi).of_subtype) (λ hi, 1))
      (begin
        intros i hi j hj hij,
        simp only [finset.mem_coe] at hi hj,
        simp  only [dif_pos hi, dif_pos hj],
        /- by_cases h : i = j,
        exfalso, exact hij h,
         -/
        -- case h : ¬ (i = j)
       convert commute_of_subtype_disjoint _ (f i hi) (f j hj),
        intro x,
        simp only [set.mem_set_of_eq, not_and],
        intros h'i h'j, apply hij, rw ← h'i, exact h'j,
    end)

def equiv.perm.of_partition {ι : Type*} [fintype ι] [decidable_eq ι] (p : α → ι) : (Π i, equiv.perm {a | p a = i}) →* equiv.perm α :=
{ to_fun := λ u, equiv.perm.of_partition_fun p (finset.univ) (λ i hi, u i),
  map_one' :=
  begin
    rw ← subgroup.mem_bot,
    apply subgroup.noncomm_prod_mem,
    intros i hi,
    simp only [dif_pos hi],
    rw subgroup.mem_bot,
    convert map_one (equiv.perm.of_subtype),
  end,
  map_mul' :=
  begin
    intros f g,
    simp only [equiv.perm.of_partition_fun],
    rw ← finset.noncomm_prod_mul_distrib ,
    apply finset.noncomm_prod_congr rfl,
    { intros x hx,
      dsimp,
      simp only [if_pos hx],
      apply map_mul, },
    { intros x hx y hy h,
      simp only [finset.mem_coe] at hx hy,
      simp only [dif_pos hx, dif_pos hy],
      apply commute_of_subtype_disjoint,
      simp only [set.mem_set_of_eq, not_and],
      intros a h' h'', apply h, rw [← h', ← h''], },
  end }

lemma equiv.perm.of_partition_coe_apply' {ι : Type*} [decidable_eq ι] (p : α → ι) (s : finset ι) (u : Π i ∈ s, equiv.perm {x | p x = i})
  (i : ι) (a : {x : α | p x = i}) : equiv.perm.of_partition_fun p s u (a : α)
  = dite (i ∈ s) (λ hi, (u i hi) a) (λ hi, a) :=
begin
  simp only [equiv.perm.of_partition_fun],
  induction s using finset.induction with j s hj ih,
  -- empty
  simp only [finset.noncomm_prod_empty, equiv.perm.coe_one, id.def, finset.not_mem_empty, if_false],
  rw dif_neg id,
  { -- insert
    rw finset.noncomm_prod_insert_of_not_mem s j _ _ hj,
    rw equiv.perm.mul_apply,
    simp only [dif_pos (finset.mem_insert_self j s)],
    split_ifs with h,
    { rw finset.mem_insert at h,
     cases h with h1 h2,
      { subst h1,
        suffices : equiv.perm.of_subtype (u i h) a = (u i h) a,
        rw ← this,
        apply congr_arg,
        specialize ih (λ i hi, u i (finset.mem_insert_of_mem hi)),
        simp only [dif_neg hj] at ih,
        conv_rhs { rw ← ih, },
        apply congr_arg2 _ _ rfl,
        apply finset.noncomm_prod_congr rfl,
        { intros k hk,
          simp only [dif_pos hk, dif_pos (finset.mem_insert_of_mem hk)], },
        { rw equiv.perm.of_subtype_apply_of_mem,
          simp only [subtype.coe_eta], exact a.prop, }, },
      { specialize ih (λ i hi, u i (finset.mem_insert_of_mem hi)),
        simp only [dif_pos h2] at ih,
        suffices : ∀ (h' : j ∈ insert j s), equiv.perm.of_subtype (u j h')
          ((u i h) a) = (u i h) a,
        rw ← this _ ,
        apply congr_arg,
        rw ← ih,
        apply congr_arg2 _ _ rfl,
        apply finset.noncomm_prod_congr rfl,
        { intros k hk,
          simp only [dif_pos hk, dif_pos (finset.mem_insert_of_mem hk)], },
        { intro h',
          rw equiv.perm.of_subtype_apply_of_not_mem,
          simp only [set.mem_set_of_eq], intro h'',
          suffices : p ((u i h) a) = i,
          apply hj, rw ← h'', rw this, exact h2,
          exact (u i h a).prop, }, }, },
    { specialize ih (λ i hi, u i (finset.mem_insert_of_mem hi)),
      simp only [finset.mem_insert, not_or_distrib] at h,
      simp only [dif_neg h.2] at ih,

      suffices : ∀ (h' : j ∈ insert j s), equiv.perm.of_subtype (u j h') a = a,
      convert this _,
      conv_rhs { rw ← ih },
      apply congr_arg2 _ _ rfl,
      apply finset.noncomm_prod_congr rfl,
      { intros k hk,
        simp only [dif_pos hk, dif_pos (finset.mem_insert_of_mem hk)], },
      { intro h',
        rw equiv.perm.of_subtype_apply_of_not_mem,
        simp only [set.mem_set_of_eq],
        intro h',
        suffices : p a = i, apply h.1,
        rw ← h', rw this,
        exact a.prop, }, }, },
end

lemma equiv.perm.of_partition_coe_apply {ι : Type*} [fintype ι] [decidable_eq ι] {p : α → ι} (u : Π i , equiv.perm {x | p x = i})
  (i : ι) (a : {x : α | p x = i}) :
  equiv.perm.of_partition p u (a : α) = (u i) a :=
begin
  dsimp [equiv.perm.of_partition],
  rw equiv.perm.of_partition_coe_apply' p (finset.univ) (λ i h, u i),
  simp only [dif_pos (finset.mem_univ i)],
end


lemma equiv.perm.of_partition_inj {ι : Type*} [fintype ι] [decidable_eq ι] (p : α → ι) : function.injective (equiv.perm.of_partition p) :=
begin
  intros u v h,
  ext i a,
  rw ← equiv.perm.of_partition_coe_apply,
  rw h,
  rw equiv.perm.of_partition_coe_apply,
end

lemma equiv.perm.of_partition_range {ι : Type*} [fintype ι] [decidable_eq ι] (p : α → ι) (f : equiv.perm α) :
  f ∈ (equiv.perm.of_partition p).range ↔  p ∘ f = p :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    ext a,
    simp only [function.comp_app],
    have ha : a ∈ { x : α | p x = p a }, rw set.mem_set_of_eq,
    have : a = (⟨a, ha⟩: { x : α | p x = p a }) := (subtype.coe_mk a ha).symm,
    rw this,
    rw equiv.perm.of_partition_coe_apply,
    simp only [subtype.coe_mk],
    exact (u (p a) ⟨a, ha⟩).prop,
   },
  { intro h,
    have h' : ∀ i a, a ∈ { x | p x = i} ↔ f a ∈ { x | p x = i },
    { intros i a, simp only [set.mem_set_of_eq],
      rw ← function.comp_app p f a, rw h, },
    let g : Π i, equiv.perm { x | p x = i} := λ i,
      f.subtype_perm (h' i),
    use g,
    ext a,
    have ha : a ∈ {x | p x = p a}, rw set.mem_set_of_eq,
    have : a = (⟨a, ha⟩: { x : α | p x = p a }) := (subtype.coe_mk a ha).symm,
    rw this,
    rw equiv.perm.of_partition_coe_apply,
    simp only [g],
    rw equiv.perm.subtype_perm_apply,
    refl, },
end

lemma equiv.perm.of_partition_card {ι : Type*}  [fintype ι] [decidable_eq ι]
  (p : α → ι) : fintype.card ({f : equiv.perm α | p ∘ f = p})
= finset.prod (⊤ : finset ι) (λ i, (fintype.card { a | p a = i }).factorial) :=
begin
  let φ := equiv.perm.of_partition p,
  let hφ_inj := equiv.perm.of_partition_inj p,
  let hφ_range := equiv.perm.of_partition_range p,

  suffices : fintype.card (Π (i : ι), equiv.perm {a | p a = i}) =
    fintype.card ({f : equiv.perm α | p ∘ f = p}),
  rw ← this,
  simp only [fintype.card_pi, set.coe_set_of, finset.top_eq_univ, fintype.card_perm],
  { rw fintype.card_eq,
    let φ' : (Π (i : ι), equiv.perm {a | p a = i}) → {f : equiv.perm α | p ∘ f = p} := λ u, ⟨φ u,
      begin
        simp only [set.mem_set_of_eq],
        rw ← hφ_range _, use u,
      end⟩,
    have hφ' : function.bijective φ',
    { split,
      { -- injectivity
        intros u v,
        simp only [φ', subtype.mk_eq_mk],
        apply hφ_inj, },
      { -- surjectivity
        rintro ⟨f, hf⟩,
        simp only [φ', subtype.mk_eq_mk, ← monoid_hom.mem_range, hφ_range f],
        exact hf, }, },
    use equiv.of_bijective φ' hφ', },
end

end cycle_types

namespace on_cycle_factors

variables {α : Type*} [decidable_eq α] [fintype α] (g : equiv.perm α)

lemma centralizer_le_stab_cycle_fact :
  mul_action.stabilizer (conj_act (equiv.perm α)) g
  ≤ mul_action.stabilizer (conj_act (equiv.perm α)) ((g.cycle_factors_finset) : set (equiv.perm α)) :=
begin
  intro k,
  simp only [mul_action.mem_stabilizer_iff],
  intro hk,
  rw [← finset.coe_smul_finset k _, ← equiv.perm.mem_cycle_factors_conj_eq, hk],
end

/- instance mul_action_on_cycle_factors
/-   mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g)
  ((g.cycle_factors_finset) : set (equiv.perm α)) -/
:= (sub_mul_action_of_stabilizer
  (conj_act (equiv.perm α))
  ((g.cycle_factors_finset) : set (equiv.perm α))).mul_action
-/

def sub_mul_action_on_cycle_factors :
  sub_mul_action (mul_action.stabilizer (conj_act (equiv.perm α)) g) (equiv.perm α) :=
{ carrier := (g.cycle_factors_finset : set(equiv.perm α)),
  smul_mem' := λ k c hc,
  begin
    have := equiv.perm.mem_cycle_factors_conj_eq ↑k g,
    rw (mul_action.mem_stabilizer_iff.mp k.prop) at this,
    rw [this, finset.coe_smul_finset],
    exact ⟨c, hc,  rfl⟩,
  end}

instance mul_action_on_cycle_factors :
  mul_action
    (mul_action.stabilizer (conj_act (equiv.perm α)) g)
    (g.cycle_factors_finset : set (equiv.perm α)) :=
(sub_mul_action_on_cycle_factors g).mul_action

def φ := mul_action.to_perm_hom
  (mul_action.stabilizer (conj_act (equiv.perm α)) g)
  (g.cycle_factors_finset : set (equiv.perm α))

lemma φ_eq : ∀ (k : conj_act (equiv.perm α))
  (hk : k ∈ mul_action.stabilizer (conj_act (equiv.perm α)) g)
  (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset),
  (φ g ⟨k, hk⟩ ⟨c, hc⟩ : equiv.perm α) = k • c :=
begin
  intros k hk c hc,
  simp only [φ],
  simp only [monoid_hom.coe_comp, function.comp_app, mul_action.to_perm_hom_apply, mul_action.to_perm_apply],
  refl,
end

lemma φ_eq' : ∀ (k : equiv.perm α)
  (hk : k ∈ mul_action.stabilizer (conj_act (equiv.perm α)) g)
  (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset),
  (φ g ⟨conj_act.to_conj_act k, hk⟩ ⟨c, hc⟩ :equiv.perm α) = k * c * k⁻¹ :=
begin
  intros k hk c hc,
  simp only [φ],
  refl,
end

/-
lemma mem_range_φ (k : equiv.perm (g.cycle_factors_finset)) :
  k ∈ (φ g).range ↔ ∀ (c : g.cycle_factors_finset), (k c: equiv.perm α).support.card = (c : equiv.perm α).support.card :=
begin
  split,
  { simp only [monoid_hom.coe_range, monoid_hom.mem_range],
    rintro ⟨⟨k, hk⟩, rfl⟩,
    rintro ⟨c, hc⟩,
    simp only [function.comp_app, φ_eq, subtype.coe_mk],
    simp_rw conj_act.smul_def,
    simp only [equiv.perm.support_conj, finset.card_map], },
  { intro hk,
    obtain ⟨a, k1, _, hk1, hk2, _⟩ := is_surjective_aux g k _,
    use k1,
    { -- mem_stabilizer
      simp only [mul_action.mem_stabilizer_iff],
      simp only [has_smul.smul],
      change k1 * g * k1⁻¹ = g,
      simp only [← hk1, mul_inv_cancel_right], },
    { ext ⟨c, hc⟩ x,
      rw [φ_eq, ← hk2 ⟨c, hc⟩],
      refl, },
    exact λ c, (hk c).symm, },
end
 -/
/- lemma hφ_range : ((φ g).range : set (equiv.perm (g.cycle_factors_finset :
  set (equiv.perm α)))) = { k : equiv.perm (g.cycle_factors_finset) |
  ∀ (c : g.cycle_factors_finset), (k c: equiv.perm α).support.card = (c : equiv.perm α).support.card } :=
begin
  ext k,
  simp only [set_like.mem_coe, mem_range_φ],
  refl,
end
 -/

variable {g}
variables (a : g.cycle_factors_finset → α) (ha : ∀ (c : g.cycle_factors_finset), a c ∈ (c : equiv.perm α).support)

variable {a}
include ha

lemma same_cycle.is_cycle_of (c : g.cycle_factors_finset) {x}  (hx : g.same_cycle (a c) x) : g.cycle_of x = c :=
by rw [equiv.perm.cycle_is_cycle_of (ha c) (c.prop), equiv.perm.same_cycle.cycle_of_eq hx]

lemma same_cycle_of_mem_support_iff (c : g.cycle_factors_finset) {x} (hx : x ∈ g.support) : g.cycle_of x = c ↔ g.same_cycle (a c) x :=
begin
  rw equiv.perm.cycle_is_cycle_of (ha c) (c.prop),
  split,
  { intro hx',
    apply and.elim_left,
    rw ← equiv.perm.mem_support_cycle_of_iff,
    rw ← hx',
    rw equiv.perm.mem_support,
    rw equiv.perm.cycle_of_apply_self,
    rw ← equiv.perm.mem_support,
    exact hx,},
  { intro hx, rw same_cycle.is_cycle_of ha c hx,
    rw equiv.perm.cycle_is_cycle_of (ha c) (c.prop), },
end

lemma same_cycle_of_mem_support : ∀ x ∈ g.support, ∃ (c : g.cycle_factors_finset),
          g.same_cycle (a c) x :=
begin
  intros x hx,
  have hcx : g.cycle_of x ∈ g.cycle_factors_finset := equiv.perm.cycle_of_mem_cycle_factors_finset_iff.mpr hx,
  use ⟨g.cycle_of x, hcx⟩,
  rw ← same_cycle_of_mem_support_iff ha _ hx,
  refl,
end

variables (a) {g}
omit ha
def Kf : equiv.perm (g.cycle_factors_finset) → (g.cycle_factors_finset) × ℤ → α :=
    λ e ⟨c, i⟩, (g ^ i) (a (e c))

lemma Kf_apply {e : equiv.perm (g.cycle_factors_finset)} {c : g.cycle_factors_finset} {i : ℤ} :
    Kf a e ⟨c, i⟩ = (g ^ i) (a (e c)) := rfl

lemma Kf_apply' {e e' : equiv.perm (g.cycle_factors_finset)} {c : g.cycle_factors_finset} {i j : ℤ} :
  Kf a (e' * e) ⟨c, i + j⟩ = (g ^ i) (Kf a e' ⟨(e c), j⟩) :=
by simp only [Kf_apply, zpow_add, equiv.perm.coe_mul]

variable {a}
include ha
lemma ha' (c : g.cycle_factors_finset) :
  g.cycle_of (a c) = (c : equiv.perm α) :=
(equiv.perm.cycle_is_cycle_of (ha c) (c.prop)).symm

-- was ha
lemma ha'2 (c : g.cycle_factors_finset) : g (a c) ≠ (a c) :=
by { rw [← equiv.perm.mem_support,
  ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff ,
  ha' ha c], exact c.prop }

-- was ha''
lemma ha'3 (c : g.cycle_factors_finset) (i : ℤ) : g.cycle_of ((g ^ i) (a c)) = c :=
by rw [equiv.perm.cycle_of_self_apply_zpow, ha' ha]

lemma haK1 -- was haK
  (e : equiv.perm (g.cycle_factors_finset)) (c : g.cycle_factors_finset) (i : ℤ) :
  g.cycle_of (Kf a e ⟨c, i⟩) = e c :=
by rw [Kf_apply, equiv.perm.cycle_of_self_apply_zpow,
  equiv.perm.cycle_is_cycle_of (ha (e c)) (e c).prop]

lemma haK2 (e : equiv.perm (g.cycle_factors_finset)) (c : g.cycle_factors_finset) (i : ℤ) :
   g (Kf a e ⟨c,i⟩) = Kf a e ⟨c, i + 1⟩ :=
by rw [Kf_apply, Kf_apply,
    ← equiv.perm.mul_apply, ← zpow_one_add, add_comm 1 i]

lemma haK3 (e : equiv.perm (g.cycle_factors_finset)) (c d : g.cycle_factors_finset) (i : ℤ) (hd : d = e c):
   d (Kf a e ⟨c,i⟩) = Kf a e ⟨c, i + 1⟩ :=
-- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
begin
  rw hd,
  change (e c : equiv.perm α) _ = _,
  rw [← haK1 ha e c i, equiv.perm.cycle_of_apply_self, haK2 ha],
end

lemma haK4 (e : equiv.perm (g.cycle_factors_finset)) (c d : g.cycle_factors_finset) (i : ℤ) (hd' : d ≠ e c) :
   d (Kf a e ⟨c,i⟩) = Kf a e ⟨c, i⟩ :=
begin
  suffices hdc : (d : equiv.perm α).disjoint (e c : equiv.perm α),
  apply or.resolve_right (equiv.perm.disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩)),
  rw ← haK1 ha e c i,
  rw equiv.perm.cycle_of_apply_self ,
  rw ← equiv.perm.cycle_of_eq_one_iff,
  rw haK1 ha e c i,
  apply equiv.perm.is_cycle.ne_one ,
  refine (equiv.perm.mem_cycle_factors_finset_iff.mp _).1,
  exact g,
  exact (e c).prop,

  apply g.cycle_factors_finset_pairwise_disjoint d.prop (e c).prop,
  rw function.injective.ne_iff (subtype.coe_injective),
  exact hd',
end

lemma haK5 (τ : equiv.perm (g.cycle_factors_finset)) (x : α) (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf a 1 cj = x)) :
     function.extend (Kf a 1) (Kf a τ) id x = x :=
by simp only [function.extend_apply' _ _ _ hx, id.def]

lemma haK6 (x : α)
  (hx : x ∉ g.support) (c : g.cycle_factors_finset) : c x = x :=
begin
  change (c : equiv.perm α) x = x,
  rw ← equiv.perm.not_mem_support,
  intro hx',
  exact hx (equiv.perm.mem_cycle_factors_finset_support_le c.prop hx'),
end

/-
lemma haK6 (x : α)
  (hx : ¬ (∃ (cj : g.cycle_factors_finset × ℤ), Kf a 1 cj = x))
  (c : g.cycle_factors_finset) : c x = x :=
begin
  by_contradiction, apply hx,
  suffices h' : x ∈ (c : equiv.perm α).support,
  suffices : g.same_cycle (a c) x,
  { obtain ⟨i, hi⟩ := this,
    use ⟨c, i⟩,
    rw [Kf_apply, ← hi, equiv.perm.coe_one, id.def], },

  apply and.left,
  rw ← equiv.perm.mem_support_cycle_of_iff,
  rw ha' ha c,
  exact h',

  rw equiv.perm.mem_support, exact h,
end
-/

lemma hkfg (e e' : equiv.perm (g.cycle_factors_finset))
    (hee' : ∀ (c : g.cycle_factors_finset), (e c : equiv.perm α).support.card = (e' c : equiv.perm α).support.card) :
    (Kf a e').factors_through (Kf a e) :=
    --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
begin
  rintros ⟨c, i⟩ ⟨d, j⟩ He,
  change (g ^ i) (a (e c)) = (g ^ j) (a (e d)) at He,
  change (g ^ i) (a (e' c)) = (g ^ j) (a (e' d)),
  suffices hcd : c = d,
  { rw hcd at He ⊢,
    rw [g.zpow_eq_zpow_on_iff i j, ha' ha] at He,
    rw [g.zpow_eq_zpow_on_iff, ha' ha, ← hee' d],
    exact He,
    { exact ha'2 ha (e' d), },
    { exact ha'2 ha (e d), }, },
  { -- d = c
      apply equiv.injective e,
      rw [← subtype.coe_inj, ← ha'3 ha (e c) i, ← ha'3 ha (e d) j, He], },
end

variable a
omit ha
noncomputable def k := λ τ, function.extend (Kf a 1) (Kf a τ) id

variable {a}
include ha
lemma k_apply (c : g.cycle_factors_finset) (i : ℤ)
  {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) :
  k a τ (Kf a 1 ⟨c,i⟩) = Kf a τ ⟨c,i⟩ :=
begin
    simp only [k],
    rw function.factors_through.extend_apply (hkfg ha 1 τ _) id ⟨c,i⟩,
    { intro c, simp only [← hτ c, equiv.perm.coe_one, id.def], },
end

lemma k_apply_base (c : g.cycle_factors_finset)
  {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) :
  k a τ (a c) = a (τ c) := k_apply ha c 0 hτ

-- was k_apply'
lemma k_apply_of_not_mem_support {τ : equiv.perm (g.cycle_factors_finset)}
  (x : α) (hx : x ∉ g.support) : k a τ x = x :=
begin
    simp only [k],
    rw function.extend_apply',
    simp only [id.def],
    intro hyp,
    obtain ⟨⟨c, i⟩, rfl⟩ := hyp,
    apply hx,
    change (g ^ i) (a c) ∈ g.support,
    rw equiv.perm.zpow_apply_mem_support ,
    rw equiv.perm.mem_support,
    exact ha'2 ha c,
end

lemma mem_support_iff_exists_Kf (x : α) :
   x ∈ g.support ↔ ∃ (c : g.cycle_factors_finset) (i : ℤ), x = Kf a 1 ⟨c,i⟩ :=
begin
  split,
  { intro hx,
    rw ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff at hx,
    use ⟨g.cycle_of x, hx⟩,
    simp only [Kf_apply, equiv.perm.coe_one, id.def],
    specialize ha ⟨g.cycle_of x, hx⟩,
    simp only [subtype.coe_mk, equiv.perm.mem_support_cycle_of_iff] at ha,
    obtain ⟨i, hi⟩ := ha.1.symm, use i, exact hi.symm, },
  { rintro ⟨c, i, rfl⟩,
    simp only [Kf_apply, equiv.perm.zpow_apply_mem_support, equiv.perm.coe_one, id.def],
    apply equiv.perm.mem_cycle_factors_finset_support_le c.prop,
    exact ha c, }
end


lemma k_commute_zpow {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) (j : ℤ):
  (k a τ) ∘ (g ^ j : equiv.perm α) = (g  ^ j : equiv.perm α) ∘ (k a τ) :=
begin
  ext x,
  simp only [function.comp_app],
  by_cases hx : x ∈ g.support,
  { rw mem_support_iff_exists_Kf ha at hx,
    obtain ⟨c, i, rfl⟩ := hx,
    suffices : ∀ e, Kf a e (c, j + i) = (g ^ j) (Kf a e (c, i)),
    rw ← this 1,
    rw k_apply ha c (j + i) hτ,
    rw k_apply ha c i hτ,
    rw ← this τ,
    { intro e,
      simpa only [mul_one, equiv.perm.coe_one, id.def] using @Kf_apply' _ _ _ g a 1 e c j i, }, } ,
  { rw k_apply_of_not_mem_support ha x hx,
    rw k_apply_of_not_mem_support ha ((g ^ j : equiv.perm α) x) _,
    rw equiv.perm.zpow_apply_mem_support,
    exact hx, },
end

lemma k_commute {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) :
  (k a τ) ∘ g = g ∘ (k a τ) :=
by simpa only [zpow_one] using k_commute_zpow ha hτ 1

lemma k_apply_gen (c : g.cycle_factors_finset) (i : ℤ)
  {σ : equiv.perm (g.cycle_factors_finset)}
  (hσ : ∀ c, ((σ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card)
  {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) :
  k a τ (Kf a σ ⟨c,i⟩) = Kf a (τ * σ) ⟨c,i⟩ :=
begin
    simp only [Kf_apply],
    rw ← function.comp_apply (k a τ),
    rw k_commute_zpow ha hτ,
    rw function.comp_apply,
    apply congr_arg,
    dsimp,
    suffices : ∀ d (τ : equiv.perm (g.cycle_factors_finset)), a (τ d) = Kf a 1 (τ d, 0),
    rw [this _ σ, k_apply ha (σ c) 0 hτ, ← function.comp_apply τ σ c, ← equiv.perm.coe_mul, this _ (τ * σ)],
    refl,
    {intros d τ, rw Kf_apply, refl, },
end

lemma k_mul (σ : equiv.perm (g.cycle_factors_finset))
  (hσ : ∀ c, ((σ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card)
  (τ : equiv.perm (g.cycle_factors_finset))
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) :
  (k a σ) ∘ (k a τ) = k a (σ * τ) :=
begin
  ext x,
  simp only [function.comp_app],
  suffices hστ : ∀ c, (((σ * τ) c) : equiv.perm α).support.card = (c : equiv.perm α).support.card,

  by_cases hx : x ∈ g.support,
  { simp only [mem_support_iff_exists_Kf ha] at hx,
    obtain ⟨c, i, rfl⟩ := hx,
    simp only [k_apply ha c i hτ, k_apply_gen ha c i hτ hσ, k_apply ha c i hστ], },
  { simp only [k_apply_of_not_mem_support ha x hx], },

  { intro c, rw [equiv.perm.coe_mul, function.comp_app, hσ, hτ], }
end

lemma k_one : k a 1 = id :=
begin
  ext x,
  by_cases hx : x ∈ g.support,
  { simp only [mem_support_iff_exists_Kf ha] at hx,
    obtain ⟨c, i, rfl⟩ := hx,
    rw k_apply ha c i, refl,
    intro c, refl, },
  simp only [id.def, k_apply_of_not_mem_support ha x hx],
end

lemma k_bij {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card) :
  function.bijective (k a τ) :=
begin
  rw fintype.bijective_iff_surjective_and_card,
  refine and.intro _ rfl,
  rw function.surjective_iff_has_right_inverse,
  use k a τ⁻¹,
  rw function.right_inverse_iff_comp ,
  rw k_mul ha, rw mul_inv_self, rw k_one ha,
  exact hτ,
  intro c, rw  [← hτ (τ⁻¹ c), equiv.perm.apply_inv_self],
end

lemma k_cycle_apply {τ : equiv.perm (g.cycle_factors_finset)}
  (hτ : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card)
  (c : g.cycle_factors_finset) (x : α):
  k a τ (c x) = (τ c) (k a τ x) :=
begin
  by_cases hx : x ∈ g.support,
  { simp only [mem_support_iff_exists_Kf ha] at hx,
    obtain ⟨d, j, rfl⟩ := hx,
    by_cases hcd : c = d,
    { rw hcd, rw haK3 ha, rw k_apply ha _ _ hτ,
      dsimp,
      rw k_apply ha _ _ hτ,
      dsimp,
      rw ← haK3 ha τ d (τ d) j rfl,
      simp only [equiv.perm.coe_one, id.def], },
    { rw haK4 ha,
      rw k_apply ha _ _ hτ,
      dsimp,
      rw haK4 ha τ d (τ c) j _,
      rw function.injective.ne_iff (equiv.injective τ), exact hcd,
      simpa only [equiv.perm.coe_one, id.def, ne.def] using hcd, }, },
  { simp only [haK6 ha x hx, k_apply_of_not_mem_support ha x hx], },
end

omit ha
lemma hφ_eq_card_of_mem_range {τ} (hτ : τ ∈ (φ g).range) : ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card :=
begin
  rintro ⟨c, hc⟩,
  obtain ⟨⟨k, hk⟩, rfl⟩ := hτ,
  simp only [φ_eq, subtype.coe_mk,conj_act.smul_def,equiv.perm.support_conj, finset.card_map],
end

noncomputable def φ'_fun {τ : equiv.perm (g.cycle_factors_finset)} (hτ :∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card):
  equiv.perm α := equiv.of_bijective (k a τ) (k_bij ha hτ)

include ha
lemma φ'_mem_stabilizer {τ : equiv.perm (g.cycle_factors_finset)} (hτ :∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card):
   conj_act.to_conj_act (φ'_fun ha hτ) ∈  mul_action.stabilizer (conj_act (equiv.perm α)) g :=
begin
  rw mul_action.mem_stabilizer_iff,
  rw conj_act.smul_def,
  rw conj_act.of_conj_act_to_conj_act,
  rw mul_inv_eq_iff_eq_mul,
  ext x,
  simp only [equiv.perm.coe_mul],
  simp only [φ'_fun],
  simp only [function.comp_app, equiv.of_bijective_apply],
  rw [← function.comp_app (k a τ)],
  rw k_commute ha hτ,
end

omit ha
variable (g)
def Iφ : subgroup (equiv.perm (g.cycle_factors_finset)) := {
carrier   := { τ | ∀ c, (τ c : equiv.perm α).support.card = (c : equiv.perm α).support.card },
one_mem'  := by simp only [set.mem_set_of_eq, equiv.perm.coe_one, id.def, eq_self_iff_true, implies_true_iff],
mul_mem'  := λ σ τ hσ hτ,
begin
  simp only [set.mem_set_of_eq, equiv.perm.coe_mul, function.comp_app] at hσ hτ ⊢,
  intro c,
  rw hσ, rw hτ,
end,
inv_mem'  := λ σ hσ,
begin
  simp only [set.mem_set_of_eq, equiv.perm.coe_mul, function.comp_app] at hσ ⊢,
  intro c,
  rw ← hσ (σ⁻¹ c),
  simp only [equiv.perm.apply_inv_self],
end, }

variable {g}
lemma mem_Iφ_iff {τ : equiv.perm (g.cycle_factors_finset)} :
  τ ∈ (Iφ g) ↔ ∀  c, (τ c : equiv.perm α).support.card = (c : equiv.perm α).support.card :=
by { simp only [Iφ], refl }

include ha
noncomputable def φ' :
  Iφ g →* (mul_action.stabilizer (conj_act (equiv.perm α)) g) := {
to_fun    := λ τhτ,
  ⟨conj_act.to_conj_act (φ'_fun ha (mem_Iφ_iff.mp τhτ.prop)),
  φ'_mem_stabilizer ha (mem_Iφ_iff.mp τhτ.prop)⟩,
map_one'  :=
begin
  simp only [subgroup.coe_one, subgroup.mk_eq_one_iff, mul_equiv_class.map_eq_one_iff],
  ext x,
  simp only
  [φ'_fun, k_one ha, subtype.val_eq_coe, subgroup.coe_one,
    equiv.of_bijective_apply, equiv.perm.coe_one],
end,
map_mul'  := λ σ τ,
begin
  simp only [subgroup.coe_mul, submonoid.mk_mul_mk, subtype.mk_eq_mk, ← conj_act.to_conj_act_mul],
  apply congr_arg,
  ext x,
  simp only
  [φ'_fun, equiv.of_bijective_apply, subtype.val_eq_coe, subgroup.coe_mul,
    equiv.perm.coe_mul, function.comp_app,
    ← k_mul ha _ (σ.prop) _ (τ.prop)],
end }

lemma hφ'_is_right_inverse : ∀ τ, (φ g) ((φ' ha) τ) = (τ : equiv.perm (g.cycle_factors_finset)) :=
begin
  rintro ⟨τ, hτ⟩,
  apply equiv.perm.ext,
  rintro ⟨c, hc⟩,
  simp only [φ', φ'_fun],dsimp,
  ext x,
  rw φ_eq g,
  rw conj_act.smul_def , simp only [conj_act.of_conj_act_to_conj_act],
  apply congr_fun,
  dsimp,
  simp only [← equiv.perm.coe_mul],
  apply congr_arg,
  rw mul_inv_eq_iff_eq_mul,
  ext y,
  simp only [equiv.perm.coe_mul, function.comp_app, equiv.of_bijective_apply],
  exact k_cycle_apply ha hτ ⟨c, hc⟩ y,
end

lemma φ'_apply {τ} (hτ) (x): (conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))) x = k a τ x := rfl

lemma coe_φ' {τ} (hτ) : k a τ = conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α)) := rfl

example (τ) (hτ) :
  commute (conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))) g :=
begin
  rw [commute, semiconj_by],
--  simp only [φ', φ'_fun],
--  simp only [subgroup.coe_mk, monoid_hom.coe_mk, conj_act.of_conj_act_to_conj_act],
  -- simp only [equiv.perm.mul_def],
  rw ← equiv.coe_inj,
--  simp only [equiv.coe_trans],
  -- change (k a τ) ∘ g = g ∘ (k a τ),
  exact k_commute ha hτ,
end

example (τ) (hτ) :
  commute (conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))) g :=
begin
  rw [commute, semiconj_by, ← mul_inv_eq_iff_eq_mul],
  rw ← mul_action.conj_act.mem_stabilizer_iff,
  exact ((φ' ha) ⟨τ, hτ⟩).prop,
end

example (τ) (hτ) :
(conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))).support
≤ g.support :=
begin
  intros x,
  simp only [equiv.perm.mem_support, φ'_apply],
  intros hx' hx, apply hx',
  rw ← equiv.perm.not_mem_support at hx,
  exact k_apply_of_not_mem_support ha x hx,
end

example (τ) (hτ) :
(conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))) ∘ a
  = a ∘ τ :=
begin
  ext c,
  exact k_apply ha c 0 hτ,
end

example (τ) (hτ) :
∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act ((conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))))) • (c : equiv.perm α) = τ c :=
begin
  intro c,
  rw conj_act.to_conj_act_of_conj_act,
  simp only [φ', φ'_fun],
  simp only [subgroup.coe_mk, monoid_hom.coe_mk],
  rw conj_act.smul_def ,
  simp only [conj_act.of_conj_act_to_conj_act],
  rw mul_inv_eq_iff_eq_mul,
  ext x,
  exact k_cycle_apply ha hτ c x,
end

example (u v : equiv.perm α) (x : α) :
  u( v x) = (u*v) x :=
begin
refl,
end

example (τ) (hτ) (c : g.cycle_factors_finset) (m n : ℕ) :
  ((conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))) ^ m) ((g ^ n : equiv.perm α) (a c)) = (g ^ n) (a ((τ ^ m) c)) :=
begin
  suffices : ∀ (m n: ℕ), commute (((conj_act.of_conj_act (φ' ha ⟨τ, hτ⟩ : conj_act(equiv.perm α))) ^ m)) (g ^ n),
  simp only [commute, semiconj_by] at this,
  rw [← equiv.perm.mul_apply, this, equiv.perm.mul_apply, embedding_like.apply_eq_iff_eq],
  induction m with m hrec,
  { simp only [pow_zero, equiv.perm.coe_one, id.def], },
  { rw [pow_succ, equiv.perm.mul_apply],
    rw [hrec],
    rw φ'_apply ha hτ,
    rw k_apply_base ha _ hτ ,rw pow_succ, rw equiv.perm.coe_mul, },
  apply commute.pow_pow,

  rw [commute, semiconj_by, ← mul_inv_eq_iff_eq_mul],
  rw ← mul_action.conj_act.mem_stabilizer_iff,
  exact ((φ' ha) ⟨τ, hτ⟩).prop,

end


omit ha

variable (g)
lemma exists_base_points : ∃ (a : g.cycle_factors_finset → α),
  ∀ c, a c ∈ (c : equiv.perm α).support :=
begin
  suffices hsupp_ne :
    ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.nonempty,
  use λ c, (hsupp_ne c).some,
  intro c, exact (hsupp_ne c).some_spec,
  { intro c,
    exact equiv.perm.support_of_cycle_nonempty
      (equiv.perm.mem_cycle_factors_finset_iff.mp c.prop).1, },
end

variable {g}
lemma Iφ_eq_range : Iφ g = (φ g).range :=
begin
  obtain ⟨a, ha⟩ := exists_base_points g,
  ext τ,
  split,
  { intro hτ, rw monoid_hom.mem_range,
    use (φ' ha) ⟨τ, hτ⟩,
    rw [hφ'_is_right_inverse, subgroup.coe_mk], },
  { rw mem_Iφ_iff, exact hφ_eq_card_of_mem_range, }
end

lemma hφ_mem_range_iff {τ} : τ ∈ (φ g).range
  ↔  ∀ c, ((τ c) : equiv.perm α).support.card = (c : equiv.perm α).support.card :=
by { simp only [← Iφ_eq_range, mem_Iφ_iff], refl }

/- To get an automatic fintype instance, we view the lengths of the cycle to the fintype `fin (fintype.card α + 1)` -/

/-- The lengths of the cycles, as a fintype -/


def fsc : g.cycle_factors_finset → fin (fintype.card α + 1) :=
  λ c, ⟨(c : equiv.perm α).support.card, nat.lt_succ_iff.mpr (c : equiv.perm α).support.card_le_univ⟩

lemma hφ_range' :
  ((φ g).range : set (equiv.perm (g.cycle_factors_finset : set (equiv.perm α))))
  = { τ : equiv.perm (g.cycle_factors_finset) | fsc ∘ τ = fsc }  :=
begin
  rw ← Iφ_eq_range,
  ext τ,
  simp only [set_like.mem_coe, mem_Iφ_iff],
  change _ ↔ fsc ∘ τ= fsc,
  simp only [fsc],
  rw function.funext_iff,
  dsimp,
  apply forall_congr,
  intro c,
  rw ← function.injective.eq_iff (fin.coe_injective),
  simp only [fin.coe_mk],
end

lemma hφ_range_card' : fintype.card ((φ g).range)
= fintype.card { k : equiv.perm (g.cycle_factors_finset) | fsc ∘ k = fsc } :=
begin
  simp_rw ← hφ_range',
  simp only [set_like.coe_sort_coe],
end

example (l : list ℕ) (n : ℕ) (hn : ∀ i ∈ l, i < n) :
  (finset.range n).prod (λ i, (list.count i l).factorial)
  = (list.map (λ (i : ℕ), (list.count i l).factorial) l.dedup).prod  :=
begin
  rw ← list.prod_to_finset ,
  apply symm,
  apply finset.prod_subset_one_on_sdiff,
  { intros i hi, rw finset.mem_range, apply hn i,
    simpa only [list.mem_to_finset, list.mem_dedup] using hi, },
  { intros i hi,
    simp only [finset.mem_sdiff, finset.mem_range, list.mem_to_finset, list.mem_dedup] at hi,
    rw list.count_eq_zero_of_not_mem hi.2, exact nat.factorial_zero, },
  { intros i hi, refl, },
  exact list.nodup_dedup l,
end

lemma _root_.fintype.card_eq_count {ι : Type*} [decidable_eq ι] (f : ι → ℕ) (s : finset ι) (n : ℕ):
  finset.card { x ∈ s | f x = n} = multiset.count n (multiset.map f s.val) :=
begin
  induction s using finset.induction with a s has ih,
  simp only [finset.sep_def, finset.filter_true_of_mem, finset.not_mem_empty, is_empty.forall_iff, implies_true_iff,
  finset.card_empty, finset.empty_val, multiset.map_zero, multiset.count_zero],

  -- simp only [set.coe_set_of, finset.insert_val],
  rw finset.insert_val_of_not_mem has,
  rw multiset.map_cons,
  rw multiset.count_cons,
  simp only [finset.sep_def, finset.filter_congr_decidable] at ih ⊢,
  rw finset.filter_insert ,
  rw apply_ite (finset.card),
  rw finset.card_insert_of_not_mem (λ h, has (finset.mem_of_mem_filter a h)),

  by_cases h : f a = n,
  rw [if_pos h, if_pos h.symm, ih],
  rw [if_neg h, if_neg (ne.symm h), ih, add_zero],
end


lemma _root_.finset.card_eq_count' {ι : Type*} [decidable_eq ι]
  (f : ι → ℕ) (s : finset ι) (n : ℕ) :
  fintype.card { x : s | f x = n} = multiset.count n (multiset.map f s.val) :=
begin
  rw ← fintype.card_eq_count,
  rw ← fintype.card_coe,
  apply fintype.card_of_bijective _,
  exact λ ⟨⟨x, hx⟩, hx'⟩, ⟨x, begin
    simp only [set.mem_set_of_eq] at hx',
    simp only [finset.sep_def, finset.mem_filter],
    exact ⟨hx, hx'⟩, end⟩,
  { split,
    rintros ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ h,
    simpa only [subtype.mk_eq_mk] using h,
    rintro ⟨x, hx⟩,
    simp only [finset.sep_def, finset.mem_filter] at hx,
    use ⟨x, hx.1⟩, exact hx.2, },
end

@[to_additive] lemma _root_.multiset.prod_to_finset {α : Type*} {M : Type*} [decidable_eq α] [comm_monoid M]
  (f : α → M) : ∀ {m : multiset α} (hm : m.nodup), m.to_finset.prod f = (m.map f).prod :=
begin
  intros m hm,
  induction m using multiset.induction with a m ih,
  simp,
  obtain ⟨not_mem, hm⟩ := multiset.nodup_cons.mp hm,
  simp [finset.prod_insert (mt multiset.mem_to_finset.mp not_mem), ih hm],
 end

lemma hφ_range_card (m : multiset ℕ) (hg : g.cycle_type = m):
  fintype.card ((φ g).range)
= (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod :=
begin
  rw hφ_range_card',
  rw equiv.perm.of_partition_card ,
  suffices hlc  : ∀ (n : fin (fintype.card α + 1)),
    fintype.card {a : (g.cycle_factors_finset) | fsc a = n} = m.count ↑n,
  suffices hl_lt : ∀ i ∈ m, i < fintype.card α + 1,

  simp_rw hlc,
  rw finset.top_eq_univ,
  rw ← finset.prod_range (λ i, (m.count i).factorial),

  rw ← multiset.prod_to_finset ,
  apply symm,
  apply finset.prod_subset_one_on_sdiff,
  { intros i hi, rw finset.mem_range, apply hl_lt,
    simpa only [multiset.mem_to_finset, multiset.mem_dedup] using hi, },
  { intros i hi,
    simp only [finset.mem_sdiff, finset.mem_range, multiset.mem_to_finset, multiset.mem_dedup] at hi, simp only,
    rw multiset.count_eq_zero_of_not_mem hi.2,
    exact nat.factorial_zero, },
  { intros i hi, refl, },
  exact m.nodup_dedup,

  { intros i hi,
    rw nat.lt_succ_iff,
    apply le_trans _ (finset.card_le_univ g.support),
    apply equiv.perm.le_card_support_of_mem_cycle_type,
    rw hg, exact hi, },

  { rintro ⟨i, hi⟩,
    rw ← hg,
    rw equiv.perm.cycle_type_def ,

    simp only [fin.coe_mk],
    rw ← fintype.card_eq_count (finset.card ∘ equiv.perm.support) (g.cycle_factors_finset) i,
    rw ← fintype.card_coe,

    let u : {x : g.cycle_factors_finset | fsc x = ⟨i, hi⟩ }
      → { x ∈ g.cycle_factors_finset | (finset.card ∘ equiv.perm.support) x = i } :=
    λ ⟨⟨x, hx⟩, hx'⟩, ⟨x, begin
      simp only [set.mem_set_of_eq, fsc] at hx',
      simp only [subtype.coe_mk, fin.mk_eq_mk] at hx',
      simp only [finset.sep_def, finset.mem_filter, function.comp_app],
      exact ⟨hx, hx'⟩, end⟩,
    have : function.bijective u,
    { split,
      rintros ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ h,
      simpa only [u, subtype.mk_eq_mk] using h,
      rintro ⟨x, hx⟩,
      simp only [finset.sep_def, finset.mem_filter, function.comp_app] at hx,
      use ⟨x, hx.1⟩,
      simp only [fsc, subtype.coe_mk, fin.mk_eq_mk], exact hx.2, },
    apply fintype.card_of_bijective this, },
end


-- noyau : commute with each cycle of g
lemma hφ_mem_ker_iff' (z : equiv.perm α) :
  conj_act.to_conj_act z ∈
    subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker
  ↔ ∀ (t : equiv.perm α) (ht : t ∈ g.cycle_factors_finset), z * t = t * z :=
begin
  split,
  { intro hz,
    rw subgroup.mem_map at hz,
    obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz,
    simp only [monoid_hom.mem_ker] at hk,
    intros t ht,
    rw [← mul_inv_eq_iff_eq_mul, ← mul_aut.conj_apply, ← conj_act.of_conj_act_to_conj_act z,
      ← conj_act.smul_eq_mul_aut_conj _ t],
    rw ← hk',
    simp only [subgroup.coe_subtype, subgroup.coe_mk],
    simp only [← φ_eq g k hkK t ht, hk],
    refl, },
  { intro H,
    rw subgroup.mem_map,
    use conj_act.to_conj_act z,
    { rw mul_action.mem_stabilizer_iff,
      rw conj_act.smul_eq_mul_aut_conj,
      rw mul_aut.conj_apply,
      rw mul_inv_eq_iff_eq_mul,
      rw conj_act.of_conj_act_to_conj_act,
      exact equiv.perm.commute_of_mem_cycles_factors_commute z g H, },
    simp only [monoid_hom.mem_ker],
    split,
    { ext ⟨c, hc⟩,
      rw φ_eq',
      rw H c hc,
      simp only [mul_inv_cancel_right, equiv.perm.coe_one, id.def, subtype.coe_mk], },
    { simp only [subgroup.coe_subtype, subgroup.coe_mk], }, },
end

/-
lemma hφ_mem_ker_iff' (z : equiv.perm α) :
  conj_act.to_conj_act z ∈
    subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker
  ↔  ∀ (s : equiv.perm α) (hs : s ∈ g.cycle_factors_finset),
    ∃ (hs' : ∀ (x : α), x ∈ s.support ↔ z x ∈ s.support),
      equiv.perm.subtype_perm z hs' ∈ subgroup.zpowers (equiv.perm.subtype_perm g (equiv.perm.mem_cycle_factors_finset_support g s hs)) :=
begin
  rw hφ_mem_ker_iff,
  split,
  { intros H c hc,
    exact (equiv.perm.centralizer_mem_cycle_factors_iff g z c hc).mp (H c hc), },
  { intros H c hc,
    exact (equiv.perm.centralizer_mem_cycle_factors_iff g z c hc).mpr (H c hc), },
end
 -/

-- un groupe symétrique x produit de groupes cycliques
lemma hφ_mem_ker_iff (z : equiv.perm α) :
  conj_act.to_conj_act z ∈
    subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker
  ↔  ∀ (s : equiv.perm α) (hs : s ∈ g.cycle_factors_finset),
    ∃ (hs' : ∀ (x : α), x ∈ s.support ↔ z x ∈ s.support),
      (equiv.perm.subtype_perm z hs').of_subtype ∈ subgroup.zpowers s :=
begin
  rw hφ_mem_ker_iff',
  refine forall_congr _,
  intro c,
  refine forall_congr _,
  intro hc,
  rw equiv.perm.centralizer_mem_cycle_factors_iff g z c hc,
end

def ψ_aux (s : finset (equiv.perm α)) (hs : s ⊆ g.cycle_factors_finset) :
  (equiv.perm ((mul_action.fixed_by (equiv.perm α) α g))
  × Π (c ∈ s), subgroup.zpowers (c : equiv.perm α))
  → equiv.perm α :=
λ (uv : equiv.perm (mul_action.fixed_by (equiv.perm α) α g)
  × Π (c ∈ s), subgroup.zpowers (c : equiv.perm α)),
  uv.fst.of_subtype
  * s.noncomm_prod
      (λ c, dite (c ∈ s) (λ hc, uv.snd c hc) (λ hc, 1))(λ c hc d hd h,
  begin
    simp only [finset.mem_coe] at hc hd,
    rw dif_pos hc, rw dif_pos hd,
    obtain ⟨m, hc'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop,
    obtain ⟨n, hd'⟩ := subgroup.mem_zpowers_iff.mp (uv.snd d hd).prop,
    rw [← hc', ← hd'],
    apply commute.zpow_zpow,
    exact g.cycle_factors_finset_mem_commute (hs hc) (hs hd) h,
  end)

variable (g)
def ψ := ψ_aux g.cycle_factors_finset (finset.subset.refl g.cycle_factors_finset)

variable {g}
lemma hψ_1 (uv)
-- (uv : (equiv.perm ((mul_action.fixed_by (equiv.perm α) α g))  × Π (c ∈ g.cycle_factors_finset), subgroup.zpowers (c : equiv.perm α)))
    (x : α) (hx : x ∈ mul_action.fixed_by _ α g) :
  ψ g uv x = uv.fst ⟨x, hx⟩ :=
begin
  simp only [ψ, ψ_aux, equiv.perm.mul_apply],
  rw ← equiv.perm.of_subtype_apply_coe,
  apply congr_arg,
  simp only [subtype.coe_mk, ← equiv.perm.smul_def],
  rw ← mul_action.mem_stabilizer_iff,
  apply subgroup.noncomm_prod_mem,
  intros c hc,
  simp only [dif_pos hc],
  rw mul_action.mem_stabilizer_iff,
  simp only [equiv.perm.smul_def],
  simp only [mul_action.mem_fixed_by, equiv.perm.smul_def, ← equiv.perm.not_mem_support] at hx,
  simp only [← equiv.perm.not_mem_support],
  intro hx', apply hx,
  obtain ⟨m, hm⟩ := (uv.snd c hc).prop, rw ← hm at hx',
  apply equiv.perm.mem_cycle_factors_finset_support_le hc,
  apply equiv.perm.support_zpow_le c m,
  exact hx',
end

/- -- Useless
lemma hψ_2_aux {ι : Type*} [decidable_eq ι] (f : ι → equiv.perm α)
  (s : finset ι)
  (hs : ∀ (i ∈ s) (j ∈ s), commute (f i) (f j))
  (hs' : ∀ (i ∈ s) (j ∈ s), (f i).disjoint (f j))
  (a : α) (ha : ∀ (j ∈ s), a ∉ (f j).support) :
  s.noncomm_prod (λ i, f i) hs a = a :=
begin
  rw ← equiv.perm.smul_def,
  rw ← mul_action.mem_stabilizer_iff,
  apply subgroup.noncomm_prod_mem,
  intros i hi,
  rw mul_action.mem_stabilizer_iff, rw equiv.perm.smul_def,
  rw ← equiv.perm.not_mem_support,
  exact ha i hi,
end -/

lemma hψ_2 (uv) (x : α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (hx : c = g.cycle_of x) :
  ψ g uv x = (uv.snd c hc : equiv.perm α) x :=
begin
  revert uv x c hc hx,
  suffices : ∀ (s : finset (equiv.perm α)) (hs : s ⊆ g.cycle_factors_finset) (uvs) (x : α) (c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (hx : c = g.cycle_of x),
  ψ_aux s hs uvs x = dite (c ∈ s) (λ h, ((uvs.snd c h) : equiv.perm α) x) (λ h, x),

  intros uv x c hc hx,
  rw [ψ, this g.cycle_factors_finset (finset.subset.rfl) uv x c hc hx, dif_pos hc],

  intro s,
  induction s using finset.induction with d s hds ih,
  { intros hs uv x c hc hx,
    simp only [ψ_aux, finset.empty_subset, finset.not_mem_empty, not_false_iff, dif_neg, finset.noncomm_prod_empty, mul_one,
  prod.forall, forall_forall_const, forall_true_left],
  rw equiv.perm.of_subtype_apply_of_not_mem,
  simp only [mul_action.mem_fixed_by, equiv.perm.smul_def],
  rw [← ne.def, ← g.is_cycle_cycle_of_iff, ← hx],
  rw equiv.perm.mem_cycle_factors_finset_iff at hc,
  exact hc.1,  },
  { rintros hs ⟨u, v⟩ x c hc hx,

    have fixes_of_ne : ∀ (d ∈ g.cycle_factors_finset) (k : subgroup.zpowers d) (h : c ≠ d), (k : equiv.perm α) x = x,
    { intros d hd k h,
      obtain ⟨m, hm⟩ := k.prop,
      rw ← hm, rw ← equiv.perm.smul_def, rw ← mul_action.mem_stabilizer_iff,
      apply subgroup.zpow_mem,
      rw mul_action.mem_stabilizer_iff, rw equiv.perm.smul_def,
      apply or.resolve_left (equiv.perm.disjoint_iff_eq_or_eq.mp
        (g.cycle_factors_finset_pairwise_disjoint hc hd h) x),
      rw ← ne.def,
      rw ← equiv.perm.mem_support,
      rw hx,
      rw equiv.perm.mem_support_cycle_of_iff,
      split,
      exact equiv.perm.same_cycle.refl g x,
      rw ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff,
      rw ← hx, exact hc, },

    simp only [ψ_aux],
    rw finset.noncomm_prod_insert_of_not_mem' _ _ _ _ hds,
    simp only [dif_pos (finset.mem_insert_self d s)],
    rw ← mul_assoc,
    rw equiv.perm.mul_apply,

    suffices : ∀ (x ∈ s),
      dite (x ∈ insert d s) (λ h, ((v x h) : equiv.perm α)) (λ h, 1)
      = dite (x ∈ s) (λ h, ((v x (finset.mem_insert_of_mem h)) : equiv.perm α)) (λ h, 1),
    rw finset.noncomm_prod_congr rfl this,
    specialize ih (subset_trans (finset.subset_insert d s) hs)
      ⟨u, λ x h, v x (finset.mem_insert_of_mem h) ⟩
      (((v d (finset.mem_insert_self d s)) : equiv.perm α) x)
      c hc, -- (hs (finset.mem_insert_self d s)),
    simp only [ψ_aux] at ih,
    rw ih _,
    by_cases hcs : c ∈ s,
    { simp only [dif_pos hcs, dif_pos (finset.mem_insert_of_mem hcs)],
      apply congr_arg,
      apply fixes_of_ne,
      exact (hs (finset.mem_insert_self d s)),
      -- c ≠ d
      intro h, apply hds, rw ← h, exact hcs, },
    { -- by_cases : c ∉ s
      simp only [dif_neg hcs],
      by_cases hcd : c = d,
      { rw hcd, simp only [dif_pos (finset.mem_insert_self d s)], },
      rw dif_neg,
      apply fixes_of_ne,
      exact (hs (finset.mem_insert_self d s)),
      exact hcd,
      -- c ∉ insert d s
      intro h, rw finset.mem_insert at h,
      cases h with h h,
      exact hcd h,
      exact hcs h, },

    { -- c = g.cycle_of ((v d _) x)
      by_cases h : c = d,
      { obtain ⟨m, hm⟩ := (v d (finset.mem_insert_self d s)).prop,
        rw ← hm,
        rw ← h,
        rw hx, rw equiv.perm.cycle_of_zpow_apply_self,
        rw equiv.perm.cycle_of_self_apply_zpow,  },
      rw fixes_of_ne,
      exact hx,
      exact hs (finset.mem_insert_self d s),
      exact h, },

    { -- ∀ …
      intros k hks,
      simp only [dif_pos hks, dif_pos (finset.mem_insert_of_mem hks)] }, },
end

variable (g)
lemma hψ_inj : function.injective (ψ g) :=
begin
  intros uv uv' h,
  rw prod.ext_iff, split,
  { ext ⟨x, hx⟩, rw ← hψ_1 uv x hx, rw ← hψ_1 uv' x hx, rw h, },
  { ext c hc x,
    by_cases hx : c = g.cycle_of x,
    { rw ← hψ_2 uv x c hc hx, rw ← hψ_2 uv' x c hc hx, rw h, },
    { obtain ⟨m, hm⟩ := subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop,
      obtain ⟨n, hn⟩ := subgroup.mem_zpowers_iff.mp (uv'.snd c hc).prop,
      rw ← hm, rw ← hn,
      suffices : ∀ (n : ℤ), (c ^ n) x = x,
      { rw this n, rw this m, },
      suffices : c x = x,
      { change c • x = x at this,
        rw ← mul_action.mem_stabilizer_iff at this,
        intro n,
        change (c ^ n) • x = x,
        rw ← mul_action.mem_stabilizer_iff,
        apply subgroup.zpow_mem _ this, },
      { rw ← equiv.perm.not_mem_support, intro hx',
        apply hx, exact equiv.perm.cycle_is_cycle_of hx' hc, }, }, },
end

lemma hφ_ker_eq_ψ_range (z : equiv.perm α) :
  conj_act.to_conj_act z ∈
    subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker
  ↔  z ∈ set.range (ψ g) :=
begin
  rw hφ_mem_ker_iff,
  rw [set.mem_range],
  split,
  { intro Hz,
    have hu : ∀ (x : α),
      x ∈ mul_action.fixed_by (equiv.perm α) α g
      ↔ z x ∈ mul_action.fixed_by (equiv.perm α) α g,
    { intro x,
      simp only [mul_action.mem_fixed_by, equiv.perm.smul_def],
      simp only [← equiv.perm.not_mem_support],
      rw not_iff_not,
      split,
      { intro hx,
        let hx' := id hx,
        rw ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff at hx',
        obtain ⟨Hz'⟩ := Hz (g.cycle_of x) hx',
        specialize Hz' x,
        apply equiv.perm.mem_cycle_factors_finset_support_le hx',
        rw ← Hz',
        rw equiv.perm.mem_support_cycle_of_iff,
        exact ⟨equiv.perm.same_cycle.refl _ _, hx⟩, },
      { intro hzx,
        let hzx' := id hzx,
        rw ← equiv.perm.cycle_of_mem_cycle_factors_finset_iff at hzx',
        apply equiv.perm.mem_cycle_factors_finset_support_le hzx',
        obtain ⟨Hz'⟩ := Hz (g.cycle_of (z x)) hzx',
        rw Hz' x,
        rw equiv.perm.mem_support_cycle_of_iff,
        exact ⟨equiv.perm.same_cycle.refl _ _, hzx⟩, }, },
    let u := equiv.perm.subtype_perm z hu,
    let v : Π (c : equiv.perm α), c ∈ g.cycle_factors_finset → ↥(subgroup.zpowers c) :=
    λ c hc, ⟨equiv.perm.of_subtype
      (z.subtype_perm (classical.some (Hz c hc))), classical.some_spec (Hz c hc) ⟩,
    use ⟨u,v⟩,
    ext x,
    by_cases hx : x ∈ g.support,
      { rw hψ_2 ⟨u, v⟩ x (g.cycle_of x) _ rfl,
        simp only [subgroup.coe_mk],
        rw equiv.perm.of_subtype_apply_of_mem,
        simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
        rw [equiv.perm.mem_support, equiv.perm.cycle_of_apply_self, ← equiv.perm.mem_support], exact hx,
        rw equiv.perm.cycle_of_mem_cycle_factors_finset_iff, exact hx, },
      { rw [equiv.perm.not_mem_support, ← equiv.perm.smul_def, ← mul_action.mem_fixed_by]  at hx,
        rw hψ_1 ⟨u, v⟩ x hx,
        simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply], }, },
  { rintro ⟨⟨u, v⟩, h⟩,
    intros c hc,
    suffices hs' : ∀ (x : α), x ∈ c.support ↔ z x ∈ c.support,
    use hs',
    suffices : (z.subtype_perm hs').of_subtype = v c hc,
    rw this, apply set_like.coe_mem,
    { ext x,
      by_cases hx : x ∈ c.support,
      { rw equiv.perm.of_subtype_apply_of_mem,
        simp only [subtype.coe_mk, equiv.perm.subtype_perm_apply],
        rw ← h,
        rw hψ_2 ⟨u,v⟩ x,
        exact equiv.perm.cycle_is_cycle_of hx hc,
        exact hx, },
      { rw equiv.perm.of_subtype_apply_of_not_mem,
        apply symm, rw ← equiv.perm.not_mem_support,
        obtain ⟨m, hm⟩ := (v c hc).prop, rw ← hm,
        intro hx', apply hx,
        exact equiv.perm.support_zpow_le c m hx',
        exact hx, }, },

  { intro x,
    suffices : ∀ (d : equiv.perm α) (hd : d ∈ g.cycle_factors_finset), x ∈ d.support → z x ∈ d.support,

    split,
    exact this c hc,
    { intro hzx,
      by_cases hx : x ∈ g.support,
      { have hx'' : x ∈ (g.cycle_of x).support,
        { rw [equiv.perm.mem_support, equiv.perm.cycle_of_apply_self, ← equiv.perm.mem_support],
          exact hx, },
        have hc' := equiv.perm.cycle_of_mem_cycle_factors_finset_iff.mpr hx,
        suffices : c = g.cycle_of x,  rw this, exact hx'',
        specialize this (g.cycle_of x) hc' hx'',
        by_contradiction h,
        simp only [equiv.perm.mem_support] at this hzx,
        cases equiv.perm.disjoint_iff_eq_or_eq.mp
          (g.cycle_factors_finset_pairwise_disjoint hc hc' h) (z x) with h1 h2,
        exact hzx h1,
        exact this h2, },
    { exfalso,
      let hzx' := (equiv.perm.mem_cycle_factors_finset_support_le hc hzx),
      apply equiv.perm.mem_support.mp (equiv.perm.mem_cycle_factors_finset_support_le hc hzx),
      rw [← equiv.perm.smul_def, ← mul_action.mem_fixed_by],
      simp only [equiv.perm.not_mem_support, ← equiv.perm.smul_def, ← mul_action.mem_fixed_by] at hx,
      rw ← h,
      rw hψ_1 ⟨u,v⟩ x hx,
      apply subtype.mem, }, },

    { intros d hd,
      simp only [equiv.perm.mem_support],
      intro hx,
      rw ← h, rw hψ_2 ⟨u, v⟩ x d hd,
      obtain ⟨m, hm⟩ := (v d hd).prop, rw ← hm,
      intro hx', apply hx,
      simp only [← equiv.perm.mul_apply] at hx',
      have : d * (d ^ m) = d ^ m * d := commute.self_zpow d m,
      rw [this, equiv.perm.mul_apply] at hx',
      simp only [embedding_like.apply_eq_iff_eq] at hx',
      exact hx',
      rw ← equiv.perm.mem_support at hx,
      exact equiv.perm.cycle_is_cycle_of hx hd, }, }, },
end

lemma hψ_range_card' : fintype.card (set.range (ψ g)) = fintype.card (φ g).ker :=
begin
  classical,
  let u : ↥(set.range (ψ g)) → ↥(φ g).ker
  -- (subgroup.map (mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype (φ g).ker)
  := λ ⟨z, hz⟩,
  begin
    rw ← hφ_ker_eq_ψ_range g at hz,
    suffices : conj_act.to_conj_act z ∈ mul_action.stabilizer (conj_act (equiv.perm α)) g,
    use ⟨conj_act.to_conj_act z, this⟩,
    have hK : function.injective ((mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype),
    apply subgroup.subtype_injective,
    rw ← subgroup.mem_map_iff_mem hK,
    simp only [subgroup.coe_subtype, subgroup.coe_mk],
    exact hz,
    { obtain ⟨u, ⟨hu, hu'⟩⟩ := hz,
      rw ← hu', exact u.prop, },
  end,
  suffices : function.bijective u,
  exact fintype.card_of_bijective this,
  split,
  { -- injectivity
    rintros ⟨z, hz⟩ ⟨w, hw⟩ hzw,
    simpa only [subtype.mk_eq_mk, mul_equiv.apply_eq_iff_eq] using hzw, },
  { -- surjectivity
    rintro ⟨w, hw⟩,
    use conj_act.of_conj_act ((mul_action.stabilizer (conj_act (equiv.perm α)) g).subtype w),
    rw ← hφ_ker_eq_ψ_range,
    simp only [subgroup.coe_subtype, conj_act.to_conj_act_of_conj_act, subgroup.mem_map, set_like.coe_eq_coe, exists_prop, exists_eq_right, hw],
    simp only [subgroup.coe_subtype, conj_act.to_conj_act_of_conj_act, subtype.mk_eq_mk, set_like.eta], },
end

lemma equiv.perm.card_fixed_by (m : multiset ℕ) (hg : g.cycle_type = m) :
  fintype.card (mul_action.fixed_by (equiv.perm α) α g)
  = fintype.card α - m.sum :=
begin
  rw [← hg, equiv.perm.sum_cycle_type, ← finset.card_compl],
  simp only [fintype.card_of_finset, set.mem_compl_iff, finset.mem_coe, equiv.perm.mem_support, not_not],
  apply congr_arg,
  ext x,
  simp only [mul_action.mem_fixed_by, equiv.perm.smul_def, finset.mem_filter, finset.mem_univ, true_and, finset.mem_compl, equiv.perm.mem_support, not_not],
end

lemma fintype.card_pfun (p : Prop) [decidable p] (β : p → Type*) [∀ hp, fintype (β hp)] :
  fintype.card (Π (hp : p), β hp) = dite p (λ h, fintype.card (β h)) (λ h, 1) :=
begin
  by_cases hp : p,
  { simp only [dif_pos hp],
    rw fintype.card_eq,
    apply nonempty.intro,
    refine equiv.Pi_subsingleton (λ (a' : p), β a') hp, },
  { simp only [dif_neg hp],
    rw fintype.card_eq_one_iff,
    have : Π (h : p), β h := λ h, false.rec (β h) (hp h),
    use this,
    intro u, ext h, exfalso, exact hp h, },
end

variable {g}
lemma hψ_range_card (m : multiset ℕ) (hg : g.cycle_type = m) :
  fintype.card (set.range (ψ g)) =
  (fintype.card α - m.sum).factorial * m.prod :=
begin
  rw set.card_range_of_injective (hψ_inj g),
  rw fintype.card_prod,
  rw fintype.card_perm,
  rw fintype.card_pi,
  apply congr_arg2 (*),
  { -- fixed points
    apply congr_arg,
    exact equiv.perm.card_fixed_by g m hg, },
  { rw [← finset.prod_compl_mul_prod (g.cycle_factors_finset), ← hg],
    suffices : (g.cycle_factors_finsetᶜ.prod
      (λ (i : equiv.perm α), fintype.card (i ∈ g.cycle_factors_finset → ↥(subgroup.zpowers i)))) = 1,
    rw [this, one_mul],
    { -- on g.cycle_factors_finset
      simp only [equiv.perm.cycle_type, finset.prod],
      apply congr_arg,
      ext n,
      simp only [multiset.count_map],
      apply congr_arg,
      simp only [← finset.filter_val], apply congr_arg,
      ext a,
      simp only [finset.mem_filter],
      rw fintype.card_pfun,
      by_cases ha : a ∈ g.cycle_factors_finset,
      { simp only [dif_pos ha],
      rw ← order_eq_card_zpowers ,
      rw equiv.perm.order_of_is_cycle ,
      rw equiv.perm.mem_cycle_factors_finset_iff at ha, exact ha.1, },
      { simp only [ha, false_and], }, },
    { -- on g.cycle_factors_finsetᶜ
      apply finset.prod_eq_one,
        intros c hc,
        rw finset.mem_compl at hc,
        rw [fintype.card_pfun, dif_neg hc], }, },
end

-- Should one parenthesize the product ?
/-- Cardinality of a centralizer in `equiv.perm α` of a given `cycle_type` -/
theorem equiv.perm.conj_stabilizer_card (g : equiv.perm α) (m : multiset ℕ)
  (hg : g.cycle_type = m) :
  fintype.card (mul_action.stabilizer (conj_act (equiv.perm α)) g) =
    (fintype.card α - m.sum).factorial
      * m.prod
      * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod :=
begin
  rw subgroup.card_eq_card_quotient_mul_card_subgroup ((φ g).ker),
  rw fintype.card_congr (quotient_group.quotient_ker_equiv_range (φ g)).to_equiv,
  rw hφ_range_card m hg,
  rw mul_comm,
  apply congr_arg2 (*) _ rfl,
  rw ← hψ_range_card m hg,
  rw hψ_range_card',
end

lemma group.conj_class_eq_conj_orbit {G : Type*} [group G] (g : G) :
  { k : G | is_conj g k } = mul_action.orbit (conj_act G) g :=
begin
  ext k,
  simp only [set.mem_set_of_eq, is_conj_iff, mul_action.mem_orbit_iff, conj_act.smul_def],
  split,
  rintro ⟨c, hc⟩,
  use conj_act.to_conj_act c, simp only [hc, conj_act.of_conj_act_to_conj_act],
  rintro ⟨x, hx⟩,
  use conj_act.of_conj_act x, simp only [hx],
end

lemma equiv.perm.conj_class_card_mul_eq (g : equiv.perm α) (m : multiset ℕ)
  (hg : g.cycle_type = m) :
  fintype.card ({ h : equiv.perm α | is_conj g h})
    * (fintype.card α - m.sum).factorial
    * m.prod
    * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod
  = (fintype.card α).factorial :=
begin
  classical,
  simp_rw group.conj_class_eq_conj_orbit g,
  simp only [mul_assoc],
  rw mul_comm,
  simp only [← mul_assoc],
  rw ← equiv.perm.conj_stabilizer_card g m hg,
  rw mul_comm,
  rw mul_action.card_orbit_mul_card_stabilizer_eq_card_group (conj_act(equiv.perm α)) g,
  rw [conj_act.card, fintype.card_perm],
end

lemma multiset.prod_pos {R : Type*} [strict_ordered_comm_semiring R] [nontrivial R] (m : multiset R) (h : ∀ a ∈ m, (0 : R) < a) :
  0 < m.prod :=
begin
  induction m using multiset.induction with a m ih,
  { simp, },
  { rw multiset.prod_cons,
    exact mul_pos (h _ $ multiset.mem_cons_self _ _) (ih $ λ a ha, h a $ multiset.mem_cons_of_mem ha) }
end

/-- Cardinality of a conjugacy class in `equiv.perm α` of a given `cycle_type` -/
theorem equiv.perm.conj_class_card (g : equiv.perm α) (m : multiset ℕ)
  (hg : g.cycle_type = m) :
  fintype.card ({ h : equiv.perm α | is_conj g h}) =
    (fintype.card α).factorial
    / ((fintype.card α - m.sum).factorial
      * m.prod
      * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod) :=
begin
  rw ← equiv.perm.conj_class_card_mul_eq g m hg,
  rw nat.div_eq_of_eq_mul_left _,
  simp only [← mul_assoc],

  -- This is the cardinal of the centralizer
  rw ← equiv.perm.conj_stabilizer_card g m hg,
  refine fintype.card_pos,
end

variable (α)

theorem equiv.perm.card_of_cycle_type_mul_eq (m: multiset ℕ) :
  (finset.univ.filter (λ g: equiv.perm α,  g.cycle_type = m)).card
  * (((fintype.card α - m.sum).factorial *
    m.prod * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod))
  =
  ite ((m.sum ≤ fintype.card α) ∧ (∀ a ∈ m, 2 ≤ a)) (fintype.card α).factorial 0 :=
begin
  split_ifs with hm hm,
  { -- nonempty case
    obtain ⟨g, hg⟩ := equiv.perm_with_cycle_type_nonempty_iff.mp hm,
    suffices : (finset.univ.filter (λ h: equiv.perm α,  h.cycle_type = m))
       = finset.univ.filter (λh : equiv.perm α, is_conj g  h),
    rw this,
    rw ← fintype.card_coe,
    simp only [equiv.perm_with_cycle_type, finset.mem_filter] at hg,
    rw ← equiv.perm.conj_class_card_mul_eq g m hg.2,
    simp only [fintype.card_coe, ← set.to_finset_card, mul_assoc],
    apply congr_arg2 _,
    { apply congr_arg,
      ext,
      simp only [finset.mem_filter, finset.mem_univ, true_and, set.mem_to_finset, set.mem_set_of_eq], },
    refl,

    ext h, simp only [finset.mem_filter, finset.mem_univ, true_and, set.mem_to_finset, set.mem_set_of_eq],
    rw is_conj_comm, rw equiv.perm.is_conj_iff_cycle_type_eq,
    simp only [equiv.perm_with_cycle_type, finset.mem_filter] at hg,
    rw hg.2, },
  { convert zero_mul _,
    rw finset.card_eq_zero,
    rw ← finset.is_empty_coe_sort,
    rw ← not_nonempty_iff,
    intro h, apply hm,
    simp only [finset.nonempty_coe_sort] at h,
    rw equiv.perm_with_cycle_type_nonempty_iff,
    exact h, },
end

/-- Cardinality of the set of `equiv.perm α` of given `cycle_type` -/
theorem equiv.perm.card_of_cycle_type (m: multiset ℕ) :
  (finset.univ.filter (λ g: equiv.perm α,  g.cycle_type = m)).card =
  if ((m.sum ≤ fintype.card α) ∧ (∀ a ∈ m, 2 ≤ a))
  then (fintype.card α).factorial / (((fintype.card α - m.sum).factorial *
    m.prod * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod))
  else 0 :=
begin
  split_ifs with hm hm,
  { -- nonempty case
    obtain ⟨g, hg⟩ := equiv.perm_with_cycle_type_nonempty_iff.mp hm,
    simp only [equiv.perm_with_cycle_type, finset.mem_filter] at hg,
    rw ← equiv.perm.conj_class_card_mul_eq g m hg.2,
    simp only [mul_assoc],
    simp only [fintype.card_coe, ← set.to_finset_card, mul_assoc],
    rw nat.div_eq_of_eq_mul_left _,
    apply congr_arg2,
    { apply congr_arg,
      ext,
      simp only [set.mem_to_finset, set.mem_set_of_eq, finset.mem_filter, finset.mem_univ, true_and],
      rw [is_conj_comm, equiv.perm.is_conj_iff_cycle_type_eq, hg.2],
      },
    refl,
    -- This is the cardinal of the centralizer
    simp only [← mul_assoc],
    rw ← equiv.perm.conj_stabilizer_card g m hg.2,
    refine fintype.card_pos, },
  { rw [finset.card_eq_zero, ← finset.is_empty_coe_sort, ← not_nonempty_iff],
    simpa only [finset.nonempty_coe_sort, equiv.perm_with_cycle_type_nonempty_iff] using hm, },
end

lemma alternating_group.of_cycle_type_eq (m : multiset ℕ) :
  finset.map ⟨subgroup.subtype (alternating_group α), subgroup.subtype_injective _⟩
      (finset.univ.filter (λ g : alternating_group α, (g : equiv.perm α).cycle_type = m))
      = ite (even (m.sum + m.card)) (finset.univ.filter (λ g : equiv.perm α, g.cycle_type = m)) ∅
:=
begin
  split_ifs with hm hm,
  { ext g, -- split,
    simp only [finset.mem_image, finset.mem_filter],
    split,
    { intro hg, rw finset.mem_map at hg,
      obtain ⟨⟨k, hk⟩, hk', rfl⟩ := hg,
      apply and.intro (finset.mem_univ _),
      simp only [finset.mem_filter, finset.mem_univ, subgroup.coe_mk, true_and] at hk',
      simp only [subgroup.coe_subtype, function.embedding.coe_fn_mk, subgroup.coe_mk],
      exact hk', },
    { rintro ⟨_, hg⟩,
      simp only [subgroup.coe_subtype, finset.mem_map, finset.mem_filter, finset.mem_univ, true_and, function.embedding.coe_fn_mk,
  exists_prop],
      use g,
      rw [equiv.perm.mem_alternating_group, equiv.perm.sign_of_cycle_type, hg, even.neg_one_pow hm],
      simp only [subgroup.coe_mk, subgroup.coe_subtype],
      exact ⟨hg, rfl⟩, }, },
  { rw finset.eq_empty_iff_forall_not_mem,
    intros g hg,
    simp only [subgroup.coe_subtype, finset.mem_map, finset.mem_filter, finset.mem_univ, true_and, function.embedding.coe_fn_mk,
  exists_prop] at hg,
    obtain ⟨⟨k, hk⟩, hkm, rfl⟩ := hg,
    rw ← nat.odd_iff_not_even at hm,
    simp only [subgroup.coe_mk] at hkm,
    simpa [equiv.perm.mem_alternating_group, equiv.perm.sign_of_cycle_type, hkm, odd.neg_one_pow hm, ← units.eq_iff] using hk, },
end


theorem alternating_group.card_of_cycle_type_mul_eq (m: multiset ℕ) :
  (finset.univ.filter (λ g: alternating_group α,  (g : equiv.perm α).cycle_type = m)).card * (((fintype.card α - m.sum).factorial *
    (m.prod * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod))) =
  ite (((m.sum ≤ fintype.card α) ∧ (∀ a ∈ m, 2 ≤ a)) ∧ even (m.sum + m.card))
  (fintype.card α).factorial 0 :=
begin
  split_ifs with hm hm,
  -- by_cases hm : (m.sum ≤ fintype.card α ∧ ∀ a ∈ m, 2 ≤ a),
  -- cases nat.even_or_odd (m.sum + m.card) with hm' hm',
  { -- m is an even cycle_type
    rw ← finset.card_map,
    rw alternating_group.of_cycle_type_eq,
    rw if_pos,
    have := equiv.perm.card_of_cycle_type_mul_eq α m,
    simp only [mul_assoc] at this,
    rw this,
    rw if_pos,
    exact hm.1,
    exact hm.2, },
  { -- m does not correspond to a permutation, or to an odd one,
    rw ← finset.card_map,
    rw alternating_group.of_cycle_type_eq,
    rw apply_ite finset.card,
    rw finset.card_empty,
    rw not_and_distrib at hm,
    by_cases hm' : even (m.sum + m.card),
    rw if_pos,
    rw equiv.perm.card_of_cycle_type,
    rw if_neg,
    exact zero_mul _,
    cases hm with hm hm, exact hm, exfalso, exact hm hm',
    exact hm',
    rw if_neg, exact zero_mul _, exact hm', },
end

theorem alternating_group.card_of_cycle_type (m: multiset ℕ) :
  (finset.univ.filter (λ g: alternating_group α,  (g : equiv.perm α).cycle_type = m)).card =
  if ((m.sum ≤ fintype.card α) ∧ (∀ a ∈ m, 2 ≤ a)) ∧ even (m.sum + m.card)
  then (fintype.card α).factorial / (((fintype.card α - m.sum).factorial *
    (m.prod * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod)))
  else 0 :=
begin
  split_ifs with hm hm,
  -- by_cases hm : (m.sum ≤ fintype.card α ∧ ∀ a ∈ m, 2 ≤ a),
  -- cases nat.even_or_odd (m.sum + m.card) with hm' hm',
  { -- m is an even cycle_type
    rw ← finset.card_map,
    rw alternating_group.of_cycle_type_eq,
    rw if_pos,
    rw equiv.perm.card_of_cycle_type α m,
    rw if_pos,
    simp only [mul_assoc],
    exact hm.1,
    exact hm.2, },
  { -- m does not correspond to a permutation, or to an odd one,
    rw ← finset.card_map,
    rw alternating_group.of_cycle_type_eq,
    rw apply_ite finset.card,
    rw finset.card_empty,
    rw not_and_distrib at hm,
    by_cases hm' : even (m.sum + m.card),
    rw if_pos,
    rw equiv.perm.card_of_cycle_type,
    rw if_neg,
    cases hm with hm hm, exact hm, exfalso, exact hm hm',
    exact hm',
    rw if_neg, exact hm', },
end


variable {α}

/- TODO !
Lorsque G est un groupe fini, H un sous-groupe d'indice 2,
la classe de conjugaison dans G d'un élément g ∈ H
C_H(g) ⬝ Z_H(g) = card H
C_G(g) ⬝ Z_G(g) = card G = 2 card H
Si Z_G(g) ≤ H, alors Z_H(g) = Z_G(g), donc C_G(g) = 2 ⬝ C_H(g)
sinon, Z_H(g) est d'indice 2 dans Z_G(g) et C_G(g) = C_H(g)
-/

/-
/-- Cardinality of a centralizer in `alternating_group α` of a given `cycle_type`-/
theorem alternating_group.conj_stabilizer_card (g : alternating_group α) (m : multiset ℕ)
  (hg : (g : equiv.perm α).cycle_type = m) :
  nat.card (mul_action.stabilizer (conj_act (alternating_group α)) g) =
    (((fintype.card α - m.sum).factorial
    * (fintype.card α - m.sum).factorial
    * m.prod * (m.dedup.map (λ (n : ℕ), (m.count n).factorial)).prod))
    / (ite ((∀ i ∈ m, odd i) ∧ m.sum + 1 ≥ fintype.card α) 2 1) := sorry
-/

/-

lemma sign_of_lift (g : equiv.perm α) (τ: equiv.perm (g.cycle_factors_finset))
  (H : ∀ c : g.cycle_factors_finset, (c : equiv.perm α).support.card = ((τ c) : equiv.perm α).support.card)
  (a : g.cycle_factors_finset → α) (k : equiv.perm α)
    (ha : ∀ (c : g.cycle_factors_finset), a c ∈ (c : equiv.perm α).support)
    (hgk : g * k = k * g)
    (hkc : ∀ (c : g.cycle_factors_finset), (conj_act.to_conj_act k) • (c : equiv.perm α) = τ c)
    (hka : k ∘ a = a ∘ τ) :
  let hτ_supp_ne : ∀ (d : equiv.perm (g.cycle_factors_finset)) (hd : d ∈ τ.cycle_factors_finset), d.support.nonempty := λ d hd, equiv.perm.support_of_cycle_nonempty (equiv.perm.mem_cycle_factors_finset_iff.mp hd).left
  in let fτn : equiv.perm (g.cycle_factors_finset) → ℕ := λ d, dite (d ∈ τ.cycle_factors_finset) (λ hd, (hτ_supp_ne d hd).some.val.support.card) (λ hd, 0)
  in k.sign = τ.cycle_factors_finset.prod (λ d, d.sign ^ (fτn d)) :=
  begin
  /- chaque cycle de τ donne lieu à des cycles de k en nombre égal au cardinal du support commun des éléments du cycle

    cycle (c1 ... cr), où les ci sont des cycles de g
   -/
  intros hτ_supp_ne fτn,
  /- let fτg : τ.cycle_factors_finset → g.cycle_factors_finset := λ d, (hτ_supp_ne d).some,
  let fgn : g.cycle_factors_finset → ℕ := λ c, c.val.support.card,
  let fτn := fgn ∘ fτg, -/
  have : ∀ (d : equiv.perm g.cycle_factors_finset) (hd : d ∈ τ.cycle_factors_finset)
    (c : g.cycle_factors_finset) (hc: c ∈ d.support), c.val.support.card = fτn d,
  begin
  { intros d hd c hc,
    suffices : ∃ (k : ℕ), (d ^ k) (hτ_supp_ne d hd).some = c,
    obtain ⟨k, rfl⟩ := this,
    rw equiv.perm.pow_apply_mem_support at hc,
    induction k with k hk,
    { dsimp only [fτn],
      rw dif_pos,
      simp only [subtype.val_eq_coe, pow_zero, equiv.perm.coe_one, id.def], },
    { rw [pow_succ, equiv.perm.mul_apply],
      suffices : d _ = τ _,
      rw this,
      rw ← hk,
      apply symm, exact H _,
      convert equiv.perm.cycle_of_apply_self _ _,
      refine equiv.perm.cycle_is_cycle_of _ hd,
      rw equiv.perm.pow_apply_mem_support, exact hc, },
    apply equiv.perm.is_cycle.exists_pow_eq ,
    exact (equiv.perm.mem_cycle_factors_finset_iff.mp hd).left,
    exact equiv.perm.mem_support.mp (hτ_supp_ne d hd).some_spec,
    exact equiv.perm.mem_support.mp hc, },
  end,

  sorry,
end

-/

example (g c : equiv.perm α) (hc : c ∈ g.cycle_factors_finset) (a : α)
  (ha : a ∈ g.support) :
  a ∈ c.support ↔ c = g.cycle_of a :=
begin
split,
{ intro ha',
  exact equiv.perm.cycle_is_cycle_of ha' hc, },
{ intro hc,
  rw [hc, equiv.perm.mem_support, equiv.perm.cycle_of_apply_self],
  simpa only [equiv.perm.mem_support] using ha, }
end


lemma sign_ψ (s : finset (equiv.perm α)) (hs : s ⊆ g.cycle_factors_finset)  (uv : equiv.perm (mul_action.fixed_by (equiv.perm α) α g)) (k : Π (c ∈ s), subgroup.zpowers (c : equiv.perm α)) :
  (on_cycle_factors.ψ_aux s hs ⟨uv, k⟩).sign
  = uv.sign * s.prod (λi,
    equiv.perm.sign (dite (i ∈ s) (λ (hc : i ∈ s), ((k i hc) : equiv.perm α)) (λ (hc : i ∉ s), 1))
  ) :=
begin
  dsimp only [ψ_aux],
  simp only [equiv.perm.sign_mul, equiv.perm.sign_of_subtype],
  rw finset.noncomm_prod_map,
  rw finset.noncomm_prod_eq_prod ,
end


end on_cycle_factors



#exit


section junk

variables (α : Type*) [decidable_eq α] [fintype α]


def K4'  := finset.filter (λ g : equiv.perm (fin 4), g = 1 ∨ (equiv.perm.cycle_type g = {2,2}))
  (set.univ).to_finset

#check K4'

/- Lean calcule K4.card = 4 mais c'est lent ! -/
-- #eval K4.card

/- c = {c1,...,cm}
  on choisit un cycle de longueur c1 : n!/(n-c1)! c1
  un autre de longueur c2 : (n-c1)!/(n-c1-c2)! c2
  etc., ce qui donne n!/((n - c.sum)! * c.prod)
  et il reste à diviser par les permutations possibles des cycles de même longueur :
  pour chaque k, dk = nombre de i tq ci = k
  diviser par prod (dk!) -/


def foo (c : multiset ℕ) (n : ℕ) := if (c.sum ≤ n) then
  n.factorial / ((n - c.sum).factorial * c.prod
  * multiset.prod ((multiset.map (λ n, (multiset.count n c).factorial) c.dedup)))
else 0

#eval foo {2} 5
#eval foo {2,2} 4
#eval foo {2,4} 5

def f : list ℕ → list ℕ
  | [] := list.nil
  | (a :: l) := (a :: list.map (nat.add a) (f l))

#eval f [2,5,9]

def list.ranges' : list ℕ → list (finset ℕ)
  | [] := list.nil
  | (a :: l) := (finset.range(a) :: list.map (finset.image (nat.add a)) (list.ranges' l))

#eval list.ranges' [2,5,4]

end junk



open_locale classical

example {G : Type*} [decidable_eq G] [fintype G] [group G] (H : subgroup G) :
  fintype.card H = fintype.card (H : set G) :=
begin
  simp only [set_like.coe_sort_coe],
end


lemma subgroup.card_subtype {G H : Type*} [fintype G] [fintype H] [group G] [group H]
  (K : subgroup G) (L : subgroup K):
fintype.card L = fintype.card (subgroup.map K.subtype L) :=
begin
  let φ := K.subtype.comp L.subtype,
  rw fintype.card_congr (equiv.of_injective ⇑φ _),
  simp only [φ],
  suffices : set.range φ = ↑(subgroup.map K.subtype L),
  simp_rw this, refl,
  simp only [φ, subgroup.coe_map, monoid_hom.coe_comp] ,
  simp_rw set.range_comp,
  apply congr_arg _,
  simp only [set.range_id', set.image_univ],
  conv_rhs { rw ← subgroup.subtype_range L,  },
  refl,
  -- φ inj
  simp only [φ, subgroup.coe_map, monoid_hom.coe_comp, subgroup.coe_subtype],
  rw function.injective.of_comp_iff ;
  refine subtype.coe_injective,
end


example {G H : Type*} [fintype G] [fintype H] [group G] [group H] (K : subgroup G)
(L : subgroup K):
fintype.card L = fintype.card (subgroup.map K.subtype L) :=
begin
  let f : ↥L → ↥(subgroup.map K.subtype L) := λ ⟨x, hx⟩, ⟨K.subtype x, begin use x, simp only [set_like.mem_coe, eq_self_iff_true, and_true, hx], end⟩,
  suffices : function.bijective f,
  apply fintype.card_of_bijective this,
  split,
end


/-
-- squeeze_simp,
  rw subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
rw fintype.card_congr (quotient_group.quotient_ker_equiv_range φ).to_equiv,
  simp only [φ],
suffices : φ.ker = ⊥,
simp only [subgroup.subtype_range, subgroup.ker_subtype],
have := monoid_hom.of_injective (hφ),
rw ← subgroup.top_subgroup_of ,
rw subgroup.subgroup_of_map_subtype,
simp only [top_inf_eq],
rw subgroup.card_eq_card_quotient_mul_card_subgroup (K.subtype.ker),
rw fintype.card_congr (quotient_group.quotient_ker_equiv_range K.subtype).to_equiv,
simp only [subgroup.subtype_range, subgroup.ker_subtype, subgroup.card_bot, mul_one],
end -/



example (f : equiv.perm α) (x : α) (hx : f x = x) (n : ℤ) : (f ^ n) x = x :=
begin
  change f • x = x at hx,
  rw ← mul_action.mem_stabilizer_iff at hx,
  change (f ^ n) • x = x,
  rw ← mul_action.mem_stabilizer_iff,
  apply subgroup.zpow_mem _ hx,
end



lemma lemm_card_product (g : equiv.perm α) :
  fintype.card (Π (c ∈  g.cycle_factors_finset), subgroup.zpowers c) =
  finset.prod (g.cycle_factors_finset) (λ c : equiv.perm α, c.support.card) :=
begin
  rw fintype.card_pi,
  rw ← finset.union_compl (g.cycle_factors_finset),
  rw finset.prod_union _,
  rw ← mul_one (finset.prod (g.cycle_factors_finset) (λ c : equiv.perm α, c.support.card)),
  apply congr_arg2,
  { apply finset.prod_congr rfl,
    intros c hc,
    let e : (c ∈ g.cycle_factors_finset → (subgroup.zpowers c)) ≃ (subgroup.zpowers c) :=
    { to_fun := λ f, f hc,
      inv_fun := λ x, function.const _ x,
      left_inv := λ f, funext (λ hc', rfl),
      right_inv := λ x, by simp only, },
    rw fintype.card_congr e,
    rw ← order_eq_card_zpowers,
    apply equiv.perm.order_of_is_cycle,
    exact (equiv.perm.mem_cycle_factors_finset_iff.mp hc).1, },
  { rw ← finset.prod_const_one,
    apply finset.prod_congr rfl,
    intros c hc,
    simp at hc,
    rw fintype.card_eq_one_iff_nonempty_unique,
    have e : (c ∈ g.cycle_factors_finset → (subgroup.zpowers c)) :=
      λ h, false.rec ↥(subgroup.zpowers c) (hc h),
    use e,
    intro f, apply funext, intro h, exfalso, exact hc h, },
  { simp only [finset.disjoint_right, finset.mem_compl, imp_self, forall_const], },
end


example (c : equiv.perm α) (x : α) :
  x ∈ c.support ↔ c x ∈ c.support := equiv.perm.apply_mem_support.symm

/-  -- Should be useless
lemma equiv.perm.of_subtype_of_subtype_perm_of_support (c : equiv.perm α) :
  c.subtype_perm_of_support.of_subtype = c :=
begin
  ext x,
  by_cases hx : x ∈ c.support,
  { apply equiv.perm.of_subtype_apply_of_mem, exact hx, },
  { rw equiv.perm.of_subtype_apply_of_not_mem,
    rw [equiv.perm.mem_support, not_not] at hx, exact hx.symm,
    exact hx, },
end

lemma equiv.perm.subtype_perm_of_support_apply_of_mem (c : equiv.perm α)
  (x : α) (hx : x ∈ c.support) :
    (c.subtype_perm_of_support (⟨x, hx⟩ : c.support) : α) = c x :=
begin
  simp only [equiv.perm.subtype_perm_of_support],
  simp only [equiv.perm.apply_mem_support, imp_self, implies_true_iff, subtype.coe_mk,
    equiv.perm.subtype_perm_of_fintype_apply],
end

lemma equiv.perm.subtype_perm_of_support_apply_pow_of_mem (c : equiv.perm α)
  (x : α) (hx : x ∈ c.support) (n : ℕ) :
    (((c.subtype_perm_of_support) ^ n) (⟨x, hx⟩ : c.support) : α) = (c ^ n) x :=
begin
  simp only [equiv.perm.subtype_perm_of_support],
  induction n with n hrec,
  { -- zero case
    simp only [pow_zero, equiv.perm.coe_one, id.def, subtype.coe_mk], },
  { -- induction case
    simp only [pow_succ],
    simp only [equiv.perm.apply_mem_support, imp_self, implies_true_iff, equiv.perm.coe_mul,
      function.comp_app, equiv.perm.subtype_perm_of_fintype_apply, subtype.coe_mk,
      embedding_like.apply_eq_iff_eq],
    exact hrec, }
end

lemma equiv.perm.subtype_perm_of_support_apply_zpow_of_mem (c : equiv.perm α)
  (x : α) (hx : x ∈ c.support) (i : ℤ) :
    (((c.subtype_perm_of_support) ^ i) (⟨x, hx⟩ : c.support) : α) = (c ^ i) x :=
begin
  induction i,
  -- nat case
  apply equiv.perm.subtype_perm_of_support_apply_pow_of_mem,
  -- neg_succ case
  simp only [zpow_neg_succ_of_nat],
  apply equiv.injective (c ^ (i+1)),
  simp only [equiv.perm.apply_inv_self],
  rw ← equiv.perm.subtype_perm_of_support_apply_pow_of_mem,
  simp only [finset.mk_coe, equiv.perm.apply_inv_self, subtype.coe_mk],
  apply finset.coe_mem,
end

lemma equiv.perm.subtype_perm_of_support_support {c : equiv.perm α} :
  (c.subtype_perm_of_support).support = ⊤ :=
begin
  simp only [equiv.perm.subtype_perm_of_support],
  rw eq_top_iff,
  rintros ⟨x, hx⟩ _,
  rw equiv.perm.mem_support,
  intro hx_eq,
  rw ← subtype.coe_inj at hx_eq,
  simp only [equiv.perm.apply_mem_support, imp_self, implies_true_iff, subtype.coe_mk,
    equiv.perm.subtype_perm_of_fintype_apply] at hx_eq,
  rw equiv.perm.mem_support at hx,
  exact hx hx_eq,
end
-/

example (g : equiv.perm α) (hg : g.is_cycle) : g.support.nonempty :=
begin
sorry,
end

example (g : equiv.perm α) (s : finset α) (hs : ∀ (x : α), x ∈ s ↔ g x ∈ s) (i : ℤ) :
  ∀ (x : α), x ∈ s ↔ (g ^ i) x ∈ s :=
begin
  intro x,
--  library_search,
sorry
end



example (s : finset α) : s → α := coe

example {α β : Type*} (a b : α) (e : α ≃ β) : a = b ↔ e a = e b :=
begin
  refine (equiv.apply_eq_iff_eq e).symm,
end

#check equiv.perm.cycle_factors_finset_pairwise_disjoint,
example (f g : equiv.perm α) (hfg : disjoint f.support g.support) :
  commute f g :=
begin
end

example {G : Type*} [group G] (H : subgroup G) (K : subgroup H) : subgroup G :=
begin
  refine subgroup.map H.subtype K,
end

example (s t : finset α) (hst : s.card = t.card): (s ≃ t) :=
begin
  exact finset.equiv_of_card_eq hst,
end

example (s t : finset α) (hst : s ≃ t) : equiv.perm α :=
begin
  exact equiv.extend_subtype hst,
end

example {ι : Type*} (s : finset ι) (l : ι → equiv.perm α) : equiv.perm α :=
begin
  apply  finset.noncomm_prod s l _,

end


theorem equiv.perm_with_list_cycle_type_card (c : list ℕ)  :
  (equiv.perm_with_cycle_type α c).card
  * (fintype.card α - c.sum).factorial * c.prod
  * list.prod (list.map (λ n, (list.count n c).factorial) c.dedup)
  = if ((c.sum ≤ fintype.card α) ∧ (∀ a ∈ c, 2 ≤ a)) then (fintype.card α).factorial else 0 :=
begin
  split_ifs with hc hc,
  { -- nonempty case
    obtain ⟨g₀, hg₀⟩ := equiv.perm_with_cycle_type_nonempty_iff.mp hc,
    simp only [equiv.perm_with_cycle_type, set.to_finset_univ, finset.mem_filter,
      finset.mem_univ, true_and] at hg₀,
    have c_eq_orb : equiv.perm_with_cycle_type α c
      = (mul_action.orbit (conj_act (equiv.perm α)) g₀).to_finset,
    { ext g,
      simp only [equiv.perm_with_cycle_type],
      simp only [set.to_finset_univ, finset.mem_filter, finset.mem_univ,
        true_and, set.mem_to_finset],
      rw ← hg₀,
      rw ← equiv.perm.is_conj_iff_cycle_type_eq,
      rw mul_action.mem_orbit_iff,
      simp only [is_conj_iff],
      split,
      { rintro ⟨k, hk⟩,
        use conj_act.to_conj_act k⁻¹,
        rw ← hk,
        simp only [has_smul.smul],
        simp only [← mul_assoc, conj_act.of_conj_act_to_conj_act,
          mul_left_inv, one_mul, inv_inv, inv_mul_cancel_right], },
      { rintro ⟨x, hx⟩,
        use conj_act.of_conj_act x⁻¹,
        simp only [has_smul.smul] at hx,
        rw ← hx,
        simp only [← mul_assoc],
        simp only [conj_act.of_conj_act_inv, mul_left_inv,
          one_mul, inv_inv, inv_mul_cancel_right], }, },

    have c_eq_orb' : (equiv.perm_with_cycle_type α ↑c).card =
       fintype.card (mul_action.orbit (conj_act (equiv.perm α)) g₀),
    simp only [c_eq_orb, set.to_finset_card],
    rw c_eq_orb',
    simp only [mul_assoc],

    rw ← equiv.perm_conj_stabilizer_card g₀ c hg₀,

    rw mul_action.card_orbit_mul_card_stabilizer_eq_card_group,
    rw ← fintype.card_perm,
    rw conj_act.card, },
  { -- empty case
    suffices : (equiv.perm_with_cycle_type α c) = ∅,
    simp only [hc, this, finset.card_empty, zero_mul, if_false],
    rw ← finset.not_nonempty_iff_eq_empty ,
    intro h,
    rw ← equiv.perm_with_cycle_type_nonempty_iff at h,
    exact hc h, },
end

example (c : multiset ℕ) : c.to_list.prod = c.prod :=
by simp only [multiset.prod_to_list]

example {β : Type*} (c : list α) (f : α → β) :
  (multiset.map f ↑c) = list.map f c :=  by simp only [multiset.coe_map]

theorem equiv.perm_with_cycle_type_card (c : multiset ℕ)  :
  (equiv.perm_with_cycle_type α c).card
  * (fintype.card α - c.sum).factorial * c.prod
  * multiset.prod (multiset.map (λ n, (multiset.count n c).factorial) c.dedup)
  = if ((c.sum ≤ fintype.card α) ∧ (∀ a ∈ c, 2 ≤ a)) then (fintype.card α).factorial else 0 :=
begin
  rw ← multiset.coe_to_list c,
  convert equiv.perm_with_list_cycle_type_card c.to_list,
  simp only [multiset.coe_to_list, multiset.sum_to_list],
  simp only [multiset.coe_to_list, multiset.prod_to_list],
  { rw [multiset.coe_dedup, multiset.coe_map, multiset.coe_prod],
    apply congr_arg,
    apply congr_arg2 list.map rfl,
    refl, },
  simp only [multiset.coe_to_list, multiset.sum_to_list],
end

def S4 := equiv.perm (fin 4)
def A4 := alternating_group (fin 4)
def K4 := commutator A4



variable (α)
def equiv.perm_with_cycle_type_card_eq (c : multiset ℕ) :=
  if ((c.sum ≤ fintype.card α) ∧ (∀ a ∈ c, 2 ≤ a))
  then (fintype.card α).factorial / ((fintype.card α - c.sum).factorial * c.prod
      * multiset.prod (multiset.map (λ n, (multiset.count n c).factorial) c.dedup))
  else 0

#check equiv.perm_with_cycle_type_card_eq

#eval equiv.perm_with_cycle_type_card_eq (fin 9) {2,2}

/- N = nombre de 2-sylow de A4 :
 #A4 = 12
  N | 3
  N = 1 mod 2
  donc N = 1 ou 3
  il faudrait dire N = 1… -/
