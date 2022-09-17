/-
Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL
-/

import tactic
import logic.equiv.basic
import .mul_action_finset

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

def list.ranges : list ℕ → list (list ℕ)
  | [] := list.nil
  | (a :: l) := (list.range(a) :: list.map (list.map (nat.add a)) (list.ranges l))

#eval list.ranges [2,5,4]

lemma list.disjoint_map {α β : Type*} (f : α → β) (s t : list α)
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

lemma list.disjoint_pmap {α β : Type*} {p : α → Prop} (f : Π (a : α), p a → β) (s t : list α)
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

def list.mk_subtype {α : Type*} {p : α → Prop} :
  Π (l : list α) (hl : ∀ a ∈ l, p a), list (subtype p)
| [] := λ _, list.nil
| (a :: l) := λ hl, (⟨a, hl a (list.mem_cons_self a l)⟩ ::
  list.mk_subtype l (λ b hb, hl b (list.mem_cons_of_mem a hb)))

lemma list.coe_mk {α → Type*} (p :α → Prop) (l : list α) (hl : ∀ a ∈ l, p a) :
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

def list.mk_subtype' {α : Type*} (p : α → Prop) (l : list α) (hl : ∀ a ∈ l, p a) :
  list (subtype p) :=
  list.pmap (λ (a : α) (ha : p a), (⟨a, ha⟩ : subtype p)) l hl

lemma list.coe_mk' {α → Type*} (p :α → Prop) (l : list α) (hl : ∀ a ∈ l, p a) :
  list.map coe (list.mk_subtype' p l hl) = l :=
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

example (p : α → Prop) [decidable_pred p] (s : finset α) (hs : ∀ a ∈ s, p a) :
  finset.image coe (finset.subtype p s) = s :=
begin
  ext,
  simp only [finset.mem_image, finset.mem_subtype, exists_prop, subtype.exists,
    subtype.coe_mk, exists_eq_right_right, and_iff_right_iff_imp],
  exact hs a,
end

example {α β : Type*} (f : α → β) (hf : function.injective f) (l : list (set α))
  (hl : list.pairwise disjoint l) :
  list.pairwise disjoint (list.map (set.image f) l) :=
begin
  rw list.pairwise_map,
  simp_rw set.disjoint_image_iff hf,
  exact hl,
end

def equiv.perm_with_cycle_type (c : multiset ℕ) :=
  finset.filter (λ (g : equiv.perm α), equiv.perm.cycle_type g = c) (set.univ).to_finset

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

lemma equiv.perm_with_cycle_type_nonempty_iff {c : list ℕ} :
  (c.sum ≤ fintype.card α ∧ (∀ a ∈ c, 2 ≤ a)) ↔ (equiv.perm_with_cycle_type α (c : multiset ℕ)).nonempty :=
begin
  split,
  { rintro ⟨hc, h2c⟩,
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := list.exists_pw_disjoint_with_card hc,
    use list.prod (list.map (λ l, list.form_perm l) p),
    simp only [equiv.perm_with_cycle_type, finset.mem_filter, set.to_finset_univ,
      finset.mem_univ, true_and],
    have hp2 : ∀ (x : list α) (hx : x ∈ p), 2 ≤ x.length,
    { intros x hx,
      apply h2c x.length,
      rw [← hp_length, list.mem_map],
      exact ⟨x, hx, rfl⟩, },
    rw equiv.perm.cycle_type_eq _ rfl,
    { -- lengths
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
    rw [← multiset.coe_sum, ← hg, equiv.perm.sum_cycle_type ],
    exact (equiv.perm.support g).card_le_univ,
    intros a ha,
    rw [← multiset.mem_coe, ← hg] at ha,
    exact equiv.perm.two_le_of_mem_cycle_type ha, },
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

def equiv.perm.cycle_factors_smul (g : equiv.perm α) :
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
    end⟩ } }


example {c : multiset ℕ} :
  (equiv.perm_with_cycle_type α c).card
  * (fintype.card α - c.sum).factorial * c.prod
  * multiset.prod (multiset.map (λ n, (multiset.count n c).factorial) c.dedup)
  = if (c.sum ≤ fintype.card α ∧ (∀ a ∈ c, 2 ≤ a)) then (fintype.card α).factorial else 0 :=
sorry

open_locale classical

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

example (g : equiv.perm α) :
  mul_action.stabilizer (conj_act (equiv.perm α)) g ≃* subgroup.centralizer (subgroup.zpowers g) :=
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

lemma equiv.perm_conj_stabilizer_card (g : equiv.perm α) (c : list ℕ)
  (hc : g.cycle_type = c) :
  fintype.card (mul_action.stabilizer (conj_act (equiv.perm α)) g) =
   (fintype.card α - c.sum).factorial * (c.prod *
    (list.map (λ (n : ℕ), (list.count n c).factorial) c.dedup).prod) :=
begin
  -- regarder l'action du stabilizateur sur g.cycle_factors
  -- on obtient un morphisme vers un produit de groupes symétriques
  -- il est surjectif
  -- noyau : un groupe symétrique x produit de groupes cycliques
  sorry
end

theorem equiv.perm_with_cycle_type_card {c : list ℕ}  :
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


def S4 := equiv.perm (fin 4)
def A4 := alternating_group (fin 4)
def K4 := commutator A4


/-- N = nombre de 2-sylow de A4 :
 #A4 = 12
  N | 3
  N = 1 mod 2
  donc N = 1 ou 3
  il faudrait dire N = 1… -/

#check K
