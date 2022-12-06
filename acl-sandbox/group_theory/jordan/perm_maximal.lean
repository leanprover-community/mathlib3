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

import .for_mathlib.alternating
import .for_mathlib.group_theory__subgroup__basic

import .primitive
import .multiple_transitivity
-- import .sub_mul_actions


import .jordan

/-# Maximal subgroups of the symmetric groups



-/
open_locale pointwise

open mul_action

/- section stabilizer

variables (G : Type*) [group G] {α : Type*} [mul_action G α]

-- open_locale classical pointwise
/-- The instance that makes the stabilizer of a set acting on that set -/
instance has_smul.stabilizer (s : set α) :
  has_smul ↥(stabilizer G s) ↥s := {
smul := λ ⟨g, hg⟩ ⟨x, hx⟩, ⟨g • x,
  begin
    rw ← mem_stabilizer_iff.mp hg,
    exact set.smul_mem_smul_set hx,
  end⟩, }

@[simp]
lemma has_smul.stabilizer_def  (s : set α)
  (g : stabilizer G s) (x : s) : coe (g • x)  = (g : G) • (x : α) :=
begin
  rw ← subtype.coe_eta g g.prop,
  rw ← subtype.coe_eta x x.prop,
  refl,
end

/-- The mul_action of stabilizer a set on that set -/
instance mul_action.of_stabilizer (s : set α) :
  mul_action (stabilizer G s) s := {
one_smul := λ ⟨x, hx⟩,
by  rw [← subtype.coe_inj, has_smul.stabilizer_def, subgroup.coe_one, one_smul],
mul_smul := λ ⟨g, hg⟩ ⟨k, hk⟩ ⟨x, hx⟩,
begin
  rw [← subtype.coe_inj, submonoid.mk_mul_mk],
  simp only [has_smul.stabilizer_def, subtype.coe_mk, mul_action.mul_smul],
end }

lemma mul_action.of_stabilizer_def (s : set α) (g : stabilizer G s) (x : s) :
  (g : G) • (x : α) = g • (x : α) := rfl

lemma mul_action.of_stabilizer_set_def (s : set α) (g : stabilizer G s) (t : set α) :
  (g : G) • t = g • t :=
begin
refl,
end

end stabilizer -/

section action_on_finsets

variables (α : Type*) [decidable_eq α] (G : Type*) [group G] [mul_action G α]
variable (n : ℕ)

def nat.finset := { s : finset α | s.card = n}

variables {α G}
lemma finset.smul_card_eq (s : finset α) (g : G) :
  (g • s).card = s.card :=
begin
  change (finset.image (λ x, g • x) s).card = _,
  rw finset.card_image_of_injective,
  exact mul_action.injective g,
end

lemma is_eq_iff_is_le (s t : n.finset α) :
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

variables (α G)
def nat.finset.mul_action.finset' :
  sub_mul_action G (finset α) := {
carrier := n.finset α,
smul_mem' :=  λ g s hs,
begin
  change (g • s).card = n,
  change s.card = n at hs,
  rw ← hs,
  rw finset.smul_card_eq,
end }

instance nat.finset.mul_action.finset :
  mul_action G (n.finset α) := (nat.finset.mul_action.finset' α G n).mul_action

variables {α G}
@[simp]
lemma nat.finset.mul_action.finset_apply {g : G} {s : finset α} {hs : s ∈ n.finset α} :
  ↑(g • (⟨s, hs⟩ : n.finset α)) = g • s := rfl

@[simp]
lemma nat.finset.mul_action.coe_apply' (g : G) (s : n.finset α) :
  ↑(g • s) = g • (↑s : finset α) :=  rfl

lemma smul_ne_iff_has_mem_not_mem {s t : n.finset α} {g : equiv.perm α} :
  g • s ≠ t ↔
  ∃ (a : α) (ha : a ∈ (s : finset α)), a ∉ g⁻¹ • (t : finset α) :=
begin
  rw ← finset.not_subset ,
  rw not_iff_comm, rw not_not,
  rw ← nat.finset.mul_action.finset_apply n,
  rw ← finset.le_eq_subset,
  rw subtype.coe_le_coe,
  simp only [subtype.coe_eta],
  rw ← is_eq_iff_is_le,
  rw smul_eq_iff_eq_inv_smul g,
  exact t.prop,
end

theorem nat.finset.mul_action_faithful (α : Type*) [decidable_eq α] [fintype α]
  (n : ℕ) (hn : 1 ≤ n) (hα : n < fintype.card α) (g : equiv.perm α) (hg : g ≠ 1) :
  ∃ (s : n.finset α), g • s ≠ s :=
  --  mul_action.fixed_by (perm α) (action_on_pairs_of (perm α) α) g ≠ ⊤ :=
begin
  have : ∃ (a : α), g • a ≠ a,
  { by_contradiction,
    push_neg at h,
    apply hg,
    ext a,
    simpa only using h a,  },
  obtain ⟨a, ha⟩ := this,
  suffices : ∃ (s : finset α), s.card = n ∧ {a} ⊆ s ∧ s ⊆ {g • a}ᶜ,
  obtain ⟨s, hs, ha, ha'0⟩ := this,
  rw finset.singleton_subset_iff at ha,
  have ha' : g • a ∉ s,
  { intro h,
    simpa only [finset.mem_compl, finset.mem_singleton, eq_self_iff_true, not_true] using ha'0 h, },
  use ⟨s, hs⟩,
  { -- g • s ≠ s,
    intro h,
    rw ← subtype.coe_inj at h,
    change g • s = s at h,
    suffices : a ∉  s,
    exact this ha,
    exfalso, apply ha',
    rw ← h,
    rw finset.mem_smul_finset,
    use ⟨a, ha, rfl⟩ },
  -- ∃ (s : finset α), s.card = n ∧ a ∈ s ∧ g • a ∉ s,

  have hA : ({a} : finset α) ⊆ { g • a }ᶜ,
  { simp only [finset.singleton_subset_iff, finset.mem_compl, finset.mem_singleton],
    intro h, exact ha h.symm, },
  obtain ⟨s, ha, ha', hs⟩ := finset.exists_intermediate_set (n - 1) _ hA,
  use s,
  split,
  rw [hs, finset.card_singleton ],
  rw nat.sub_add_cancel hn,
  split, exact ha, exact ha',

  -- n - 1 + {a}.card ≤ {g • a}ᶜ.card
  simp only [finset.card_singleton, nat.sub_add_cancel hn, finset.card_compl ],
  exact nat.le_pred_of_lt hα,
end


example {s : set α} {a : α} {g : equiv.perm α} :
  a ∉ g⁻¹ • s ↔ g • a ∈ sᶜ :=
begin
  rw set.mem_smul_set_iff_inv_smul_mem, rw inv_inv, rw ← set.mem_compl_iff,
end


variable (α)
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

variables {α n}
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
  simp only [fin.mk_eq_mk],
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

variable [fintype α]

theorem nat.finset_nontrivial (h1 : 0 < n) (h2 : n < fintype.card α): nontrivial (n.finset α) :=
begin
  suffices : nonempty (n.finset α),
  obtain ⟨s, hs⟩ := this,
  change s.card = n at hs,
  let h'1 := id h1,
  rw [← hs, finset.card_pos] at h'1, obtain ⟨a, ha⟩ := h'1,
  let h'2 := id h2,
  rw [← hs, finset.card_lt_iff_ne_univ, ne.def, ← finset.coe_eq_univ, ← ne.def,
    set.ne_univ_iff_exists_not_mem] at h'2,
  obtain ⟨b, hb⟩ := h'2,
  let t : finset α := insert b (finset.erase s a),
  rw nontrivial_iff ,
  use ⟨s, hs⟩,
  use t,
  change t.card = n,
  rw finset.card_insert_of_not_mem,
  rw finset.card_erase_of_mem ha,
  rw hs, rw nat.sub_add_cancel , exact h1,
  intro h, apply hb, apply finset.erase_subset , exact h,
  intro h, rw subtype.mk_eq_mk at h, apply hb, rw h, exact finset.mem_insert_self b _,

  obtain ⟨s, hs, hs'⟩ := finset.exists_smaller_set finset.univ n _,
  use ⟨s, hs'⟩, apply_instance, exact le_of_lt h2,
end

theorem nat.finset_is_pretransitive : is_pretransitive (equiv.perm α) (n.finset α) :=
begin
  refine is_pretransitive_of_surjective_map (embedding_to_finset.map_surjective) _,
  apply is_pretransitive.mk,
  intros f f',
  have hα : n ≤ fintype.card α,
  { rw ← fintype.card_fin n, exact fintype.card_le_of_embedding f },
  /- have hα' : ↑n ≤ enat.card α,
  { unfold enat.card,
    rw enat.coe_nat_le_iff_le,
    refine le_trans _ (cardinal.mk_set_le (set.range f)),
    apply le_of_eq,
    rw ← cardinal.lift_inj ,
    rw cardinal.mk_range_eq_lift (embedding_like.injective f),
    simp only [cardinal.lift_nat_cast, cardinal.mk_fin] },
 -/
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
  simp only [part_enat.card_eq_coe_fintype_card],
  simp only [part_enat.card_eq_coe_fintype_card],
end

/- lemma exists_covby_le {α : Type*} [partial_order α] [fintype α] (a b : α) (hab : a < b):
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
-/

/- example (s t : set α) (g : G) : g • s ⊆ t ↔ s ⊆ g⁻¹ • t :=
begin
exact set.set_smul_subset_iff,
end

example (s t : finset α) (g : G) : g • s ⊆ t ↔ s ⊆ g⁻¹ • t :=
begin
simp only [← finset.coe_subset, finset.coe_smul_finset],
exact set.set_smul_subset_iff,
end

lemma exc (s t : n.finset α) (g : equiv.perm α) :
  g • s ≤ t ↔ g • (s : set α) ≤ t :=
begin
simp only [coe_coe, set.le_eq_subset],
change g • ↑s ≤ ↑t ↔ _,
change ⟨g • ↑↑ s,_⟩ ≤ ↑t ↔ _,

end

lemma exa' (s t : n.finset α) (g : equiv.perm α) :
  g • s ≤ t ↔ s ≤ g⁻¹ • t :=
begin
  rw ← exa, rw ← exa,
  exact smul_eq_iff_eq_inv_smul g,
end

lemma exb {s t : n.finset α} {g : equiv.perm α} :
  g • s ≠ t ↔
  ∃ (a : α) (ha : a ∈ (s : finset α)), a ∉ g⁻¹ • (t : finset α) :=
begin
  rw ← finset.not_subset ,
  rw not_iff_comm, rw not_not,
  rw ← nat.finset.mul_action.finset_apply n,
  rw ← finset.le_eq_subset,
  rw subtype.coe_le_coe,
  simp only [subtype.coe_eta],
  rw ← is_eq_iff_is_le,
  rw smul_eq_iff_eq_inv_smul g,
  exact t.prop,
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

    rw nat.finset.mul_action.finset_apply' α (equiv.perm α) n
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
 -/

open_locale classical

lemma set.subset_of_eq {α : Type*} {s t : set α} (h : s = t) : s ⊆ t := h ▸ set.subset.refl _

lemma le_stabilizer_iff (G : Type*) [group G] [mul_action G α] (s : set α) (H : subgroup G) :
  H ≤ stabilizer G s ↔ ∀ g ∈ H, g • s ⊆ s :=
begin
  split,
  { intros hyp g hg,
    apply set.subset_of_eq,
    rw ← mem_stabilizer_iff,
    exact hyp hg, },
  intro hyp,
  intros g hg,
  rw mem_stabilizer_iff,
  apply subset_antisymm,
  exact hyp g hg,
  intros x hx, use g⁻¹ • x, split,
  apply hyp g⁻¹ (inv_mem hg),
  simp only [set.smul_mem_smul_set_iff, hx],
  simp only [smul_inv_smul],
end

lemma is_pretransitive.of_partition (G : Type*) [group G] [mul_action G α] (s : set α) :
  (∀ (a ∈ s) (b ∈ s), ∃ (g : G), g • a = b) →
  (∀ (a ∈ sᶜ) (b ∈ sᶜ), ∃ (g : G), g • a = b) →
  (stabilizer G s ≠ ⊤) →
  -- (∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b) →
  is_pretransitive G α :=
begin
  intros hs hs' hG,
  suffices hss' : (∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b),
  obtain ⟨a, b, g, ha, hb, hgab⟩ := hss',
  apply is_pretransitive.mk_base a,
  intro x,
  cases em (x ∈ s) with hx hx',
  exact hs a ha x hx,
  rw ← set.mem_compl_iff at hx',
  obtain ⟨k, hk⟩ := hs' b hb x hx',
  use k * g,
  rw [mul_action.mul_smul, hgab, hk],
  --
  by_contradiction hyp,
  push_neg at hyp,
  apply hG,
  rw [eq_top_iff, mul_action.le_stabilizer_iff],
  intros g _,
  rintros b ⟨a, ha, hgab⟩,
  by_contradiction hb,
  exact hyp a b g ha (set.mem_compl hb) hgab,
end

lemma swap_mem_stabilizer {a b : α} {s : set α} (ha : a ∈ s) (hb : b ∈ s) :
  equiv.swap a b ∈ stabilizer (equiv.perm α) s :=
begin
  suffices : (equiv.swap a b) • s ⊆ s,
  { rw mem_stabilizer_iff,
    apply set.subset.antisymm,
    exact this,
    exact set.subset_set_smul_iff.mpr this, },
  rintros _ ⟨x, hx, rfl⟩,
  simp only [equiv.perm.smul_def],
  cases em (x = a) with hxa hxa',
  rw [hxa, equiv.swap_apply_left], exact hb,
  cases em (x = b) with hxb hxb',
  rw [hxb, equiv.swap_apply_right], exact ha,
  rw equiv.swap_apply_of_ne_of_ne hxa' hxb', exact hx,
end

lemma ne_one_of_is_swap {f : equiv.perm α} (hf : f.is_swap) : f ≠ 1 :=
begin
  intro h1,
  obtain ⟨x, y, hxy, h⟩ := hf,
  rw h1 at h, apply hxy,
  rw ← equiv.swap_apply_left x y, rw ← h,
  simp only [equiv.perm.coe_one, id.def],
end

lemma swap_is_swap_iff {a b : α} : (equiv.swap a b).is_swap ↔ a ≠ b :=
begin
  split,
  { intros h hab,
    suffices : equiv.swap a b ≠ 1,
    { apply this,
      rw [← hab, equiv.swap_self],
      ext x, simp only [equiv.coe_refl, equiv.perm.coe_one], },
    exact ne_one_of_is_swap h, },
  { intro h, use a, use b, exact ⟨h, rfl⟩, },
end

lemma fintype.card_add_compl (s : set α) : fintype.card s + fintype.card (sᶜ : set α) = fintype.card α :=
begin
  rw fintype.card_compl_set ,
  rw add_comm,
  rw nat.sub_add_cancel,
  exact set_fintype_card_le_univ s,
end

lemma card_smul_eq (s : set α) (g : equiv.perm α) : fintype.card (g • s : set α)  = fintype.card s :=
begin
  rw ← set.coe_to_finset s,
  simp only [← set.to_finset_card],
  change ((λ x, g • x) '' ↑(s.to_finset)).to_finset.card = _,
  simp_rw ← finset.coe_image ,
  simp only [finset.to_finset_coe],
  rw finset.card_image_of_injective _ (mul_action.injective g),
end

lemma moves_in (G : subgroup (equiv.perm α)) (t : set α) (hGt : stabilizer (equiv.perm α) t < G) :
  ∀ (a ∈ t) (b ∈ t), ∃ (g : G), g • a = b :=
begin
  intros a ha b hb,
  use equiv.swap a b,
  apply le_of_lt hGt,
  apply swap_mem_stabilizer ha hb,
  change (equiv.swap a b) • a = b,
  simp only [equiv.perm.smul_def],
  rw equiv.swap_apply_left,
end

example (s : finset α) (g : equiv.perm α) : (g • s).card  = s.card :=
begin
  change (finset.image (λ x, g • x)  s).card = _,
  rw finset.card_image_of_injective _ (mul_action.injective g),
end

example (s t : set α) (hst : s ⊆ t) : fintype.card s ≤ fintype.card t :=
begin
  exact set.card_le_of_subset hst,
end

lemma nat.add_lt_of_le_lt (a b c d : ℕ) (hab : a ≤ c) (hbd : b < d) : a + b < c + d :=
begin
apply nat.lt_of_lt_of_le,
apply nat.add_lt_add_left _ a, use d, exact hbd,
apply nat.add_le_add_right hab d,
end

lemma fixing_subgroup_le_stabilizer (s : set α) : fixing_subgroup (equiv.perm α) s ≤ stabilizer (equiv.perm α) s :=
begin
  intros k hk,
  rw mem_fixing_subgroup_iff at hk,
  rw mem_stabilizer_iff,
  change (λ x, k • x) '' s = s,
  conv_rhs { rw ← set.image_id s},
  apply set.image_congr ,
  simp only [id.def],
  exact hk,
end

lemma stabilizer_ne_top (s : set α) (hs : s.nonempty) (hsc : sᶜ.nonempty) :
  stabilizer (equiv.perm α) s ≠ ⊤ :=
begin
  obtain ⟨a, ha⟩ := hs,
  obtain ⟨b, hb⟩ := hsc,
  intro h,
  rw set.mem_compl_iff at hb, apply hb,
  have hg : equiv.swap a b ∈ stabilizer (equiv.perm α) s,
  { rw h, apply subgroup.mem_top },
  rw mem_stabilizer_iff at hg,
  rw ← hg,
  rw set.mem_smul_set,
  use a, use ha, apply equiv.swap_apply_left,
end

example (p q : Prop) (hq : q) : p → q := begin
exact imp_intro hq,
end

theorem stabilizer_empty_eq_top (G : Type*) [group G] (α : Type*) [mul_action G α] :
  stabilizer G (∅ : set α) = ⊤ :=
begin
  rw eq_top_iff,
  intro g, apply imp_intro,
  rw mem_stabilizer_iff,
  simp only [set.smul_set_empty],
end

theorem stabilizer_univ_eq_top (G : Type*) [group G] (α : Type*) [mul_action G α] :
  stabilizer G (set.univ : set α) = ⊤ :=
begin
  rw eq_top_iff,
  intro g, apply imp_intro,
  rw mem_stabilizer_iff,
  simp only [set.smul_set_univ],
end

theorem stabilizer_nonempty_ne_top (α : Type*)
  (s : set α) (hs : s.nonempty) (hs' : sᶜ.nonempty) :
  (stabilizer (equiv.perm α) s) ≠ ⊤ :=
begin
  obtain ⟨a : α, ha : a ∈ s⟩ := hs,
  obtain ⟨b : α, hb : b ∈ sᶜ⟩ := hs',
  intro h,
  let g := equiv.swap a b,
  have h' : g ∈ ⊤ :=  subgroup.mem_top g,
  rw [← h , mem_stabilizer_iff] at h',
  rw set.mem_compl_iff at hb,
  apply hb,
  rw ← h',
  use a,
  exact and.intro ha (equiv.swap_apply_left a b)
end

example (G : Type*) [group G] [fintype G] (H : subgroup G) :
  fintype.card H ≤ fintype.card G :=
begin
  apply nat.le_of_dvd, refine fintype.card_pos,
  refine subgroup.card_subgroup_dvd_card H,
end


lemma subgroup_of_group_of_order_two {G : Type*} [group G] [fintype G] (hG : fintype.card G = 2)
  (H : subgroup G) : H = ⊥ ∨ H = ⊤ :=
begin
  cases le_or_lt (fintype.card H) 1,
  { apply or.intro_left, apply subgroup.eq_bot_of_card_le, exact h, },
  { apply or.intro_right, apply subgroup.eq_top_of_card_eq,
    apply le_antisymm,
    { apply nat.le_of_dvd, refine fintype.card_pos,
      refine subgroup.card_subgroup_dvd_card H, },
    rw hG, exact h, },
end

lemma has_swap_of_lt_stabilizer (s : set α)
  (G : subgroup (equiv.perm α))
  (hG : stabilizer (equiv.perm α) s < G) : ∃ (g : equiv.perm α), g.is_swap ∧ g ∈ G :=
begin
    have : ∀ (t : set α), 1 < fintype.card t →
      ∃ (g : equiv.perm α), g.is_swap ∧ g ∈ (stabilizer (equiv.perm α) t),
    { intros t ht,
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ := fintype.exists_pair_of_one_lt_card ht,
      simp only [ne.def, subtype.mk_eq_mk] at h,
      use equiv.swap a b,
      split,
      rw swap_is_swap_iff, exact h,
      apply swap_mem_stabilizer ha hb, },

    have hs : s.nonempty,
    { by_contradiction,
      rw set.not_nonempty_iff_eq_empty  at h,
      apply ne_top_of_lt hG,
      rw h,
      apply stabilizer_empty_eq_top, },
    have hsc : sᶜ.nonempty,
    { by_contradiction,
      rw set.not_nonempty_iff_eq_empty  at h,
      apply ne_top_of_lt hG,
      rw ← stabilizer_compl, rw h,
      apply stabilizer_empty_eq_top, },

    cases lt_or_le 1 (fintype.card s) with h1 h1',
    { obtain ⟨g, hg, hg'⟩ := this s h1,
      use g, apply and.intro hg,
      exact le_of_lt hG hg',  },
    cases lt_or_le 1 (fintype.card (sᶜ : set α)) with h1c h1c',
    { obtain ⟨g, hg, hg'⟩ := this sᶜ _,
      use g, apply and.intro hg,
      rw stabilizer_compl at hg', exact le_of_lt hG hg',
      convert h1c },
    have hs1 : fintype.card s = 1,
    { apply le_antisymm h1',
      change 0 < fintype.card s,
      rw fintype.card_pos_iff , exact set.nonempty_coe_sort.mpr hs, },
    have hsc1 : fintype.card (sᶜ : set α) = 1,
    { apply le_antisymm,
      convert h1c',
      change 0 < _,
      rw [fintype.card_pos_iff, set.nonempty_coe_sort],
      exact hsc, },

    have hα : fintype.card α = 2, by rw [← fintype.card_add_compl s, hs1, hsc1],

    cases subgroup_of_group_of_order_two _ G,
    exfalso, exact ne_bot_of_gt hG h,
    { rw h,
      rw ← stabilizer_univ_eq_top (equiv.perm α) α,
      apply this,
      apply lt_of_lt_of_le one_lt_two,
      apply le_of_eq,
      rw ← hα, apply symm,
      rw set_fintype_card_eq_univ_iff,
      -- because one_lt_two needs it!
      apply_instance, },

    rw [fintype.card_perm, hα], norm_num,
end

example (s : set α) (g : equiv.perm α) :
  s.subsingleton ↔ (g • s).subsingleton :=
  begin
  change _ ↔ ((λ x, g • x) '' s).subsingleton,
  split,
  intro hs, apply set.subsingleton.image, exact hs,
  intro hgs, apply set.subsingleton_of_image _ s hgs,
  apply function.bijective.injective,
  apply mul_action.bijective,
end


theorem equiv.perm.is_maximal_stab' (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card s < fintype.card (sᶜ : set α)) :
  subgroup.is_maximal (stabilizer (equiv.perm α) s) :=
begin
  split, split,
  -- stabilizer (equiv.perm α) s ≠ ⊤
  exact stabilizer_ne_top s h0 h1,

  -- ∀ (G : subgroup (equiv.perm α)), stabilizer (equiv.perm α) s < b) → b = ⊤
  intros G hG,
  -- We need to prove that G = ⊤
  -- G contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_of_lt_stabilizer s G hG,
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_swap _ g hg_swap hg,
  -- G acts transitively
  haveI : is_pretransitive G α,
  { apply is_pretransitive.of_partition G s,
    { apply moves_in, exact hG, },
    { apply moves_in, rw stabilizer_compl, exact hG, },
    { intro h,
      apply lt_irrefl G, apply lt_of_le_of_lt _ hG,
      --  G ≤ stabilizer (equiv.perm α) s,
      intros g hg,
      rw mem_stabilizer_iff,
      rw ← subgroup.coe_mk G g hg,
      change (⟨g, hg⟩ : ↥G) • s = s,
      rw ← mem_stabilizer_iff,
      change _ ∈ stabilizer ↥G s,
      rw h, exact subgroup.mem_top ⟨g, hg⟩, }, },

  apply is_preprimitive.mk,

  /- The proof needs 4 steps -/
  /- Step 1 : No block is equal to sᶜ
     This uses that fintype.card s < fintype.card sᶜ.
     In the equality case, fintype.card s = fintype.card sᶜ, it is possible that B = sᶜ,
     then G is the wreath product,
     this is case (b) of the O'Nan-Scott classification of max'l subgroups of the symmetric group -/
    have hB_ne_sc : ∀ (B : set α) (hB : is_block G B), ¬(B = sᶜ),
    { intros B hB hBsc,
      obtain ⟨b, hb⟩ := h1, rw ← hBsc at hb,
      obtain ⟨a, ha⟩ := h0,
      obtain ⟨k, hk⟩ := exists_smul_eq G b a,
      suffices : fintype.card (B : set α) ≤ fintype.card s,
      { apply nat.lt_irrefl (fintype.card B),
        apply lt_of_le_of_lt this,
        simp_rw hBsc, exact hα, },
      rw ← card_smul_eq B k,
      apply set.card_le_of_subset ,
      change k • B ⊆ s,
      rw [← set.disjoint_compl_right_iff_subset, ← hBsc],
      apply or_iff_not_imp_left.mp (is_block.def_one.mp hB k),
      intro h,
      apply set.not_mem_empty a,
      rw ← set.inter_compl_self s,
      split,
        exact ha,
        rw [← hk, ← hBsc, ← h, set.smul_mem_smul_set_iff], exact hb },

    /- Step 2 : A block contained in sᶜ is a subsingleton-/
    have hB_not_le_sc : ∀ (B : set α) (hB : is_block G B) (hBsc : B ⊆ sᶜ), B.subsingleton,
    { intros B hB hBsc,
      suffices : B = coe '' (coe ⁻¹' B : set (sᶜ : set α)),
      rw this,
      apply set.subsingleton.image ,

      suffices : is_trivial_block (coe ⁻¹' B : set (sᶜ : set α)),
      apply or.resolve_right this,

      intro hB',
      apply hB_ne_sc B hB,
      apply set.subset.antisymm hBsc,
      intros x hx,
      rw [← subtype.coe_mk x hx, ← set.mem_preimage],
      rw [hB', set.top_eq_univ], apply set.mem_univ,

      { -- is_trivial_block (coe ⁻¹' B : set (sᶜ : set α)),
        suffices : is_preprimitive (stabilizer G (sᶜ : set α)) (sᶜ : set α),
        refine is_preprimitive.has_trivial_blocks this _,

        -- is_block (coe ⁻¹' B : set (sᶜ : set α))
        let φ' : stabilizer G (sᶜ: set α) → G := coe,
        let f' : (sᶜ : set α) →ₑ[φ'] α := {
          to_fun := coe,
          map_smul' := λ ⟨m, hm⟩ x,
          by simp only [φ', has_smul.smul_stabilizer_def, subgroup.coe_mk], },
        apply mul_action.is_block_preimage f' hB,

        -- is_preprimitive (stabilizer G (sᶜ : set α)) (sᶜ : set α)
        let φ : stabilizer G (sᶜ : set α) → equiv.perm (sᶜ : set α) := mul_action.to_perm,
        let f : (sᶜ : set α) →ₑ[φ] (sᶜ : set α) := {
            to_fun := id,
            map_smul' := λ g x,  by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
        have hf : function.bijective f := function.bijective_id,
        rw is_preprimitive_of_bijective_map_iff _ hf,
        exact equiv.perm.is_preprimitive ↥sᶜ,

        -- function.surjective φ,
        -- will need to adjust for alternating_group

        intro g,
        suffices : equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) sᶜ,
        use equiv.perm.of_subtype g,
        { apply le_of_lt hG,
          rw ← stabilizer_compl,
          exact this, },
        { rw mem_stabilizer_iff,
          change (equiv.perm.of_subtype g) • sᶜ = sᶜ,
          rw ← mem_stabilizer_iff,
          exact this, },
        { ext ⟨x, hx⟩,
          change (equiv.perm.of_subtype g) • x = _,
          simp only [equiv.perm.smul_def],
          rw equiv.perm.of_subtype_apply_of_mem, },

        { -- equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) sᶜ
          rw mem_stabilizer_iff,
          apply set.subset.antisymm,
          { intro x,
            rw set.mem_smul_set ,
            rintro ⟨y, hy, rfl⟩,
            simp only [equiv.perm.smul_def],
            rw equiv.perm.of_subtype_apply_of_mem g hy,
            refine subtype.mem _, },
          { intros x hx,
            obtain ⟨y, hy⟩ := equiv.surjective g ⟨x, hx⟩,
            rw set.mem_smul_set,
            use y,
            apply and.intro (y.prop),
            simp only [hy, equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe,
              subtype.coe_mk], }, }, },

      { -- B = coe '' (coe ⁻¹' B : set (sᶜ : set α)),
        apply set.subset.antisymm,
        intros x hx,
        use ⟨x, hBsc hx⟩,
        simp only [hx, set.mem_preimage, subtype.coe_mk, eq_self_iff_true, and_self],
        exact set.image_preimage_subset coe B, }, },

    /-
    have hBs_block : ∀ (B : set α), is_block G B → is_block (equiv.perm s) (coe ⁻¹' B : set s),
    { intros B hB,
      rw is_block.def_one,
      intro g,
      suffices : ∃ (k : stabilizer G s), (∀ (x : s) , g • x = k • x),
      obtain ⟨k, hk⟩ := this,
      rw is_block.def_one at hB,
      suffices hgk : g • (coe ⁻¹' B) = coe ⁻¹' (k • B), rw hgk, simp_rw hgk,
      cases hB k with hB_eq hB_dis,
      { change k • B = B at hB_eq,
        apply or.intro_left, rw hB_eq, },
      { -- change disjoint (k • B) B at hB_dis,
        apply or.intro_right,
        refine disjoint.preimage coe hB_dis, },
      -- g • (coe ⁻¹' B) = coe ⁻¹' (k • B),
      { ext,
        simp only [set.mem_preimage, set.mem_smul_set_iff_inv_smul_mem],
        suffices : ↑(g⁻¹ • x) = k⁻¹ • ↑x, rw this,
        set y := g⁻¹ • x,
        have hy : x = g • y, by rw smul_inv_smul,
        rw [eq_inv_smul_iff, hy, hk y, has_smul.stabilizer_def],
        refl, },
      -- ∃ (k : stabilizer G s), (∀ (x : s) , g • x = k • x)
      { have : g.of_subtype ∈ stabilizer (equiv.perm α) s,
        { rw mem_stabilizer_iff,
          ext x,
          split,
          { rintro ⟨y, hy, rfl⟩,
            simp only [equiv.perm.smul_def],
            rw ← subtype.coe_mk y hy,
            rw equiv.perm.of_subtype_apply_coe ,
            rw ← equiv.perm.smul_def, simp only [subtype.coe_prop] },
          { intro hx,
            let y := g⁻¹ • (⟨x, hx⟩ : s),
            use y,
            split,
            exact y.prop,
            rw [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe, ←equiv.perm.smul_def],
            rw smul_inv_smul,
            refl, } },
        use g.of_subtype,
        { apply le_of_lt hG, exact this, },
        { rw mem_stabilizer_iff,
          change g.of_subtype • s = s,
          rw ← mem_stabilizer_iff,
          exact this, },
        { intro x,
          rw ← subtype.coe_inj,
          rw has_smul.stabilizer_def,
          simp only [equiv.perm.smul_def, subgroup.coe_mk],
          change _ = g.of_subtype • ↑x,
          rw equiv.perm.smul_def,
          rw equiv.perm.of_subtype_apply_coe }, }, }, -/

    /- Step 3 : A block contained in s is a subsingleton -/
    have hB_not_le_s : ∀ (B : set α) (hB : is_block G B), (B ⊆ s) → B.subsingleton,
    { intros B hB hBs,

      suffices hB_coe : B = coe '' (coe ⁻¹' B : set ↥s),

      suffices : is_trivial_block (coe ⁻¹' B : set s),
      cases this with hB' hB',
      { -- trivial case
        rw hB_coe,
        apply set.subsingleton.image,
        exact hB', },
      { -- coe ⁻¹' B = s
        have hBs' : B = s,
        { apply set.subset.antisymm hBs,
          intros x hx,
          rw ← subtype.coe_mk x hx,
          rw ← set.mem_preimage,
          rw hB',
          rw set.top_eq_univ,
          apply set.mem_univ, },

      have : ∃ g' ∈ G, g' • s ≠ s,
      { by_contradiction,
        apply  (ne_of_lt hG),
        push_neg at h,
        apply le_antisymm,
        exact le_of_lt hG,
        intros g' hg', rw mem_stabilizer_iff, exact h g' hg', },
      obtain ⟨g', hg', hg's⟩ := this,
      cases is_block.def_one.mp hB ⟨g', hg'⟩ with h h,
      { -- case g' • B = B : absurd, since B = s and choice of g'
        exfalso,
        apply hg's, rw ← hBs', exact h, },
      { -- case g' • B disjoint from B

        suffices : (g' • B).subsingleton,
        apply set.subsingleton_of_image _ B this,
        apply function.bijective.injective,
        apply mul_action.bijective,

        apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B),
        exact is_block_of_block _ hB,
        rw ← hBs',
        apply disjoint.subset_compl_right ,
        exact h, }, },




      -- is_trivial_block (coe ⁻¹' B : set s),
      suffices : is_preprimitive (stabilizer G s) (s : set α),
      refine is_preprimitive.has_trivial_blocks this _,

      -- is_block (coe ⁻¹' B : set s)
      let φ' : stabilizer G s → G := coe,
      let f' : s →ₑ[φ'] α := {
        to_fun := coe,
      map_smul' := λ ⟨m, hm⟩ x,
      by simp only [φ', has_smul.smul_stabilizer_def], },
      apply mul_action.is_block_preimage f' hB,

      -- is_preprimitive (stabilizer G s) s
      let φ : stabilizer G s → equiv.perm s := mul_action.to_perm,
      let f : s →ₑ[φ] s := {
          to_fun := id,
          map_smul' := λ g x,  by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
      have hf : function.bijective f := function.bijective_id,
      rw is_preprimitive_of_bijective_map_iff _ hf,
      exact equiv.perm.is_preprimitive s,

      -- function.surjective φ,
      -- will need to adjust for alternating_group

      intro g,
      suffices : equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s,
      use equiv.perm.of_subtype g,
      { apply le_of_lt hG, exact this, },
      { rw mem_stabilizer_iff,
        change (equiv.perm.of_subtype g) • s = s,
        rw ← mem_stabilizer_iff,
        exact this, },
      { ext ⟨x, hx⟩,
        change (equiv.perm.of_subtype g) • x = _,
        simp only [equiv.perm.smul_def],
        rw equiv.perm.of_subtype_apply_of_mem, },

      { -- equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s
        rw mem_stabilizer_iff,
        apply set.subset.antisymm,
        { intro x,
          rw set.mem_smul_set ,
          rintro ⟨y, hy, rfl⟩,
          simp only [equiv.perm.smul_def],
          rw equiv.perm.of_subtype_apply_of_mem g hy,
          refine subtype.mem _, },
        { intros x hx,
          obtain ⟨y, hy⟩ := equiv.surjective g ⟨x, hx⟩,
          rw set.mem_smul_set,
          use y,
          apply and.intro (y.prop),
          simp only [hy, equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe,
            subtype.coe_mk], }, },

      { -- B = coe '' (coe ⁻¹' B : set ↥s),
        apply set.subset.antisymm,
        intros x hx,
        use ⟨x, hBs hx⟩,
        simp only [hx, set.mem_preimage, subtype.coe_mk, eq_self_iff_true, and_self],
        exact set.image_preimage_subset coe B, }, },

    intros B hB,
    unfold is_trivial_block,

    rw or_iff_not_imp_left ,
    intro hB',

    obtain ⟨a, ha, ha'⟩ := set.not_subset_iff_exists_mem_not_mem.mp
      (λ h, hB' ((hB_not_le_sc B hB) h)),
    rw set.not_mem_compl_iff at ha',

    obtain ⟨b, hb, hb'⟩ := set.not_subset_iff_exists_mem_not_mem.mp
      (λ h, hB' ((hB_not_le_s B hB) h)),
    rw ← set.mem_compl_iff at hb',

    have hsc_le_B : sᶜ ⊆ B,
    {   intros x hx',
        suffices : ∃ (k : fixing_subgroup (equiv.perm α) s), k • b = x,
        obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this,
        suffices : k • B = B,
        rw [← hkbx, ← this, set.smul_mem_smul_set_iff],
        exact hb,
        { -- k • B = B,
          apply or_iff_not_imp_right.mp (is_block.def_one.mp hB ⟨k, _⟩),
          { rw set.not_disjoint_iff_nonempty_inter,
            change (k • B ∩ B).nonempty,
            use a,
            split,
              rw mem_fixing_subgroup_iff at hk,
              rw ← hk a ha',
              exact set.smul_mem_smul_set ha,
              exact ha, },
          { -- ↑k ∈ G
            apply le_of_lt hG,
            exact fixing_subgroup_le_stabilizer s hk, } },
        { -- ∃ (k : fixing_subgroup (equiv.perm α) s), k • b = x,
          suffices : is_pretransitive (fixing_subgroup (equiv.perm α) s)
            (sub_mul_action.of_fixing_subgroup (equiv.perm α) s),
          resetI,
          obtain ⟨k, hk⟩ := exists_smul_eq (fixing_subgroup (equiv.perm α) s)
            (⟨b, hb'⟩ : sub_mul_action.of_fixing_subgroup (equiv.perm α) s)
            ⟨x, hx'⟩,
          use k,
          rw [← subtype.coe_inj, sub_mul_action.coe_smul] at hk,
          exact hk,
          -- is_pretransitive …
          rw is_pretransitive_iff_is_one_pretransitive,
          apply remaining_transitivity',
          simp only [part_enat.card_eq_coe_fintype_card],
          { rw add_comm,
            rw ← fintype.card_add_compl s,
            simp only [add_le_add_iff_left],
            change 0 < _,
            rw fintype.card_pos_iff ,
            simp only [set.nonempty_coe_sort],
            exact h1,  },
          exact equiv_perm_is_fully_pretransitive α, }, },

    -- Conclusion of the proof : B = ⊤
    rw eq_top_iff,
    intros x _,
    obtain ⟨b, hb⟩ := h1,
    obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x,
    suffices : g • B = B,
    { rw [← hgbx, ← this, set.smul_mem_smul_set_iff],
      exact hsc_le_B hb, },
    -- g • B = B,
    apply or_iff_not_imp_right.mp (is_block.def_one.mp hB ⟨g, hg⟩),
    rw set.not_disjoint_iff_nonempty_inter,
    change (g • B ∩ B).nonempty,
    apply aux_pigeonhole,

    -- card B + card (g • B) = card B + card B
    -- ... ≥ card sᶜ + card sᶜ
    -- ... > card s + card s ᶜ = card α
    rw ← fintype.card_add_compl s,
    apply nat.lt_of_lt_of_le,
    { apply nat.add_lt_add_right _ (fintype.card (sᶜ : set α)),
      use (fintype.card (sᶜ : set α)),
      exact hα, },
    apply nat.add_le_add,
    { apply le_trans (set.card_le_of_subset hsc_le_B),
      apply le_of_eq,
      rw ← set.coe_to_finset B,
      simp only [← set.to_finset_card],
      change _ = ((λ x, g • x) '' ↑(B.to_finset)).to_finset.card,
      simp_rw ← finset.coe_image ,
      simp only [finset.to_finset_coe],
      rw finset.card_image_of_injective _ (mul_action.injective g) },
    exact set.card_le_of_subset hsc_le_B,
end

/-- stabilizer (equiv.perm α) s is a maximal subgroup of equiv.perm α,
provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem equiv.perm.is_maximal_stab (s : set α) (h0 : s.nonempty) (h1 : sᶜ.nonempty)
  (hα : fintype.card α ≠ 2 * fintype.card ↥s) : subgroup.is_maximal (stabilizer (equiv.perm α) s) :=
begin
  cases nat.lt_trichotomy (fintype.card s) (fintype.card (sᶜ : set α)) with hs hs',
  { exact equiv.perm.is_maximal_stab' s h0 h1 hs, },
  cases hs' with hs hs,
  { exfalso, apply hα,
    rw [← fintype.card_add_compl s, ← hs, ← two_mul], },
  { rw ← compl_compl s at h0,
    rw ← stabilizer_compl,
    apply equiv.perm.is_maximal_stab' sᶜ h1 h0,
    simp_rw compl_compl s,
    convert hs },
end

/-- The action of equiv.perm α on the n-element subsets of α is preprimitive
provided 1 ≤ n < #α and #α ≠ 2*n -/
theorem nat.finset_is_preprimitive_of (h_one_le : 1 ≤ n) (hn : n < fintype.card α)
  (hα : fintype.card α ≠ 2 * n) : is_preprimitive (equiv.perm α) (n.finset α) :=
begin
  classical,
  cases nat.eq_or_lt_of_le h_one_le with h_one h_one_lt,
  { -- n = 1 :
    let f : α →[equiv.perm α] nat.finset α 1 := {
      to_fun := λ x, ⟨{x}, finset.card_singleton x⟩,
      map_smul' := λ g x, rfl
    },
    rw ← h_one,
    suffices hf : function.surjective f,
    { apply is_preprimitive_of_surjective_map hf,
      exact equiv.perm.is_preprimitive α, },
    rintro ⟨s, hs⟩,
    change s.card = 1 at hs,
    rw finset.card_eq_one at hs,
    obtain ⟨a, ha⟩ := hs,
    use a,
    simp only [ha, equivariant_map.coe_mk], refl, },

  -- h_one_lt : 1 < n
  haveI : nontrivial α,
  { rw ← fintype.one_lt_card_iff_nontrivial,
    exact lt_trans h_one_lt hn },
  haveI ht : is_pretransitive (equiv.perm α) (n.finset α) := nat.finset_is_pretransitive,
  haveI : nontrivial (n.finset α) :=
    nat.finset_nontrivial (lt_trans (nat.lt_succ_self 0) h_one_lt) hn,
  obtain ⟨sn : n.finset α⟩ := nontrivial.to_nonempty,
  let s := sn.val,
  let hs : s.card = n := sn.prop,
  -- have hs : (s : finset α).card = n := s.prop,
  rw ← maximal_stabilizer_iff_preprimitive (equiv.perm α) sn,
  have : stabilizer (equiv.perm α) sn = stabilizer (equiv.perm α) (s : set α),
  { ext g,
    simp only [mem_stabilizer_iff],
    rw ← subtype.coe_inj,
    change g • s = s ↔ _,
    rw [← finset.coe_smul_finset, ← finset.coe_inj], },
  rw this,
  apply equiv.perm.is_maximal_stab (s : set α),
  { simp only [finset.coe_nonempty, ← finset.card_pos, hs],
    apply lt_trans one_pos h_one_lt, },
  { simp only [← finset.coe_compl, finset.coe_nonempty, ← finset.card_compl_lt_iff_nonempty,
      compl_compl, hs],
    exact hn, },
  { simp only [finset.coe_sort_coe, fintype.card_coe, hs],
    exact hα, },
  apply_instance,
end

end action_on_finsets
