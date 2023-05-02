/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.basic tactic.group
import group_theory.group_action.sub_mul_action

import .sub_mul_actions
import .multiple_transitivity
import .for_mathlib.extensions
import group_theory.group_action.embedding

open_locale pointwise

open mul_action

def nat.finset (α : Type*) (n : ℕ) := { s : finset α | s.card = n}

lemma nat.finset.def (α : Type*) (n : ℕ) (s : nat.finset α n) : (s : finset α).card = n :=  s.prop

lemma nat.finset_mem.def (α : Type*) (n : ℕ) (s : finset α) (hs : s ∈ nat.finset α n) :
  s.card = n := by simpa only

variables (α : Type*) [decidable_eq α] (G : Type*) [group G] [mul_action G α]

variables {α G}

lemma finset.smul_card_eq (s : finset α) (g : G) :
  (g • s).card = s.card :=
begin
  change (finset.image (λ x, g • x) s).card = _,
  rw finset.card_image_of_injective,
  exact mul_action.injective g,
end

variable (n : ℕ)

lemma is_eq_iff_is_le (s t : n.finset α) :
  s = t ↔ s ≤ t :=
begin
split,
  { intro h, rw h, exact le_refl t, },
  { intro h,
  rw ← subtype.coe_inj,
    -- rw ← subtype.coe_eta s s.prop, rw ← subtype.coe_eta t t.prop,
    -- rw ← subtype.coe_inj,
    -- simp only [subtype.coe_mk],
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

lemma smul_ne_iff_has_mem_not_mem {s t : n.finset α} {g : G} :
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

theorem nat.finset.mul_action_faithful [fintype α]
  (hn : 1 ≤ n) (hα : n < fintype.card α)
  -- (g : equiv.perm α)
  {g : G}
  (hg : (mul_action.to_perm g : equiv.perm α) ≠ 1) :
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


example {s : set α} {a : α} {g : G} :
  a ∉ g⁻¹ • s ↔ g • a ∈ sᶜ :=
begin
  rw set.mem_smul_set_iff_inv_smul_mem, rw inv_inv, rw ← set.mem_compl_iff,
end

example : mul_action G (fin n ↪ α):=
begin
  apply_instance,
end

example : mul_action G (n.finset α):=
begin
  apply_instance,
end


-- variable (α n)
variable (α)
variable (G)
variable (n)

def embedding_to_finset.map : (fin n ↪ α) →[G] n.finset α := {
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
  ↑((embedding_to_finset.map α G n).to_fun f)  =  finset.univ.map f := rfl

lemma embedding_to_finset.map_surjective : function.surjective (embedding_to_finset.map α G n) :=
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

  rw embedding_to_finset.map,
  simp only [equivariant_map.coe_mk, subtype.coe_mk, finset.mem_map, finset.mem_univ,
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

theorem nat.finset_is_pretransitive_of_multiply_pretransitive {G : Type*} [group G] [mul_action G α]
  (h : is_multiply_pretransitive G α n) :
  is_pretransitive G (n.finset α) :=
begin
  refine is_pretransitive_of_surjective_map (embedding_to_finset.map_surjective α G n) _,
  exact h
end

theorem nat.finset_is_pretransitive : is_pretransitive (equiv.perm α) (n.finset α) :=
begin
  apply nat.finset_is_pretransitive_of_multiply_pretransitive,
  apply equiv_perm_is_multiply_pretransitive,
end

def nat.finset_compl {m : ℕ} (hm : m + n = fintype.card α) :
  nat.finset α n →[G] nat.finset α m := {
to_fun := λ ⟨s, hs⟩, ⟨(sᶜ : finset α),
  begin
    change (sᶜ).card = m, change s.card = n at hs,
    rw [finset.card_compl , hs, nat.sub_eq_iff_eq_add _,  hm],
    rw ← hm, apply nat.le_add_left,
  end⟩,
map_smul' := λ g ⟨s, hs⟩,
  begin
    apply subtype.coe_injective,
    simp only [id.def, nat.finset.mul_action.coe_apply'],
    change (g • s)ᶜ = g • sᶜ,
    ext, simp only [finset.mem_compl],
    change ¬(a∈ g • s) ↔ _,
    simp [← finset.inv_smul_mem_iff],
  end, }

lemma nat.finset_compl_bijective {m : ℕ} (hm : m + n = fintype.card α) :
  function.bijective (nat.finset_compl α G n hm) :=
begin
  rw nat.finset_compl,
  split,
  { rintros ⟨s, hs⟩ ⟨t, ht⟩ h,
    rw ← subtype.coe_inj at h,
    change sᶜ = tᶜ at h,

    apply subtype.coe_injective,
    change s = t,
    rw ← compl_compl s, rw h, rw compl_compl, },
  { rintro ⟨s, hs⟩,
    have hn : n + m = fintype.card α, { rw add_comm, exact hm },
    use nat.finset_compl α G m hn ⟨s, hs⟩,
    apply subtype.coe_injective,
    change sᶜᶜ = s, rw compl_compl,  },
end

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



#lint
