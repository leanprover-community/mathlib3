/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic.lift

import group_theory.group_action.basic
import group_theory.group_action.sub_mul_action
import group_theory.group_action.fixing_subgroup

import data.setoid.partition
import order.rel_classes
import algebra.big_operators.order
import group_theory.subgroup.pointwise

import .ad_mathlib
import .ad_sub_mul_actions

open_locale big_operators pointwise

open_locale classical

section partition
variables {α : Type*}

open_locale big_operators classical

/-- A partion of a type induces partitions on subsets -/
lemma setoid.is_partition_on {α : Type*} {P : set (set α)} (hP : setoid.is_partition P) (s : set α) :
  setoid.is_partition { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ } :=
begin
  split,
  { intro h ,
    obtain ⟨t, htP, ht, hts⟩ := set.mem_set_of_eq.mp h,
    apply hts,
    rw [← subtype.image_preimage_coe, ht,set.image_empty] },
  { intro a,
    obtain ⟨t, ht⟩ := hP.right ↑a,
    simp only [exists_unique_iff_exists, exists_prop, and_imp] at ht,
    use coe ⁻¹' t,
    split,
    { simp only [ne.def, set.mem_set_of_eq, set.mem_preimage, exists_unique_iff_exists, exists_prop],
      use t,
      apply and.intro ht.left.left,
      apply and.intro rfl,
      intro h, rw ← set.mem_empty_eq (a : α), rw ← h,
      exact set.mem_inter (ht.left.right) (subtype.mem a),
      exact (ht.left.right) },
    { simp only [ne.def, set.mem_set_of_eq, exists_unique_iff_exists, exists_prop, and_imp,
        forall_exists_index],
      intros y x hxP hxy hxs hay, rw ← hxy,
      rw subtype.preimage_coe_eq_preimage_coe_iff ,
      refine congr_arg2 _ _ rfl,
      apply ht.right x hxP, rw [← set.mem_preimage, hxy], exact hay } }
end

/-- The cardinal of ambient fintype equals
  the sum of cardinals of the parts of a partition (finset style)-/
lemma partition.card_of_partition' [fintype α] {c : finset (finset α)}
  (hc : setoid.is_partition
    ({ s : set α | ∃ (t : finset α), s.to_finset = t ∧ t ∈ c } : set (set α))) :
  ∑ (s : finset α) in c, s.card = fintype.card α :=
begin
  rw [← mul_one (fintype.card α), ← finset.sum_card],
  intro a,
  rw finset.card_eq_one,
  obtain ⟨s, hs, hs'⟩ := hc.right a,
  simp only [exists_unique_iff_exists, exists_prop, and_imp, exists_eq_left', set.mem_set_of_eq]
    at hs hs',
  have hs'2 : ∀ (z : finset α), z ∈ c → a ∈ z → z = s.to_finset,
  { intros z hz ha,
    rw [← finset.coe_inj, set.coe_to_finset],
    refine  hs' z _ (finset.mem_coe.mpr ha),
  -- To get the correct type automatically and perform the rewrite
    suffices : ∀ {u v : finset α}, v ∈ c → u = v → u ∈ c,
    { refine this hz _,
      rw [← finset.coe_inj, set.coe_to_finset] },
    { intros u v hu huv, rw huv, exact hu },
  },
  use s.to_finset,
  ext t,
  simp only [finset.mem_filter, finset.mem_singleton],
  split,
  { rintro ⟨ht,ha⟩,
    exact hs'2 t ht ha },
  { intro ht,
    rw ← ht at hs, apply and.intro hs.left,
    rw ht, simp only [set.mem_to_finset],  exact hs.right,}
end

/-- The cardinal of ambient fintype equals
  the sum of cardinals of the parts of a partition (set style)-/
lemma partition.card_of_partition [fintype α] {c : set (set α)} (hc : setoid.is_partition c) :
  ∑ (s : set α) in c.to_finset, s.to_finset.card = fintype.card α :=
begin
  let c' : finset (finset α) := { s : finset (α) | (s : set α) ∈ c }.to_finset,
  have hcc' : c = { s : set α | ∃ (t : finset α), s.to_finset = t ∧ t ∈ c' },
  { simp only [set.mem_to_finset, set.mem_set_of_eq, exists_eq_left',
      set.coe_to_finset, set.set_of_mem_eq] },
  rw hcc' at hc,
  rw ← partition.card_of_partition'  hc,
  have hi : ∀ (a : set α) (ha : a ∈ c.to_finset), a.to_finset ∈ c',
  { intros a ha,
    simp only [set.mem_to_finset, set.mem_set_of_eq, set.coe_to_finset],
    simpa only [set.mem_to_finset] using ha,  },
  have hj : ∀ (a : finset α) (ha : a ∈ c'), (a : set α) ∈ c.to_finset,
  { intros a ha, simpa only [set.mem_to_finset] using ha },
  rw finset.sum_bij' _ hi _ _ hj,
  { intros a ha, simp only [set.coe_to_finset],  },
  { intros a ha, rw [← finset.coe_inj, set.coe_to_finset] },
  { intros a ha, refl },
end

/-- Given a partition of the ambient finite type,
the cardinal of a set is the sum of the cardinalities of its trace on the parts of the partition -/
lemma setoid.is_partition.card_set_eq_sum_parts {α : Type*} [fintype α] (s : set α)
  {P : set (set α)} (hP : setoid.is_partition P) :
  s.to_finset.card =
    finset.sum P.to_finset (λ (t : set α), (s ∩ t).to_finset.card) :=
begin
  rw ← finset.card_bUnion,
  apply congr_arg,
  { rw ← finset.coe_inj, simp only [set.coe_to_finset, finset.coe_bUnion],
    rw [set.bUnion_eq_Union, ← set.inter_Union, ← set.sUnion_eq_Union],
    rw setoid.is_partition.sUnion_eq_univ hP,
    exact (set.inter_univ s).symm },
  { intros t ht u hu htu,
    simp only [set.mem_to_finset] at ht hu,
    simp only [set.to_finset_disjoint_iff],
    exact set.disjoint_of_subset (set.inter_subset_right s t) (set.inter_subset_right s u)
      (setoid.is_partition.pairwise_disjoint hP ht hu htu) }
end

/-- The cardinality of a finite type is
  the sum of the cardinalities of the parts of any partition -/
lemma setoid.is_partition.card_eq_sum_parts {α : Type*} [fintype α] {P : set (set α)}
  (hP : setoid.is_partition P) :
  fintype.card α =
    finset.sum P.to_finset (λ (t : set α), t.to_finset.card) :=
begin
  change finset.univ.card = _,
  have : ∀ (t : set α) (ht : t ∈ P.to_finset), t.to_finset.card = (set.univ ∩ t).to_finset.card,
  { intros t ht, apply congr_arg,
    rw set.to_finset_inj, exact (set.univ_inter t).symm,  },
  simp_rw finset.sum_congr rfl this,
  simpa only [set.to_finset_univ, set.to_finset_card, fintype.card_of_finset]
    using setoid.is_partition.card_set_eq_sum_parts (set.univ) hP,
end

/-- The cardinality of a finset is the sum of the cardinalities
of the traces of any partition of the ambient type  -/
lemma setoid.is_partition.card_finset_eq_sum_parts {α : Type*}
  {P : set (set α)} (hP : setoid.is_partition P)
  {s : finset α}  :
  let P' := { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ } in
  let hP' := setoid.is_partition_on hP in
  s.card =
    finset.sum P'.to_finset (λ (t : set ↥s), t.to_finset.card) :=
begin
  -- let P' := { u : set ↥s | ∃ (t : set α), t ∈ P ∧ coe ⁻¹' t = u ∧ t ∩ s ≠ ∅ },
  -- let hP' := setoid.is_partition_on hP,
/-   have fs : fintype ↥(↑s : set α) := finset_coe.fintype s,
  have fcs : fintype.card ↥s =  fintype.card ↥(s : set α) :=
  by simp only [fintype.card_coe, finset.coe_sort_coe, fintype.card_coe],
  have fcs' : fintype.card ↥(s : set α) = s.card :=
  by simp only [finset.coe_sort_coe, fintype.card_coe],
  -/
  have this :=
    @partition.card_of_partition _ (finset_coe.fintype s) _ (setoid.is_partition_on hP (s : set α)),
  simp only [finset.coe_sort_coe, fintype.card_coe] at this,
  rw ← this,
  apply congr_arg2,
  { apply finset.coe_injective ,
    simp only [ne.def, set.coe_to_finset],
    exact rfl },
  { ext, apply congr_arg, rw set.to_finset_inj }
end

end partition

/-!
# Finite permutation groups
A formalization of Wielandt's book, *Finite permutation groups*

-/

section Maximal_Subgroups
variables {G : Type*} [group G]

namespace subgroup

/-- A subgroup is maximal if it is maximal in the collection of proper subgroups. -/
class is_maximal (K : subgroup G) : Prop :=
(out : is_coatom K)

theorem is_maximal_def {K : subgroup G} : K.is_maximal ↔ is_coatom K := ⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem is_maximal.ne_top {K : subgroup G} (h : K.is_maximal) : K ≠ ⊤ := (is_maximal_def.1 h).1

theorem is_maximal_iff {K: subgroup G} : K.is_maximal ↔
  K ≠ ⊤ ∧ ∀ (H: subgroup G) g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ :=
begin
  split,
  { intro hK, split, exact is_maximal.ne_top hK,
  intros H g hKH hgK hgH,
  suffices : K < H,
    apply (is_maximal_def.1 hK).2, assumption,
  have zKH : K ≠ H, { rw ne.def, intro z, rw z at hgK, exact hgK hgH },
  exact (ne.le_iff_lt zKH).mp hKH,},
  { rintros ⟨ hG, hmax ⟩,
  split, split, assumption,
  introsI H hKH,
  obtain ⟨ g, hgH, hgK ⟩ := (set.exists_of_ssubset hKH),
  exact hmax H g (le_of_lt hKH) hgK hgH },
end

theorem is_maximal.eq_of_le {K H: subgroup G} (hK : K.is_maximal) (hH : H ≠ ⊤) (KH : K ≤ H) :
  K = H :=
eq_iff_le_not_lt.2 ⟨KH, λ h, hH (hK.1.2 _ h)⟩

end subgroup
end Maximal_Subgroups

/- Chapter 1 -/
section FundamentalConcepts


-- Section 6 : Blocks

namespace mul_action

section has_scalar

variables (G X : Type*) [has_scalar G X]

/-- A fixed block is an invariant subset -/
def is_fixed_block -- (G X : Type*) [group G] [hGX : mul_action G X]
  (B : set X) := ∀ (g : G), g • B = B


def is_invariant_block (B : set X) := ∀ (g : G), g • B ≤ B

-- Possible redefinition :
-- (range (λ g : G, g • B)).pairwise_disjoint id
/-- A block is a set which is either fixed or moved to a disjoint subset -/
def is_block -- (G X : Type*) [group G] [hGX : mul_action G X]
  (B : set X) := (set.range $ λ g : G, g • B).pairwise_disjoint id
  -- ∀ (g : G), g • B = B ∨ disjoint (g • B) B

lemma is_block.def {B : set X} (hB : is_block G X B) (g g' : G) :
  g • B = g' • B ∨ disjoint (g • B) (g' • B) :=
begin
  cases em (g • B = g' • B),
  refine or.intro_left _ h,
  apply or.intro_right,
  exact hB (set.mem_range_self g) (set.mem_range_self g') h,
end

end has_scalar

section group

variables (G X : Type*) [group G] [mul_action G X]

lemma is_block.def_one {B : set X} (hB : is_block G X B) (g : G) :
  g • B = B ∨ disjoint (g • B) B :=
begin
  let h := is_block.def G X hB g (1 : G),
  rw one_smul at h, exact h,
end

lemma is_block.mk {B : set X} :
  is_block G X B ↔ (∀ (g : G), g • B = B ∨ disjoint (g • B) B) :=
begin
  split,
  { intros hB g, exact is_block.def_one G X hB g },
  { intros hB,
    intros u hu v hv,
    obtain ⟨g, rfl⟩ := hu, obtain ⟨g', rfl⟩ := hv,
    simp only [ne.def],
    intro hgg',
    let k := g⁻¹ * g',
    have hk : g * k = g' := by { rw mul_inv_cancel_left},
    rw [← hk, ← smul_smul, function.on_fun],
    simp only [id.def],
    cases (hB k) with heq hdis,
    { exfalso, apply hgg', rw [← hk, ← smul_smul, heq] },
    refine disjoint.image hdis.symm _ _ _,
    exact set.univ,
    apply function.injective.inj_on ,
    apply mul_action.injective,
    repeat { simp only [set.subset_univ] } }
end

lemma is_block.mk_notempty {B : set X}  :
  is_block G X B ↔ ∀ (g : G), (g • B) ∩ B ≠ ∅ → g • B = B :=
begin
  split,
  { intros hB g hg,
    rw is_block.mk at hB,
    cases hB g,
    exact h,
    { exfalso, apply hg,
      simpa only [disjoint_iff] using h } },
  { intro hB,
    rw is_block.mk,
    intro g,
    cases em (g • B ∩ B = ∅) with h h',
    apply or.intro_right, rw set.disjoint_iff_inter_eq_empty, exact h,
    apply or.intro_left, exact hB g h', },
end

lemma is_block.mk_mem {B : set X} :
  is_block G X B ↔ ∀ (g : G) (a : X) (ha : a ∈ B) (hga : g • a ∈ B), g • B = B :=
begin
  split,
  { intros hB g a ha hga,
    cases is_block.def_one G X hB g⁻¹ with h h',
    { rw [smul_eq_iff_eq_inv_smul, h] },
    exfalso, rw ← set.mem_empty_eq a,
    rw [disjoint_iff, set.inf_eq_inter, set.bot_eq_empty] at h',
    rw [← h', set.mem_inter_eq],
    apply and.intro _ ha,
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv],
    exact hga },
  { intro H,  rw is_block.mk, intro g,
    cases set.eq_empty_or_nonempty (g • B ∩ B),
    { apply or.intro_right, rw disjoint_iff, simpa using h },
    { apply or.intro_left,
      obtain ⟨a, hga, ha⟩ := h,
      rw smul_eq_iff_eq_inv_smul, apply symm,
      rw mem_smul_set_iff_inv_smul_mem at hga,
      exact H g⁻¹ a ha hga } }
end

-- was : is_block_def'
lemma is_block.def_mem {B : set X} (hB : is_block G X B) (a : X) (g : G) :
  a ∈ B → g • a ∈ B → g • B = B := (is_block.mk_mem G X).mp hB g a

lemma is_block.mk_subset {B : set X} :
    is_block G X B ↔ ∀ (g : G) (b : X) (hb : b ∈ B) (hb' : b ∈ g • B), g • B ≤ B :=
begin
  split,
  { intros hB g b hb hgb,
    rw [set.le_eq_subset, set_smul_subset_iff,
      is_block.def_mem G X hB b g⁻¹ hb (mem_smul_set_iff_inv_smul_mem.mp hgb)] },
  { rw is_block.mk_notempty,
    intros hB g hg,
    rw set.ne_empty_iff_nonempty at hg,
    obtain ⟨b : X, hb' : b ∈ g • B, hb : b ∈ B⟩ := set.nonempty_def.mp hg,
    apply le_antisymm,
    { exact hB g b hb hb' },
    suffices : g⁻¹ • B ≤ B,
    { rw set.le_eq_subset at this ⊢,
      rw [← inv_inv g, ← set_smul_subset_iff], exact this },
    exact hB g⁻¹ (g⁻¹ • b) (mem_smul_set_iff_inv_smul_mem.mp hb') (smul_mem_smul_set_iff.mpr hb) }
end

/-- Subsingletons are (trivial) blocks -/
lemma subsingleton_is_block (B : set X) (hB : B.subsingleton) : is_block G X B :=
begin
  rw is_block.mk_mem,
  intros g a ha hga,
  ext b,
  have hB1 : B = { a },
  { ext b,
    rw set.subsingleton.eq_singleton_of_mem hB ha, },
  have hB2 : B = { g • a},
  { ext b, rw set.subsingleton.eq_singleton_of_mem hB hga, },
  have hB3 : g • B = { g • a },
  { rw hB1, simp only [set.smul_set_singleton], },
  rw hB3, rw ← hB2,
end

/-- The empty set is a block -/
lemma bot_is_block : is_block G X (⊥ : set X) :=
begin
  rw is_block.mk,
  intro g, apply or.intro_left,
  simp only [set.bot_eq_empty, set.smul_set_empty],
end

/-- Singletons are blocks -/
lemma singleton_is_block (x : X) : is_block G X ({x} : set X) :=
begin
  rw is_block.mk,
  intro g,
  cases em (g • x = x) with h h',
  { apply or.intro_left,
    simp only [h, set.smul_set_singleton]  },
  apply or.intro_right,
  simp only [set.smul_set_singleton, set.disjoint_singleton, ne.def],
  exact h',
end

/-- An invariant block is a block -/
lemma is_block_of_invariant (B : set X) (hfB : is_invariant_block G X B) :
  is_block G X B :=
begin
 --  unfold is_fixed_block at hfB,
  rw is_block.mk,
  intro g, apply or.intro_left,
  apply le_antisymm,
  exact hfB g,
  { intros x hx,
    rw mem_smul_set_iff_inv_smul_mem,
    apply hfB g⁻¹,
    exact smul_mem_smul_set_iff.mpr hx },
end

/-- A fixed block is a block -/
lemma is_block_of_fixed (B : set X) (hfB : is_fixed_block G X B) :
  is_block G X B :=
begin
  rw is_block.mk,
  unfold is_fixed_block at hfB,
  intro g, apply or.intro_left, exact hfB g,
end

/-- An orbit is a block -/
lemma is_block_of_orbit (a : X) : is_block G X (orbit G a) :=
begin
  apply is_block_of_fixed,
  intro g, apply smul_orbit,
end

/-- The full set is a block -/
lemma top_is_block : is_block G X (⊤ : set X) :=
begin
  apply is_block_of_fixed,
  intro g,
  simp only [set.top_eq_univ, set.smul_set_univ],
end

/-- Is B is a block for an action G, it is a block for the action of any subgroup of G -/
lemma subgroup.is_block {H : subgroup G} {B : set X} (hfB : is_block G X B) :
  is_block H X B :=
begin
  rw is_block.mk, intro h,
  simpa only using is_block.def_one G X hfB h
end

lemma sub_mul_action.is_block {C : sub_mul_action G X} {B : set X}
  (hB : is_block G X B) : is_block G ↥C (coe ⁻¹' B) :=
begin
  rw is_block.mk,
  intro g,
  cases is_block.def_one G X hB g with heq hdis,
  { apply or.intro_left,  ext,
    rw mem_smul_set_iff_inv_smul_mem,
    simp only [set.mem_preimage, sub_mul_action.coe_smul_of_tower],
    rw  [← mem_smul_set_iff_inv_smul_mem, heq],  },
  { apply or.intro_right,
    simp only [disjoint_iff, set.inf_eq_inter, set.bot_eq_empty, set.eq_empty_iff_forall_not_mem],
    intros x hx,
    refine set.disjoint_left.mp hdis _ _,
    use ↑x,
    { obtain ⟨y, hy, rfl⟩ := hx.left,
      simp only [sub_mul_action.coe_smul_of_tower, smul_mem_smul_set_iff],
      exact set.mem_preimage.mp hy },
    { exact set.mem_preimage.mp hx.right } }
end

lemma sub_mul_action.smul_coe_eq_coe_smul {C : sub_mul_action G X} {B : set C} {g : G} :
  g • (coe '' B : set X) = coe '' (g • B) :=
begin
  ext, split,
  { intro hx, obtain ⟨y, hy, rfl⟩ := hx,
    obtain ⟨z, hz, rfl⟩ := hy,
    use g • z,
    split,
      exact ⟨z, hz, rfl⟩,
      rw sub_mul_action.coe_smul_of_tower },
  { intro hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    obtain ⟨z, hz, rfl⟩ := hy,
    rw sub_mul_action.coe_smul_of_tower,
    use ↑z, split,
      exact ⟨z, hz, rfl⟩, refl }
end

lemma sub_mul_action.is_block_coe {C : sub_mul_action G X} {B : set C} :
  is_block G C B ↔ is_block G X (coe '' B) :=
begin
  simp only [is_block.mk],
  apply forall_congr,
  intro g,
  rw sub_mul_action.smul_coe_eq_coe_smul,
  apply or_congr (set.image_eq_image subtype.coe_injective).symm,
  simp only [set.disjoint_iff, set.subset_empty_iff],
    rw ← set.inj_on.image_inter (set.inj_on_of_injective subtype.coe_injective _)
      (set.subset_univ _) (set.subset_univ _),
    simp only [set.image_eq_empty]
end

lemma is_block.of_top_iff (B : set X) :
  is_block G X B ↔ is_block (⊤ : subgroup G) X B :=
begin
  simp only [is_block.mk],
  split,
  intros h g, exact h g,
  intros h g, exact h ⟨g, subgroup.mem_top g⟩
end

lemma orbit.equal_or_disjoint {a b : X} :
  orbit G a = orbit G b ∨ disjoint (orbit G a) (orbit G b) :=
begin
  cases em (disjoint (orbit G a) (orbit G b)) with h h,
  { apply or.intro_right, exact h },
  apply or.intro_left,
  rw set.not_disjoint_iff at h,
  obtain ⟨x, hxa, hxb⟩ := h,
  rw ← orbit_eq_iff at hxa hxb,
  rw [← hxa, ← hxb],
end

/-- The intersection of two blocks is a block -/
lemma is_block.inter {B₁ B₂ : set X} (h₁ : is_block G X B₁) (h₂ : is_block G X B₂) :
  is_block G X (B₁ ∩ B₂) :=
begin
  rw is_block.mk,
  intro g,
  rw set.smul_set_inter,
  cases is_block.def_one G X h₁ g with h₁ h₁, -- em (disjoint (g • B₁) B₁) with h h,
  { cases is_block.def_one G X h₂ g with h₂ h₂,
    { apply or.intro_left, rw [h₁, h₂] },
    apply or.intro_right,
    apply disjoint.inter_left', apply disjoint.inter_right',
    exact h₂ },
  { apply or.intro_right,
    apply disjoint.inter_left, apply disjoint.inter_right,
    exact h₁ }
end

/-- An intersection of blocks is a block -/
lemma is_block.Inter {ι : Type*} {B : ι → set X} (hB : ∀ i : ι,
  is_block G X (B i)) : is_block G X (⋂ i, B i) :=
begin
  rw is_block.mk,
  cases em (is_empty ι) with hι hι,
  { -- ι = ∅, block = ⊤
    suffices : (⋂ (i : ι), B i) = set.univ,
    { rw this, exact is_block.def_one G X (top_is_block G X) },
    simp only [set.top_eq_univ, set.Inter_eq_univ],
    intro i, exfalso, apply hι.false, exact i },

  intro g, rw set.smul_set_Inter,
  cases em (∃ (i : ι), disjoint (g • (B i)) (B i)) with h h,
  { obtain ⟨j,hj⟩ := h,
    apply or.intro_right,
      -- rw set.smul_Inter h,
    refine disjoint.mono _ _ _ ,
    exact (g • (B j)) , exact (B j),
    apply set.Inter_subset ,
    apply set.Inter_subset,
    exact hj },
  simp only [not_exists] at h,
  apply or.intro_left,
  have : ∀ (i : ι) , g • (B i) = B i := λ i, or.resolve_right (is_block.def_one G X (hB i) g) (h i),
  rw set.Inter_congr this
end

lemma is_block.of_subgroup_of_conjugate {B : set X} (H : subgroup G)
  (hB : is_block H X B) (g : G) :
  is_block (subgroup.map (mul_equiv.to_monoid_hom (mul_aut.conj g)) H) X (g • B) :=
begin
  rw is_block.mk,
  intro h',
  obtain ⟨h, hH, hh⟩ := subgroup.mem_map.mp (set_like.coe_mem h'),
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply] at hh,
  suffices : h' • g • B = g • h • B,
  simp only [this],
  cases is_block.def_one H X hB ⟨h, hH⟩ with heq hdis,
  { apply or.intro_left,
    apply congr_arg,
    exact heq },
  { apply or.intro_right,
    apply set.disjoint_image_of_injective (mul_action.injective g),
    exact hdis },
  suffices : (h' : G) • g •  B = g • h • B,
    rw ← this, refl,
  rw ← hh,
  rw smul_smul (g * h * g⁻¹) g B,
  rw smul_smul g h B,
  simp only [inv_mul_cancel_right],
end

/-- A translate of a block is a block -/
lemma is_block_of_block {B : set X} (g : G) (hB : is_block G X B) :
  is_block G X (g • B) :=
begin
  rw is_block.of_top_iff at hB ⊢,
  suffices : subgroup.map (mul_equiv.to_monoid_hom (mul_aut.conj g)) ⊤ = ⊤,
  rw ← this,
  refine is_block.of_subgroup_of_conjugate G X _ hB g,
  suffices : ⊤ = subgroup.comap (mul_equiv.to_monoid_hom (mul_aut.conj g)) ⊤,
  { rw this,
    refine subgroup.map_comap_eq_self_of_surjective _ _,
    exact mul_equiv.surjective (mul_aut.conj g),  },
  rw subgroup.comap_top
end

/-- A block_system of X is a partition of X into blocks -/
def is_block_system (B : set (set X)) :=
  setoid.is_partition B ∧ (∀ (b : set X), b ∈ B → is_block G X b)

/-- Translates of a block form a `block_system` -/
lemma is_block_system.of_block [hGX : mul_action.is_pretransitive G X]
  {B : set X} (hB : is_block G X B) (hBe : B.nonempty) :
  is_block_system G X (set.range (λ (g : G), g • B)) :=
begin
  split,
  split,
  { simp only [set.mem_range, not_exists],
    intros x hx,
    change (λ b, x • b) '' B = ∅ at hx,
    rw set.image_eq_empty at hx,
    exact set.nonempty.ne_empty hBe hx },
  { intro a,
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe,
    let hGX_exists := hGX.exists_smul_eq,
    obtain ⟨g : G, hab : (g • b) = a⟩ := hGX_exists b a,
    have hg : a ∈ g • B,
    { change a ∈ (λ b, g • b) '' B,
      rw set.mem_image, use b, exact ⟨hb, hab⟩ },
    use (g • B),
    split,
    { simp only [set.mem_range, exists_apply_eq_apply, exists_unique_iff_exists, exists_true_left],
      exact hg },
    simp only [set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index, forall_apply_eq_imp_iff'],
    intros g' hg',
    apply symm,
    apply or.resolve_right (is_block.def G X hB g g'),
    rw set.not_disjoint_iff,
    use a, exact ⟨hg, hg'⟩ },
  intro b, rintros ⟨g, hg : g • B = b⟩,
  rw ← hg, exact is_block_of_block G X g hB,
end

/-- Orbits of an element form a partition -/
lemma is_partition.of_orbits :
  setoid.is_partition (set.range (λ (a : X), orbit G a)) :=
begin
  split,
  { rintro ⟨a, ha : orbit G a = ∅⟩,
    apply set.nonempty.ne_empty (mul_action.orbit_nonempty a),
    exact ha },
  intro a, use orbit G a,
  split,
  simp only [set.mem_range_self, mem_orbit_self, exists_unique_iff_exists, exists_true_left],
  simp only [set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index, forall_apply_eq_imp_iff'],
  intros b hb,
  rw orbit_eq_iff,
  obtain ⟨g, rfl⟩ := mul_action.mem_orbit_iff.mp hb,
  use g⁻¹, simp only [inv_smul_smul]
end


open_locale classical


lemma card_of_block_mul_card_of_orbit_of [hfX : fintype X] [is_pretransitive G X]
  (B : set X) [hB_ne : B.nonempty] (hB : is_block G X B) :
  (set.range (λ (g : G), g • B)).to_finset.card * fintype.card B = fintype.card X :=
begin
  rw setoid.is_partition.card_eq_sum_parts (is_block_system.of_block G X hB hB_ne).left,
  rw [finset.sum_congr rfl _, finset.sum_const (fintype.card ↥B), nsmul_eq_mul, nat.cast_id],
  intros s hs,
  simp only [set.mem_to_finset, set.mem_range] at hs,
  obtain ⟨g, rfl⟩ := hs,
  simp only [← set.to_finset_card],
  rw ← finset.card_image_of_injective B.to_finset (mul_action.injective g),
  refine congr_arg _ _,
  simp only [← finset.coe_inj, set.coe_to_finset, finset.coe_image, set.image_smul],
end

lemma card_of_block_divides [hfX : fintype X] [is_pretransitive G X]
  (B : set X) [hB_ne : B.nonempty] (hB : is_block G X B)  :
  fintype.card B ∣ fintype.card X :=
begin
  rw ← @card_of_block_mul_card_of_orbit_of G X _ _ hfX _ B hB_ne hB,
  simp only [dvd_mul_left],
end

/- §7. Imprimitivity -/

/-- An auxiliary lemma, variant of normal_mul' ,
with an explicit N.normal hypothesis,
so that the typeclass inference machine works.
-/

lemma normal_mul'' (N : subgroup G) (nN : N.normal) (K : subgroup G)
  (h : N ⊔ K = ⊤) (g : G) : ∃ (n : N) (k : K), g = n * k :=
begin
    have hg : g ∈ ↑(N ⊔ K), { rw h, exact subgroup.mem_top g,},
    rw [subgroup.normal_mul, set.mem_mul] at hg,
    obtain ⟨x, y, hx, hy, hxy⟩ := hg,
    use x, exact hx, use y, exact hy, rw eq_comm at hxy, exact hxy,
end

lemma orbit.is_pretransitive' (a : X) (ha : mul_action.orbit G a = ⊤) : is_pretransitive G X :=
begin
  apply is_pretransitive.mk,
  have : ∀ (x : X), ∃ (g : G), g • a = x,
  { intro x, rw [← mul_action.mem_orbit_iff, ha, set.top_eq_univ], apply set.mem_univ },
  intros x y,
  obtain ⟨g, hx⟩ := this x,
  obtain ⟨h, hy⟩ := this y,
  use h * g⁻¹,
  rw ← hx, rw [smul_smul, inv_mul_cancel_right], exact hy
end

theorem orbit.is_block_of_normal (N : subgroup G) [nN : subgroup.normal N] (a : X) :
  is_block G X (orbit N a) :=
begin
  rw is_block.mk,
  intro g,
  suffices : g • (orbit N a) = orbit N (g • a),
  { rw this, exact orbit.equal_or_disjoint N X },

  ext,
  split,
  { rintros ⟨b, ⟨h, hb' : h • a = b⟩, hb⟩,
    rw [← hb, ← hb'],
    suffices : g • h • a = (g * h * g⁻¹) • g • a, rw this,
      suffices : g * h * g⁻¹ ∈ N,
      rw ← set_like.coe_mk (g * h * g⁻¹) this,
      refine mul_action.mem_orbit (g • a) (⟨g * h * g⁻¹, this⟩ : N),
    apply nN.conj_mem, apply set_like.coe_mem,
    rw [smul_smul, inv_mul_cancel_right, ← smul_smul], refl },
  rintros ⟨n, hn : n • g • a = x⟩,
  use (g⁻¹ * n * g) • a,
  split,
  { use g⁻¹ * n * g,
    have this := nN.conj_mem n _ g⁻¹,
    rw inv_inv g at this, exact this,
    apply set_like.coe_mem,
    refl },
  rw [← hn, smul_smul, ← mul_assoc, ← mul_assoc, mul_right_inv, one_mul,
    ← smul_smul], refl,
end

/-- The orbits of a normal subgroup form a block system -/
theorem is_block_system.of_normal (N : subgroup G) [nN : subgroup.normal N] :
  is_block_system G X (set.range (λ a, orbit N a)) :=
begin
  split,
    apply is_partition.of_orbits,
  intro b, rintros ⟨a, rfl⟩,
  apply orbit.is_block_of_normal,
end

-- TODO : Is the assumption B.finite necessary ?
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3 )-/
lemma is_block.of_subset (hGX : is_pretransitive G X) (a : X) (B : set X) (hfB : B.finite) :
  is_block G X (⋂ (k : G) (hg : a ∈ k • B), k • B) :=
begin
  let hGX_exists := hGX.exists_smul_eq,
  let B' := (⋂ (k : G) (hg : a ∈ k • B), k • B),
  cases set.eq_empty_or_nonempty B with hfB_e hfB_ne,
  { suffices : (⋂ (k : G) (hg : a ∈ k • B), k • B) = set.univ,
    rw this, apply top_is_block,
    simp only [set.Inter_eq_univ],
    intros k hk, exfalso,
    rw hfB_e at hk, simpa only [set.smul_set_empty] using hk },

  have hB'₀ : ∀ (k : G) (hk : a ∈ k • B), B' ≤ k • B,
  { intros k hk, apply set.bInter_subset_of_mem, exact hk },

  have hfB' : B'.finite,
  { obtain ⟨b, hb : b ∈ B⟩ := hfB_ne,
    obtain ⟨k, hk : k • b = a⟩ := hGX_exists b a,
    have hk' : a ∈ k • B, use b, exact ⟨hb, hk⟩,
    apply set.finite.subset _ (hB'₀ k hk'),
    apply set.finite.map,
    exact hfB },

  -- have hB' : ∀ (x : X) (hx : x ∈ B') (k : G), a ∈ k • B → x ∈ k • B,
  -- { intros x hx k ha, exact hB'₀ k ha hx},

  have ha : a ∈ B',
  { apply set.mem_bInter, intro g, intro h, exact h },
  have hag : ∀ (g : G), a ∈ g • B' → B' ≤ g • B',
  { intro g, intro hg,
    -- a = g • b ; b ∈ B' ; a ∈ k • B → b ∈ k • B
    intro x, intro hx,
    use g⁻¹ • x, split,
    { apply set.mem_bInter, intro k, rintro (hk : a ∈ k • B),
      rw [← mem_smul_set_iff_inv_smul_mem ,  smul_smul],
      apply hB'₀, --  x hx,
      rw [← smul_smul, mem_smul_set_iff_inv_smul_mem],
      apply hB'₀, -- (g⁻¹ • a) (),
      exact hk, exact mem_smul_set_iff_inv_smul_mem.mp hg, exact hx },
    simp only [smul_inv_smul] },

  have hag' : ∀ (g : G), a ∈ g • B' → B' = g • B',
  { intros g hg,
    rw ← set.finite.to_finset_inj,
    refine finset.eq_of_subset_of_card_le _ _,
    exact hfB', apply set.finite.map, exact hfB',

    rw set.finite.to_finset_mono,
    exact hag g hg,
    apply eq.ge,
    rw set.finite.card_to_finset _,
    swap, exact set.finite.fintype hfB',
    rw set.finite.card_to_finset _,
    swap, apply set.finite.fintype,
    apply set.finite.map, exact hfB',
    apply symm,
    apply set.card_image_of_injective ,
    apply mul_action.injective },

  rw is_block.mk_notempty,
  intros g hg,
  rw set.ne_empty_iff_nonempty at hg,
  obtain ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩ := set.nonempty_def.mp hg,
  obtain ⟨k : G, hk : k • a = b⟩ := hGX_exists a b,
  have hak : a ∈ k⁻¹ • B',
  { use b, apply and.intro hb, rw [← hk, inv_smul_smul] },
  have hagk : a ∈ (k⁻¹ * g) • B',
  { rw [mul_smul, mem_smul_set_iff_inv_smul_mem, inv_inv, hk],
    exact hb' },
  have hkB' : B' = k⁻¹ • B' := hag' k⁻¹ hak,
  have hgkB' : B' = (k⁻¹ * g) • B' := hag' (k⁻¹ * g) hagk,
  rw mul_smul at hgkB',
  rw ← smul_eq_iff_eq_inv_smul at hkB' hgkB',
  rw [← hgkB', hkB']
end

end group

section primitivity

/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/

variables (G X : Type*) [group G] [mul_action G X]

structure is_preprimitive
extends is_pretransitive G X : Prop :=
(has_trivial_blocks : ∀ {B : set X}, (is_block G X B) →
  subsingleton B ∨  B = ⊤)
-- B = ∅ ∨ (∃ (x : X), B = {x}) ∨ B = ⊤

/-
lemma is_preprimitive.mk'  [hGX : is_pretransitive G X]
  (hGX' : ∀ (B : set X),  (is_block G X B) → subsingleton B ∨ B = ⊤) :
  is_preprimitive G X :=
begin
  apply is_preprimitive.mk,
  exact hGX,
  intros B hB,
  cases hGX' B hB,
  { rw set.subsingleton_coe at h,
    cases set.subsingleton.eq_empty_or_singleton h with h' h',
    apply or.intro_left, exact h',
    apply or.intro_right, apply or.intro_left, exact h'},
  apply or.intro_right, apply or.intro_right, exact h,
end
-/

/-- In a preprimitive action,
  any normal subgroup that acts nontrivially is pretransitive
  (Wielandt, th. 7.1)-/
theorem transitive_of_normal_of_preprimitive (N : subgroup G) [nN : subgroup.normal N]
  (hGX : mul_action.is_preprimitive G X) (hNX : mul_action.fixed_points N X ≠ ⊤) :
  mul_action.is_pretransitive N X :=
begin
    have : ∃ (x : X), x ∉ fixed_points N X,
    { rw [← set.ne_univ_iff_exists_not_mem, ← set.top_eq_univ],
      exact hNX },
    obtain ⟨a, ha⟩ := this,
    suffices : mul_action.orbit N a = ⊤,
    { rw set.top_eq_univ at this,
      refine mul_action.orbit.is_pretransitive' _ _ _ this },
    cases hGX.has_trivial_blocks (orbit.is_block_of_normal G X N a) with h h,
    { exfalso,
      apply ha, simp only [mem_fixed_points], intro x,
      rw ← set.mem_singleton_iff,
      suffices : orbit N a = {a},
      { rw ← this, use x, },
      ext b,
      rw set.subsingleton.eq_singleton_of_mem ((orbit ↥N a).subsingleton_coe.mp h)
          (mul_action.mem_orbit_self a)  },

    /- { exfalso, -- orbit N a = ∅
      apply set.nonempty.ne_empty (mul_action.orbit_nonempty a),
      rw ← h },
    cases h with h h,
    { exfalso, -- orbit N a = {x}
      have ha' : orbit N a = {a},
      { obtain ⟨x,hx⟩ := h,
        let haB : a ∈ orbit N a := mul_action.mem_orbit_self a,
        rw [hx, set.mem_singleton_iff] at haB,
        rw [hx, haB] },
      apply ha,
      rw mem_fixed_points, intro n,
      let hn : n • a ∈ (orbit N a) := mul_action.mem_orbit a n,
      rw [ha', set.mem_singleton_iff] at hn,
      exact hn }, -/

    -- orbit N a = ⊤
    exact h,
end

/-- Theorem of Rudio (Wieland, 1964, Th. 8.1) -/
theorem rudio [hpGX : is_preprimitive G X]
  (A : set X) (hfA : A.finite) (hA : A.nonempty) (hA' : A ≠ ⊤)
  (a b : X) (h : a ≠ b):  ∃ (g : G), a ∈ g • A ∧ b ∉ g • A :=
begin
  let B := ⋂ (g : G) (ha : a ∈ g • A), (g • A),
  have hB : is_block G X B :=
    is_block.of_subset G X hpGX.to_is_pretransitive a A hfA,
  suffices : b ∉ B,
  { rw set.mem_Inter at this,
    simpa only [set.mem_Inter, not_forall, exists_prop] using this,
  },
  suffices : B = {a},
  { rw this, rw set.mem_singleton_iff,
    exact ne.symm h },
  have ha : a ∈ B,
  { rw set.mem_Inter, intro g, simp only [set.mem_Inter, imp_self] },
  cases hpGX.has_trivial_blocks hB with hyp hyp,
  { apply set.subsingleton.eq_singleton_of_mem (B.subsingleton_coe.mp hyp),
    rw set.mem_Inter, intro g, simp only [set.mem_Inter, imp_self] },


  /-
  { exfalso, rw hyp at ha, rw ← set.mem_empty_eq a, exact ha },
  cases hyp with hyp hyp,
  { obtain ⟨x,hx⟩ := hyp, rw hx at ha ⊢,
    rw set.singleton_eq_singleton_iff,
    rw set.mem_singleton_iff at ha, exact ha.symm },
-/
  exfalso, apply hA',
  suffices : ∃ (g : G), a ∈ g • A,
  { obtain ⟨g, hg⟩ := this,
    have : B ≤ g • A,
    { rw set.le_eq_subset,
      exact set.bInter_subset_of_mem hg },
      rw [hyp, top_le_iff] at this,
      rw eq_top_iff, intros x hx,
      suffices : g • x ∈ g • A,
        simpa only [smul_mem_smul_set_iff] using this,
      rw this, simp only [set.top_eq_univ] },

  obtain ⟨x, hx⟩ := hA,
  let htGX := hpGX.to_is_pretransitive.exists_smul_eq,
  obtain ⟨g, hg⟩ := htGX x a,
  use g, use x, exact ⟨hx, hg⟩
end

/- For transitive actions, construction of the lattice equivalence
  `stabilizer_block_equiv` between
  - blocks of `mul_action G X` containing a point a ∈ X,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of a under a subgroup containing the stabilizer of a
 is a block -/
lemma is_block_of_suborbit [htGX : is_pretransitive G X] {H : subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
  is_block G X (mul_action.orbit H a) :=
begin
  let hGX_exists := htGX.exists_smul_eq,
  rw is_block.mk_subset, intros g b,
  rintro ⟨h,rfl⟩,
  simp,
  intro hb',
  suffices : g ∈ H,
  { rw [← subgroup.coe_mk H g this,  ← subgroup.smul_def],
    apply smul_orbit_subset },
  rw [mem_smul_set_iff_inv_smul_mem, subgroup.smul_def, ← mul_action.mul_smul] at hb',
  obtain ⟨k : ↥H, hk⟩ := hb',
  simp only at hk,
  rw [mul_action.mul_smul, ← smul_eq_iff_eq_inv_smul, ← inv_inv (h : G),
    ← smul_eq_iff_eq_inv_smul, ← mul_action.mul_smul, subgroup.smul_def, ← mul_action.mul_smul] at hk,
  rw ← mem_stabilizer_iff at hk,
  let hk' := hH hk,
  rw [subgroup.mul_mem_cancel_right, subgroup.mul_mem_cancel_left] at hk',
  exact hk',
  apply subgroup.inv_mem, exact set_like.coe_mem h,
  exact set_like.coe_mem k,
end

/-- If B is a block containing a , then the stabilizer of B contains the stabilizer of a -/
lemma stabilizer_of_block {B : set X} (hB : is_block G X B) {a : X} (ha : a ∈ B) :
  stabilizer G a ≤ stabilizer G B :=
begin
  intros g hg,
  rw mem_stabilizer_iff at hg ⊢,
  cases is_block.def_one G X hB g with h h',
  exact h,
  exfalso, rw ← set.mem_empty_eq a,
  rw [disjoint_iff, set.inf_eq_inter, set.bot_eq_empty] at h',
  rw [← h', set.mem_inter_eq],
  split,
  rw ← hg, rw smul_mem_smul_set_iff, exact ha,
  exact ha
end

/-- A block is the orbit of a under its stabilizer -/
lemma block_of_stabilizer_of_block [htGX : is_pretransitive G X] {B : set X} (hB : is_block G X B) {a : X} (ha : a ∈ B) :
  mul_action.orbit (stabilizer G B) a = B :=
begin
  let htGX_exists := htGX.exists_smul_eq,
  ext, split,
  { -- rw mul_action.mem_orbit_iff, intro h,
    rintro ⟨k, rfl⟩,
    let z := mem_stabilizer_iff.mp (set_like.coe_mem k),
    rw ← subgroup.smul_def at z,
    let zk : k • a ∈ k • B := smul_mem_smul_set_iff.mpr ha,
    rw z at zk, exact zk },
  intro hx,
  obtain ⟨k, rfl⟩ := htGX_exists a x,
  use k,
  { rw mem_stabilizer_iff,
    exact is_block.def_mem G X hB a k ha hx },
  refl,
end

/-- A subgroup containing the stabilizer of a is the stabilizer of the orbit of a under that subgroup -/
lemma stabilizer_of_block_of_stabilizer [htGX : is_pretransitive G X] {a : X} {H : subgroup G} (hH : stabilizer G a ≤ H) :
  stabilizer G (orbit H a) = H :=
begin
  let htGX_exists := htGX.exists_smul_eq,
  ext g, split,
  { intro hg, rw mem_stabilizer_iff at hg,
    suffices : g • a ∈ orbit H a,
    { rw mem_orbit_iff at this,
      obtain ⟨k, hk⟩ := this,
      rw ← (subgroup.mul_mem_cancel_left H (set_like.coe_mem k⁻¹)),
      rw smul_eq_iff_eq_inv_smul at hk,
      apply hH,
      rw mem_stabilizer_iff, rw mul_action.mul_smul,
      rw ← subgroup.smul_def, exact hk.symm },
    rw ← hg,
    simp only [smul_mem_smul_set_iff, mem_orbit_self] },
  intro hg,
  rw mem_stabilizer_iff,
  rw [← subgroup.coe_mk H g hg,  ← subgroup.smul_def],
  apply smul_orbit,
end

/-- Order equivalence between blocks in X containing a point a
 and subgroups of G containing the stabilizer of a (Wielandt, th. 7.5)-/
noncomputable
theorem stabilizer_block_equiv [htGX : is_pretransitive G X] (a : X) :
  { B : set X // a ∈ B ∧ is_block G X B } ≃o set.Ici (stabilizer G a) :=
{ to_fun := λ ⟨B, ha, hB⟩, ⟨stabilizer G B, stabilizer_of_block G X hB ha⟩,
  inv_fun := λ ⟨H, hH⟩, ⟨mul_action.orbit H a, mul_action.mem_orbit_self a, is_block_of_suborbit G X hH⟩,
  left_inv := λ ⟨B, ha, hB⟩, (id (propext subtype.mk_eq_mk)).mpr (block_of_stabilizer_of_block G X hB ha),
  right_inv := λ ⟨H, hH⟩, (id (propext subtype.mk_eq_mk)).mpr (stabilizer_of_block_of_stabilizer G X hH),
  map_rel_iff' := begin
rintro ⟨B, ha, hB⟩, rintro ⟨B', ha', hB'⟩,
simp only [equiv.coe_fn_mk, subtype.mk_le_mk, set.le_eq_subset],
split,
{ intro hBB',
  rw ← block_of_stabilizer_of_block G X hB ha,
  rw ← block_of_stabilizer_of_block G X hB' ha',
  intro x, rintro ⟨k, rfl⟩, use k, apply hBB', exact set_like.coe_mem k,
  refl },
{ intro hBB',
  intro g, simp only [mem_stabilizer_iff],
  intro hgB,
  apply is_block.def_mem G X hB' a g ha', apply hBB', rw ← hgB,
  simp only [smul_mem_smul_set_iff], exact ha }, end,
}

/- Couldn't use in a straightforward way the order equivalence
for proving the next theorem — what a pity ! -/
instance block.has_top (a : X) : order_top {B // a ∈ B ∧ is_block G X B} :=
let ha : a ∈ (⊤ : set X) := trivial in
let htop : is_block G X ⊤ := top_is_block G X in
{ top := ⟨⊤, ha, top_is_block G X⟩,
    le_top := λ ⟨B, ha, hB⟩,
    begin
      simp only [set.top_eq_univ, subtype.mk_le_mk, set.le_eq_subset, set.subset_univ],
    end,  }

/-- An pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
theorem maximal_stabilizer_iff_primitive [hnX : nontrivial X] [htGX : is_pretransitive G X]
  (a : X) : (stabilizer G a).is_maximal ↔ is_preprimitive G X :=
begin
  let htGX_exists := htGX.exists_smul_eq,
  split,
  { intro ha,
    apply is_preprimitive.mk htGX,
    intros B hB,
    rw or_iff_not_imp_left, intro hB',
--    rw [← not_nontrivial_iff_subsingleton, not_not] at hB',

    suffices this : ∃ (k : G), a ∈ k • B,
    { obtain ⟨k, hk⟩ := this,
      have hkB : is_block G X (k • B) := is_block_of_block G X k hB,
      cases lt_or_eq_of_le (stabilizer_of_block G X hkB hk),
      { -- k • B = ⊤
--        apply or.intro_right,
        have : stabilizer G (k • B) = ⊤ := (subgroup.is_maximal_def.mp ha).right _ h,
        have H : ∀ (g : G) (x : X), x ∈ k • B → g • x ∈ k • B,
        { intros g x hx,
          suffices hg : g ∈ stabilizer G (k • B),
          { rw mem_stabilizer_iff at hg, rw ← hg,
            simp only [smul_mem_smul_set_iff],  exact hx },
          rw subgroup.is_maximal_def at ha,
          rw ha.right _ h,
          simp only [subgroup.mem_top] },

        rw eq_top_iff, intros b _,
        obtain ⟨h, h'⟩ := htGX_exists a b,
        apply smul_mem_smul_set_iff.mp,
        apply H k b ,
        rw ← h', exact H h a hk },

      -- k • B = {a}
      exfalso,
      apply hB',
      rw set.subsingleton_coe,
      refine set.subsingleton_of_image (mul_action.injective k) _ _,
      change (k • B).subsingleton,
      suffices : k • B = { a },
      { rw this, simp only [set.subsingleton_singleton] },

      rw ← block_of_stabilizer_of_block G X (singleton_is_block G X a) (set.mem_singleton a),
      rw ← block_of_stabilizer_of_block G X hkB hk,
      rw ← h,
      suffices : stabilizer G ({a} : set X) = stabilizer G a, rw ← this,

      ext,
      simp only [mem_stabilizer_iff, set.smul_set_singleton, set.singleton_eq_singleton_iff] },

    rw [← not_nontrivial_iff_subsingleton, not_not] at hB',
    obtain ⟨b, _, _⟩ := hB',
    obtain ⟨k, hk⟩ := htGX_exists b a,
    use k, rw ← hk, simp only [smul_mem_smul_set_iff],
    exact subtype.mem b },

  intro hGX,
  refine {out := _},
  split,
  { obtain ⟨b, hb⟩ := (nontrivial_iff_exists_ne a).mp hnX,
    obtain ⟨g, rfl⟩ := htGX_exists a b,
    suffices : g ∉ stabilizer G a,
    { intro h, apply this, rw h, exact subgroup.mem_top g },
    rw mem_stabilizer_iff, exact hb },
  { intros H hH,
    rw ← stabilizer_of_block_of_stabilizer G X (le_of_lt hH),
    suffices : orbit H a = (⊤ : set X),
    { rw this,
      rw eq_top_iff,
      intros g _,
      rw mem_stabilizer_iff,
      simp only [set.top_eq_univ, set.smul_set_univ] },

    cases hGX.has_trivial_blocks (is_block_of_suborbit G X (le_of_lt hH)) with hyp hyp,
    { exfalso,
      rw set.subsingleton_coe at hyp,
      apply not_le_of_gt hH,
      intros h hH,
      rw mem_stabilizer_iff,
      refine hyp _ _,
      { use h, exact hH,  simp, refl, },
      exact mem_orbit_self a },
    exact hyp },
end

/-- Theorem 8.4 : if the action of a subgroup H on an orbit is primitive,
   and if that orbit is small enough, then the action of G is primitive -/
theorem is_primitive_of_subgroup' [hfX : fintype X] [decidable_eq X] (htGX : is_pretransitive G X)
  (H : subgroup G) {C : sub_mul_action H X} (hH : is_preprimitive H C)
  (hC : 2 * C.carrier.to_finset.card > fintype.card X) :
  is_preprimitive G X :=
begin
  apply is_preprimitive.mk htGX,
  intros B hB,

  cases subsingleton_or_nontrivial B with hB_ss hB_nt,
  exact or.intro_left _ hB_ss,

  rw or_iff_not_imp_right,
  intro hB_ne_top,

  have hB_ne : nonempty ↥B :=  @nontrivial.to_nonempty _ hB_nt,
  have hB_ne' : 0 < fintype.card B := fintype.card_pos_iff.mpr hB_ne,
  rw set.nonempty_coe_sort at hB_ne,

  suffices : fintype.card B < 2,
  { rw [← not_nontrivial_iff_subsingleton, ← fintype.one_lt_card_iff_nontrivial, not_lt],
    exact nat.lt_succ_iff.mp this },

  have hcard_eq : ∀ (g : G), B.to_finset.card = (g • B).to_finset.card,
  { intro g,
    rw finset.card_congr (λ b hb, g • b) _ _ _ ,
    swap,
    { intros a ha, simp, simp at ha, exact ⟨a,ha,rfl⟩, },
    { intros a b _ _ h,
      apply mul_action.injective g,
      simp only at h, exact h },
    { intros b hb,
      simp only [set.mem_to_finset] at hb,
      obtain ⟨a, ha, rfl⟩ := hb,
      use a, use (set.mem_to_finset.mpr ha) } },

  have hba : ∀ (g : G), is_block H C (coe ⁻¹' (g • B)),
  { intro g,
    apply sub_mul_action.is_block,
    exact subgroup.is_block G X (is_block_of_block G X g hB) },

  have hyp : ∀ (g : G), ¬ (C : set X) ≤ (g • B),
  { intros g hg,
    suffices : 2 * B.to_finset.card > fintype.card X,
    { obtain ⟨k, hXk⟩ := @card_of_block_divides G X _ _ _ _ B hB_ne hB,
      simp only [mul_comm, hXk, set.to_finset_card] at this,
      have hk : k < 2, { rw ← (mul_lt_mul_right hB_ne'), exact this },

      cases nat.eq_or_lt_of_le (nat.le_of_lt_succ hk) with hk1 hk0,
      { apply hB_ne_top,
        rw [hk1, mul_one] at hXk,
        simp only [set.top_eq_univ],
        rw [← set.coe_to_finset B, ← finset.coe_univ, finset.coe_inj],
        apply finset.eq_univ_of_card B.to_finset, rw hXk,
        exact set.to_finset_card B },
      { rw [nat.eq_zero_of_le_zero (nat.le_of_lt_succ hk0), mul_zero] at hXk,
        exfalso,
        have : fintype.card ↥B ≤ fintype.card X := set_fintype_card_le_univ B,
        rw hXk at this,
        rw (nat.eq_zero_of_le_zero this) at hB_ne',
        exact lt_irrefl 0 hB_ne' } },

    apply lt_of_lt_of_le hC,
    simp only [mul_le_mul_left, nat.succ_pos'],
    rw hcard_eq,
    rw set.le_eq_subset at hg,
    refine le_trans _ (finset.card_le_of_subset (set.to_finset_mono.mpr hg)),
    apply le_of_eq, apply congr_arg,
    simp only [set.to_finset_inj], exact rfl },

  -- À ce point, on a prouvé hyp :
  -- ∀ g, g • B ne contient pas C.
  -- On reformule :
  have hyp : ∀ (g : G), (coe ⁻¹' (g • B) : set C) ≠ (⊤ : set C),
  { simp only [not_exists, set.le_eq_subset] at hyp,
    intros g h,
    apply hyp g,
    intros x hx,
    let hx' := set.mem_univ (⟨x, hx⟩ : ↥C),
    rw set.top_eq_univ at h,
    rw [← h, set.mem_preimage, sub_mul_action.coe_mk] at hx',
    exact hx' },

  -- en déduire, via la preprimitivité (hH), que (C ∩ (g • B)) ≤ 1
  have hyp' : ∀ (g : G), (coe ⁻¹' (g • B) : set C).to_finset.card ≤ 1,
  { intro g,

    let h := or.resolve_right (hH.has_trivial_blocks (hba g)) (hyp g),
    simp only [set.to_finset_card],
    exact fintype.card_le_one_iff_subsingleton.mpr h },

  -- on reformule :
  have hyp' : ∀ (g : G), (C.carrier ∩ (g • B)).to_finset.card ≤ 1,
  { intro g,
    apply le_trans _ (hyp' g),
    apply le_of_eq,
    rw ← finset.card_image_of_inj_on (function.injective.inj_on (subtype.coe_injective) _),
    refine congr_arg _ _, apply_instance,
    rw [← finset.coe_inj, set.coe_to_finset, finset.coe_image, set.coe_to_finset],
    rw set.inter_comm,
    simp_rw [← subtype.image_preimage_coe] },

  -- en déduire que le système de blocs { g • B } a pour cardinal au moins card(C)
  have : C.carrier.to_finset.card ≤ (set.range (λ g, g • B)).to_finset.card,
  { rw setoid.is_partition.card_set_eq_sum_parts C.carrier
      (is_block_system.of_block G X hB hB_ne).left,
    rw finset.card_eq_sum_ones,
    refine finset.sum_le_sum _,
    intros t ht,
    simp only [set.mem_to_finset, set.mem_range] at ht,
    obtain ⟨g, ht⟩ := ht,
    rw ← ht,
    exact (hyp' g) },

  have thisX : fintype.card X = fintype.card B * (set.range (λ (g : G), g • B)).to_finset.card,
  { rw ← @card_of_block_mul_card_of_orbit_of G X _ _ _ _ B hB_ne hB,
    conv_rhs { rw mul_comm, } },
  /- On peut conclure que B < 2 :
 via thisX : X = P * B, this : C ≤ P, hC : 2 * C > X -/

  rw thisX at hC, -- 2 * C > P * B
  apply lt_of_mul_lt_mul_right',
  apply lt_of_le_of_lt _ hC,
  exact nat.mul_le_mul_left _ this,
end

end primitivity

end mul_action

end FundamentalConcepts
