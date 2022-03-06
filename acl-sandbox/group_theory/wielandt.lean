/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.subgroup.pointwise
import group_theory.coset
import group_theory.quotient_group
import group_theory.abelianization
import group_theory.group_action.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.conj_act
import .ad_sub_mul_actions

import order.partition.finpartition

import data.setoid.partition
import data.set.basic
import data.fintype.basic
import order.rel_classes

open_locale big_operators pointwise

/-
# Finite permutation groups
A formalization of Wielandt's book, *Finite permutation groups*

-/

section Maximal_Subgroups
variables {G : Type*} [group G]

namespace subgroup
/-- An subgroup is maximal if it is maximal in the collection of proper subgroups. -/
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
  exact hmax H g (le_of_lt hKH) hgK hgH, },
end

theorem is_maximal.eq_of_le {K H: subgroup G}
  (hK : K.is_maximal) (hH : H ≠ ⊤) (KH : K ≤ H) : K = H :=
eq_iff_le_not_lt.2 ⟨KH, λ h, hH (hK.1.2 _ h)⟩

end subgroup
end Maximal_Subgroups

/- Chapter 1 -/
section FundamentalConcepts

variables (G X : Type*) [group G] [mul_action G X]

-- Section 6 : Blocks

namespace mul_action

/-- A fixed block is an invariant subset -/
def is_fixed_block -- (G X : Type*) [group G] [hGX : mul_action G X] 
  (B : set X) := ∀ (g : G), g • B = B 

def is_invariant_block (B : set X) := ∀ (g : G), g • B ≤ B

/-- A block is a set which is either fixed or moved to a disjoint subset -/
def is_block -- (G X : Type*) [group G] [hGX : mul_action G X] 
  (B : set X) := ∀ (g : G), g • B = B ∨ disjoint (g • B) B

lemma is_block' {B : set X} (hB : is_block G X B) :
  ∀ (g g' : G), g • B = g' • B ∨ disjoint (g • B) (g' • B) :=
begin
  intros g g',
  let k := g⁻¹ * g', 
  have hk : g * k = g' := by { rw mul_inv_cancel_left},
  rw [← hk, ← smul_smul],
  cases hB k with heq hdis,
  { apply or.intro_left, rw heq },
  apply or.intro_right,
    refine disjoint.image hdis.symm _ _ _, 
    exact set.univ,
    apply function.injective.inj_on , 
    apply mul_action.injective,
    repeat { simp only [set.subset_univ], }
end

lemma is_block_def' {B : set X} (hB : is_block G X B) (a : X) (g : G):
  a ∈ B → g • a ∈ B → g • B = B :=
begin
  intros ha hga,
  cases hB g⁻¹ with h h',
  { rw [smul_eq_iff_eq_inv_smul, h], },
  exfalso, rw ← set.mem_empty_eq a, 
  rw [disjoint_iff, set.inf_eq_inter, set.bot_eq_empty] at h', 
  rw [← h', set.mem_inter_eq], 
  split,
  rw mem_smul_set_iff_inv_smul_mem, rw inv_inv, exact hga,
  exact ha,
end

lemma is_block_mk {B : set X} (hB : ∀ (g : G), (g • B) ∩ B ≠ ∅ → g • B = B) :
  is_block G X B :=
begin
  intro g, 
  cases em (g • B ∩ B = ∅) with h h', 
  apply or.intro_right, rw set.disjoint_iff_inter_eq_empty, exact h,
  apply or.intro_left, exact hB g h',
end


lemma is_block_mk' {B : set X} (hB : ∀ (g : G) (b : X) (hb : b ∈ B) (hb' : b ∈ g • B), g • B ≤ B) :
    is_block G X B :=
begin
  apply is_block_mk,
  intros g hg,
  rw set.ne_empty_iff_nonempty at hg,
  obtain ⟨b : X, hb' : b ∈ g • B, hb : b ∈ B⟩ := set.nonempty_def.mp hg,

  apply le_antisymm, 
  exact hB g b hb hb', 

  suffices : g⁻¹ • B ≤ B, 
  { rw set.le_eq_subset at this ⊢, 
    rw [← inv_inv g, ← set_smul_subset_iff], exact this },
  refine hB g⁻¹ (g⁻¹ • b) _ _,
  rw ← mem_smul_set_iff_inv_smul_mem, exact hb', 
  rw smul_mem_smul_set_iff, exact hb, 
end

/-- The empty set is a block -/
lemma bot_is_block : is_block G X (⊥ : set X) :=
begin
  intro g, apply or.intro_left,
  simp only [set.bot_eq_empty, set.smul_set_empty], 
end

/-- Singletons are blocks -/
lemma singleton_is_block (x : X) : is_block G X ({x} : set X) :=
begin
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
  intro g, apply or.intro_left, 
  apply le_antisymm, 
  exact hfB g, 
  { intros x hx, 
    rw mem_smul_set_iff_inv_smul_mem,
    apply hfB g⁻¹,
    exact smul_mem_smul_set_iff.mpr hx, },
end

/-- A fixed block is a block -/
lemma is_block_of_fixed (B : set X) (hfB : is_fixed_block G X B) :
  is_block G X B :=
begin
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


lemma subgroup.is_block (H : subgroup G) (B : set X) (hfB : is_block G X B) : 
  is_block H X B :=
begin
  intro h, exact hfB h, 
end

lemma is_block.of_top_iff (B : set X) :
  is_block G X B ↔ is_block (⊤ : subgroup G) X B :=
begin
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
  intro g,
  rw ← set.smul_inter,
  cases h₁ g with h₁ h₁, -- em (disjoint (g • B₁) B₁) with h h,
  { cases h₂ g with h₂ h₂, 
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
  cases em (is_empty ι) with hι hι,
  { -- ι = ∅, block = ⊤
    suffices : (⋂ (i : ι), B i) = set.univ,
    { rw this, exact top_is_block G X },
    simp only [set.top_eq_univ, set.Inter_eq_univ], 
    intro i, exfalso, apply hι.false, exact i },

  intro g, rw ← set.smul_Inter (not_is_empty_iff.mp hι),
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
  have : ∀ (i : ι) , g • (B i) = B i := λ i, or.resolve_right (hB i g) (h i),
  rw set.Inter_congr this
end

lemma is_block.of_subgroup_of_conjugate {B : set X} (H : subgroup G)
  (hB : is_block H X B) (g : G) : 
  is_block (subgroup.map (mul_equiv.to_monoid_hom (mul_aut.conj g)) H) X (g • B) :=
begin
  intro h',
  obtain ⟨h, hH, hh⟩ := subgroup.mem_map.mp (set_like.coe_mem h'), 
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply] at hh, 
  suffices : h' • g • B = g • h • B, 
  simp only [this], 
  cases hB ⟨h, hH⟩ with heq hdis,
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

def is_block_system (B : set (set X)) :=
  setoid.is_partition B ∧ (∀ (b : set X), b ∈ B → is_block G X b)

lemma is_block_system.of_block {B : set X} (hB : is_block G X B) (hBe : B.nonempty) [hGX : mul_action.is_pretransitive G X]:
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
    apply or.resolve_right (is_block' G X hB g g'), 
    rw set.not_disjoint_iff, 
    use a, exact ⟨hg, hg'⟩ },
  intro b, rintros ⟨g, hg : g • B = b⟩, 
  rw ← hg, exact is_block_of_block G X g hB,
end

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


noncomputable
lemma test2 [hfX : fintype X] (c : set (set X)) : fintype ↥c :=
begin
  have fin_ssX : fintype (set(set(X))) := set.fintype,
  apply set.finite.fintype,
  exact set.finite.of_fintype c,
end

lemma test (c : set (set X)) (hc : setoid.is_partition c) :
  ∀ (x : set X), x ∈ c → ∀ (y : set X), y ∈ c → x ≠ y → disjoint (id x) (id y) :=
begin
  refine setoid.is_partition.pairwise_disjoint hc,
end

lemma card_of_partition_eq [hfX : fintype X] {c : set (set X)} (hc : setoid.is_partition c) 
  [fintype ↥c] [Π (b : set X), fintype b] :
  ∑ b in c.to_finset, fintype.card b = fintype.card X :=
begin
  let Pc : finpartition _ :=
  { parts := c.to_finset,
    sup_indep := begin 
      intros t ht i hi hit,  
      refine setoid.is_partition.pairwise_disjoint hc _ _ _,
      simpa only [set.mem_to_finset] using hi,
      simp, 
      sorry, 
    end,
    sup_parts := sorry, 
    not_bot_mem := sorry},

  refine finpartition.sum_card_parts _,
  have hc' : ∀ (x : finset X), x ∈ c.to_finset → ∀ (y : finset X), y ∈ c.to_finset → x ≠ y → disjoint (id x) (id y),
    refine setoid.is_partition.pairwise_disjoint _,
    simp only [set.mem_to_finset_val], exact hc,
  let h1 := finset.card_bUnion hc', 
  let hc1 := setoid.is_partition.sUnion_eq_univ hc,
  rw ← finset.card_univ, 



  sorry,
end

lemma card_of_block_mul_card_of_orbit_of [hfX : fintype X] 
  (B : set X) (hB : is_block G X B) [fintype B] [fintype (orbit G B)] :
  fintype.card B * fintype.card (orbit G B) = fintype.card X :=
begin
sorry 
end


lemma card_of_block_divides [hfX : fintype X] (B : set X) (hB : is_block G X B) 
  [fintype B] :
  fintype.card B ∣ fintype.card X := 
begin
  rw ← card_of_block_mul_card_of_orbit_of G X B, 
end

/- §7. Imprimitivity -/

/-- An auxiliary lemma, variant of normal_mul' ,
with an explicit N.normal hypothesis,
so that the typeclass inference machine works.
-/

lemma normal_mul'' (N:subgroup G) (nN:N.normal) (K: subgroup G)
    (h : N ⊔ K = ⊤) (g:G) : ∃(n:N) (k:K), g = n*k :=
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
  { intro x, rw [← mul_action.mem_orbit_iff, ha, set.top_eq_univ], apply set.mem_univ, },
  intros x y, 
  obtain ⟨g, hx⟩ := this x, 
  obtain ⟨h, hy⟩ := this y,
  use h * g⁻¹,
  rw ← hx, rw [smul_smul, inv_mul_cancel_right], exact hy 
end

theorem orbit.is_block_of_normal (N : subgroup G) [nN : subgroup.normal N] (a : X) :
  is_block G X (orbit N a) :=
begin
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
    rw [smul_smul, inv_mul_cancel_right, ← smul_smul], refl, },
  rintros ⟨n, hn : n • g • a = x⟩, 
  use (g⁻¹ * n * g) • a, 
  split,
  { use g⁻¹ * n * g,  
    have this := nN.conj_mem n _ g⁻¹, 
    rw inv_inv g at this, exact this,
    apply set_like.coe_mem, 
    refl, },
  rw [← hn, smul_smul, ← mul_assoc, ← mul_assoc, mul_right_inv, one_mul,
    ← smul_smul], refl,
end

theorem is_block_system.of_normal (N : subgroup G) [nN : subgroup.normal N] :
  is_block_system G X (set.range (λ a, orbit N a)) :=
begin
  split,
    apply is_partition.of_orbits,
  intro b, rintros ⟨a, rfl⟩, 
  apply orbit.is_block_of_normal,
end


/-- An action is preprimitive is it is pretransitive and 
the only blocks are the trivial ones -/
structure is_preprimitive
extends is_pretransitive G X : Prop :=
(has_trivial_blocks : ∀ {B : set X}, (is_block G X B) →
  B = ∅ ∨ (∃ (x : X), B = {x}) ∨ B = ⊤)

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
    { exfalso, -- orbit N a = ∅
      apply set.nonempty.ne_empty (mul_action.orbit_nonempty a), 
      rw ← h, },
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
      exact hn },
    -- orbit N a = ⊤
    exact h, 
end

-- TODO : Is the assumption B.finite necessary ?
/-- The intersection of the translates of a finite subset which contain a given point
is a block -/
lemma is_block.of_subset (hGX : is_pretransitive G X) (a : X) (B : set X)
  (hfB : B.finite) (hfB' : B.nonempty) :
  is_block G X (⋂ (k : G) (hg : a ∈ k • B), k • B) :=
begin
  let hGX_exists := hGX.exists_smul_eq,

  let B' := (⋂ (k : G) (hg : a ∈ k • B), k • B),
--   change is_block G X B', 

  have hB'₀ : ∀ (k : G) (hk : a ∈ k • B), B' ≤ k • B,
  { intros k hk, apply set.bInter_subset_of_mem, exact hk },

  have hfB' : B'.finite,
  { obtain ⟨b, hb : b ∈ B⟩ := hfB', 
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
    simp only [smul_inv_smul], }, 
  
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

  apply is_block_mk,
  intros g hg, 
  rw set.ne_empty_iff_nonempty at hg,
  obtain ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩ := set.nonempty_def.mp hg,

  obtain ⟨k : G, hk : k • a = b⟩ := hGX_exists a b,

  have hak : a ∈ k⁻¹ • B', 
  { use b, apply and.intro hb, rw [← hk, inv_smul_smul], },

  have hagk : a ∈ (k⁻¹ * g) • B', 
  { rw [mul_smul, mem_smul_set_iff_inv_smul_mem, inv_inv, hk],
    exact hb' },

  have hkB' : B' = k⁻¹ • B' := hag' k⁻¹ hak, 
  have hgkB' : B' = (k⁻¹ * g) • B' := hag' (k⁻¹ * g) hagk, 
  rw mul_smul at hgkB', 
  rw ← smul_eq_iff_eq_inv_smul    at hkB' hgkB', 
  rw ← hgkB', rw hkB', 
end

/-- Theorem of Rudio (Wieland, 1964, Th. 8.1) -/
theorem rudio [hpGX : is_preprimitive G X] (A : set X) (hfA : A.finite) (hA : A.nonempty) (hA' : A ≠ ⊤)
  (a b : X) (h : a ≠ b):  ∃ (g : G), a ∈ g • A ∧ b ∉ g • A :=
begin
  let B := ⋂ (g : G) (ha : a ∈ g • A), (g • A),
  have hB : is_block G X B :=
    is_block.of_subset G X hpGX.to_is_pretransitive a A hfA hA,
  suffices : b ∉ B, 
  { rw set.mem_Inter at this,
    simpa only [set.mem_Inter, not_forall, exists_prop] using this, 
  },
  suffices : B = {a},
  { rw this, rw set.mem_singleton_iff, 
    exact ne.symm h, },
  have ha : a ∈ B, 
  { rw set.mem_Inter, intro g, simp only [set.mem_Inter, imp_self] },
  cases hpGX.has_trivial_blocks hB with hyp hyp,
  { exfalso, rw hyp at ha, rw ← set.mem_empty_eq a, exact ha },
  cases hyp with hyp hyp,
  { obtain ⟨x,hx⟩ := hyp, rw hx at ha ⊢, 
    rw set.singleton_eq_singleton_iff, 
    rw set.mem_singleton_iff at ha, exact ha.symm },

  exfalso, apply hA', 
  suffices : ∃ (g : G), a ∈ g • A, 
  { obtain ⟨g, hg⟩ := this,
    have : B ≤ g • A, 
    { rw set.le_eq_subset,
      exact set.bInter_subset_of_mem hg, },
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
  - subgroups of G containing `stabilizer G a`. -/

/-- The orbit of a under a subgroup containing the stabilizer of a
 is a block -/
lemma is_block_of_suborbit [htGX : is_pretransitive G X] {H : subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
  is_block G X (mul_action.orbit H a) :=
begin
  let hGX_exists := htGX.exists_smul_eq,
  apply is_block_mk', intros g b,
  rintro ⟨h,rfl⟩, 
  simp,  
  intro hb', 
  suffices : g ∈ H,
  { rw [← subgroup.coe_mk H g this,  ← subgroup.smul_def], 
    apply smul_orbit_subset, },
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
  cases hB g with h h', 
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
    exact is_block_def' G X hB a k ha hx },
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
 and subgroups of G containing the stabilizer of a -/
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
  apply is_block_def' G X hB' a g ha', apply hBB', rw ← hgB,
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

theorem maximal_stabilizer_iff_primitive [hnX : nontrivial X] [htGX : is_pretransitive G X] (a : X) :
  (stabilizer G a).is_maximal ↔ is_preprimitive G X :=
begin
  let htGX_exists := htGX.exists_smul_eq,
  split,
  { intro ha, 
    apply is_preprimitive.mk htGX, 
    intros B hB, 
    rw or_iff_not_imp_left, intro hB', 
    suffices this : ∃ (k : G), a ∈ k • B, 
    { obtain ⟨k, hk⟩ := this,
      have hkB : is_block G X (k • B) := is_block_of_block G X k hB,
      cases  lt_or_eq_of_le (stabilizer_of_block G X hkB hk),
      { -- k • B = ⊤
        apply or.intro_right, 
        have : stabilizer G (k • B) = ⊤,
        { rw subgroup.is_maximal_def at ha, 
          apply ha.2, exact h, },
        rw eq_top_iff, 
        intros b _,  
        suffices : k • b ∈ k • B, exact smul_mem_smul_set_iff.mp this,
        obtain ⟨h, h'⟩ := htGX_exists a b,
        have H : ∀(g : G) (x : X), x ∈ k • B → g • x ∈ k • B, 
        { intros g x hx, 
          suffices hg : g ∈ stabilizer G (k • B),
          rw mem_stabilizer_iff at hg, rw ← hg, 
          simp only [smul_mem_smul_set_iff],  exact hx, 
          rw this, simp only [subgroup.mem_top],},
        have Hb : b ∈ k • B, { rw ← h', exact H h a hk, },
        exact H k b Hb },
      -- k • B = {a}
      have : {a} = k • B, 
      { rw ← block_of_stabilizer_of_block G X (singleton_is_block G X a) (set.mem_singleton a),
        rw ← block_of_stabilizer_of_block G X hkB hk, 
        rw ← h, 
        have : stabilizer G ({a} : set X) = stabilizer G a,
        { ext, 
          simp only [mem_stabilizer_iff, set.smul_set_singleton, set.singleton_eq_singleton_iff] }, 
        rw ← this }, 
        apply or.intro_left, 
        use k⁻¹ • a, 
        ext, rw [← set.smul_set_singleton, this, inv_smul_smul] },
    obtain ⟨b, hb : b ∈ B⟩ := set.ne_empty_iff_nonempty.mp hB',
    obtain ⟨k, hk⟩ := htGX_exists b a, 
    use k, rw ← hk, simp only [smul_mem_smul_set_iff], exact hb },
  intro hGX, 
  refine {out := _},
  split, 
  { obtain ⟨b, hb⟩ := (nontrivial_iff_exists_ne a).mp hnX, 
    obtain ⟨g, rfl⟩ := htGX_exists a b, 
    suffices : g ∉ stabilizer G a,
    { intro h, apply this, rw h, exact subgroup.mem_top g, },
    rw mem_stabilizer_iff, exact hb, },
  { intros H hH, 
    rw ← stabilizer_of_block_of_stabilizer G X (le_of_lt hH), 
    suffices : orbit H a = (⊤ : set X),
    rw this, 
    rw eq_top_iff, intros g _, 
      rw mem_stabilizer_iff, 
      simp only [set.top_eq_univ, set.smul_set_univ], 
    cases hGX.has_trivial_blocks (is_block_of_suborbit G X (le_of_lt hH)), 
    { exfalso, apply set.not_mem_empty a, rw ← h, simp only [mem_orbit_self],  },
    cases h,
    { exfalso, apply not_le_of_gt hH, 
      obtain ⟨x, h⟩ := h, 
      suffices : x = a,
      { rw this at h, 
        intros g hg, rw mem_stabilizer_iff, 
        rw [← set.mem_singleton_iff, ← h],
        use ⟨g, hg⟩, refl, },
      apply symm, 
      rw [← set.mem_singleton_iff, ← h], 
      exact mul_action.mem_orbit_self a },
    exact h },
end


/- Theorem 8.4 : if the action of a subgroup H on an orbit is primitive,
   and if that orbit is small enough, then the action of G is primitive -/
theorem is_primitive_of_subgroup [hfX : fintype X] (htGX : is_pretransitive G X) 
  (H : subgroup G) (a : X) (hH : is_preprimitive H (orbit H a)) :
  let hf_orbit :=  set.finite.of_fintype (orbit H a) in 
  (2 * hf_orbit.to_finset.card > fintype.card X) → 
  is_preprimitive G X :=
  begin
    let hf_orbit := set.finite.of_fintype (orbit H a),
    simp only, 
    intro hA, 
    apply is_preprimitive.mk htGX, 
    intros B hB, 
    let hfB := set.finite.of_fintype B, 
    have : ∀ (g : G), is_block H X ((orbit H a) ∩ (g • B)), 
    { intro g, 
      apply is_block.inter H X, 
      exact is_block_of_orbit H X a,
      apply subgroup.is_block, 
      apply is_block_of_block,
      exact hB },
    cases em (∃ (g : G), (orbit H a) ≤ (g • B)) with hyp hyp,
    { obtain ⟨g,hg⟩ := hyp, 
      suffices : 2 * hfB.to_finset.card > fintype.card X,
      sorry,
      sorry,
    },
    { sorry, }
  end

lemma test (m n : ℕ) (hm : 2 * m > n) (hn : n > 0) (hmn : m ∣ n) : m  = n :=
begin
  let hkm := nat.div_mul_cancel hmn, 
  rw ← nat.div_mul_cancel hmn at hm, 
 --  suffices : n/m = 1,
 --  { rw this at hk, simpa only [one_mul] using hk, },
  --  rw mul_le_mul_iff_left at hm,
  cases nat.eq_zero_or_pos (n/m) with hk hk,
  { exfalso,
    rw [hk, zero_mul] at hkm, 
    apply gt_irrefl n,
    rw hkm at hn, exact hn, },
  cases nat.eq_or_lt_of_le hk with hk hk,
  { rw [← hkm, ← hk, one_mul], },
  exfalso,
  apply not_lt.mpr (nat.succ_le_iff.mpr hk),
  exact lt_of_mul_lt_mul_right' hm,
end


end mul_action

end FundamentalConcepts



#exit


example (hX : fintype X) (A : set X) : A.finite :=
begin
exact set.finite.of_fintype A,
end


example (A B : set X) (h : A ≤ B) (hB : B.finite) :
let hA : A.finite := set.finite.subset hB h in
hA.to_finset.card ≤ hB.to_finset.card :=
begin
  let hA := set.finite.subset hB h, 
 
  simp, 
  rw @set.finite.card_to_finset _ _ hA.fintype hA, 
  rw @set.finite.card_to_finset _ _ hB.fintype hB, 
  apply set.card_le_of_subset, 
  apply h,
end

example (hX : fintype X) (A B : set X) (h : A ≤ B)  :
let hA : set.finite A := set.finite.of_fintype A in
let hB : set.finite B := set.finite.of_fintype B in
hA.to_finset.card ≤ hB.to_finset.card :=
begin
  let hA := set.finite.of_fintype A, 
  let hB := set.finite.of_fintype B, 
  simp, 
  apply finset.card_le_of_subset, 
  rw set.finite.to_finset_mono, 
  exact h,
end

example (s t : set X) (hs : s.finite) (ht : t.finite) (hst : s ≤ t) 
(hc : hs.to_finset.card = ht.to_finset.card) :
  s = t :=
begin
  rw ← set.finite.to_finset_inj, 
  refine finset.eq_of_subset_of_card_le _ _,
    exact hs, exact ht, 
  rw set.finite.to_finset_mono, exact hst, 
  exact eq.ge hc,
end


example (B : set X) (g k : G) (hg : g • B = B) (hk : k • B = B):
  g • B ≤ k • B :=
  begin
  rw hg, rw hk, rw set.le_eq_subset, 
  end


example (H : subgroup G) (a : X) (g : G) (h : H) :
  h • g • a = (↑h * g) • a :=
  begin
    rw mul_action.mul_smul, rw subgroup.smul_def, 
  end


