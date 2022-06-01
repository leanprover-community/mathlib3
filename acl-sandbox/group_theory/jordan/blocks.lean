/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import data.setoid.partition
import group_theory.group_action.basic
import group_theory.group_action.sub_mul_action
import group_theory.subgroup.pointwise
import data.set.pointwise
import algebra.big_operators.order
import .for_mathlib.stabilizer
import .for_mathlib.pretransitive.
import .equivariant_map
import .sub_mul_action
import .for_mathlib.partitions

/-! # Blocks

Given `has_scalar G X`, an action of a group `G` on a type `X`, we define

- the predicate `is_block G B` states that `B : set X` is a block,
which means that the sets `g • B`, for `g ∈ G` form a partition of `X`.

- a bunch of lemmas that gives example of “trivial” blocks : ⊥, ⊤, singletons, orbits…

- the structure `is_preprimitive G X` that says that the action is preprimitive,
namely, the only blocks are ⊤ and subsingletons.

The definition is essentially important for `mul_action G X`.

-/

open_locale big_operators pointwise

namespace mul_action

section has_scalar

variables (G : Type*) {X : Type*} [has_scalar G X]

/-- A fixed block is an invariant subset -/
def is_fixed_block (B : set X) := ∀ (g : G), g • B = B

def is_invariant_block (B : set X) := ∀ (g : G), g • B ≤ B

/-- A block is a set which is either fixed or moved to a disjoint subset -/
def is_block (B : set X) := (set.range (λ g : G, g • B)).pairwise_disjoint id

/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
structure is_preprimitive
extends is_pretransitive G X : Prop :=
(has_trivial_blocks : ∀ {B : set X}, (is_block G B) → subsingleton B ∨  B = ⊤)

lemma is_block.def {B : set X} (hB : is_block G B) (g g' : G) :
  g • B = g' • B ∨ disjoint (g • B) (g' • B) :=
begin
  cases em (g • B = g' • B),
  refine or.intro_left _ h,
  apply or.intro_right,
  exact hB (set.mem_range_self g) (set.mem_range_self g') h,
end

end has_scalar

section group

variables (G: Type*) [group G] {X : Type*} [mul_action G X]

lemma is_block.def_one {B : set X} (hB : is_block G B) (g : G) :
  g • B = B ∨ disjoint (g • B) B :=
begin
  let h := is_block.def G hB g (1 : G),
  rw one_smul at h, exact h,
end

lemma is_block.mk {B : set X} :
  is_block G B ↔ (∀ (g : G), g • B = B ∨ disjoint (g • B) B) :=
begin
  split,
  { intros hB g, exact is_block.def_one G hB g },
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
  is_block G B ↔ ∀ (g : G), (g • B) ∩ B ≠ ∅ → g • B = B :=
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
  is_block G B ↔ ∀ (g : G) (a : X) (ha : a ∈ B) (hga : g • a ∈ B), g • B = B :=
begin
  split,
  { intros hB g a ha hga,
    cases is_block.def_one G hB g⁻¹ with h h',
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
lemma is_block.def_mem {B : set X} (hB : is_block G B) (a : X) (g : G) :
  a ∈ B → g • a ∈ B → g • B = B := (is_block.mk_mem G).mp hB g a

lemma is_block.mk_subset {B : set X} :
    is_block G B ↔ ∀ (g : G) (b : X) (hb : b ∈ B) (hb' : b ∈ g • B), g • B ≤ B :=
begin
  split,
  { intros hB g b hb hgb,
    rw [set.le_eq_subset, set_smul_subset_iff,
      is_block.def_mem G hB b g⁻¹ hb (mem_smul_set_iff_inv_smul_mem.mp hgb)] },
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
lemma subsingleton_is_block (B : set X) (hB : B.subsingleton) : is_block G B :=
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


/-- Singletons are blocks -/
lemma singleton_is_block (x : X) : is_block G ({x} : set X) :=
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
lemma is_block_of_invariant (B : set X) (hfB : is_invariant_block G B) :
  is_block G B :=
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
lemma is_block_of_fixed (B : set X) (hfB : is_fixed_block G B) :
  is_block G B :=
begin
  rw is_block.mk,
  unfold is_fixed_block at hfB,
  intro g, apply or.intro_left, exact hfB g,
end

/-- An orbit is a block -/
lemma is_block_of_orbit (a : X) : is_block G (orbit G a) :=
begin
  apply is_block_of_fixed,
  intro g, apply smul_orbit,
end

variable (X)
/-- The full set is a block -/
lemma top_is_block : is_block G (⊤ : set X) :=
begin
  apply is_block_of_fixed,
  intro g,
  simp only [set.top_eq_univ, set.smul_set_univ],
end

/-- The empty set is a block -/
lemma bot_is_block : is_block G (⊥ : set X) :=
begin
  rw is_block.mk,
  intro g, apply or.intro_left,
  simp only [set.bot_eq_empty, set.smul_set_empty],
end

variable {X}
/-- Is B is a block for an action G, it is a block for the action of any subgroup of G -/
lemma subgroup.is_block {H : subgroup G} {B : set X} (hfB : is_block G B) :
  is_block H B :=
begin
  rw is_block.mk, intro h,
  simpa only using is_block.def_one G hfB h
end

lemma is_block_preimage {H Y: Type*} [group H] [mul_action H Y]
  {φ : H →* G} {j : Y →ₑ[φ] X}
  {B : set X} (hB : is_block G B) :
  is_block H (j ⁻¹' B) :=
begin
  rw is_block.mk,
  intro g,
  cases is_block.def_one G hB (φ g) with heq hdis,
  { apply or.intro_left,
    rw [← equivariant_map.preimage_smul_setₑ, heq] },
  { apply or.intro_right,
    rw ← equivariant_map.preimage_smul_setₑ,
    apply set.disjoint_preimage, exact hdis }
end

lemma sub_mul_action.is_block {C : sub_mul_action G X} {B : set X}
  (hB : is_block G B) : is_block G (coe ⁻¹' B : set C) :=
begin
  rw ← sub_mul_action.inclusion.to_fun_eq_coe,
  change is_block G (C.inclusion ⁻¹' B),
  exact @is_block_preimage G _ X _ G C _ _ (monoid_hom.id G) C.inclusion B hB
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
  is_block G B ↔ is_block G (coe '' B : set X) :=
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
  is_block G B ↔ is_block (⊤ : subgroup G) B :=
begin
  simp only [is_block.mk],
  split,
  intros h g, exact h g,
  intros h g, exact h ⟨g, subgroup.mem_top g⟩
end

lemma orbit.equal_or_disjoint (a b : X) :
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
lemma is_block.inter {B₁ B₂ : set X} (h₁ : is_block G B₁) (h₂ : is_block G B₂) :
  is_block G (B₁ ∩ B₂) :=
begin
  rw is_block.mk,
  intro g,
  rw set.smul_set_inter,
  cases is_block.def_one G h₁ g with h₁ h₁, -- em (disjoint (g • B₁) B₁) with h h,
  { cases is_block.def_one G h₂ g with h₂ h₂,
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
  is_block G (B i)) : is_block G (⋂ i, B i) :=
begin
  rw is_block.mk,
  cases em (is_empty ι) with hι hι,
  { -- ι = ∅, block = ⊤
    suffices : (⋂ (i : ι), B i) = set.univ,
    { rw this, exact is_block.def_one G (top_is_block G X) },
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
  have : ∀ (i : ι) , g • (B i) = B i := λ i, or.resolve_right (is_block.def_one G (hB i) g) (h i),
  rw set.Inter_congr this
end

lemma is_block.of_subgroup_of_conjugate {B : set X} {H : subgroup G}
  (hB : is_block H B) (g : G) :
  is_block (subgroup.map (mul_equiv.to_monoid_hom (mul_aut.conj g)) H) (g • B) :=
begin
  rw is_block.mk,
  intro h',
  obtain ⟨h, hH, hh⟩ := subgroup.mem_map.mp (set_like.coe_mem h'),
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply] at hh,
  suffices : h' • g • B = g • h • B,
  simp only [this],
  cases is_block.def_one H hB ⟨h, hH⟩ with heq hdis,
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
lemma is_block_of_block {B : set X} (g : G) (hB : is_block G B) :
  is_block G (g • B) :=
begin
  rw is_block.of_top_iff at hB ⊢,
  suffices : subgroup.map (mul_equiv.to_monoid_hom (mul_aut.conj g)) ⊤ = ⊤,
  rw ← this,
  refine is_block.of_subgroup_of_conjugate G hB g,
  suffices : ⊤ = subgroup.comap (mul_equiv.to_monoid_hom (mul_aut.conj g)) ⊤,
  { rw this,
    refine subgroup.map_comap_eq_self_of_surjective _ _,
    exact mul_equiv.surjective (mul_aut.conj g),  },
  rw subgroup.comap_top
end

/-- A block_system of X is a partition of X into blocks -/
def is_block_system (B : set (set X)) :=
  setoid.is_partition B ∧ (∀ (b : set X), b ∈ B → is_block G b)

/-- Translates of a block form a `block_system` -/
lemma is_block_system.of_block (hGX : mul_action.is_pretransitive G X)
  {B : set X} (hB : is_block G B) (hBe : B.nonempty) :
  is_block_system G (set.range (λ (g : G), g • B)) :=
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
    apply or.resolve_right (is_block.def G hB g g'),
    rw set.not_disjoint_iff,
    use a, exact ⟨hg, hg'⟩ },
  intro b, rintros ⟨g, hg : g • B = b⟩,
  rw ← hg, exact is_block_of_block G g hB,
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
  { simp only [set.mem_range_self, mem_orbit_self, exists_unique_iff_exists, exists_true_left] },
  { simp only [set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff'],
    intros b hb,
    rw orbit_eq_iff,
    obtain ⟨g, rfl⟩ := mul_action.mem_orbit_iff.mp hb,
    use g⁻¹, simp only [inv_smul_smul] }
end


open_locale classical pointwise

theorem orbit.is_block_of_normal (N : subgroup G) [nN : subgroup.normal N] (a : X) :
  is_block G (orbit N a) :=
begin
  rw is_block.mk,
  intro g,
  suffices : g • (orbit N a) = orbit N (g • a),
  { rw this, apply orbit.equal_or_disjoint },

  change (λ x : X, g • x) '' set.range (λ (k : N), k • a)
    = set.range (λ (k : N), k • (g • a)),
  simp only [set.image_smul],
  rw set.smul_set_range ,
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
  is_block_system G (set.range (λ a : X, orbit N a)) :=
begin
  split,
  { apply is_partition.of_orbits },
  { intro b, rintros ⟨a, rfl⟩,
    apply orbit.is_block_of_normal },
end


section finite

lemma card_of_block_mul_card_of_orbit_of [hfX : fintype X] (hGX : is_pretransitive G X)
  {B : set X} (hB : is_block G B) (hB_ne : B.nonempty) :
  (set.range (λ (g : G), g • B)).to_finset.card * fintype.card B = fintype.card X :=
begin
  rw setoid.is_partition.card_eq_sum_parts (is_block_system.of_block G hGX hB hB_ne).left,
  rw [finset.sum_congr rfl _, finset.sum_const (fintype.card ↥B), nsmul_eq_mul, nat.cast_id],
  intros s hs,
  simp only [set.mem_to_finset, set.mem_range] at hs,
  obtain ⟨g, rfl⟩ := hs,
  simp only [← set.to_finset_card],
  rw ← finset.card_image_of_injective B.to_finset (mul_action.injective g),
  refine congr_arg _ _,
  simp only [← finset.coe_inj, set.coe_to_finset, finset.coe_image, set.image_smul],
end

lemma card_of_block_divides [hfX : fintype X] (hGX : is_pretransitive G X)
  {B : set X} (hB : is_block G B) (hB_ne : B.nonempty) :
  fintype.card B ∣ fintype.card X :=
begin
  rw ← card_of_block_mul_card_of_orbit_of G hGX hB hB_ne,
  simp only [dvd_mul_left],
end

-- TODO : Is the assumption B.finite necessary ?
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3 )-/
lemma is_block.of_subset (hGX : is_pretransitive G X) (a : X) (B : set X) (hfB : B.finite) :
  is_block G (⋂ (k : G) (hg : a ∈ k • B), k • B) :=
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

end finite

end group

end mul_action
