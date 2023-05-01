/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import .for_mathlib.stabilizer
import .for_mathlib.pretransitive
import .for_mathlib.partitions
import .for_mathlib.set
-- import data.setoid.partition
import .equivariant_map
import .sub_mul_actions
import .maximal_subgroups

-- import group_theory.group_action.basic
-- import group_theory.group_action.sub_mul_action
-- import group_theory.subgroup.pointwise
-- import data.set.pointwise
-- import data.nat.prime
-- import algebra.big_operators.order


/-! # Blocks

Given `has_smul G X`, an action of a group `G` on a type `X`, we define

- the predicate `is_block G B` states that `B : set X` is a block,
which means that the sets `g • B`, for `g ∈ G` form a partition of `X`.

- a bunch of lemmas that gives example of “trivial” blocks : ⊥, ⊤, singletons, orbits…

-/

open_locale big_operators pointwise

namespace mul_action

section has_smul

variables (G : Type*) {X : Type*} [has_smul G X]

-- Change terminology : is_fully_invariant ?
/-- A fixed block is a fully invariant subset -/
def is_fixed_block (B : set X) := ∀ (g : G), g • B = B

/-- An invariant block is a set which is stable under has_smul -/
def is_invariant_block (B : set X) := ∀ (g : G), g • B ≤ B

/-- A trivial block is a subsingleton or ⊤ (it is not necessarily a block…)-/
def is_trivial_block (B : set X) := B.subsingleton ∨ B = ⊤

/-- A block is a set which is either fixed or moved to a disjoint subset -/
def is_block (B : set X) := (set.range (λ g : G, g • B)).pairwise_disjoint id

variables {G X}

/-- A set B is a block iff for all g, g',
the sets g • B and g' • B are either equal or disjoint -/
lemma is_block.def {B : set X} :
  is_block G B ↔ ∀ (g g' : G),
  g • B = g' • B ∨ disjoint (g • B) (g' • B) :=
begin
  split,
  { intros hB g g',
    cases em (g • B = g' • B),
    refine or.intro_left _ h,
    apply or.intro_right,
    exact hB (set.mem_range_self g) (set.mem_range_self g') h },
  { intro hB,
    unfold is_block,
    intros C hC C' hC',
    obtain ⟨g, rfl⟩ := hC,
    obtain ⟨g', rfl⟩ := hC',
    intro hgg',
    cases hB g g',
    { exfalso, exact hgg' h},
    exact h },
end

/-- Alternate definition of a block -/
lemma is_block.mk_notempty {B : set X}  :
  is_block G B ↔ ∀ (g g' : G), (g • B) ∩ (g' • B) ≠ ∅ → g • B = g' • B :=
begin
  rw is_block.def,
  apply forall_congr, intro g,
  apply forall_congr, intro g',
  rw set.disjoint_iff_inter_eq_empty,
  exact or_iff_not_imp_right,
end

/-- A fixed block is a block -/
lemma is_block_of_fixed {B : set X} (hfB : is_fixed_block G B) :
  is_block G B :=
begin
  rw is_block.def,
  intros g g',
  apply or.intro_left,
  rw [hfB g, hfB g']
end

variable (X)
/-- The empty set is a block -/
lemma bot_is_block : is_block G (⊥ : set X) :=
begin
  rw is_block.def,
  intros g g', apply or.intro_left,
  simp only [set.bot_eq_empty, set.smul_set_empty]
end

/-- Singletons are (trivial) blocks -/
variable {X}
lemma singleton_is_block (a : X) : is_block G ({a} : set X) :=
begin
  rw is_block.def,
  intros g g',
  simp only [set.smul_set_singleton, set.singleton_eq_singleton_iff,
    set.disjoint_singleton, ne.def],
  apply em,
end

/-- Subsingletons are (trivial) blocks -/
lemma subsingleton_is_block {B : set X} (hB : B.subsingleton) : is_block G B :=
begin
  cases set.subsingleton.eq_empty_or_singleton hB,
  { rw h, apply bot_is_block },
  { obtain ⟨a, ha⟩ := h, rw ha, apply singleton_is_block }
end

end has_smul

section group

variables {G: Type*} [group G] {X : Type*} [mul_action G X]

lemma is_block.def_one {B : set X} :
  is_block G B ↔ ∀ (g : G), g • B = B ∨ disjoint (g • B) B :=
begin
  rw is_block.def, split,
  { intros hB g,
    simpa only [one_smul] using hB g 1 },
  { intros hB,
    intros g g',
    cases hB (g'⁻¹ * g),
    { apply or.intro_left,
      rw [← inv_inv g', eq_inv_smul_iff, smul_smul],
      exact h },
    { apply or.intro_right,
      rw set.disjoint_iff at h ⊢,
      rintros x ⟨hx, hx'⟩,
      simp only [set.mem_empty_iff_false],
      suffices : (g'⁻¹ • x) ∈ (g'⁻¹ * g) • B ⊓ B,
      apply h this,
      simp only [set.inf_eq_inter, set.mem_inter_iff],
      simp only [← set.mem_smul_set_iff_inv_smul_mem],
      rw ← smul_smul, rw smul_inv_smul,
      exact ⟨hx, hx'⟩ } }
end

lemma is_block.mk_notempty_one {B : set X}  :
  is_block G B ↔ ∀ (g : G), (g • B) ∩ B ≠ ∅ → g • B = B :=
begin
  rw is_block.def_one,
  apply forall_congr,
  intro g,
  rw set.disjoint_iff_inter_eq_empty,
  exact or_iff_not_imp_right,
end

example(s : set X) : s ≠ ∅ ↔   s.nonempty := begin
exact set.nonempty_iff_ne_empty.symm,
end

example (p q r : Prop) : p → q → r ↔ q → p → r :=
imp.swap


lemma is_block.mk_mem {B : set X} :
  is_block G B ↔ ∀ (g : G) (a : X) (ha : a ∈ B) (hga : g • a ∈ B), g • B = B :=
begin
  rw is_block.mk_notempty_one,
  simp_rw [← set.nonempty_iff_ne_empty, set.nonempty_def],
  simp_rw [set.mem_inter_iff],
  simp_rw exists_imp_distrib,
  simp_rw [and_imp],
  simp_rw [set.mem_smul_set_iff_inv_smul_mem],
  simp_rw imp.swap,
  split,
  { intros H g a ha hga,
    rw ← eq_inv_smul_iff, apply symm,
    refine H g⁻¹ a ha _, rw inv_inv, exact hga, },
  { intros H g a ha hga,
    rw ← eq_inv_smul_iff, apply symm,
    exact H g⁻¹ a ha hga, },
end

-- was : is_block_def'
lemma is_block.def_mem {B : set X} (hB : is_block G B) (a : X) (g : G) :
  a ∈ B → g • a ∈ B → g • B = B := is_block.mk_mem.mp hB g a

lemma is_block.mk_subset {B : set X} :
    is_block G B ↔ ∀ (g : G) (b : X) (hb : b ∈ B) (hb' : b ∈ g • B), g • B ≤ B :=
begin
  split,
  { intros hB g b hb hgb,
    rw [set.le_eq_subset, set.set_smul_subset_iff,
      is_block.def_mem hB b g⁻¹ hb (set.mem_smul_set_iff_inv_smul_mem.mp hgb)] },
  { rw is_block.mk_notempty_one,
    intros hB g hg,
    rw ← set.nonempty_iff_ne_empty at hg,
    obtain ⟨b : X, hb' : b ∈ g • B, hb : b ∈ B⟩ := set.nonempty_def.mp hg,
    apply le_antisymm,
    { exact hB g b hb hb' },
    suffices : g⁻¹ • B ≤ B,
    { rw set.le_eq_subset at this ⊢,
      rw [← inv_inv g, ← set.set_smul_subset_iff], exact this },
    exact hB g⁻¹ (g⁻¹ • b)
      (set.mem_smul_set_iff_inv_smul_mem.mp hb') (set.smul_mem_smul_set_iff.mpr hb) }
end

/-- An invariant block is a block -/
lemma is_block_of_invariant (B : set X) (hfB : is_invariant_block G B) :
  is_block G B :=
begin
  rw is_block.def_one,
  intro g, apply or.intro_left,
  apply le_antisymm,
  exact hfB g,
  { intros x hx,
    rw set.mem_smul_set_iff_inv_smul_mem,
    apply hfB g⁻¹,
    rw set.smul_mem_smul_set_iff, exact hx },
end

/-- An orbit is a block -/
lemma is_block_of_orbit (a : X) : is_block G (orbit G a) :=
begin
  apply is_block_of_fixed,
  intro g, apply smul_orbit,
end

variable (X)
/-- The full set is a (trivial) block -/
lemma top_is_block : is_block G (⊤ : set X) :=
begin
  apply is_block_of_fixed,
  intro g,
  simp only [set.top_eq_univ, set.smul_set_univ],
end

variables {G X}
/-- Is B is a block for an action G, it is a block for the action of any subgroup of G -/
lemma subgroup.is_block {H : subgroup G} {B : set X} (hfB : is_block G B) :
  is_block H B :=
begin
  rw is_block.def_one, rintro ⟨g, hg⟩,
  simpa only using is_block.def_one.mp hfB g
end

lemma is_block_preimage {H Y: Type*} [group H] [mul_action H Y]
  {φ : H → G} (j : Y →ₑ[φ] X)
  {B : set X} (hB : is_block G B) :
  is_block H (j ⁻¹' B) :=
begin
  rw is_block.def_one,
  intro g,
  cases is_block.def_one.mp hB (φ g) with heq hdis,
  { apply or.intro_left,
    rw [← equivariant_map.preimage_smul_setₑ, heq] },
  { apply or.intro_right,
    rw ← equivariant_map.preimage_smul_setₑ,
    apply disjoint.preimage, exact hdis, }
end

lemma is_block_image {H Y: Type*} [group H] [mul_action H Y]
  {φ : G → H}  (j : X →ₑ[φ] Y)
  (hφ : function.surjective φ) (hj : function.injective j)
  {B : set X} (hB : is_block G B) :
  is_block H (j '' B) :=
begin
  rw is_block.def,
  intros h h',
  obtain ⟨g, rfl⟩ := hφ h,
  obtain ⟨g', rfl⟩ := hφ h',
  simp only [← equivariant_map.image_smul_setₑ],
  cases is_block.def.mp hB g g' with h h,
  { apply or.intro_left, rw h },
  { apply or.intro_right,
    exact set.disjoint_image_of_injective hj h }
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
  simp only [is_block.def_one],
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
  simp only [is_block.def_one],
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
  rw is_block.def_one,
  intro g,
  rw set.smul_set_inter,
  cases is_block.def_one.mp h₁ g with h₁ h₁, -- em (disjoint (g • B₁) B₁) with h h,
  { cases is_block.def_one.mp h₂ g with h₂ h₂,
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
  rw is_block.def_one,
  cases em (is_empty ι) with hι hι,
  { -- ι = ∅, block = ⊤
    suffices : (⋂ (i : ι), B i) = set.univ,
    { rw this, exact is_block.def_one.mp (top_is_block X) },
    simp only [set.top_eq_univ, set.Inter_eq_univ],
    intro i, exfalso, apply hι.false, exact i },

  intro g, rw smul_set_Inter,
  cases em (∃ (i : ι), disjoint (g • (B i)) (B i)) with h h,
  { obtain ⟨j,hj⟩ := h,
    apply or.intro_right,
      -- rw set.smul_Inter h,
    refine disjoint.mono _ _ hj ,
    apply set.Inter_subset ,
    apply set.Inter_subset },
  simp only [not_exists] at h,
  apply or.intro_left,
  have : ∀ (i : ι) , g • (B i) = B i := λ i, or.resolve_right (is_block.def_one.mp (hB i) g) (h i),
  rw set.Inter_congr this
end

lemma is_block.of_subgroup_of_conjugate {B : set X} {H : subgroup G}
  (hB : is_block H B) (g : G) :
  is_block (subgroup.map (mul_equiv.to_monoid_hom (mul_aut.conj g)) H) (g • B) :=
begin
  rw is_block.def_one,
  intro h',
  obtain ⟨h, hH, hh⟩ := subgroup.mem_map.mp (set_like.coe_mem h'),
  simp only [mul_equiv.coe_to_monoid_hom, mul_aut.conj_apply] at hh,
  suffices : h' • g • B = g • h • B,
  simp only [this],
  cases is_block.def_one.mp hB ⟨h, hH⟩ with heq hdis,
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
  refine is_block.of_subgroup_of_conjugate hB g,
  suffices : ⊤ = subgroup.comap (mul_equiv.to_monoid_hom (mul_aut.conj g)) ⊤,
  { rw this,
    refine subgroup.map_comap_eq_self_of_surjective _ _,
    exact mul_equiv.surjective (mul_aut.conj g),  },
  rw subgroup.comap_top
end

variable (G)
/-- A block_system of X is a partition of X into blocks -/
def is_block_system (B : set (set X)) :=
  setoid.is_partition B ∧ (∀ (b : set X), b ∈ B → is_block G b)

variable {G}
-- The following proof is absurdly complicated !
/-- Translates of a block form a `block_system` -/
lemma is_block_system.of_block [hGX : mul_action.is_pretransitive G X]
  {B : set X} (hB : is_block G B) (hBe : B.nonempty) :
  is_block_system G (set.range (λ (g : G), g • B)) :=
begin
  split,
  split,
  { simp only [set.mem_range, not_exists],
    intros x hx, apply set.nonempty.ne_empty hBe,
    rw ← set.image_eq_empty,
    exact hx },
  { intro a,
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe,
    obtain ⟨g, hab⟩ := exists_smul_eq G b a,
    have hg : a ∈ g • B,
    { change a ∈ (λ b, g • b) '' B,
      rw set.mem_image, use b, exact ⟨hb, hab⟩ },
    use (g • B),
    split,
    { simp only [set.mem_range, exists_apply_eq_apply, exists_unique_iff_exists, exists_true_left],
      exact hg },
    { simp only [set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index, forall_apply_eq_imp_iff'],
      intros g' hg',
      apply symm,
      apply or.resolve_right (is_block.def.mp hB g g'),
      rw set.not_disjoint_iff,
      use a, exact ⟨hg, hg'⟩ } },
  intro b, rintros ⟨g, hg : g • B = b⟩,
  rw ← hg, exact is_block_of_block g hB,
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

section normal

/-- An orbit of a normal subgroup is a block -/
theorem orbit.is_block_of_normal {N : subgroup G} (nN : subgroup.normal N) (a : X) :
  is_block G (orbit N a) :=
begin
  rw is_block.def_one,
  intro g,
  suffices : g • (orbit N a) = orbit N (g • a),
  { rw this, apply orbit.equal_or_disjoint },

  change (λ x : X, g • x) '' set.range (λ (k : N), k • a)
    = set.range (λ (k : N), k • (g • a)),
  simp only [set.image_smul, set.smul_set_range],
  ext,
  simp only [set.mem_range],
  split,
  { rintro ⟨⟨k, hk⟩, rfl⟩,
    use g * k * g⁻¹,
    apply nN.conj_mem, exact hk,
    change (g * k * g⁻¹) • g • a = g • k • a,
    rw [smul_smul, inv_mul_cancel_right, ← smul_smul] },
  { rintro ⟨⟨k, hk⟩, rfl⟩,
    use g⁻¹ * k * g⁻¹⁻¹,
    apply nN.conj_mem, exact hk,
    change g • (g⁻¹ * k * g⁻¹⁻¹) • a = k • g • a,
    simp only [← mul_assoc, ← smul_smul, smul_inv_smul, inv_inv] }
end

/-- The orbits of a normal subgroup form a block system -/
theorem is_block_system.of_normal {N : subgroup G} (nN : subgroup.normal N) :
  is_block_system G (set.range (λ a : X, orbit N a)) :=
begin
  split,
  { apply is_partition.of_orbits },
  { intro b, rintros ⟨a, rfl⟩,
    exact orbit.is_block_of_normal nN a},
end

end normal

section stabilizer

/- For transitive actions, construction of the lattice equivalence
  `stabilizer_block_equiv` between
  - blocks of `mul_action G X` containing a point a ∈ X,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of a under a subgroup containing the stabilizer of a
 is a block -/
lemma is_block_of_suborbit {H : subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
  is_block G (mul_action.orbit H a) :=
begin
  rw is_block.mk_subset, intros g b,
  rintro ⟨h,rfl⟩,
  simp,
  intro hb',
  suffices : g ∈ H,
  { rw [← subgroup.coe_mk H g this,  ← subgroup.smul_def],
    apply smul_orbit_subset },
  rw [set.mem_smul_set_iff_inv_smul_mem, subgroup.smul_def, ← mul_action.mul_smul] at hb',
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
lemma stabilizer_of_block {B : set X} (hB : is_block G B) {a : X} (ha : a ∈ B) :
  stabilizer G a ≤ stabilizer G B :=
begin
  intros g hg,
  rw mem_stabilizer_iff at hg ⊢,
  cases is_block.def_one.mp hB g with h h',
  exact h,
  exfalso, rw ← set.mem_empty_iff_false a,
  rw [disjoint_iff, set.inf_eq_inter, set.bot_eq_empty] at h',
  rw [← h', set.mem_inter_iff],
  split,
  rw ← hg, rw set.smul_mem_smul_set_iff, exact ha,
  exact ha
end

/-- A block is the orbit of a under its stabilizer -/
lemma block_of_stabilizer_of_block  [htGX : is_pretransitive G X]
  {B : set X} (hB : is_block G B) {a : X} (ha : a ∈ B) :
  mul_action.orbit (stabilizer G B) a = B :=
begin
  ext, split,
  { -- rw mul_action.mem_orbit_iff, intro h,
    rintro ⟨k, rfl⟩,
    let z := mem_stabilizer_iff.mp (set_like.coe_mem k),
    rw ← subgroup.smul_def at z,
    let zk : k • a ∈ k • B := set.smul_mem_smul_set_iff.mpr ha,
    rw z at zk, exact zk },
  intro hx,
  obtain ⟨k, rfl⟩ := exists_smul_eq G a x,
  use k,
  { rw mem_stabilizer_iff,
    exact is_block.def_mem hB a k ha hx },
  refl,
end

/-- A subgroup containing the stabilizer of a is the stabilizer of the orbit of a under that subgroup -/
lemma stabilizer_of_block_of_stabilizer
  {a : X} {H : subgroup G} (hH : stabilizer G a ≤ H) :
  stabilizer G (orbit H a) = H :=
begin
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
    simp only [set.smul_mem_smul_set_iff, mem_orbit_self] },
  intro hg,
  rw mem_stabilizer_iff,
  rw [← subgroup.coe_mk H g hg,  ← subgroup.smul_def],
  apply smul_orbit,
end

variable (G)
/-- Order equivalence between blocks in X containing a point a
 and subgroups of G containing the stabilizer of a (Wielandt, th. 7.5)-/
def stabilizer_block_equiv [htGX : is_pretransitive G X] (a : X) :
  { B : set X // a ∈ B ∧ is_block G B } ≃o set.Ici (stabilizer G a) := {
to_fun := λ ⟨B, ha, hB⟩, ⟨stabilizer G B, stabilizer_of_block hB ha⟩,
inv_fun := λ ⟨H, hH⟩, ⟨mul_action.orbit H a,
mul_action.mem_orbit_self a, is_block_of_suborbit hH⟩,
left_inv := λ ⟨B, ha, hB⟩,
  (id (propext subtype.mk_eq_mk)).mpr (block_of_stabilizer_of_block hB ha),
right_inv := λ ⟨H, hH⟩,
  (id (propext subtype.mk_eq_mk)).mpr (stabilizer_of_block_of_stabilizer hH),
map_rel_iff' :=
begin
rintro ⟨B, ha, hB⟩, rintro ⟨B', ha', hB'⟩,
simp only [equiv.coe_fn_mk, subtype.mk_le_mk, set.le_eq_subset],
split,
{ intro hBB',
  rw ← block_of_stabilizer_of_block hB ha,
  rw ← block_of_stabilizer_of_block hB' ha',
  intro x, rintro ⟨k, rfl⟩, use k, apply hBB', exact set_like.coe_mem k,
  refl },
{ intro hBB',
  intro g,
  change g ∈ stabilizer G B → g ∈ stabilizer G B',
  simp only [mem_stabilizer_iff],
  intro hgB,
  apply is_block.def_mem hB' a g ha',
  apply hBB',
  rw ← hgB,
  simp_rw [set.smul_mem_smul_set_iff], exact ha },
end }

end stabilizer


section finite

open_locale classical

/-- The cardinality of the ambient is the product of
  of the cardinality of a block
  by the cardinality of the set of iterates of that block -/
lemma card_of_block_mul_card_of_orbit_of [hfX : fintype X] [hGX : is_pretransitive G X]
  {B : set X} (hB : is_block G B) (hB_ne : B.nonempty) :
  fintype.card B * fintype.card (set.range (λ (g : G), g • B)) = fintype.card X :=
begin
  rw setoid.is_partition.card_eq_sum_parts (is_block_system.of_block hB hB_ne).left,
  rw [finset.sum_congr rfl _, finset.sum_const (fintype.card ↥B),
    nsmul_eq_mul, nat.cast_id, mul_comm],
  { rw ← set.to_finset_card },
  { intros s hs,
    simp only [set.mem_to_finset, set.mem_range] at hs,
    obtain ⟨g, rfl⟩ := hs,
    simp only [set.to_finset_card],
    { refine eq.trans _ (eq.trans (smul_set_card_eq g B) _),
      all_goals { apply fintype.card_congr', refl } } }
end

/-- The cardinality of a block divides the cardinality of the ambient type -/
lemma card_of_block_divides [hfX : fintype X] [hGX : is_pretransitive G X]
  {B : set X} (hB : is_block G B) (hB_ne : B.nonempty) :
  fintype.card B ∣ fintype.card X :=
begin
  rw ← card_of_block_mul_card_of_orbit_of hB hB_ne,
  simp only [dvd_mul_right],
end

/-- A too large block is equal to ⊤ -/
lemma is_top_of_large_block [hfX : fintype X] [hGX : is_pretransitive G X]
  {B : set X} (hB : is_block G B) (hB' : fintype.card X < 2 * fintype.card B) :
  B = ⊤ :=
begin
  cases nat.eq_zero_or_pos (fintype.card B),
  { exfalso, rw h at hB', simpa using hB', },
  rw [set.top_eq_univ, ← set.to_finset_inj, set.to_finset_univ,
    ← finset.card_eq_iff_eq_univ, set.to_finset_card],
  have : B.nonempty,
  { rw [← set.nonempty_coe_sort, ← fintype.card_pos_iff],
    exact h },
  obtain ⟨k, h⟩ := card_of_block_divides hB this,
  cases nat.lt_or_ge k 2 with hk hk,
  rw nat.lt_succ_iff at hk,
  cases lt_or_eq_of_le hk with hk hk,
  { simp only [nat.lt_one_iff] at hk,
    rw [hk, mul_zero] at h,
    apply le_antisymm (set_fintype_card_le_univ B),
    rw h, apply nat.zero_le },
  { rw [hk, mul_one] at h, exact h.symm, },
  { exfalso,
    rw [lt_iff_not_ge] at hB', apply hB',
    rw [mul_comm, h],
    refine nat.mul_le_mul_left _ hk }
end

/-- If a block has too much translates, it is a singleton  -/
lemma is_top_of_small_block [hfX : fintype X] [hGX : is_pretransitive G X]
  {B : set X} (hB : is_block G B)
  (hX : nontrivial X)
  (hB' :  fintype.card X < 2 * fintype.card (set.range (λ g : G, (g • B : set X)))) :
  B.subsingleton :=
begin
  rw [← set.subsingleton_coe, ← fintype.card_le_one_iff_subsingleton],
  cases set.eq_empty_or_nonempty B,
  { exfalso,
    rw ← fintype.one_lt_card_iff_nontrivial at hX,
    rw lt_iff_not_le at hX,
    apply hX, rw ← nat.lt_succ_iff,
    rw ← mul_one (1 : ℕ).succ,
    apply lt_of_lt_of_le hB',
    apply mul_le_mul_left',
    rw fintype.card_le_one_iff ,
    have : ∀ (x : set.range (λ (g : G), g • B)), ↑x = (∅ : set X),
    { rintro ⟨x, hx⟩,
      simp_rw [h, set.smul_set_empty] at hx,
      simp only [subtype.coe_mk],
      apply set.range_const_subset hx },
    intros s t, rw ← subtype.coe_inj,
    simp only [this] },
  let hk := card_of_block_mul_card_of_orbit_of hB h,
  cases nat.lt_or_ge (fintype.card B) 2 with hb hb,
  rwa nat.lt_succ_iff at hb,
  exfalso,
  rw [← hk, lt_iff_not_ge] at hB', apply hB',
  refine nat.mul_le_mul_right _ hb
end

-- TODO : Is the assumption B.finite necessary ?
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3 )-/
lemma is_block.of_subset [hGX : is_pretransitive G X] (a : X) (B : set X) (hfB : B.finite) :
  is_block G (⋂ (k : G) (hg : a ∈ k • B), k • B) :=
begin
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
    obtain ⟨k, hk : k • b = a⟩ := exists_smul_eq G b a,
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
      rw [← set.mem_smul_set_iff_inv_smul_mem ,  smul_smul],
      apply hB'₀, --  x hx,
      rw [← smul_smul, set.mem_smul_set_iff_inv_smul_mem],
      apply hB'₀ k hk, -- (g⁻¹ • a) (),
      exact set.mem_smul_set_iff_inv_smul_mem.mp hg,
      exact hx },
    simp only [smul_inv_smul] },

  have hag' : ∀ (g : G), a ∈ g • B' → B' = g • B',
  { intros g hg,
    rw ← set.finite.to_finset_inj,
    refine finset.eq_of_subset_of_card_le _ _,
    exact hfB', apply set.finite.map, exact hfB',

    rw set.finite.to_finset_subset,
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

  rw is_block.mk_notempty_one,
  intros g hg,
  rw ← set.nonempty_iff_ne_empty at hg,
  obtain ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩ := set.nonempty_def.mp hg,
  obtain ⟨k : G, hk : k • a = b⟩ := exists_smul_eq G a b,
  have hak : a ∈ k⁻¹ • B',
  { use b, apply and.intro hb, rw [← hk, inv_smul_smul] },
  have hagk : a ∈ (k⁻¹ * g) • B',
  { rw [mul_smul, set.mem_smul_set_iff_inv_smul_mem, inv_inv, hk],
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


#lint
