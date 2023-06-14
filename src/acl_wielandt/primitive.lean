/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/



import .for_mathlib.stabilizer
import .for_mathlib.pretransitive
import .for_mathlib.set
import .equivariant_map
import .sub_mul_actions
import .for_mathlib.partitions
import .maximal_subgroups
import .for_mathlib.commutators
import .blocks

import data.setoid.partition
import group_theory.group_action.basic
import group_theory.group_action.sub_mul_action
import group_theory.subgroup.pointwise

import group_theory.abelianization
import group_theory.commutator
import group_theory.quotient_group

import data.set.pointwise.basic
import data.nat.prime
import data.fintype.basic
import data.fintype.card

import algebra.big_operators.order



/-!
# Primitive actions and the Iwasawa criterion

## Definitions

- `is_preprimitive G X`
a structure that says that the action of a type `G`
on a type `X` (defined by an instance `has_smul G X`) is *preprimitive*,
namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
(The pretransitivity assumption is essentially trivial, because orbits are blocks,
unless the action itself is trivial.)

The notion which is introduced in classical books on group theory
is restricted to `mul_action` of groups.
In fact, it may be irrelevant if the action is degenerate,
when “trivial blocks” might not be blocks.
Moreover, the classical notion is *primitive*,
which assumes moreover that `X` is not empty.

- `is_quasipreprimitive G X`
a structure that says that the `mul_action`
of the group `G` on the type `X` is *quasipreprimitive*,
namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity under equivariant maps, for images and preimages.

## Relation with stabilizers

- `is_preprimitive_of_block_order`
relates primitivity and the fact that the inclusion
order on blocks containing is simple.

- `maximal_stabilizer_iff_preprimitive`
an action is preprimitive iff the stabilizers of points are maximal subgroups.

## Relation with normal subgroups

- `is_preprimitive.is_quasipreprimitive`
preprimitive actions are quasipreprimitive

## Particular results for actions on finite types

- `is_preprimitive_of_prime` :
a pretransitive action on a finite type of prime cardinal is preprimitive

- `is_preprimitive_of_large_image`
Given an equivariant map from a preprimitive action,
if the image is at least twice the codomain, then the codomain is preprimitive

- `rudio`
Theorem of Rudio :
Given a preprimitive action of a group `G` on `X`, a finite `A : set X`
and two points, find a translate of `A` that contains one of them
and not the other one.
The proof relies on `is_block.of_subset` that itself requires finiteness of `A`,
but I don't know whether the theorem does…

## Iwasawa criterion

- `iwasawa_structure`
the structure underlying the Iwasawa criterion for simplicity

- `commutator_le_iwasawa` and `is_simple_iwasawa`
give two versions of that Iwasawa criterion

-/
open mul_action

section primitive

variables (G : Type*) (X : Type*)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
class is_preprimitive [has_smul G X]
extends is_pretransitive G X : Prop :=
(has_trivial_blocks' : ∀ {B : set X}, (is_block G B) → is_trivial_block B)

/-- A `mul_action` of a group is quasipreprimitive if any normal subgroup that has no fixed point acts pretransitively -/
class is_quasipreprimitive [group G] [mul_action G X]
extends is_pretransitive G X : Prop :=
(pretransitive_of_normal : ∀ {N : subgroup G} (nN : N.normal),
  fixed_points N X ≠ ⊤ → mul_action.is_pretransitive N X)


variables {G X}
lemma is_preprimitive.has_trivial_blocks [has_smul G X] (h : is_preprimitive G X) {B : set X}
  (hB : is_block G B) : B.subsingleton ∨ B = ⊤ :=
begin
  apply h.has_trivial_blocks', exact hB,
end

lemma is_preprimitive.on_subsingleton [has_smul G X] [nonempty G] [subsingleton X] :
  is_preprimitive G X :=
begin
  haveI : is_pretransitive G X,
  { apply is_pretransitive.mk,
    intros x y,
    use classical.arbitrary G,
    rw eq_iff_true_of_subsingleton ,
    trivial },
  apply is_preprimitive.mk,
  intros B hB,
  apply or.intro_left,
  exact set.subsingleton_of_subsingleton,
end

lemma is_trivial_block.of_card_le_2 [fintype X] (hX : fintype.card X ≤ 2) (B : set X) :
  is_trivial_block B :=
begin
  classical,
  cases le_or_lt (fintype.card B) 1 with h1 h1,
  { apply or.intro_left,
    rw [← set.subsingleton_coe,  ← fintype.card_le_one_iff_subsingleton],
    exact h1 },
  { apply or.intro_right,
    rw [set.top_eq_univ, ← set_fintype_card_eq_univ_iff],
    exact le_antisymm (set_fintype_card_le_univ B) (le_trans hX h1), },
end

variables [group G] [mul_action G X]

open_locale big_operators pointwise

variables {G X}

lemma is_trivial_block_of_block {B : set X} (g : G) (hB : is_trivial_block B):
  is_trivial_block (g • B) :=
begin
  cases hB,
  { apply or.intro_left,
    apply set.subsingleton.image hB },
  { apply or.intro_right,
    rw hB,
    rw eq_top_iff,
    intros x _,
    rw set.mem_smul_set_iff_inv_smul_mem,
    exact set.mem_univ _, }
end

lemma is_trivial_block_of_block_iff {B : set X} (g : G) :
  is_trivial_block B ↔  is_trivial_block (g • B) :=
begin
  split,
  exact is_trivial_block_of_block g,
  { intro hgB,
    rw ← inv_smul_smul g B,
    apply is_trivial_block_of_block,
    exact hgB }
end

lemma is_preprimitive.mk_mem [htGX : is_pretransitive G X] (a : X)
  (H : ∀ (B : set X) (ha : a ∈ B) (hB : is_block G B), is_trivial_block B) :
  is_preprimitive G X :=
begin
  apply is_preprimitive.mk,
  intros B hB,
  cases set.eq_empty_or_nonempty B,
  { apply or.intro_left, rw h, exact set.subsingleton_empty },
  { obtain ⟨b, hb⟩ := h,
    obtain ⟨g, hg⟩ := exists_smul_eq G b a,
    rw is_trivial_block_of_block_iff g,
    refine H (g • B) _ (is_block_of_block g hB),
    use b, exact ⟨hb, hg⟩ }
end

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) (based condition) -/
lemma is_preprimitive.mk_mem' (a : X) (ha : a ∉ fixed_points G X)
  (H : ∀ (B : set X) (haB : a ∈ B) (hB : is_block G B), is_trivial_block B) :
  is_preprimitive G X :=
begin
  haveI : is_pretransitive G X,
  { apply is_pretransitive.mk_base a,
    cases H (orbit G a) (mem_orbit_self a) (is_block_of_orbit a) with H H,
    { exfalso, apply ha,
      rw set.subsingleton_iff_singleton (mem_orbit_self a) at H ,
      simp only [mem_fixed_points], intro g,
      rw ← set.mem_singleton_iff, rw ← H,
      exact mem_orbit a g },
    { intro x, rw [← mul_action.mem_orbit_iff, H], exact set.mem_univ x } },
  apply is_preprimitive.mk,
  intros B hB,
  cases set.eq_empty_or_nonempty B,
  { apply or.intro_left, rw h, exact set.subsingleton_empty },
  { obtain ⟨b, hb⟩ := h,
    obtain ⟨g, hg⟩ := exists_smul_eq G b a,
    rw is_trivial_block_of_block_iff g,
    refine H (g • B) _ (is_block_of_block g hB),
    use b, exact ⟨hb, hg⟩ }
end

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/
lemma is_preprimitive.mk' (Hnt:  fixed_points G X ≠ ⊤)
  (H : ∀ (B : set X) (hB : is_block G B), is_trivial_block B) :
  is_preprimitive G X :=
begin
  have : ∃ (a : X),  a ∉ fixed_points G X,
  { by_contradiction, push_neg at h, apply Hnt, rw eq_top_iff,
    intros a _, exact h a },
  obtain ⟨a, ha⟩ := this,
  apply is_preprimitive.mk_mem' a ha,
  intros B _, exact H B,
end

end primitive

section equivariant_map

variables {M : Type*} [group M] {α : Type*} [mul_action M α]
variables {N β : Type*} [group N] [mul_action N β]

lemma is_trivial_block_of_surjective_map {φ : M → N} {f : α →ₑ[φ] β}
  (hf : function.surjective f) {B : set α}
  (hB : is_trivial_block B) : is_trivial_block (f '' B) :=
begin
  cases hB with hB hB,
  { apply or.intro_left, apply set.subsingleton.image hB },
  { apply or.intro_right, rw hB,
    simp only [set.top_eq_univ, set.image_univ, set.range_iff_surjective],
    exact hf }
end

lemma is_trivial_block_of_injective_map {φ : M → N} {f : α →ₑ[φ] β}
  (hf : function.injective f) {B : set β}
  (hB : is_trivial_block B) : is_trivial_block (f ⁻¹' B) :=
begin
  cases hB with hB hB,
  apply or.intro_left, exact set.subsingleton.preimage hB hf,
  apply or.intro_right, simp only [hB, set.top_eq_univ], apply set.preimage_univ,
end

lemma is_preprimitive_of_surjective_map
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f)
  (h : is_preprimitive M α) : is_preprimitive N β :=
begin
  haveI : is_pretransitive N β := is_pretransitive_of_surjective_map hf h.to_is_pretransitive,
  apply is_preprimitive.mk,
  { intros B hB,
    rw ← (set.image_preimage_eq B hf),
    apply is_trivial_block_of_surjective_map hf,
    apply h.has_trivial_blocks,
    apply is_block_preimage,
    exact hB }
end

/-
lemma is_pretransitive_of_bijective_map_iff
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f.to_fun)
  (h : is_preprimitive M α) : is_preprimitive N β :=

(f : mul_action_bihom M α N β)
  (hf : function.bijective f.to_fun) (hφ : function.surjective f.to_monoid_hom.to_fun) :
  is_pretransitive M α ↔ is_pretransitive N β :=
begin
  split,
  apply is_pretransitive_of_bihom f (function.bijective.surjective hf),
  intro hN, let hN_eq := hN.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨k, hk⟩ := exists_smul_eq N (f.to_fun x) (f.to_fun y),
  obtain ⟨g, rfl⟩ := hφ k,
  use g,
  apply function.bijective.injective hf,
  rw ← f.map_smul', exact hk,
end -/

lemma is_preprimitive_of_bijective_map_iff
  {φ : M → N} {f : α →ₑ[φ] β}
  (hφ : function.surjective φ) (hf : function.bijective f) :
  is_preprimitive M α ↔ is_preprimitive N β :=
begin
  split,
  apply is_preprimitive_of_surjective_map (hf.surjective),
  { intro hN,
    haveI := (is_pretransitive_of_bijective_map_iff hφ hf).mpr hN.to_is_pretransitive,
    apply is_preprimitive.mk,
    { intros B hB,
      rw ← set.preimage_image_eq B hf.injective,
      apply is_trivial_block_of_injective_map hf.injective,
      apply hN.has_trivial_blocks,
      apply is_block_image f hφ hf.injective,
      exact hB } }
end

lemma is_preprimitive_of_bijective_map_iff'
  (φ : M → N) (f : α →ₑ[φ] β)
  (hφ : function.surjective φ) (hf : function.bijective f) :
  is_preprimitive M α ↔ is_preprimitive N β :=
begin
  split,
  apply is_preprimitive_of_surjective_map (hf.surjective),
  { intro hN,
    haveI := (is_pretransitive_of_bijective_map_iff hφ hf).mpr hN.to_is_pretransitive,
    apply is_preprimitive.mk,
    { intros B hB,
      rw ← set.preimage_image_eq B hf.injective,
      apply is_trivial_block_of_injective_map hf.injective,
      apply hN.has_trivial_blocks,
      apply is_block_image f hφ hf.injective,
      exact hB } }
end


end equivariant_map

section stabilizer

variables (G : Type*) [group G] {X : Type*} [mul_action G X]

open_locale big_operators pointwise

instance block.bounded_order_of_mem (a : X) : bounded_order {B : set X // a ∈ B ∧ is_block G B} := {
top := ⟨⊤,
begin rw set.top_eq_univ, apply set.mem_univ end,
top_is_block X⟩,
le_top :=
begin
  rintro ⟨B, ha, hB⟩,
  simp only [set.top_eq_univ, subtype.mk_le_mk, set.le_eq_subset, set.subset_univ],
end,
bot := ⟨{a}, set.mem_singleton a, singleton_is_block a⟩,
bot_le :=
begin
  rintro ⟨B, ha, hB⟩,
  simp only [subtype.mk_le_mk, set.le_eq_subset, set.singleton_subset_iff],
  exact ha
end }

lemma block.bounded_order_of_mem.top_eq (a : X) :
  ((block.bounded_order_of_mem G a).top : set X) = ⊤ := rfl

lemma block.bounded_order_of_mem.bot_eq (a : X) :
  ((block.bounded_order_of_mem G a).bot : set X) = {a} := rfl

lemma block.mem_is_nontrivial_order_of_nontrivial [nontrivial X] (a : X) :
  nontrivial {B : set X // a ∈ B ∧ is_block G B } :=
begin
  rw nontrivial_iff,
  use (block.bounded_order_of_mem G a).bot,
  use (block.bounded_order_of_mem G a).top,
  intro h,
  rw ← subtype.coe_inj at h,
  simp only [block.bounded_order_of_mem.top_eq, block.bounded_order_of_mem.bot_eq] at h,
  obtain ⟨b, hb⟩ := exists_ne a,
  apply hb,
  rw ← set.mem_singleton_iff,
  rw h,
  rw set.top_eq_univ, apply set.mem_univ,
end

/-- A pretransitive action on a nontrivial type is preprimitive iff
the set of blocks containing a given element is a simple order -/
theorem is_preprimitive_iff_is_simple_order_blocks [htGX : is_pretransitive G X] [nontrivial X]
  (a : X) : is_preprimitive G X ↔ is_simple_order {B : set X // a ∈ B ∧ is_block G B}  :=
begin
  haveI : nontrivial {B : set X // a ∈ B ∧ is_block G B} :=
    block.mem_is_nontrivial_order_of_nontrivial G a,
  split,
  { intro hGX', apply is_simple_order.mk,
    rintro ⟨B, haB, hB⟩,
    simp only [← subtype.coe_inj, subtype.coe_mk],
    cases hGX'.has_trivial_blocks hB,
    { apply or.intro_left,
      change B = ↑(block.bounded_order_of_mem G a).bot,
      rw block.bounded_order_of_mem.bot_eq,
      exact set.subsingleton.eq_singleton_of_mem h haB },
    { apply or.intro_right,
      change B = ↑(block.bounded_order_of_mem G a).top,
      exact h } },
  { intro h, let h_bot_or_top := h.eq_bot_or_eq_top,
    apply is_preprimitive.mk_mem a,
    intros B haB hB,
    cases h_bot_or_top ⟨B, haB, hB⟩ with hB' hB';
    simp only [← subtype.coe_inj, subtype.coe_mk] at hB',
    { apply or.intro_left,
      rw hB', exact set.subsingleton_singleton },
    { apply or.intro_right,
      rw hB', refl },
    apply_instance }
end

/-- An pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
theorem maximal_stabilizer_iff_preprimitive [htGX : is_pretransitive G X] [hnX : nontrivial X]
  (a : X) : (stabilizer G a).is_maximal ↔ is_preprimitive G X :=
begin
--  let s := stabilizer_block_equiv a,
  rw is_preprimitive_iff_is_simple_order_blocks G a,
  rw subgroup.is_maximal_def,
  rw ← set.is_simple_order_Ici_iff_is_coatom,
  simp only [is_simple_order_iff_is_coatom_bot],
  rw ← order_iso.is_coatom_iff (stabilizer_block_equiv G a),
  rw order_iso.map_bot,
end

/-- In a preprimitive action, stabilizers are maximal subgroups -/
lemma has_maximal_stabilizers_of_preprimitive [hnX : nontrivial X] (hpGX : is_preprimitive G X)
  (a : X) : (stabilizer G a).is_maximal :=
begin
  haveI : is_pretransitive G X := hpGX.to_is_pretransitive,
  rw maximal_stabilizer_iff_preprimitive,
  exact hpGX,
end


end stabilizer

section normal

variables {M : Type*} [group M] {α : Type*} [mul_action M α]

/-- If a subgroup acts nontrivially, then the type is nontrivial -/
lemma isnontrivial_of_nontrivial_action {N : subgroup M} (h : fixed_points N α ≠ ⊤) :
  nontrivial α :=
begin
  apply or.resolve_left (subsingleton_or_nontrivial α),
  intro hα, apply h,
  rw eq_top_iff, intros x hx,
  rw mem_fixed_points,  intro g,
  rw subsingleton_iff  at hα,
  apply hα
end

/-
theorem pretransitive_of_normal_of_preprimitive {N : subgroup M} (nN : subgroup.normal N)
  (hGX : is_preprimitive M α) (hNX : fixed_points N α ≠ ⊤) :
  mul_action.is_pretransitive N α :=
begin
  have : ∃ (x : α), x ∉ fixed_points N α,
  { rw [← set.ne_univ_iff_exists_not_mem, ← set.top_eq_univ],
    exact hNX },
  obtain ⟨a, ha⟩ := this,
  rw ← mul_action.orbit.is_pretransitive_iff a,
  apply or.resolve_left (hGX.has_trivial_blocks (orbit.is_block_of_normal nN a)),
  intro h,
  apply ha, simp only [mem_fixed_points], intro n,
  rw ← set.mem_singleton_iff,
  suffices : orbit N a = {a}, { rw ← this, use n, },
  { ext b,
    rw set.subsingleton.eq_singleton_of_mem h (mul_action.mem_orbit_self a) },
end
-/

/-- In a preprimitive action,
  any normal subgroup that acts nontrivially is pretransitive
  (Wielandt, th. 7.1)-/
theorem is_preprimitive.is_quasipreprimitive (hGX : is_preprimitive M α) :
  is_quasipreprimitive M α :=
begin
  apply is_quasipreprimitive.mk,
  intros N hN hNX,
  have : ∃ (x : α), x ∉ fixed_points N α,
  { rw [← set.ne_univ_iff_exists_not_mem, ← set.top_eq_univ],
    exact hNX },
  obtain ⟨a, ha⟩ := this,
  rw ← mul_action.orbit.is_pretransitive_iff a,
  apply or.resolve_left (hGX.has_trivial_blocks (orbit.is_block_of_normal hN a)),
  intro h,
  apply ha, simp only [mem_fixed_points], intro n,
  rw ← set.mem_singleton_iff,
  suffices : orbit N a = {a}, { rw ← this, use n, },
  { ext b,
    rw set.subsingleton.eq_singleton_of_mem h (mul_action.mem_orbit_self a) },
end

/-
/-- If the action of M on α is primitive,
then for any normal subgroup N that acts nontrivially,
any a : α, the groups N and (stabilizer G a) generate M.
-/
lemma prim_to_full (is_prim: is_preprimitive M α)
  (a: α) (N : subgroup M) (nN : subgroup.normal N) (hNX : mul_action.fixed_points N α ≠ ⊤) :
  N ⊔ (mul_action.stabilizer M a) = ⊤ :=
begin
  haveI : is_pretransitive M α := is_prim.to_is_pretransitive,
  let is_pretrans := is_prim.to_is_pretransitive.exists_smul_eq,
  haveI : nontrivial α := isnontrivial_of_nontrivial_action hNX,
  -- Using that stabilizers are maximal, we reduce the assertion to contradicting
  -- an inclusion N ≤ stabilizer M a
  rw [← maximal_stabilizer_iff_preprimitive M a, subgroup.is_maximal_def, is_coatom] at is_prim,
  apply is_prim.right (N ⊔ (mul_action.stabilizer M a)),
  rw right_lt_sup, intro hz,
  -- The contradiction come from the hypothesis that N acts nontrivially
  apply hNX,
  -- Synthetically, N = g • N • g⁻¹ is contained in stabilizer M (g • a),
  -- so acts trivially in g • a.
  -- Using transitivity of the action, we get that N acts trivially
  -- (This is done by hand)
  rw [mul_action.fixed_points, set.top_eq_univ],
  apply set.eq_univ_of_forall,
  intro y, rw set.mem_set_of_eq, rintro ⟨g, hg⟩,
  change g • y = y,
  obtain ⟨h, hy⟩ := is_pretrans y a,
  rw smul_eq_iff_eq_inv_smul at hy,
  rw hy,
  rw ← smul_eq_iff_eq_inv_smul,
  simp only [← mul_smul, ← mul_assoc],
  rw ← mul_action.mem_stabilizer_iff,
  apply hz,
  apply nN.conj_mem g _ h,
  exact hg
end

lemma normal_core_of_stabilizer_acts_trivially (trans: is_pretransitive M α) (a: α) :
  mul_action.fixed_points (stabilizer M a).normal_core α = ⊤  :=
begin
  let trans_eq := trans.exists_smul_eq,
  rw eq_top_iff,
/-  apply (fixing_subgroup_fixed_points_gc M α).le_u,
  simp only [set.top_eq_univ, function.comp_app, order_dual.to_dual_le],
-/
  intros x _,
  rw mem_fixed_points, rintro ⟨g, hg⟩,
  change g • x = x,
  obtain ⟨k, hk⟩ := trans_eq x a,
  rw smul_eq_iff_eq_inv_smul at hk,
  rw hk,
  rw ← smul_eq_iff_eq_inv_smul,
  simp only [← mul_smul, ← mul_assoc],
  rw ← mem_stabilizer_iff,
  apply subgroup.normal_core_le,
  apply (stabilizer M a).normal_core_normal.conj_mem,
  exact hg
end

example (N K : subgroup M) (h : K < K ⊔ N) : ¬ (N ≤ K) :=
begin
exact left_lt_sup.mp h
end


lemma prim_to_full' (is_prim: is_preprimitive M α)
  (a: α) {N : subgroup M} (nN : subgroup.normal N) (hNX : mul_action.fixed_points N α ≠ ⊤) :
  N ⊔ (mul_action.stabilizer M a) = ⊤ :=
begin
  haveI : is_pretransitive M α := is_prim.to_is_pretransitive,
  resetI,
  let is_pretrans := is_prim.to_is_pretransitive.exists_smul_eq,
  haveI : nontrivial α := isnontrivial_of_nontrivial_action hNX,
  let is_prim' := id is_prim,
  rw [← maximal_stabilizer_iff_preprimitive M a, subgroup.is_maximal_def, is_coatom] at is_prim,
  apply is_prim.right (N ⊔ (mul_action.stabilizer M a)),
  rw right_lt_sup, intro hz, apply hNX,
  rw ← N.normal_core_eq_self,
  rw eq_top_iff,
  refine le_trans _ ((fixed_points_subgroup_antitone M α) (subgroup.normal_core_mono hz)),
  simp only,
  rw normal_core_of_stabilizer_acts_trivially is_prim'.to_is_pretransitive,
  exact le_of_eq rfl
end

-/

end normal

section finite

variables {M : Type*} [group M] {α : Type*} [mul_action M α]
variables {N β : Type*} [group N] [mul_action N β]

open_locale classical big_operators pointwise

/-- A pretransitive action on a set of prime order is preprimitive -/
lemma is_preprimitive_of_prime [fintype α] [hGX : is_pretransitive M α]
  (hp : nat.prime (fintype.card α)) : is_preprimitive M α :=
begin
  apply is_preprimitive.mk,
  intros B hB,
  cases subsingleton_or_nontrivial B with hB' hB',
  { apply or.intro_left, rw ← set.subsingleton_coe, exact hB' },
  apply or.intro_right,
  have : B.nonempty, rw ← set.nonempty_coe_sort, exact @nontrivial.to_nonempty _ hB',
  cases (nat.dvd_prime hp).mp (card_of_block_divides hB this),
  { exfalso,
    rw ← fintype.one_lt_card_iff_nontrivial at hB',
    exact ne_of_lt hB' h.symm },
  rw [set.top_eq_univ, ← set.coe_to_finset B, ← set.coe_to_finset set.univ, finset.coe_inj],
  rw [set.to_finset_univ, ← finset.card_eq_iff_eq_univ, ← h],
  simp only [set.to_finset_card],
  exact set_fintype set.univ,
end

/-- The target of an equivariant map of large image is preprimitive if the source is -/
theorem is_preprimitive_of_large_image
  [fintype β] [htβ : is_pretransitive N β]
  {φ : M → N} {f : α →ₑ[φ] β}
  (hM : is_preprimitive M α)
  (hf' : fintype.card β < 2 * fintype.card (set.range f)) : is_preprimitive N β :=
begin
  apply is_preprimitive.mk,
  intros B hB,

  cases subsingleton_or_nontrivial B with hB hB_nt,
  apply or.intro_left, rwa set.subsingleton_coe at hB,

  unfold is_trivial_block, rw or_iff_not_imp_right,
  intro hB_ne_top,

  have hB_ne : nonempty ↥B :=  @nontrivial.to_nonempty _ hB_nt,
  have hB_ne' : 0 < fintype.card B := fintype.card_pos_iff.mpr hB_ne,
  rw set.nonempty_coe_sort at hB_ne,

  -- We reduce to proving fintype.card ↥B < 2
  rw [← set.subsingleton_coe, ← fintype.card_le_one_iff_subsingleton, ← nat.lt_succ_iff],

  -- We reduce to proving that
  -- fintype.card (set.range f) ≤ fintype.card (set.range (λ g, g • B))

  apply lt_of_mul_lt_mul_right,
  apply lt_of_le_of_lt _ hf',
  rw ← card_of_block_mul_card_of_orbit_of hB hB_ne,
  apply nat.mul_le_mul_left _,

  -- We reduce to proving that
  -- fintype.card (set.range f ∩ g • B)) ≤ 1 for every g
  simp only [← set.to_finset_card],
  rw setoid.is_partition.card_set_eq_sum_parts (set.range f)
      (is_block_system.of_block hB hB_ne).left,
  rw finset.card_eq_sum_ones,
  refine finset.sum_le_sum _,
  intros t ht,
  simp only [set.mem_to_finset, set.mem_range] at ht,
  obtain ⟨g, ht⟩ := ht,
  rw ← ht,
  rw set.to_finset_card,

 -- It suffices to prove that the preimage is subsingleton
  rw [fintype.card_le_one_iff_subsingleton, set.inter_comm, ← set.image_preimage_eq_inter_range,
    set.subsingleton_coe],
  apply set.subsingleton.image,

  -- Since the action of M on α is primitive, it suffices to prove that
  -- the preimage is a block which is not ⊤
  apply or.resolve_right (hM.has_trivial_blocks (is_block_preimage f (is_block_of_block g hB))),
  intro h,
  have h' : ⊤ ⊆ f ⁻¹' (g • B) := subset_of_eq h.symm,
  rw [set.top_eq_univ, ← set.image_subset_iff, set.image_univ] at h',

  -- We will prove that B is large, which will contradict the assumption that it is not ⊤
  apply hB_ne_top,
  apply is_top_of_large_block hB,

  -- It remains to show that fintype.card β < 2 * fintype.card B
  apply lt_of_lt_of_le hf',
  simp only [mul_le_mul_left, nat.succ_pos'],
  rw ← smul_set_card_eq g B,
  -- This last step is disgusting :
  -- the types are identical, but not the proofs that they are finite
  refine le_trans _ (le_trans (set.card_le_of_subset h') _),
  apply le_of_eq, refl,
  apply le_of_eq, refl,
  exact zero_le (fintype.card ↥(set.range ⇑f)),
end

/-- Theorem of Rudio (Wielandt, 1964, Th. 8.1) -/
theorem rudio (hpGX : is_preprimitive M α)
  (A : set α) (hfA : A.finite) (hA : A.nonempty) (hA' : A ≠ ⊤)
  (a b : α) (h : a ≠ b):  ∃ (g : M), a ∈ g • A ∧ b ∉ g • A :=
begin
  let B := ⋂ (g : M) (ha : a ∈ g • A), (g • A),
  suffices : b ∉ B,
  { rw set.mem_Inter at this,
    simpa only [set.mem_Inter, not_forall, exists_prop] using this,
  },
  suffices : B = {a},
  { rw this, rw set.mem_singleton_iff, exact ne.symm h },
  have ha : a ∈ B,
  { rw set.mem_Inter, intro g, simp only [set.mem_Inter, imp_self] },
  -- B is a block hence is a trivial block
  cases hpGX.has_trivial_blocks (is_block.of_subset a A hfA) with hyp hyp,
  { -- B.subsingleton
    apply set.subsingleton.eq_singleton_of_mem hyp,
    rw set.mem_Inter, intro g, simp only [set.mem_Inter, imp_self] },
  { -- B = ⊤ : contradiction
    change B = ⊤ at hyp,
    exfalso, apply hA',
    suffices : ∃ (g : M), a ∈ g • A,
    { obtain ⟨g, hg⟩ := this,
      have : B ≤ g • A,
      { rw set.le_eq_subset, exact set.bInter_subset_of_mem hg },
      rw [hyp, top_le_iff, ← eq_inv_smul_iff] at this,
      rw [this, set.top_eq_univ, set.smul_set_univ] },
    -- ∃ (g : M), a ∈ g • A
    obtain ⟨x, hx⟩ := hA,
    obtain ⟨g, hg⟩ := mul_action.exists_smul_eq M x a,
    use g, use x, exact ⟨hx, hg⟩ },
end

end finite

section iwasawa


open_locale big_operators pointwise

variables {M : Type*} [group M] {α : Type*} [mul_action M α]

variables (M α)
/-- The structure underlying the Iwasawa criterion -/
structure iwasawa_structure :=
  (T : α → subgroup M)
  (is_comm: ∀ (x: α), (T x).is_commutative)
  (is_conj: ∀ (g: M), ∀ (x : α), T (g • x) = mul_aut.conj g • (T x))
  (is_generator: supr T = ⊤)

/- Variante de la structure d'Iwasawa :
* M action primitive sur α
* a : α
* A := T a, sous-groupe commutatif de G
* g • a = a → mul_aut.conj g A = A
* stabilizer M a ≤ normalizer A
* subgroup.normal_closure A = ⊤

Ou encore : (?)
* A : subgroup M, commutative
* normalizer A maximal
* subgroup.normal_closure A = ⊤

-/

variables {M α}
/-- The Iwasawa criterion : If a quasiprimitive action of a group G on X
has an Iwasawa structure, then any normal subgroup that acts nontrivially
contains the group of commutators. -/
theorem commutator_le_iwasawa (is_qprim: is_quasipreprimitive M α) (IwaS : iwasawa_structure M α)
  {N : subgroup M} (nN : N.normal) (hNX : mul_action.fixed_points N α ≠ ⊤) :
  commutator M ≤ N :=
begin
  haveI is_transN := is_qprim.pretransitive_of_normal nN hNX,
  haveI ntα : nontrivial α := (isnontrivial_of_nontrivial_action hNX),
  obtain a : α := nontrivial.to_nonempty.some,
  refine contains_commutators_of N nN (IwaS.T a) _ (IwaS.is_comm a),
  -- by contains_commutators_of, it suffices to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff, ← IwaS.is_generator, supr_le_iff],
  intro x,
  obtain ⟨g, rfl⟩ := mul_action.exists_smul_eq N a x,
  rw [subgroup.smul_def, IwaS.is_conj g a],
  rintros _ ⟨k, hk, rfl⟩,
  have hg' : ↑g ∈ N ⊔ IwaS.T a := subgroup.mem_sup_left (subtype.mem g),
  have hk' : k ∈ N ⊔ IwaS.T a := subgroup.mem_sup_right hk,
  exact (N ⊔ IwaS.T a).mul_mem ((N ⊔ IwaS.T a).mul_mem hg' hk') ((N ⊔ IwaS.T a).inv_mem hg'),
end

/-- The Iwasawa criterion for simplicity -/
theorem is_simple_iwasawa
  (is_nontrivial : nontrivial M) (is_perfect : commutator M = ⊤)
  (is_qprim : is_quasipreprimitive M α) (is_faithful : has_faithful_smul M α)
  (IwaS : iwasawa_structure M α) : is_simple_group M :=
begin
  refine ⟨is_nontrivial.exists_pair_ne, λ N nN, _⟩,
  cases (or_iff_not_imp_left.mpr (commutator_le_iwasawa is_qprim IwaS nN)),
  { refine or.inl (N.eq_bot_iff_forall.mpr (λ n hn, _)),
    apply is_faithful.eq_of_smul_eq_smul,
    intro x,
    rw one_smul,
    exact set.eq_univ_iff_forall.mp h x ⟨n, hn⟩ },
  { exact or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h)) },
end

end iwasawa


#lint
