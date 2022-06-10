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
import data.nat.prime
import data.fintype.basic
import algebra.big_operators.order
import .for_mathlib.stabilizer
import .for_mathlib.pretransitive
import .for_mathlib.set
import .equivariant_map
import .sub_mul_actions
import .for_mathlib.partitions
import .maximal_subgroups
import .blocks


/-!
# Primitive actions

- The structure `is_preprimitive G X` that says that the action of a type `G`
on a type `T` (defined by an instance `has_scalar G X`) is *preprimitive*, namely,
it is pretransitive and the only blocks are ⊤ and subsingletons.

The notion which is introduced in classical groups is restricted to `mul_action` of groups.
In fact, it may be irrelevant if the action is degenerate,
when “trivial blocks” might not be blocks.
Moreover, the classical notion is *primitive*,
which assumes moreover that `X` is not empty.

- We prove some straightforward theorems that relate preprimitivity under equivariant maps,
for images and preimages.

-
-/
open mul_action


section primitive

variables (G : Type*) (X : Type*)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
structure is_preprimitive [has_scalar G X]
extends is_pretransitive G X : Prop :=
(has_trivial_blocks : ∀ {B : set X}, (is_block G B) → is_trivial_block B)

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
    use ⟨g⁻¹ • x, set.mem_univ _, smul_inv_smul g x⟩ }
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

lemma is_preprimitive.mk_mem (htGX : is_pretransitive G X) (a : X)
  (H : ∀ (B : set X) (ha : a ∈ B) (hB : is_block G B), is_trivial_block B) :
  is_preprimitive G X :=
begin
  let ht_eq := htGX.exists_smul_eq,
  apply is_preprimitive.mk htGX,
  intros B hB,
  cases set.eq_empty_or_nonempty B,
  { apply or.intro_left, rw h, exact set.subsingleton_empty },
  { obtain ⟨b, hb⟩ := h,
    obtain ⟨g, hg⟩ := ht_eq b a,
    rw is_trivial_block_of_block_iff g,
    refine H (g • B) _ (is_block_of_block g hB),
    use b, exact ⟨hb, hg⟩ }
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
  {φ : M → N} {f : α →ₑ[φ] β} (hf : function.surjective f.to_fun)
  (h : is_preprimitive M α) : is_preprimitive N β :=
begin
  let h.htb := h.has_trivial_blocks,
  apply is_preprimitive.mk,
  { apply is_pretransitive_of_surjective_map hf,
    exact h.to_is_pretransitive },
  { intros B hB,
    rw ← (set.image_preimage_eq B hf),
    apply is_trivial_block_of_surjective_map hf,
    apply h.htb,
    simp only [equivariant_map.to_fun_eq_coe],
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
  obtain ⟨k, hk⟩ := hN_eq (f.to_fun x) (f.to_fun y),
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
    apply is_preprimitive.mk,
    { rw is_pretransitive_of_bijective_map_iff hφ hf,
      exact hN.to_is_pretransitive },
    { intros B hB,
      rw ← set.preimage_image_eq B hf.injective,
      apply is_trivial_block_of_injective_map hf.injective,
      apply hN.has_trivial_blocks,
      apply is_block_image f hφ hf.injective,
      exact hB } }
end

end equivariant_map

section normal

variables {M : Type*} [group M] {α : Type*} [mul_action M α]

/-- In a preprimitive action,
  any normal subgroup that acts nontrivially is pretransitive
  (Wielandt, th. 7.1)-/
theorem transitive_of_normal_of_preprimitive (N : subgroup M) [nN : subgroup.normal N]
  (hGX : is_preprimitive M α) (hNX : fixed_points N α ≠ ⊤) :
  mul_action.is_pretransitive N α :=
begin
  have : ∃ (x : α), x ∉ fixed_points N α,
  { rw [← set.ne_univ_iff_exists_not_mem, ← set.top_eq_univ],
    exact hNX },
  obtain ⟨a, ha⟩ := this,
  rw ← mul_action.orbit.is_pretransitive_iff N a,
  apply or.resolve_left (hGX.has_trivial_blocks (orbit.is_block_of_normal nN a)),
  intro h,
  apply ha, simp only [mem_fixed_points], intro n,
  rw ← set.mem_singleton_iff,
  suffices : orbit N a = {a}, { rw ← this, use n, },
  { ext b,
    rw set.subsingleton.eq_singleton_of_mem h (mul_action.mem_orbit_self a) },
end

end normal

section stabilizer

variables (G : Type*) [group G] (X : Type*) [mul_action G X]

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
  ((block.bounded_order_of_mem G X a).top : set X) = ⊤ := rfl

lemma block.bounded_order_of_mem.bot_eq (a : X) :
  ((block.bounded_order_of_mem G X a).bot : set X) = {a} := rfl

lemma block.mem_is_nontrivial_order_of_nontrivial [nontrivial X] (a : X) :
  nontrivial {B : set X // a ∈ B ∧ is_block G B } :=
begin
  rw nontrivial_iff,
  use (block.bounded_order_of_mem G X a).bot,
  use (block.bounded_order_of_mem G X a).top,
  intro h,
  rw ← subtype.coe_inj at h,
  simp only [block.bounded_order_of_mem.top_eq, block.bounded_order_of_mem.bot_eq] at h,
  obtain ⟨b, hb⟩ := exists_ne a,
  apply hb,
  rw ← set.mem_singleton_iff,
  rw h,
  rw set.top_eq_univ, apply set.mem_univ,
end

theorem is_preprimitive_of_block_order (htGX : is_pretransitive G X) [nontrivial X] (a : X) :
  is_preprimitive G X ↔ is_simple_order {B : set X // a ∈ B ∧ is_block G B}  :=
begin
  haveI : nontrivial {B : set X // a ∈ B ∧ is_block G B} :=
    block.mem_is_nontrivial_order_of_nontrivial G X a,
  split,
  { intro hGX', apply is_simple_order.mk,
    rintro ⟨B, haB, hB⟩,
    simp only [← subtype.coe_inj, subtype.coe_mk],
    cases hGX'.has_trivial_blocks hB,
    { apply or.intro_left,
      change B = ↑(block.bounded_order_of_mem G X a).bot,
      rw block.bounded_order_of_mem.bot_eq,
      exact set.subsingleton.eq_singleton_of_mem h haB },
    { apply or.intro_right,
      change B = ↑(block.bounded_order_of_mem G X a).top,
      exact h } },
  { intro h, let h_bot_or_top := h.eq_bot_or_eq_top,
    apply is_preprimitive.mk_mem htGX a,
    intros B haB hB,
    cases h_bot_or_top ⟨B, haB, hB⟩ with hB' hB';
    simp only [← subtype.coe_inj, subtype.coe_mk] at hB',
    { apply or.intro_left,
      rw hB', exact set.subsingleton_singleton },
    { apply or.intro_right,
      rw hB', refl } }
end

/-- An pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
theorem maximal_stabilizer_iff_primitive [hnX : nontrivial X] [htGX : is_pretransitive G X]
  (a : X) : (stabilizer G a).is_maximal ↔ is_preprimitive G X :=
begin
  let s := stabilizer_block_equiv htGX a,
  rw is_preprimitive_of_block_order G X htGX a,
  rw subgroup.is_maximal_def,
  rw ← set.is_simple_order_Ici_iff_is_coatom,
  simp only [is_simple_order_iff_is_coatom_bot],
  rw ← order_iso.is_coatom_iff (stabilizer_block_equiv htGX a) _,
  rw order_iso.map_bot,
end

end stabilizer

section finite

variables {M : Type*} [group M] {α : Type*} [mul_action M α]
variables {N β : Type*} [group N] [mul_action N β]

open_locale classical big_operators pointwise

lemma is_preprimitive_of_prime [fintype α] (hGX : is_pretransitive M α)
  (hp : nat.prime (fintype.card α)) : is_preprimitive M α :=
begin
  apply is_preprimitive.mk,
  exact hGX,
  intros B hB,
  cases subsingleton_or_nontrivial B with hB' hB',
  { apply or.intro_left, rw ← set.subsingleton_coe, exact hB' },
  apply or.intro_right,
  have : B.nonempty, rw ← set.nonempty_coe_sort, exact @nontrivial.to_nonempty _ hB',
  cases (nat.dvd_prime hp).mp (card_of_block_divides hGX hB this),
  { exfalso,
    rw ← fintype.one_lt_card_iff_nontrivial at hB',
    exact ne_of_lt hB' h.symm },
  rw [set.top_eq_univ, ← set.coe_to_finset B, ← set.coe_to_finset set.univ, finset.coe_inj],
  rw [set.to_finset_univ, ← finset.card_eq_iff_eq_univ, ← h],
  simp only [set.to_finset_card],
  exact set_fintype set.univ,
end

theorem is_primitive_of_large_image
  [fintype β] (htβ : is_pretransitive N β)
  {φ : M → N} {f : α →ₑ[φ] β}
  (hM : is_preprimitive M α)
  (hf' : fintype.card β < 2 * fintype.card (set.range f)) : is_preprimitive N β :=
begin
  apply is_preprimitive.mk htβ,
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
  apply lt_of_mul_lt_mul_right',
  apply lt_of_le_of_lt _ hf',
  rw ← card_of_block_mul_card_of_orbit_of htβ hB hB_ne,
  apply nat.mul_le_mul_left _,

  -- We reduce to proving that
  -- fintype.card (set.range f ∩ g • B)) ≤ 1 for every g
  simp only [← set.to_finset_card],
  rw setoid.is_partition.card_set_eq_sum_parts (set.range f)
      (is_block_system.of_block htβ hB hB_ne).left,
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
  apply set.subsingleton.image ,
  -- Since the action of M on α is primitive, it suffices to prove that
  -- the preimage is a block which is not ⊤
  apply or.resolve_right
    (hM.has_trivial_blocks (is_block_preimage f (is_block_of_block g hB))),
  intro h,
  have h' : ⊤ ⊆ f ⁻¹' (g • B) := subset_of_eq h.symm,
  rw [set.top_eq_univ, ← set.image_subset_iff, set.image_univ] at h',

  -- We will prove that B is large, which will contradict the assumption that it is not ⊤
  apply hB_ne_top,
  apply is_top_of_large_block htβ hB,

  -- It remains to show that 2 * fintype.card B > fintype.card β
  apply lt_of_lt_of_le hf',
  simp only [mul_le_mul_left, nat.succ_pos'],
  rw ← set.smul_set_card_eq g B,
  -- This last step is disgusting :
  -- the types are identical, but not the proofs that they are finite
  refine le_trans _ (le_trans (set.card_le_of_subset h') _),
  all_goals { apply le_of_eq, apply fintype.card_congr', refl }
end

end finite

#lint
