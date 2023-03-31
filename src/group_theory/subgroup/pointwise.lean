/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.subgroup.mul_opposite
import group_theory.submonoid.pointwise
import group_theory.group_action.conj_act

/-! # Pointwise instances on `subgroup` and `add_subgroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the actions

* `subgroup.pointwise_mul_action`
* `add_subgroup.pointwise_mul_action`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

The pointwise section of this file is almost identical to `group_theory/submonoid/pointwise.lean`.
Where possible, try to keep them in sync.
-/

open set
open_locale pointwise

variables {α G A S : Type*}

@[simp, to_additive]
lemma inv_coe_set [has_involutive_inv G] [set_like S G] [inv_mem_class S G] {H : S} :
  (H : set G)⁻¹ = H :=
set.ext $ λ _, inv_mem_iff

variables [group G] [add_group A] {s : set G}

namespace subgroup

@[simp, to_additive] lemma inv_subset_closure (S : set G) : S⁻¹ ⊆ closure S :=
λ s hs, by { rw [set_like.mem_coe, ←subgroup.inv_mem_iff], exact subset_closure (mem_inv.mp hs) }

@[to_additive]
lemma closure_to_submonoid (S : set G) : (closure S).to_submonoid = submonoid.closure (S ∪ S⁻¹) :=
begin
  refine le_antisymm (λ x hx, _) (submonoid.closure_le.2 _),
  { refine closure_induction hx (λ x hx, submonoid.closure_mono (subset_union_left S S⁻¹)
      (submonoid.subset_closure hx)) (submonoid.one_mem _) (λ x y hx hy, submonoid.mul_mem _ hx hy)
      (λ x hx, _),
    rwa [←submonoid.mem_closure_inv, set.union_inv, inv_inv, set.union_comm] },
  { simp only [true_and, coe_to_submonoid, union_subset_iff, subset_closure, inv_subset_closure] }
end

@[to_additive] lemma closure_induction_left {p : G → Prop} {x : G}
  (h : x ∈ closure s) (H1 : p 1) (Hmul : ∀ (x ∈ s) y, p y → p (x * y))
  (Hinv : ∀ (x ∈ s) y, p y → p (x⁻¹ * y)) : p x :=
let key := (closure_to_submonoid s).le in submonoid.closure_induction_left (key h) H1 $
  λ x hx, hx.elim (Hmul x) $ λ hx y hy, (congr_arg _ $ inv_inv x).mp $ Hinv x⁻¹ hx y hy

@[to_additive] lemma closure_induction_right {p : G → Prop} {x : G}
  (h : x ∈ closure s) (H1 : p 1) (Hmul : ∀ x (y ∈ s), p x → p (x * y))
  (Hinv : ∀ x (y ∈ s), p x → p (x * y⁻¹)) : p x :=
let key := (closure_to_submonoid s).le in submonoid.closure_induction_right (key h) H1 $
  λ x y hy, hy.elim (Hmul x y) $ λ hy hx, (congr_arg _ $ inv_inv y).mp $ Hinv x y⁻¹ hy hx

@[simp, to_additive] lemma closure_inv (s : set G) : closure s⁻¹ = closure s :=
by simp only [← to_submonoid_eq, closure_to_submonoid, inv_inv, union_comm]

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of
`k` and their inverse, and is preserved under multiplication, then `p` holds for all elements of
the closure of `k`. -/
@[to_additive "An induction principle for additive closure membership. If `p` holds for `0` and all
elements of `k` and their negation, and is preserved under addition, then `p` holds for all
elements of the additive closure of `k`."]
lemma closure_induction'' {p : G → Prop} {x} (h : x ∈ closure s) (Hk : ∀ x ∈ s, p x)
  (Hk_inv : ∀ x ∈ s, p x⁻¹) (H1 : p 1) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
closure_induction_left h H1 (λ x hx y hy, Hmul x y (Hk x hx) hy) $ λ x hx y,
  Hmul x⁻¹ y $ Hk_inv x hx

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_eliminator, to_additive /-" An induction principle for elements of `⨆ i, S i`.
If `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. "-/]
lemma supr_induction {ι : Sort*} (S : ι → subgroup G) {C : G → Prop} {x : G} (hx : x ∈ ⨆ i, S i)
  (hp : ∀ i (x ∈ S i), C x)
  (h1 : C 1)
  (hmul : ∀ x y, C x → C y → C (x * y)) : C x :=
begin
  rw supr_eq_closure at hx,
  refine closure_induction'' hx (λ x hx, _) (λ x hx, _) h1 hmul,
  { obtain ⟨i, hi⟩ := set.mem_Union.mp hx,
    exact hp _ _ hi, },
  { obtain ⟨i, hi⟩ := set.mem_Union.mp hx,
    exact hp _ _ (inv_mem hi), },
end

/-- A dependent version of `subgroup.supr_induction`. -/
@[elab_as_eliminator, to_additive /-"A dependent version of `add_subgroup.supr_induction`. "-/]
lemma supr_induction' {ι : Sort*} (S : ι → subgroup G) {C : Π x, (x ∈ ⨆ i, S i) → Prop}
  (hp : ∀ i (x ∈ S i), C x (mem_supr_of_mem i ‹_›))
  (h1 : C 1 (one_mem _))
  (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›))
  {x : G} (hx : x ∈ ⨆ i, S i) : C x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ ⨆ i, S i) (hc : C x hx), hc),
  refine supr_induction S hx (λ i x hx, _) _ (λ x y, _),
  { exact ⟨_, hp _ _ hx⟩ },
  { exact ⟨_, h1⟩ },
  { rintro ⟨_, Cx⟩ ⟨_, Cy⟩,
    refine ⟨_, hmul _ _ _ _ Cx Cy⟩ },
end

@[to_additive]
lemma closure_mul_le (S T : set G) : closure (S * T) ≤ closure S ⊔ closure T :=
Inf_le $ λ x ⟨s, t, hs, ht, hx⟩, hx ▸ (closure S ⊔ closure T).mul_mem
    (set_like.le_def.mp le_sup_left $ subset_closure hs)
    (set_like.le_def.mp le_sup_right $ subset_closure ht)

@[to_additive]
lemma sup_eq_closure (H K : subgroup G) : H ⊔ K = closure (H * K) :=
le_antisymm
  (sup_le
    (λ h hh, subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩)
    (λ k hk, subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩))
  (by conv_rhs { rw [← closure_eq H, ← closure_eq K] }; apply closure_mul_le)

@[to_additive]
private def mul_normal_aux (H N : subgroup G) [hN : N.normal] : subgroup G :=
{ carrier := (H : set G) * N,
  one_mem' := ⟨1, 1, H.one_mem, N.one_mem, by rw mul_one⟩,
  mul_mem' := λ a b ⟨h, n, hh, hn, ha⟩ ⟨h', n', hh', hn', hb⟩,
    ⟨h * h', h'⁻¹ * n * h' * n',
    H.mul_mem hh hh', N.mul_mem (by simpa using hN.conj_mem _ hn h'⁻¹) hn',
    by simp [← ha, ← hb, mul_assoc]⟩,
  inv_mem' := λ x ⟨h, n, hh, hn, hx⟩,
    ⟨h⁻¹, h * n⁻¹ * h⁻¹, H.inv_mem hh, hN.conj_mem _ (N.inv_mem hn) h,
    by rw [mul_assoc h, inv_mul_cancel_left, ← hx, mul_inv_rev]⟩ }

/-- The carrier of `H ⊔ N` is just `↑H * ↑N` (pointwise set product) when `N` is normal. -/
@[to_additive "The carrier of `H ⊔ N` is just `↑H + ↑N` (pointwise set addition)
when `N` is normal."]
lemma mul_normal (H N : subgroup G) [N.normal] : (↑(H ⊔ N) : set G) = H * N :=
set.subset.antisymm
  (show H ⊔ N ≤ mul_normal_aux H N,
    by { rw sup_eq_closure, apply Inf_le _, dsimp, refl })
  ((sup_eq_closure H N).symm ▸ subset_closure)

@[to_additive]
private def normal_mul_aux (N H : subgroup G) [hN : N.normal] : subgroup G :=
{ carrier := (N : set G) * H,
  one_mem' := ⟨1, 1, N.one_mem, H.one_mem, by rw mul_one⟩,
  mul_mem' := λ a b ⟨n, h, hn, hh, ha⟩ ⟨n', h', hn', hh', hb⟩,
    ⟨n * (h * n' * h⁻¹), h * h',
    N.mul_mem hn (hN.conj_mem _ hn' _), H.mul_mem hh hh',
    by simp [← ha, ← hb, mul_assoc]⟩,
  inv_mem' := λ x ⟨n, h, hn, hh, hx⟩,
    ⟨h⁻¹ * n⁻¹ * h, h⁻¹,
    by simpa using hN.conj_mem _ (N.inv_mem hn) h⁻¹, H.inv_mem hh,
    by rw [mul_inv_cancel_right, ← mul_inv_rev, hx]⟩ }

/-- The carrier of `N ⊔ H` is just `↑N * ↑H` (pointwise set product) when `N` is normal. -/
@[to_additive "The carrier of `N ⊔ H` is just `↑N + ↑H` (pointwise set addition)
when `N` is normal."]
lemma normal_mul (N H : subgroup G) [N.normal] : (↑(N ⊔ H) : set G) = N * H :=
set.subset.antisymm
  (show N ⊔ H ≤ normal_mul_aux N H,
    by { rw sup_eq_closure, apply Inf_le _, dsimp, refl })
  ((sup_eq_closure N H).symm ▸ subset_closure)

@[to_additive] lemma mul_inf_assoc (A B C : subgroup G) (h : A ≤ C) :
  (A : set G) * ↑(B ⊓ C) = (A * B) ⊓ C :=
begin
  ext,
  simp only [coe_inf, set.inf_eq_inter, set.mem_mul, set.mem_inter_iff],
  split,
  { rintros ⟨y, z, hy, ⟨hzB, hzC⟩, rfl⟩,
    refine ⟨_, mul_mem (h hy) hzC⟩,
    exact ⟨y, z, hy, hzB, rfl⟩ },
  rintros ⟨⟨y, z, hy, hz, rfl⟩, hyz⟩,
  refine ⟨y, z, hy, ⟨hz, _⟩, rfl⟩,
  suffices : y⁻¹ * (y * z) ∈ C, { simpa },
  exact mul_mem (inv_mem (h hy)) hyz
end

@[to_additive] lemma inf_mul_assoc (A B C : subgroup G) (h : C ≤ A) :
  ((A ⊓ B : subgroup G) : set G) * C = A ⊓ (B * C) :=
begin
  ext,
  simp only [coe_inf, set.inf_eq_inter, set.mem_mul, set.mem_inter_iff],
  split,
  { rintros ⟨y, z, ⟨hyA, hyB⟩, hz, rfl⟩,
    refine ⟨A.mul_mem hyA (h hz), _⟩,
    exact ⟨y, z, hyB, hz, rfl⟩ },
  rintros ⟨hyz, y, z, hy, hz, rfl⟩,
  refine ⟨y, z, ⟨_, hy⟩, hz, rfl⟩,
  suffices : (y * z) * z⁻¹ ∈ A, { simpa },
  exact mul_mem hyz (inv_mem (h hz))
end

instance sup_normal (H K : subgroup G) [hH : H.normal] [hK : K.normal] : (H ⊔ K).normal :=
{ conj_mem := λ n hmem g,
  begin
    change n ∈ ↑(H ⊔ K) at hmem,
    change g * n * g⁻¹ ∈ ↑(H ⊔ K),
    rw [normal_mul, set.mem_mul] at *,
    rcases hmem with ⟨h, k, hh, hk, rfl⟩,
    refine ⟨g * h * g⁻¹, g * k * g⁻¹, hH.conj_mem h hh g, hK.conj_mem k hk g, _⟩,
    simp
  end }

@[to_additive] lemma smul_opposite_image_mul_preimage {H : subgroup G} (g : G) (h : H.opposite)
  (s : set G) : (λ y, h • y) '' (has_mul.mul g ⁻¹' s) = has_mul.mul g ⁻¹' ((λ y, h • y) '' s) :=
by { ext x, cases h, simp [(•), mul_assoc] }

/-! ### Pointwise action -/

section monoid
variables [monoid α] [mul_distrib_mul_action α G]

/-- The action on a subgroup corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (subgroup G) :=
{ smul := λ a S, S.map (mul_distrib_mul_action.to_monoid_End _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (monoid_hom.map_mul _ _ _)).trans (S.map_map _ _).symm,}

localized "attribute [instance] subgroup.pointwise_mul_action" in pointwise
open_locale pointwise

lemma pointwise_smul_def {a : α} (S : subgroup G) :
  a • S = S.map (mul_distrib_mul_action.to_monoid_End _ _ a) := rfl

@[simp] lemma coe_pointwise_smul (a : α) (S : subgroup G) : ↑(a • S) = a • (S : set G) := rfl

@[simp] lemma pointwise_smul_to_submonoid (a : α) (S : subgroup G) :
  (a • S).to_submonoid = a • S.to_submonoid := rfl

lemma smul_mem_pointwise_smul (m : G) (a : α) (S : subgroup G) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set G))

lemma mem_smul_pointwise_iff_exists (m : G) (a : α) (S : subgroup G) :
  m ∈ a • S ↔ ∃ (s : G), s ∈ S ∧ a • s = m :=
(set.mem_smul_set : m ∈ a • (S : set G) ↔ _)

@[simp] lemma smul_bot (a : α) : a • (⊥ : subgroup G) = ⊥ := map_bot _
lemma smul_sup (a : α) (S T : subgroup G) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

lemma smul_closure (a : α) (s : set G) : a • closure s = closure (a • s) :=
monoid_hom.map_closure _ _

instance pointwise_central_scalar [mul_distrib_mul_action αᵐᵒᵖ G] [is_central_scalar α G] :
  is_central_scalar α (subgroup G) :=
⟨λ a S, congr_arg (λ f, S.map f) $ monoid_hom.ext $ by exact op_smul_eq_smul _⟩

lemma conj_smul_le_of_le {P H : subgroup G} (hP : P ≤ H) (h : H) :
  mul_aut.conj (h : G) • P ≤ H :=
begin
  rintro - ⟨g, hg, rfl⟩,
  exact H.mul_mem (H.mul_mem h.2 (hP hg)) (H.inv_mem h.2),
end

lemma conj_smul_subgroup_of {P H : subgroup G} (hP : P ≤ H) (h : H) :
  mul_aut.conj h • P.subgroup_of H = (mul_aut.conj (h : G) • P).subgroup_of H :=
begin
  refine le_antisymm _ _,
  { rintro - ⟨g, hg, rfl⟩,
    exact ⟨g, hg, rfl⟩ },
  { rintro p ⟨g, hg, hp⟩,
    exact ⟨⟨g, hP hg⟩, hg, subtype.ext hp⟩ },
end

end monoid

section group
variables [group α] [mul_distrib_mul_action α G]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : subgroup G} {x : G} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : subgroup G} {x : G} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : subgroup G} {x : G} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : subgroup G} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_subset_iff {a : α} {S T : subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma subset_pointwise_smul_iff {a : α} {S T : subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

@[simp] lemma smul_inf (a : α) (S T : subgroup G) : a • (S ⊓ T) = a • S ⊓ a • T :=
by simp [set_like.ext_iff, mem_pointwise_smul_iff_inv_smul_mem]

/-- Applying a `mul_distrib_mul_action` results in an isomorphic subgroup -/
@[simps] def equiv_smul (a : α) (H : subgroup G) : H ≃* (a • H : subgroup G) :=
(mul_distrib_mul_action.to_mul_equiv G a).subgroup_map H

lemma subgroup_mul_singleton {H : subgroup G} {h : G} (hh : h ∈ H) :
  (H : set G) * {h} = H :=
begin
  refine le_antisymm _ (λ h' hh',
    ⟨h' * h⁻¹, h, H.mul_mem hh' (H.inv_mem hh), rfl, inv_mul_cancel_right h' h⟩),
  rintros _ ⟨h', h, hh', rfl : _ = _, rfl⟩,
  exact H.mul_mem hh' hh,
end

lemma singleton_mul_subgroup {H : subgroup G} {h : G} (hh : h ∈ H) :
  {h} * (H : set G) = H :=
begin
  refine le_antisymm _ (λ h' hh', ⟨h, h⁻¹ * h', rfl, H.mul_mem (H.inv_mem hh) hh',
    mul_inv_cancel_left h h'⟩),
  rintros _ ⟨h, h', rfl : _ = _, hh', rfl⟩,
  exact H.mul_mem hh hh',
end

lemma normal.conj_act {G : Type*} [group G] {H : subgroup G} (hH : H.normal ) (g : conj_act G) :
  g • H = H :=
begin
  ext,
  split,
  { intro h,
    have := hH.conj_mem (g⁻¹ • x) _ (conj_act.of_conj_act g),
    rw subgroup.mem_pointwise_smul_iff_inv_smul_mem at h,
    dsimp at *,
    rw conj_act.smul_def at *,
    simp only [conj_act.of_conj_act_inv, conj_act.of_conj_act_to_conj_act, inv_inv] at *,
    convert this,
    simp only [←mul_assoc, mul_right_inv, one_mul, mul_inv_cancel_right],
    rw subgroup.mem_pointwise_smul_iff_inv_smul_mem at h,
    exact h},
  { intro h,
    rw [subgroup.mem_pointwise_smul_iff_inv_smul_mem, conj_act.smul_def],
    apply hH.conj_mem,
    exact h}
end

@[simp] lemma smul_normal (g : G) (H : subgroup G) [h : normal H] : mul_aut.conj g • H = H :=
h.conj_act g

end group

section group_with_zero
variables [group_with_zero α] [mul_distrib_mul_action α G]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : subgroup G)
  (x : G) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set G) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : subgroup G) (x : G) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set G) x

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : subgroup G) (x : G) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set G) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : subgroup G} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : subgroup G} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : subgroup G} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

end subgroup

namespace add_subgroup

section monoid
variables [monoid α] [distrib_mul_action α A]

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (add_subgroup A) :=
{ smul := λ a S, S.map (distrib_mul_action.to_add_monoid_End _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (monoid_hom.map_mul _ _ _)).trans (S.map_map _ _).symm,}

localized "attribute [instance] add_subgroup.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : add_subgroup A) : ↑(a • S) = a • (S : set A) := rfl

@[simp] lemma pointwise_smul_to_add_submonoid (a : α) (S : add_subgroup A) :
  (a • S).to_add_submonoid = a • S.to_add_submonoid := rfl

lemma smul_mem_pointwise_smul (m : A) (a : α) (S : add_subgroup A) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set A))

lemma mem_smul_pointwise_iff_exists (m : A) (a : α) (S : add_subgroup A) :
  m ∈ a • S ↔ ∃ (s : A), s ∈ S ∧ a • s = m :=
(set.mem_smul_set : m ∈ a • (S : set A) ↔ _)

instance pointwise_central_scalar [distrib_mul_action αᵐᵒᵖ A] [is_central_scalar α A] :
  is_central_scalar α (add_subgroup A) :=
⟨λ a S, congr_arg (λ f, S.map f) $ add_monoid_hom.ext $ by exact op_smul_eq_smul _⟩

end monoid

section group
variables [group α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : add_subgroup A} {x : A} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : add_subgroup A} {x : A} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : add_subgroup A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : add_subgroup A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_le_iff {a : α} {S T : add_subgroup A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma le_pointwise_smul_iff {a : α} {S T : add_subgroup A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : add_subgroup A)
  (x : A) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set A) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : add_subgroup A) (x : A) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set A) x

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : add_subgroup A) (x : A) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set A) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : add_subgroup A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : add_subgroup A} :
  a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : add_subgroup A} :
  S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

end add_subgroup
