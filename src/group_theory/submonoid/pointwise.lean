/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.set.pointwise.smul
import group_theory.submonoid.membership
import order.well_founded_set

/-! # Pointwise instances on `submonoid`s and `add_submonoid`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides:

* `submonoid.has_inv`
* `add_submonoid.has_neg`

and the actions

* `submonoid.pointwise_mul_action`
* `add_submonoid.pointwise_mul_action`

which matches the action of `mul_action_set`.

These are all available in the `pointwise` locale.

Additionally, it provides various degrees of monoid structure:
* `add_submonoid.has_one`
* `add_submonoid.has_mul`
* `add_submonoid.mul_one_class`
* `add_submonoid.semigroup`
* `add_submonoid.monoid`
which is available globally to match the monoid structure implied by `submodule.idem_semiring`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `algebra/pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `set`s.

-/

open set

variables {α : Type*} {G : Type*} {M : Type*} {R : Type*} {A : Type*}
variables [monoid M] [add_monoid A]


/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/
namespace submonoid
open_locale pointwise

variables {s t u : set M}

@[to_additive]
lemma mul_subset {S : submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
by { rintro _ ⟨p, q, hp, hq, rfl⟩, exact submonoid.mul_mem _ (hs hp) (ht hq) }

@[to_additive]
lemma mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ submonoid.closure u :=
mul_subset (subset.trans hs submonoid.subset_closure) (subset.trans ht submonoid.subset_closure)

@[to_additive]
lemma coe_mul_self_eq (s : submonoid M) : (s : set M) * s = s :=
begin
  ext x,
  refine ⟨_, λ h, ⟨x, 1, h, s.one_mem, mul_one x⟩⟩,
  rintro ⟨a, b, ha, hb, rfl⟩,
  exact s.mul_mem ha hb
end

@[to_additive]
lemma closure_mul_le (S T : set M) : closure (S * T) ≤ closure S ⊔ closure T :=
Inf_le $ λ x ⟨s, t, hs, ht, hx⟩, hx ▸ (closure S ⊔ closure T).mul_mem
    (set_like.le_def.mp le_sup_left $ subset_closure hs)
    (set_like.le_def.mp le_sup_right $ subset_closure ht)

@[to_additive]
lemma sup_eq_closure (H K : submonoid M) : H ⊔ K = closure (H * K) :=
le_antisymm
  (sup_le
    (λ h hh, subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩)
    (λ k hk, subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩))
  (by conv_rhs { rw [← closure_eq H, ← closure_eq K] }; apply closure_mul_le)

@[to_additive]
lemma pow_smul_mem_closure_smul {N : Type*} [comm_monoid N] [mul_action M N]
  [is_scalar_tower M N N] (r : M) (s : set N) {x : N} (hx : x ∈ closure s) :
  ∃ n : ℕ, r ^ n • x ∈ closure (r • s) :=
begin
  apply @closure_induction N _ s
    (λ (x : N), ∃ n : ℕ, r ^ n • x ∈ closure (r • s)) _ hx,
  { intros x hx,
    exact ⟨1, subset_closure ⟨_, hx, by rw pow_one⟩⟩ },
  { exact ⟨0, by simpa using one_mem _⟩ },
  { rintro x y ⟨nx, hx⟩ ⟨ny, hy⟩,
    use nx + ny,
    convert mul_mem hx hy,
    rw [pow_add, smul_mul_assoc, mul_smul, mul_comm, ← smul_mul_assoc, mul_comm] }
end

variables [group G]

open_locale pointwise

/-- The submonoid with every element inverted. -/
@[to_additive /-" The additive submonoid with every element negated. "-/]
protected def has_inv : has_inv (submonoid G) :=
{ inv := λ S,
  { carrier := (S : set G)⁻¹,
    one_mem' := show (1 : G)⁻¹ ∈ S, by { rw inv_one, exact S.one_mem },
    mul_mem' := λ a b (ha : a⁻¹ ∈ S) (hb : b⁻¹ ∈ S), show (a * b)⁻¹ ∈ S,
      by { rw mul_inv_rev, exact S.mul_mem hb ha } } }

localized "attribute [instance] submonoid.has_inv" in pointwise
open_locale pointwise

@[simp, to_additive] lemma coe_inv (S : submonoid G) : ↑(S⁻¹) = (S : set G)⁻¹ := rfl

@[simp, to_additive] lemma mem_inv {g : G} {S : submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S := iff.rfl

@[to_additive] instance : has_involutive_inv (submonoid G) :=
set_like.coe_injective.has_involutive_inv _ $ λ _, rfl

@[simp, to_additive] lemma inv_le_inv (S T : submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
set_like.coe_subset_coe.symm.trans set.inv_subset_inv

@[to_additive] lemma inv_le (S T : submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
set_like.coe_subset_coe.symm.trans set.inv_subset

/-- `submonoid.has_inv` as an order isomorphism. -/
@[to_additive /-" `add_submonoid.has_neg` as an order isomorphism "-/, simps]
def inv_order_iso : submonoid G ≃o submonoid G :=
{ to_equiv := equiv.inv _,
  map_rel_iff' := inv_le_inv }

@[to_additive] lemma closure_inv (s : set G) : closure s⁻¹ = (closure s)⁻¹ :=
begin
  apply le_antisymm,
  { rw [closure_le, coe_inv, ←set.inv_subset, inv_inv],
    exact subset_closure },
  { rw [inv_le, closure_le, coe_inv, ←set.inv_subset],
    exact subset_closure }
end

@[simp, to_additive]
lemma inv_inf (S T : submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ :=
set_like.coe_injective set.inter_inv

@[simp, to_additive]
lemma inv_sup (S T : submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹ :=
(inv_order_iso : submonoid G ≃o submonoid G).map_sup S T

@[simp, to_additive]
lemma inv_bot : (⊥ : submonoid G)⁻¹ = ⊥ :=
set_like.coe_injective $ (set.inv_singleton 1).trans $ congr_arg _ inv_one

@[simp, to_additive]
lemma inv_top : (⊤ : submonoid G)⁻¹ = ⊤ :=
set_like.coe_injective $ set.inv_univ

@[simp, to_additive]
lemma inv_infi {ι : Sort*} (S : ι → submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
(inv_order_iso : submonoid G ≃o submonoid G).map_infi _

@[simp, to_additive]
lemma inv_supr {ι : Sort*} (S : ι → submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
(inv_order_iso : submonoid G ≃o submonoid G).map_supr _

end submonoid

namespace submonoid

section monoid
variables [monoid α] [mul_distrib_mul_action α M]

/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (submonoid M) :=
{ smul := λ a S, S.map (mul_distrib_mul_action.to_monoid_End _ M a),
  one_smul := λ S, by { ext, simp, },
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f : monoid.End M, S.map f) (monoid_hom.map_mul _ _ _)).trans
      (S.map_map _ _).symm,}

localized "attribute [instance] submonoid.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : submonoid M) : ↑(a • S) = a • (S : set M) := rfl

lemma smul_mem_pointwise_smul (m : M) (a : α) (S : submonoid M) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set M))

lemma mem_smul_pointwise_iff_exists (m : M) (a : α) (S : submonoid M) :
  m ∈ a • S ↔ ∃ (s : M), s ∈ S ∧ a • s = m :=
(set.mem_smul_set : m ∈ a • (S : set M) ↔ _)

@[simp] lemma smul_bot (a : α) : a • (⊥ : submonoid M) = ⊥ := map_bot _
lemma smul_sup (a : α) (S T : submonoid M) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

lemma smul_closure (a : α) (s : set M) : a • closure s = closure (a • s) :=
monoid_hom.map_mclosure _ _

instance pointwise_central_scalar [mul_distrib_mul_action αᵐᵒᵖ M] [is_central_scalar α M] :
  is_central_scalar α (submonoid M) :=
⟨λ a S, congr_arg (λ f : monoid.End M, S.map f) $ monoid_hom.ext $ by exact op_smul_eq_smul _⟩

end monoid

section group
variables [group α] [mul_distrib_mul_action α M]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : submonoid M} {x : M} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : submonoid M} {x : M} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : submonoid M} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_subset_iff {a : α} {S T : submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma subset_pointwise_smul_iff {a : α} {S T : submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [mul_distrib_mul_action α M]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : submonoid M)
  (x : M) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set M) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : submonoid M) (x : M) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set M) x

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : submonoid M) (x : M) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set M) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : submonoid M} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

open_locale pointwise

@[to_additive]
lemma mem_closure_inv {G : Type*} [group G] (S : set G) (x : G) :
  x ∈ submonoid.closure S⁻¹ ↔ x⁻¹ ∈ submonoid.closure S :=
by rw [closure_inv, mem_inv]

end submonoid

namespace add_submonoid

section monoid
variables [monoid α] [distrib_mul_action α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action α (add_submonoid A) :=
{ smul := λ a S, S.map (distrib_mul_action.to_add_monoid_End _ A a),
  one_smul := λ S, (congr_arg (λ f : add_monoid.End A, S.map f)
    (monoid_hom.map_one _)).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f : add_monoid.End A, S.map f) (monoid_hom.map_mul _ _ _)).trans
      (S.map_map _ _).symm,}

localized "attribute [instance] add_submonoid.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (a : α) (S : add_submonoid A) : ↑(a • S) = a • (S : set A) := rfl

lemma smul_mem_pointwise_smul (m : A) (a : α) (S : add_submonoid A) : m ∈ S → a • m ∈ a • S :=
(set.smul_mem_smul_set : _ → _ ∈ a • (S : set A))

lemma mem_smul_pointwise_iff_exists (m : A) (a : α) (S : add_submonoid A) :
  m ∈ a • S ↔ ∃ (s : A), s ∈ S ∧ a • s = m :=
(set.mem_smul_set : m ∈ a • (S : set A) ↔ _)

@[simp] lemma smul_bot (a : α) : a • (⊥ : add_submonoid A) = ⊥ := map_bot _
lemma smul_sup (a : α) (S T : add_submonoid A) : a • (S ⊔ T) = a • S ⊔ a • T := map_sup _ _ _

@[simp] lemma smul_closure (a : α) (s : set A) : a • closure s = closure (a • s) :=
add_monoid_hom.map_mclosure _ _

instance pointwise_central_scalar [distrib_mul_action αᵐᵒᵖ A] [is_central_scalar α A] :
  is_central_scalar α (add_submonoid A) :=
⟨λ a S, congr_arg (λ f : add_monoid.End A, S.map f) $
  add_monoid_hom.ext $ by exact op_smul_eq_smul _⟩

end monoid

section group
variables [group α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff {a : α} {S : add_submonoid A} {x : A} :
  a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff

lemma mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : add_submonoid A} {x : A} :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem

lemma mem_inv_pointwise_smul_iff {a : α} {S : add_submonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff

@[simp] lemma pointwise_smul_le_pointwise_smul_iff {a : α} {S T : add_submonoid A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff

lemma pointwise_smul_le_iff {a : α} {S T : add_submonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff

lemma le_pointwise_smul_iff {a : α} {S T : add_submonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff

end group

section group_with_zero
variables [group_with_zero α] [distrib_mul_action α A]

open_locale pointwise

@[simp] lemma smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : add_submonoid A)
  (x : A) : a • x ∈ a • S ↔ x ∈ S :=
smul_mem_smul_set_iff₀ ha (S : set A) x

lemma mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : add_submonoid A) (x : A) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
mem_smul_set_iff_inv_smul_mem₀ ha (S : set A) x

lemma mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : add_submonoid A) (x : A) :
  x ∈ a⁻¹ • S ↔ a • x ∈ S :=
mem_inv_smul_set_iff₀ ha (S : set A) x

@[simp] lemma pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : add_submonoid A} :
  a • S ≤ a • T ↔ S ≤ T :=
set_smul_subset_set_smul_iff₀ ha

lemma pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : add_submonoid A} :
  a • S ≤ T ↔ S ≤ a⁻¹ • T :=
set_smul_subset_iff₀ ha

lemma le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : add_submonoid A} :
  S ≤ a • T ↔ a⁻¹ • S ≤ T :=
subset_set_smul_iff₀ ha

end group_with_zero

end add_submonoid

/-! ### Elementwise monoid structure of additive submonoids

These definitions are a cut-down versions of the ones around `submodule.has_mul`, as that API is
usually more useful. -/
namespace add_submonoid

open_locale pointwise

section add_monoid_with_one
variables [add_monoid_with_one R]

instance : has_one (add_submonoid R) :=
⟨(nat.cast_add_monoid_hom R).mrange⟩

theorem one_eq_mrange :
  (1 : add_submonoid R) = (nat.cast_add_monoid_hom R).mrange := rfl

lemma nat_cast_mem_one (n : ℕ) : (n : R) ∈ (1 : add_submonoid R) := ⟨_, rfl⟩

@[simp] lemma mem_one {x : R} : x ∈ (1 : add_submonoid R) ↔ ∃ n : ℕ, ↑n = x := iff.rfl

theorem one_eq_closure : (1 : add_submonoid R) = closure {1} :=
begin
  simp only [closure_singleton_eq, mul_one, one_eq_mrange],
  congr' 1 with n,
  simp,
end

theorem one_eq_closure_one_set : (1 : add_submonoid R) = closure 1 := one_eq_closure
end add_monoid_with_one

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring R]

/-- Multiplication of additive submonoids of a semiring R. The additive submonoid `S * T` is the
smallest R-submodule of `R` containing the elements `s * t` for `s ∈ S` and `t ∈ T`. -/
instance : has_mul (add_submonoid R) :=
⟨λ M N, ⨆ s : M, N.map $ add_monoid_hom.mul s.1⟩

theorem mul_mem_mul {M N : add_submonoid R} {m n : R} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
(le_supr _ ⟨m, hm⟩ : _ ≤ M * N) ⟨n, hn, rfl⟩

theorem mul_le {M N P : add_submonoid R} : M * N ≤ P ↔ ∀ (m ∈ M) (n ∈ N), m * n ∈ P :=
⟨λ H m hm n hn, H $ mul_mem_mul hm hn,
λ H, supr_le $ λ ⟨m, hm⟩, map_le_iff_le_comap.2 $ λ n hn, H m hm n hn⟩

@[elab_as_eliminator] protected theorem mul_induction_on
  {M N : add_submonoid R}
  {C : R → Prop} {r : R} (hr : r ∈ M * N)
  (hm : ∀ (m ∈ M) (n ∈ N), C (m * n))
  (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
(@mul_le _ _ _ _ ⟨C, ha, by simpa only [zero_mul] using hm _ (zero_mem _) _ (zero_mem _)⟩).2 hm hr

open_locale pointwise

-- this proof is copied directly from `submodule.span_mul_span`
theorem closure_mul_closure (S T : set R) : closure S * closure T = closure (S * T) :=
begin
  apply le_antisymm,
  { rw mul_le, intros a ha b hb,
    apply closure_induction ha,
    work_on_goal 1 { intros, apply closure_induction hb,
      work_on_goal 1 { intros, exact subset_closure ⟨_, _, ‹_›, ‹_›, rfl⟩ } },
    all_goals { intros, simp only [mul_zero, zero_mul, zero_mem,
        left_distrib, right_distrib, mul_smul_comm, smul_mul_assoc];
      solve_by_elim [add_mem _ _, zero_mem _]
        { max_depth := 4, discharger := tactic.interactive.apply_instance } } },
  { rw closure_le, rintros _ ⟨a, b, ha, hb, rfl⟩,
    exact mul_mem_mul (subset_closure ha) (subset_closure hb) }
end

lemma mul_eq_closure_mul_set (M N : add_submonoid R) : M * N = closure (M * N) :=
by rw [←closure_mul_closure, closure_eq, closure_eq]

@[simp] theorem mul_bot (S : add_submonoid R) : S * ⊥ = ⊥ :=
eq_bot_iff.2 $ mul_le.2 $ λ m hm n hn, by rw [add_submonoid.mem_bot] at hn ⊢; rw [hn, mul_zero]

@[simp] theorem bot_mul (S : add_submonoid R) : ⊥ * S = ⊥ :=
eq_bot_iff.2 $ mul_le.2 $ λ m hm n hn, by rw [add_submonoid.mem_bot] at hm ⊢; rw [hm, zero_mul]

@[mono] theorem mul_le_mul {M N P Q : add_submonoid R} (hmp : M ≤ P) (hnq : N ≤ Q) :
  M * N ≤ P * Q :=
mul_le.2 $ λ m hm n hn, mul_mem_mul (hmp hm) (hnq hn)

theorem mul_le_mul_left {M N P : add_submonoid R} (h : M ≤ N) : M * P ≤ N * P :=
mul_le_mul h (le_refl P)

theorem mul_le_mul_right {M N P : add_submonoid R} (h : N ≤ P) : M * N ≤ M * P :=
mul_le_mul (le_refl M) h

lemma mul_subset_mul {M N : add_submonoid R} : (↑M : set R) * (↑N : set R) ⊆ (↑(M * N) : set R) :=
by { rintros _ ⟨i, j, hi, hj, rfl⟩, exact mul_mem_mul hi hj }

end non_unital_non_assoc_semiring

section non_unital_non_assoc_ring
variables [non_unital_non_assoc_ring R]

/-- `add_submonoid.has_pointwise_neg` distributes over multiplication.

This is available as an instance in the `pointwise` locale. -/
protected def has_distrib_neg : has_distrib_neg (add_submonoid R) :=
{ neg := has_neg.neg,
  neg_mul := λ x y, begin
    refine le_antisymm
      (mul_le.2 $ λ m hm n hn, _)
      ((add_submonoid.neg_le _ _).2 $ mul_le.2 $ λ m hm n hn, _);
    simp only [add_submonoid.mem_neg, ←neg_mul] at *,
    { exact mul_mem_mul hm hn },
    { exact mul_mem_mul (neg_mem_neg.2 hm) hn },
  end,
  mul_neg := λ x y, begin
    refine le_antisymm
      (mul_le.2 $ λ m hm n hn, _)
      ((add_submonoid.neg_le _ _).2 $ mul_le.2 $ λ m hm n hn, _);
    simp only [add_submonoid.mem_neg, ←mul_neg] at *,
    { exact mul_mem_mul hm hn,},
    { exact mul_mem_mul hm (neg_mem_neg.2 hn) },
  end,
  ..add_submonoid.has_involutive_neg }

localized "attribute [instance] add_submonoid.has_distrib_neg" in pointwise

end non_unital_non_assoc_ring

section non_assoc_semiring
variables [non_assoc_semiring R]

instance : mul_one_class (add_submonoid R) :=
{ one := 1,
  mul := (*),
  one_mul := λ M, by rw [one_eq_closure_one_set, ←closure_eq M, closure_mul_closure, one_mul],
  mul_one := λ M, by rw [one_eq_closure_one_set, ←closure_eq M, closure_mul_closure, mul_one] }

end non_assoc_semiring

section non_unital_semiring
variables [non_unital_semiring R]

instance : semigroup (add_submonoid R) :=
{ mul := (*),
  mul_assoc := λ M N P,
    le_antisymm (mul_le.2 $ λ mn hmn p hp,
      suffices M * N ≤ (M * (N * P)).comap (add_monoid_hom.mul_right p), from this hmn,
      mul_le.2 $ λ m hm n hn, show m * n * p ∈ M * (N * P), from
      (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
    (mul_le.2 $ λ m hm np hnp,
      suffices N * P ≤ (M * N * P).comap (add_monoid_hom.mul_left m), from this hnp,
      mul_le.2 $ λ n hn p hp, show m * (n * p) ∈ M * N * P, from
      mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp) }

end non_unital_semiring

section semiring
variables [semiring R]

instance : monoid (add_submonoid R) :=
{ one := 1,
  mul := (*),
  ..add_submonoid.semigroup,
  ..add_submonoid.mul_one_class }

lemma closure_pow (s : set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
| 0 := by rw [pow_zero, pow_zero, one_eq_closure_one_set]
| (n + 1) := by rw [pow_succ, pow_succ, closure_pow, closure_mul_closure]

lemma pow_eq_closure_pow_set (s : add_submonoid R) (n : ℕ) : s ^ n = closure ((s : set R) ^ n) :=
by rw [←closure_pow, closure_eq]

lemma pow_subset_pow {s : add_submonoid R} {n : ℕ} : (↑s : set R)^n ⊆ ↑(s^n) :=
(pow_eq_closure_pow_set s n).symm ▸ subset_closure

end semiring

end add_submonoid

namespace set.is_pwo
variables [ordered_cancel_comm_monoid α] {s : set α}

@[to_additive]
lemma submonoid_closure (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.is_pwo) :
  is_pwo ((submonoid.closure s) : set α) :=
begin
  rw submonoid.closure_eq_image_prod,
  refine (h.partially_well_ordered_on_sublist_forall₂ (≤)).image_of_monotone_on _,
  exact λ l1 hl1 l2 hl2 h12, h12.prod_le_prod' (λ x hx, hpos x $ hl2 x hx)
end

end set.is_pwo
