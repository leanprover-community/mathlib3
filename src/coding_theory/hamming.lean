/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import analysis.normed_space.basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

In this file we define `ham β`, the type synonym of a Pi type with the Hamming distance `ham_dist` and weight `ham_wt` attached, and the various instances that arise
from the properties of these definitions.

-/

open fintype

/--
Type synonym for a Pi type which we equip with the Hamming metric, adding all relevant
instances as needed.
-/
def ham {ι : Type*} (β : ι → Type*) : Type* := Π i, β i

instance {ι : Type*} (β : ι → Type*) [Π i, inhabited (β i)] : inhabited (ham β) :=
⟨λ i, default⟩

local notation `𝓗[` K`,` n`]` := ham (λ _ : fin n, K)

namespace hamming
variables {α ι : Type*} {β : ι → Type*}

/-- `to_ham` is the identity function to the `ham` of a type.  -/
@[pattern] def to_ham : (Π i, β i) ≃ ham β := equiv.refl _

/-- `of_ham` is the identity function from the `ham` of a type.  -/
@[pattern] def of_ham : ham β ≃ Π i, β i := equiv.refl _

@[simp] lemma to_ham_symm_eq                : (@to_ham _ β).symm = of_ham := rfl
@[simp] lemma of_ham_symm_eq                : (@of_ham _ β).symm = to_ham := rfl
@[simp] lemma to_ham_of_ham (x : ham β)     : to_ham (of_ham x) = x := rfl
@[simp] lemma of_ham_to_ham (x : Π i, β i)  : of_ham (to_ham x) = x := rfl
@[simp] lemma to_ham_inj {x y : Π i, β i}   : to_ham x = to_ham y ↔ x = y := iff.rfl
@[simp] lemma of_ham_inj {x y : ham β}      : of_ham x = of_ham y ↔ x = y := iff.rfl

instance [Π i, has_zero (β i)] : has_zero (ham β) := pi.has_zero
instance [Π i, has_sub (β i)] : has_sub (ham β) := pi.has_sub
instance [Π i, has_scalar α (β i)] : has_scalar α (ham β) := pi.has_scalar
instance [has_zero α] [Π i, has_zero (β i)] [Π i, smul_with_zero α (β i)] :
smul_with_zero α (ham β) := pi.smul_with_zero _
instance [Π i, add_monoid (β i)] : add_monoid (ham β) := pi.add_monoid
instance [Π i, add_comm_monoid (β i)] : add_comm_monoid (ham β) := pi.add_comm_monoid
instance [Π i, add_comm_group (β i)] : add_comm_group (ham β) := pi.add_comm_group
instance [semiring α] [Π i, add_comm_monoid (β i)] [Π i, module α (β i)] :
module α (ham β) := pi.module _ _ _

section decidable_eq

variables {β} [fintype ι] [Π i, decidable_eq (β i)]

/--
The Hamming distance function to the naturals.
-/
def ham_dist (x y : ham β) := card {i // x i ≠ y i}

lemma ham_dist_smul_le [Π i, has_scalar α (β i)] (k : α) (x y : ham β) :
ham_dist (k • x) (k • y) ≤ ham_dist x y :=
card_subtype_mono _ _ (λ i h H, h (by rw [pi.smul_apply, pi.smul_apply, H]))

lemma ham_dist_smul [Π i, has_scalar α (β i)] {k : α}
(hk : ∀ i, is_smul_regular (β i) k) (x y : ham β) :
ham_dist x y = ham_dist (k • x) (k • y) :=
le_antisymm (card_subtype_mono _ _ (λ _ h H, h (hk _ H))) (ham_dist_smul_le _ _ _)

lemma ham_dist_eq (x y : ham β) : ham_dist x y = card {i // x i ≠ y i} := rfl

lemma ham_dist_comm (x y : ham β) : ham_dist x y = ham_dist y x :=
by simp_rw [ham_dist_eq, ne_comm]

lemma ham_dist_triangle (x y z : ham β) : ham_dist x z ≤ ham_dist x y + ham_dist y z :=
begin
  simp_rw ham_dist_eq,
  refine le_trans (card_subtype_mono _ _ (λ _ h, _)) (card_subtype_or _ _),
  by_contra' H, exact h (eq.trans H.1 H.2)
end

lemma ham_dist_eq_zero {x y : ham β} : ham_dist x y = 0 ↔ x = y :=
begin
  rw [function.funext_iff, ham_dist_eq, card_eq_zero_iff],
  exact ⟨ λ h i, imp_of_not_imp_not _ _ (λ H, h.elim' ⟨i, H⟩) h,
          λ h, subtype.is_empty_of_false (λ i H, H (h _))⟩
end

lemma ham_dist_self (x : ham β) : ham_dist x x = 0 := ham_dist_eq_zero.mpr rfl

lemma eq_of_ham_dist_eq_zero (x y : ham β) :
ham_dist x y = 0 → x = y := ham_dist_eq_zero.mp

lemma ham_dist_ne_zero {x y : ham β} : ham_dist x y ≠ 0 ↔ x ≠ y :=
not_iff_not.mpr ham_dist_eq_zero

lemma ham_dist_pos {x y : ham β} : 0 < ham_dist x y ↔ x ≠ y :=
by rw [←ham_dist_ne_zero, iff_not_comm, not_lt, nat.le_zero_iff]

lemma ham_dist_eq_zero_iff_forall_eq {x y : ham β} :
ham_dist x y = 0 ↔ ∀ i, x i = y i := by rw [ham_dist_eq_zero, function.funext_iff]

lemma ham_dist_ne_zero_iff_exists_ne {x y : ham β} :
ham_dist x y ≠ 0 ↔ ∃ i, x i ≠ y i := by rw [ham_dist_ne_zero, function.ne_iff]

section has_zero

variable [Π i, has_zero (β i)]

/--
The Hamming weight function to the naturals.
-/
def ham_wt (x : ham β) : ℕ := ham_dist x 0

lemma ham_wt_smul_le [has_zero α] [Π i, smul_with_zero α (β i)] (k : α) (x : ham β) :
ham_wt (k • x) ≤ ham_wt x :=
by rw [ham_wt, ← smul_zero' (ham β) k]; exact ham_dist_smul_le _ _ _

lemma ham_wt_smul [has_zero α] [Π i, smul_with_zero α (β i)] {k : α}
(hk : ∀ i, is_smul_regular (β i) k) (x : ham β) : ham_wt x = ham_wt (k • x) :=
by simp_rw ham_wt; nth_rewrite 1 ← smul_zero' (ham β) k; exact ham_dist_smul hk _ _

lemma ham_wt_eq (x : ham β) : ham_wt x = card {i // x i ≠ 0} := rfl

lemma ham_wt_eq_zero {x : ham β} : ham_wt x = 0 ↔ x = 0 := ham_dist_eq_zero

lemma ham_wt_zero : ham_wt (0 : ham β) = 0 := ham_dist_self _

lemma zero_of_ham_wt_eq_zero (x : ham β) :
ham_wt x = 0 → x = 0 := eq_of_ham_dist_eq_zero _ _

lemma ham_wt_ne_zero {x : ham β} : ham_wt x ≠ 0 ↔ x ≠ 0 := ham_dist_ne_zero

lemma ham_wt_pos {x : ham β} : 0 < ham_wt x ↔ x ≠ 0 := ham_dist_pos

lemma ham_wt_zero_iff_forall_zero {x : ham β} : ham_wt x = 0 ↔ ∀ i, x i = 0 :=
ham_dist_eq_zero_iff_forall_eq

lemma ham_wt_pos_iff_exists_nz {x : ham β} : ham_wt x ≠ 0 ↔ ∃ i, x i ≠ 0 :=
ham_dist_ne_zero_iff_exists_ne

end has_zero

lemma ham_dist_eq_ham_wt_sub [Π i, add_group (β i)] (x y : ham β) :
ham_dist x y = ham_wt (x - y) :=
by simp_rw [ham_dist_eq, ham_wt_eq, pi.sub_apply, sub_ne_zero]

instance : has_dist (ham β) := ⟨λ x y, ham_dist x y⟩

@[simp, push_cast] lemma dist_eq_ham_dist (x y : ham β) :
dist x y = ham_dist x y := rfl

instance : pseudo_metric_space (ham β) :=
{ dist_self           := by push_cast; exact_mod_cast ham_dist_self,
  dist_comm           := by push_cast; exact_mod_cast ham_dist_comm,
  dist_triangle       := by push_cast; exact_mod_cast ham_dist_triangle,
  ..ham.has_dist }

instance : metric_space (ham β) :=
{ eq_of_dist_eq_zero  := by push_cast; exact_mod_cast eq_of_ham_dist_eq_zero,
  ..ham.pseudo_metric_space }

instance [Π i, has_zero (β i)] : has_norm (ham β) := ⟨λ x, ham_wt x⟩

@[simp, push_cast] lemma norm_eq_ham_wt [Π i, has_zero (β i)] (x : ham β) :
∥x∥ = ham_wt x := rfl

instance [Π i, add_comm_group (β i)] : semi_normed_group (ham β) :=
{ dist_eq := by push_cast; exact_mod_cast ham_dist_eq_ham_wt_sub, ..pi.add_comm_group }

instance [Π i, add_comm_group (β i)] : normed_group (ham β) :=
{ ..ham.semi_normed_group }

/-
Want something like this:
instance [Π i, add_comm_group (β i)] {α : Type*} [normed_field α]
[Π i, module α (β i)] : normed_space α (ham β) := sorry

But this isn't true. There is no existing structure tha
 captures properties like ham_wt_smul_le.

This is unfortunate - because the module structure ought to
combine with the metric structure!
-/

end decidable_eq

end hamming
#lint
