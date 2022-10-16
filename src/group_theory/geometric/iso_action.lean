/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgi Kocharyan
-/
import analysis.normed.group.basic
import topology.metric_space.isometry
import .mathlib

open classical metric set
open_locale big_operators pointwise

variables {α β E : Type*}

class iso_add_action (α β : Type*) [add_monoid α] [pseudo_metric_space β] extends add_action α β :=
(iso_vadd : ∀ g : α, isometry ((+ᵥ) g : β → β))

@[to_additive]
class iso_mul_action (α β : Type*) [monoid α] [pseudo_metric_space β] extends mul_action α β :=
(iso_smul : ∀ g : α, isometry ((•) g : β → β))

section monoid
variables [monoid α] [pseudo_metric_space β] [iso_mul_action α β]

@[to_additive] lemma isometry_smul : ∀ g : α, isometry ((•) g : β → β) := iso_mul_action.iso_smul

@[simp, to_additive] lemma dist_smul_smul (g : α) (x y : β) : dist (g • x) (g • y) = dist x y :=
(isometry_smul g).dist_eq _ _

@[simp, to_additive] lemma diam_smul (g : α) (s : set β) : diam (g • s) = diam s :=
(isometry_smul g).diam_image _

end monoid

section group
variables [group α] [pseudo_metric_space β] [iso_mul_action α β]

@[to_additive]
lemma dist_inv_smul_left (g : α) (x y : β) : dist (g⁻¹ • x) y = dist x (g • y) :=
by rw [←dist_smul_smul g, smul_inv_smul]

@[to_additive]
lemma dist_inv_smul_right (g : α) (x y : β) : dist x (g⁻¹ • y) = dist (g • x) y :=
by rw [←dist_smul_smul g, smul_inv_smul]

end group

@[to_additive, priority 100] -- See note [lower instance priority]
instance seminormed_group.to_iso_mul_action [seminormed_group E] : iso_mul_action Eᵐᵒᵖ E :=
{ iso_smul := λ a, isometry.of_dist_eq $ λ _ _, dist_mul_right _ _ _ }

@[to_additive, priority 100] -- See note [lower instance priority]
instance seminormed_comm_group.to_iso_mul_action [seminormed_comm_group E] : iso_mul_action E E :=
{ iso_smul := λ a, isometry.of_dist_eq $ dist_mul_left _ }

instance additive.iso_add_action [monoid α] [pseudo_metric_space β] [iso_mul_action α β] :
  iso_add_action (additive α) β :=
{ iso_vadd := isometry_smul }

instance multiplicative.iso_mul_action [add_monoid α] [pseudo_metric_space β] [iso_add_action α β] :
  iso_mul_action (multiplicative α) β :=
{ iso_smul := isometry_vadd }

instance [add_group_with_one α] [pseudo_metric_space α] : iso_add_action ℕ α :=
{ iso_vadd := λ n, isometry.of_dist_eq $ λ a b, by simp }

@[simp] lemma vadd_def (n : ℕ) (a : α) : n +ᵥ a = ↑n + a := rfl

end nat

namespace int
variables {α : Type*} [add_group_with_one α]

instance : add_action ℤ α := add_action.comp_hom _ $ int.cast_add_hom α

@[simp] lemma vadd_def (n : ℤ) (a : α) : n +ᵥ a = ↑n + a := rfl

end int

namespace rat
variables {α : Type*} [division_ring α] [char_zero α]

instance : add_action ℚ α := add_action.comp_hom _ $ (rat.cast_hom α).to_add_monoid_hom

@[simp] lemma vadd_def (q : ℚ) (a : α) : q +ᵥ a = ↑q + a := rfl

end rat

-- This is basically `metric.cthickening`
def set_closed_ball [pseudo_metric_space α] (s : set α) (ε : ℝ) : set α :=
{y : α | ∃ x : α, x ∈ s ∧ dist y x ≤ ε}

lemma self_set_closed_ball [pseudo_metric_space α] (s : set α) (ε : ℝ) (enonneg : 0 ≤ ε)
  (x : α) (hx : x ∈ s) :
  x ∈ set_closed_ball s ε :=
⟨x, hx, by rwa dist_self⟩

theorem isom_of_set_closed_ball [group α] [pseudo_metric_space β] [iso_mul_action α β]
  (s : set β) (g : α) (ε : ℝ) :
  g • set_closed_ball s ε = set_closed_ball (g • s) ε :=
begin
  refine subset_antisymm _ _,
  { rintro x ⟨y, ⟨z, hz, hyz⟩, rfl⟩,
    exact ⟨g • z, ⟨z, hz, rfl⟩, by rwa dist_smul_smul⟩ },
-- before here could have had α monoid
  rintro x ⟨y, ⟨z, hz, rfl⟩, hy⟩,
  exact ⟨g⁻¹ • x, ⟨z, hz, by rwa [←inv_smul_smul g z, dist_smul_smul]⟩, smul_inv_smul _ _⟩,
end

theorem diam_of_ball_of_diam [pseudo_metric_space α] (B : set α) (ε : ℝ) (epos: 0 ≤ ε) :
  diam (set_closed_ball B ε) ≤ 2*ε + diam B :=
begin
  refine diam_le_of_forall_dist_le _ _,
  linarith [@diam_nonneg _ _ B],
  rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩,
  calc
    dist x y ≤ dist x a + dist y b + dist a b : dist_triangle4_right _ _ _ _
    ...      ≤ ε + ε + diam B : add_le_add_three hxa hyb $ dist_le_diam_of_mem sorry ha hb
    ...      ≤ 2*ε + diam B : by linarith
end

variables (α) [group α]

section mul_action
variables [mul_action α β] (s : set β)

def proper_action_set : set α := {g : α | (s ∩ g • s).nonempty}

def translates_cover : Prop := ∀ x : β, ∃ g : α, x ∈ g • s

variables {α s} {g : α} {b : ℝ} {x : β}

lemma mem_proper_action_set : g ∈ proper_action_set α s ↔ (s ∩ g • s).nonempty := iff.rfl

@[simp] lemma inv_mem_proper_action_set : g⁻¹ ∈ proper_action_set α s ↔ g ∈ proper_action_set α s :=
by rw [mem_proper_action_set, mem_proper_action_set, ←@smul_set_nonempty _ _ _ _ g, smul_set_inter,
  smul_inv_smul, inter_comm]

lemma translates_cover.Union_eq (hs : translates_cover α s) : (⋃ g : α, g • s) = univ :=
eq_univ_of_forall $ λ x, mem_Union.2 $ hs _

protected lemma translates_cover.nonempty [nonempty β] (hs : translates_cover α s) : s.nonempty :=
let ⟨x⟩ := ‹nonempty β›, ⟨g, hx⟩ := hs x in smul_set_nonempty.1 ⟨x, hx⟩

end mul_action

variables (α) [pseudo_metric_space β] [iso_mul_action α β] {s : set β} {g : α} {b : ℝ} {x : β}

/-- There is a constant bounding the distance between `x` and `t • x` for all `t` in the generating
set. -/
lemma proper_action_set_bound (hb : 0 ≤ b) (finitediam : bounded s) (xs : x ∈ s) :
  ∃ k, 0 < k ∧ ∀ t ∈ proper_action_set α (set_closed_ball s (2 * b)), dist x (t • x) ≤ k :=
begin
  obtain ⟨k, hk⟩ := finitediam,
  have knonneg : 0 ≤ k := dist_nonneg.trans (hk x xs x xs),
  refine ⟨2 * (k + 2 * b) + 1, by positivity, _⟩,
  rintro _ ⟨y, ⟨z, zs, hz⟩, a, ⟨m, ms, hm⟩, rfl⟩,
  have dxy := (dist_triangle_right _ _ _).trans (add_le_add (hk x xs z zs) hz),
  have dyt : dist (t • a) (t • x) ≤ k + 2*b,
  { rw [dist_smul_smul, dist_comm],
    exact le_trans (dist_triangle_right _ _ _) (add_le_add (hk x xs m ms) hm) },
  refine (dist_triangle _ (t • a) _).trans _,
  linarith,
end
