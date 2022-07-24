/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Georgi Kocharyan.
-/
import algebra.big_operators
import topology.metric_space.emetric_space
import topology.metric_space.isometry

open classical metric
open_locale big_operators pointwise

class isom_action (α β : Type*) [monoid α] [pseudo_metric_space β] extends mul_action α β :=
(isom : ∀ g : α, isometry ((•) g : β → β))

section monoid
variables {α β : Type*} [monoid α] [pseudo_metric_space β] [isom_action α β]

lemma isometry_smul : ∀ g : α, isometry (λ x : β, g • x) := isom_action.isom

@[simp] lemma dist_smul_smul (g : α) (x y : β) : dist (g • x) (g • y) = dist x y :=
(isometry_smul g).dist_eq _ _

variables [group α]

lemma dist_smul_inv (g : α) (h : α) (x y : β) : dist (g • x) (h • y) = dist x ((g⁻¹*h) • y) :=
sorry



@[simp] lemma diam_smul (g : α) (s : set β) : diam (g • s) = diam s :=
(isom_action.isom g).diam_image _

end monoid

section group
variables {α β : Type*} [group α] [pseudo_metric_space β] [isom_action α β]

lemma dist_of_inv_isom (g h : α) (x y : β) : dist (g • x) (h • y) = dist x ((g⁻¹*h) • y) :=
begin
  have k : dist (g • x) (h • y) = dist ((g⁻¹*g) • x) ((g⁻¹ * h) • y),
  { repeat {rw ← smul_smul,},
    rw dist_smul_smul g⁻¹ },
  rw k,
  simp,
end

end group

theorem isom_img_mul{α β : Type*} [group α] [pseudo_metric_space β] [isom_action α β]
  (g : α) (s : set β) (x : β) (hx : x ∈ g • s ) (h : α) : h • x ∈ (h * g) • s :=
by { obtain ⟨z, hz, rfl⟩ := hx, exact ⟨z, hz, mul_smul _ _ _⟩ }

-- This is basically `metric.cthickening`
def set_closed_ball {α : Type*} [pseudo_metric_space α] (s : set α) (ε : ℝ) : set α :=
{y : α | ∃ x : α, x ∈ s ∧ dist y x ≤ ε}

lemma self_set_closed_ball {α : Type*} [pseudo_metric_space α] (s : set α) (ε : ℝ) (enonneg : 0 ≤ ε)
  (x : α) (hx : x ∈ s) :
  x ∈ set_closed_ball s ε :=
⟨x, hx, by rwa dist_self⟩

theorem isom_of_set_closed_ball {α β : Type*} [group α] [pseudo_metric_space β] [isom_action α β]
  (s : set β) (g : α) (ε : ℝ) :
  g • (set_closed_ball s ε) = set_closed_ball (g • s) ε :=
begin
  refine subset_antisymm _ _,
  { rintro x ⟨y, ⟨z, hz, hyz⟩, rfl⟩,
    exact ⟨g • z, ⟨z, hz, rfl⟩, by rwa dist_smul_smul⟩ },
-- before here could have had α monoid
  rintro x ⟨y, ⟨z, hz, rfl⟩, hy⟩,
  exact ⟨g⁻¹ • x, ⟨z, hz, by rwa [←inv_smul_smul g z, dist_smul_smul]⟩, smul_inv_smul _ _⟩,
end

theorem diam_of_ball_of_diam {α : Type*} [pseudo_metric_space α] (B : set α) (ε : ℝ) (epos: 0 ≤ ε) :
  diam (set_closed_ball B ε) ≤ 2*ε + diam B :=
begin
  apply diam_le_of_forall_dist_le,
  linarith [@diam_nonneg _ _ B],
  rintro x ⟨a, ha, hxa⟩ y ⟨b, hb, hyb⟩,
  calc
    dist x y ≤ dist x a + dist y b + dist a b : dist_triangle4_right _ _ _ _
    ...      ≤ ε + ε + diam B : add_le_add_three hxa hyb $ dist_le_diam_of_mem sorry ha hb
    ...      ≤ 2*ε + diam B : by linarith
end

def proper_action_set (α : Type*) {β : Type*} [monoid α] [pseudo_metric_space β]
  [isom_action α β] (s : set β) : set α :=
   {g : α | s ∩ g • s ≠ ∅}

def translates_cover (α : Type*) {β : Type*} [monoid α] [pseudo_metric_space β] [isom_action α β]
  (s : set β) : Prop :=
∀ x : β, x ∈ ⋃ g : α, g • s

theorem exists_cover_element{α β : Type*} [monoid α] [pseudo_metric_space β] [isom_action α β]
  {s : set β} (h : translates_cover α s) (x : β) : ∃ g : α, x ∈ g • s :=
set.mem_Union.1 (h _)

noncomputable def cover_element{α β : Type*} [monoid α] [pseudo_metric_space β] [isom_action α β]
  {s : set β} (h : translates_cover α s) (x : β) : α :=
classical.some (exists_cover_element h x)
