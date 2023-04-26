import analysis.normed.order.basic
import algebra.order.lattice_group

section solid

variables {α : Type*} [add_comm_group α] [lattice α]

def is_solid (s : set α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s

def solid_closure (s : set α) : set α := {x | ∃ y ∈ s, |x| ≤ |y|}

lemma is_solid_solid_closure (s : set α) : is_solid (solid_closure s) :=
λ x ⟨y, hy, hxy⟩ z hzx, ⟨y, hy, hzx.trans hxy⟩

class has_solid_norm (α : Type*) [normed_add_comm_group α] [lattice α] : Prop :=
(solid :  ∀ ⦃x y : α⦄, |x| ≤ |y| → ‖x‖ ≤ ‖y‖)

lemma solid [normed_add_comm_group α] [lattice α] [has_solid_norm α] {a b : α} (h : |a| ≤ |b|) :
  ‖a‖ ≤ ‖b‖ := has_solid_norm.solid h

alias solid ← norm_le_norm_of_abs_le_abs

instance : has_solid_norm ℝ := ⟨λ _ _, id⟩

instance : has_solid_norm ℚ := ⟨λ _ _ _, by simpa only [norm, ← rat.cast_abs, rat.cast_le]⟩

end solid
