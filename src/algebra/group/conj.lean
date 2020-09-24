/-
Copyright (c) 2018  Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import algebra.group.hom
import data.equiv.basic

/-!
# Conjugacy of group elements
-/

universes u v
variables {α : Type u} {β : Type v}

variables [group α] [group β]

/-- We say that `a` is conjugate to `b` if for some `c` we have `c * a * c⁻¹ = b`. -/
def is_conj (a b : α) := ∃ c : α, c * a * c⁻¹ = b

@[refl] lemma is_conj_refl (a : α) : is_conj a a :=
⟨1, by rw [one_mul, one_inv, mul_one]⟩

@[symm] lemma is_conj_symm {a b : α} : is_conj a b → is_conj b a
| ⟨c, hc⟩ := ⟨c⁻¹, by rw [← hc, mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left]⟩

@[trans] lemma is_conj_trans {a b c : α} : is_conj a b → is_conj b c → is_conj a c
| ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ := ⟨c₂ * c₁, by rw [← hc₂, ← hc₁, mul_inv_rev]; simp only [mul_assoc]⟩

@[simp] lemma is_conj_one_right {a : α} : is_conj 1 a  ↔ a = 1 :=
⟨by simp [is_conj, is_conj_refl] {contextual := tt}, by simp [is_conj_refl] {contextual := tt}⟩

@[simp] lemma is_conj_one_left {a : α} : is_conj a 1 ↔ a = 1 :=
calc is_conj a 1 ↔ is_conj 1 a : ⟨is_conj_symm, is_conj_symm⟩
... ↔ a = 1 : is_conj_one_right

@[simp] lemma conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
begin
  rw [mul_inv_rev _ b⁻¹, mul_inv_rev b _, inv_inv, mul_assoc],
end

@[simp] lemma conj_mul {a b c : α} : (b * a * b⁻¹) * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
begin
  assoc_rw inv_mul_cancel_right,
  repeat {rw mul_assoc},
end

@[simp] lemma is_conj_iff_eq {α : Type*} [comm_group α] {a b : α} : is_conj a b ↔ a = b :=
⟨λ ⟨c, hc⟩, by rw [← hc, mul_right_comm, mul_inv_self, one_mul], λ h, by rw h⟩

protected lemma monoid_hom.map_is_conj (f : α →* β) {a b : α} : is_conj a b → is_conj (f a) (f b)
| ⟨c, hc⟩ := ⟨f c, by rw [← f.map_mul, ← f.map_inv, ← f.map_mul, hc]⟩

namespace group

/--
Inner automorphisms of a group.
-/
def inner_aut (c : α) : α →* α :=
{ to_fun := λ x, c * x * c⁻¹,
  map_one' := by simp,
  map_mul' := by simp }

lemma inner_aut_left_inv (c : α) : function.left_inverse (inner_aut c⁻¹) (inner_aut c) :=
by { intro x, dsimp [inner_aut], rw inv_inv,
     apply mul_eq_of_eq_mul_inv, apply inv_mul_eq_of_eq_mul, apply mul_assoc, }

lemma inner_aut_right_inv (c : α) : function.right_inverse (inner_aut c⁻¹) (inner_aut c) :=
by { convert inner_aut_left_inv c⁻¹, rw inv_inv }

/--
The inner automorphism `inner_aut` as an equivalence.
-/
def inner_aut_equiv (c : α) : α ≃ α :=
{ to_fun := inner_aut c,
  inv_fun := inner_aut c⁻¹,
  left_inv := inner_aut_left_inv c,
  right_inv := inner_aut_right_inv c }

end group
