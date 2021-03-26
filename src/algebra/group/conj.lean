/-
Copyright (c) 2018  Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import algebra.group.hom
import algebra.group.semiconj
import data.equiv.mul_add_aut

/-!
# Conjugacy of group elements

See also `mul_aut.conj` and `quandle.conj`.
-/

universes u v
variables {α : Type u} {β : Type v}

section monoid

variables [monoid α] [monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def is_conj (a b : α) := ∃ c : units α, semiconj_by ↑c a b

@[refl] lemma is_conj_refl (a : α) : is_conj a a :=
⟨1, semiconj_by.one_left a⟩

@[symm] lemma is_conj_symm {a b : α} : is_conj a b → is_conj b a
| ⟨c, hc⟩ := ⟨c⁻¹, hc.units_inv_symm_left⟩

@[trans] lemma is_conj_trans {a b c : α} : is_conj a b → is_conj b c → is_conj a c
| ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ := ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

@[simp] lemma is_conj_iff_eq {α : Type*} [cancel_comm_monoid α] {a b : α} : is_conj a b ↔ a = b :=
⟨λ ⟨c, hc⟩, semiconj_by_iff_eq.1 hc, λ h, by rw h⟩

protected lemma monoid_hom.map_is_conj (f : α →* β) {a b : α} : is_conj a b → is_conj (f a) (f b)
| ⟨c, hc⟩ := ⟨units.map f c, by rw [units.coe_map, semiconj_by, ← f.map_mul, hc.eq, f.map_mul]⟩

end monoid

section group

variables [group α] [group β]

@[simp] lemma is_conj_iff {a b : α} :
  is_conj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
⟨λ ⟨c, hc⟩, ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, λ ⟨c, hc⟩,
  ⟨⟨c, c⁻¹, mul_inv_self c, inv_mul_self c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[simp] lemma is_conj_one_right {a : α} : is_conj 1 a  ↔ a = 1 :=
⟨λ ⟨c, hc⟩, mul_right_cancel (hc.symm.trans ((mul_one _).trans (one_mul _).symm)), λ h, by rw [h]⟩

@[simp] lemma is_conj_one_left {a : α} : is_conj a 1 ↔ a = 1 :=
calc is_conj a 1 ↔ is_conj 1 a : ⟨is_conj_symm, is_conj_symm⟩
... ↔ a = 1 : is_conj_one_right

@[simp] lemma conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
((mul_aut.conj b).map_inv a).symm

@[simp] lemma conj_mul {a b c : α} : (b * a * b⁻¹) * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
((mul_aut.conj b).map_mul a c).symm

lemma conj_injective {x : α} : function.injective (λ (g : α), x * g * x⁻¹) :=
(mul_aut.conj x).injective

end group
