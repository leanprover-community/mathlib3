/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.heyting.basic

/-!
# Co-Heyting boundary

The boundary of an element of a co-Heyting algebra is the intersection of its Heyting negation with
itself. The boundary in the co-Heyting algebra of closed sets coincides with the topological
boundary. s ∪ t s ∩ t

## Main declarations

* `coheyting.boundary`: Co-Heyting boundary. `coheyting.boundary a = a ⊓ ￢a`

## Notation

`∂ a` is notation for `coheyting.boundary a` in locale `heyting`.
-/

variables {α : Type*} [coheyting_algebra α] {a b : α}

namespace coheyting

def boundary (a : α) : α := a ⊓ ￢a

localized "prefix `∂ `:120 := coheyting.boundary" in heyting

lemma inf_hnot_self (a : α) : a ⊓ ￢a = ∂ a := rfl

lemma boundary_le : ∂ a ≤ a := inf_le_left
lemma boundary_le_hnot : ∂ a ≤ ￢a := inf_le_right

@[simp] lemma boundary_bot : ∂ (⊥ : α) = ⊥ := bot_inf_eq
@[simp] lemma boundary_top : ∂ (⊤ : α) = ⊥ := by rw [boundary, hnot_top, inf_bot_eq]

lemma boundary_hnot_le (a : α) : ∂ ￢a ≤ ∂ a := inf_comm.trans_le $ inf_le_inf_right _ hnot_hnot_le

@[simp] lemma boundary_hnot_hnot (a : α) : ∂ ￢￢a = ∂ ￢a :=
by simp_rw [boundary, hnot_hnot_hnot, inf_comm]

lemma hnot_boundary (a : α) : ￢ ∂ a = ￢a ⊔ ￢￢a := hnot_inf_distrib _ _

/-- **Leibniz rule** for the co-Heyting boundary. -/
lemma boundary_inf (a b : α) : ∂ (a ⊓ b) = ∂ a ⊓ b ⊔ a ⊓ ∂ b :=
by { unfold boundary, rw [hnot_inf_distrib, inf_sup_left, inf_right_comm, ←inf_assoc] }

lemma boundary_inf_le : ∂ (a ⊓ b) ≤ ∂ a ⊔ ∂ b :=
(boundary_inf _ _).trans_le $ sup_le_sup inf_le_left inf_le_right

lemma boundary_sup_le : ∂ (a ⊔ b) ≤ ∂ a ⊔ ∂ b :=
begin
  rw [boundary, inf_sup_right],
  exact sup_le_sup (inf_le_inf_left _ $ hnot_anti le_sup_left)
    (inf_le_inf_left _ $ hnot_anti le_sup_right),
end

/- The intuitionistic version of `coheyting.boundary_le_boundary_sup_sup_boundary_inf_left`. Either
proof can be obtained from the other using the equivalence of Heyting algebras and intuitionistic
logic and duality between Heyting and co-Heyting algebras. It is crucial that the following proof be
intuitionistic. -/
example (a b : Prop) : ((a ∧ b) ∨ ¬(a ∧ b)) ∧ ((a ∨ b) ∨ ¬ (a ∨ b)) → a ∨ ¬ a :=
begin
  rintro ⟨⟨ha, hb⟩ | hnab, (ha | hb) | hnab⟩;
    try { exact or.inl ha },
  { exact or.inr (λ ha, hnab ⟨ha, hb⟩) },
  { exact or.inr (λ ha, hnab $ or.inl ha) }
end

lemma boundary_le_boundary_sup_sup_boundary_inf_left : ∂ a ≤ ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) :=
begin
  simp only [boundary, sup_inf_left, sup_inf_right, sup_right_idem, le_inf_iff, sup_assoc,
    @sup_comm _ _ _ a],
  refine ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩, _⟩;
    try { exact le_sup_of_le_left inf_le_left };
    refine inf_le_of_right_le _,
  { rw [hnot_le_iff_codisjoint_right, codisjoint_left_comm],
    exact codisjoint_hnot_left },
  { refine le_sup_of_le_right _,
    rw hnot_le_iff_codisjoint_right,
    exact codisjoint_hnot_right.mono_right (hnot_anti inf_le_left) }
end

lemma boundary_le_boundary_sup_sup_boundary_inf_right : ∂ b ≤ ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) :=
by { rw [@sup_comm _ _ a, inf_comm], exact boundary_le_boundary_sup_sup_boundary_inf_left }

lemma boundary_sup_sup_boundary_inf (a b : α) : ∂ (a ⊔ b) ⊔ ∂ (a ⊓ b) = ∂ a ⊔ ∂ b :=
le_antisymm (sup_le boundary_sup_le boundary_inf_le) $ sup_le
  boundary_le_boundary_sup_sup_boundary_inf_left boundary_le_boundary_sup_sup_boundary_inf_right

lemma boundary_idem (a : α) : ∂ ∂ a = ∂ a :=
by { rw [boundary, hnot_boundary, inf_eq_left], exact inf_le_right.trans le_sup_left }

lemma hnot_hnot_sup_boundary (a : α) : ￢￢a ⊔ ∂ a = a :=
by { rw [boundary, sup_inf_left, hnot_sup_self, inf_top_eq, sup_eq_right], exact hnot_hnot_le }

end coheyting
