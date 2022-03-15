/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.valuation.integers
import ring_theory.ideal.local_ring

/-!
# Valuation Rings

-/

class valuation_ring (A : Type*) [comm_ring A] [is_domain A] : Prop :=
(cond [] : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a)

variables (A : Type*) [comm_ring A] [is_domain A] [valuation_ring A]

namespace valuation_ring

instance : local_ring A :=
begin
  constructor,
  intros a,
  obtain ⟨c,(h|h)⟩ := valuation_ring.cond a (1-a),
  { left,
    apply is_unit_of_mul_eq_one _ (c+1),
    simp [mul_add, h] },
  { right,
    apply is_unit_of_mul_eq_one _ (c+1),
    simp [mul_add, h] }
end

instance [decidable_rel ((≤) : ideal A → ideal A → Prop)] : linear_order (ideal A) :=
{ le_total := begin
    intros α β,
    by_cases h : α ≤ β, { exact or.inl h },
    erw not_forall at h,
    push_neg at h,
    obtain ⟨a,h₁,h₂⟩ := h,
    right,
    intros b hb,
    obtain ⟨c,(h|h)⟩ := valuation_ring.cond a b,
    { rw ← h,
      exact ideal.mul_mem_right _ _ h₁ },
    { exfalso, apply h₂, rw ← h,
      apply ideal.mul_mem_right _ _ hb },
  end,
  decidable_le := infer_instance,
  ..(infer_instance : complete_lattice (ideal A)) }

end valuation_ring
