/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.valuation.integers
import ring_theory.ideal.local_ring
import ring_theory.localization.fraction_ring
import tactic.field_simp

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[comm_ring A] [is_domain A] [valuation_ring A] [field K] [algebra A K] [is_fraction_ring A K]`,
there is a natural valuation `valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebra_map A K` agrees with `(valuation A K).integer`.

We also show that valuation rings are local and that their lattice of ideals is totally ordered.
-/

/-- An integral domain is called a `valuation ring` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
class valuation_ring (A : Type*) [comm_ring A] [is_domain A] : Prop :=
(cond [] : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a)


namespace valuation_ring

section
variables (A : Type*) [comm_ring A]
variables (K : Type*) [field K] [algebra A K]

/-- The value group of the valuation ring `A`. -/
def value_group : Type* := quotient (mul_action.orbit_rel Aˣ K)

instance : inhabited (value_group A K) := ⟨quotient.mk' 0⟩

instance : has_le (value_group A K) := has_le.mk $ λ x y,
quotient.lift_on₂' x y (λ a b, ∃ c : A, c • b = a)
begin
  rintros _ _ a b ⟨c,rfl⟩ ⟨d,rfl⟩, ext,
  split,
  { rintros ⟨e,he⟩, dsimp at he, use ((c⁻¹ : Aˣ) * e * d),
    apply_fun (λ t, c⁻¹ • t) at he,
    simpa [mul_smul] using he },
  { rintros ⟨e,he⟩, dsimp,
    use (d⁻¹ : Aˣ) * c * e,
    erw [← he, ← mul_smul, ← mul_smul],
    congr' 1,
    rw mul_comm,
    simp only [← mul_assoc, ← units.coe_mul, mul_inv_self, one_mul] }
end

instance : has_zero (value_group A K) := ⟨quotient.mk' 0⟩
instance : has_one (value_group A K) := ⟨quotient.mk' 1⟩

instance : has_mul (value_group A K) := has_mul.mk $ λ x y,
quotient.lift_on₂' x y (λ a b, quotient.mk' $ a * b)
begin
  rintros _ _ a b ⟨c,rfl⟩ ⟨d,rfl⟩,
  apply quotient.sound',
  dsimp,
  use c * d,
  simp only [mul_smul, algebra.smul_def, units.smul_def, ring_hom.map_mul,
    units.coe_mul],
  ring,
end

instance : has_inv (value_group A K) := has_inv.mk $ λ x,
quotient.lift_on' x (λ a, quotient.mk' a⁻¹)
begin
  rintros _ a ⟨b,rfl⟩,
  apply quotient.sound',
  use b⁻¹,
  dsimp,
  rw [units.smul_def, units.smul_def, algebra.smul_def, algebra.smul_def,
    mul_inv₀, ring_hom.map_units_inv],
end

variables [is_domain A] [valuation_ring A] [is_fraction_ring A K]

lemma le_total (a b : value_group A K) : a ≤ b ∨ b ≤ a :=
begin
  rcases a with ⟨a⟩, rcases b with ⟨b⟩,
  obtain ⟨xa,ya,hya,rfl⟩ : ∃ (a b : A), _ := is_fraction_ring.div_surjective a,
  obtain ⟨xb,yb,hyb,rfl⟩ : ∃ (a b : A), _ := is_fraction_ring.div_surjective b,
  have : (algebra_map A K) ya ≠ 0 :=
    is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors hya,
  have : (algebra_map A K) yb ≠ 0 :=
    is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors hyb,
  obtain ⟨c,(h|h)⟩ := valuation_ring.cond (xa * yb) (xb * ya),
  { right,
    use c,
    rw algebra.smul_def,
    field_simp,
    simp only [← ring_hom.map_mul, ← h], congr' 1, ring },
  { left,
    use c,
    rw algebra.smul_def,
    field_simp,
    simp only [← ring_hom.map_mul, ← h], congr' 1, ring }
end

noncomputable
instance : linear_ordered_comm_group_with_zero (value_group A K) :=
{ le_refl := by { rintro ⟨⟩, use 1, rw one_smul },
  le_trans := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e,rfl⟩ ⟨f,rfl⟩, use (e * f), rw mul_smul },
  le_antisymm := begin
    rintros ⟨a⟩ ⟨b⟩ ⟨e,rfl⟩ ⟨f,hf⟩,
    by_cases hb : b = 0, { simp [hb] },
    have : is_unit e,
    { apply is_unit_of_dvd_one,
      use f, rw mul_comm,
      rw [← mul_smul, algebra.smul_def] at hf,
      nth_rewrite 1 ← one_mul b at hf,
      rw ← (algebra_map A K).map_one at hf,
      exact is_fraction_ring.injective _ _
        (cancel_comm_monoid_with_zero.mul_right_cancel_of_ne_zero hb hf).symm },
    apply quotient.sound',
    use [this.unit, rfl],
  end,
  le_total := le_total _ _,
  decidable_le := by { classical, apply_instance },
  mul_assoc := by { rintros ⟨a⟩ ⟨b⟩ ⟨c⟩, apply quotient.sound', rw mul_assoc, apply setoid.refl' },
  one_mul := by { rintros ⟨a⟩, apply quotient.sound', rw one_mul, apply setoid.refl' },
  mul_one := by { rintros ⟨a⟩, apply quotient.sound', rw mul_one, apply setoid.refl' },
  mul_comm := by { rintros ⟨a⟩ ⟨b⟩, apply quotient.sound', rw mul_comm, apply setoid.refl' },
  mul_le_mul_left := begin
    rintros ⟨a⟩ ⟨b⟩ ⟨c,rfl⟩ ⟨d⟩,
    use c, simp only [algebra.smul_def], ring,
  end,
  zero_mul := by { rintros ⟨a⟩, apply quotient.sound', rw zero_mul, apply setoid.refl' },
  mul_zero := by { rintros ⟨a⟩, apply quotient.sound', rw mul_zero, apply setoid.refl' },
  zero_le_one := ⟨0, by rw zero_smul⟩,
  exists_pair_ne := begin
    use [0,1],
    intro c, obtain ⟨d,hd⟩ := quotient.exact' c,
    apply_fun (λ t, d⁻¹ • t) at hd,
    simpa using hd,
  end,
  inv_zero := by { apply quotient.sound', rw inv_zero, apply setoid.refl' },
  mul_inv_cancel := begin
    rintros ⟨a⟩ ha,
    apply quotient.sound',
    use 1,
    simp only [one_smul],
    apply (mul_inv_cancel _).symm,
    contrapose ha,
    simp only [not_not] at ha ⊢,
    rw ha, refl,
  end,
  ..(infer_instance : has_le (value_group A K)),
  ..(infer_instance : has_mul (value_group A K)),
  ..(infer_instance : has_inv (value_group A K)),
  ..(infer_instance : has_zero (value_group A K)),
  ..(infer_instance : has_one (value_group A K)) }

/-- Any valuation ring induces a valuation on its fraction field. -/
def valuation : valuation K (value_group A K) :=
{ to_fun := quotient.mk',
  map_zero' := rfl,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_add_le_max' := begin
    intros a b,
    obtain ⟨xa,ya,hya,rfl⟩ : ∃ (a b : A), _ := is_fraction_ring.div_surjective a,
    obtain ⟨xb,yb,hyb,rfl⟩ : ∃ (a b : A), _ := is_fraction_ring.div_surjective b,
    have : (algebra_map A K) ya ≠ 0 :=
      is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors hya,
    have : (algebra_map A K) yb ≠ 0 :=
      is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors hyb,
    obtain ⟨c,(h|h)⟩ := valuation_ring.cond (xa * yb) (xb * ya),
    dsimp,
    { apply le_trans _ (le_max_left _ _),
      use (c + 1),
      rw algebra.smul_def,
      field_simp,
      simp only [← ring_hom.map_mul, ← ring_hom.map_add, ← (algebra_map A K).map_one, ← h],
      congr' 1, ring },
    { apply le_trans _ (le_max_right _ _),
      use (c + 1),
      rw algebra.smul_def,
      field_simp,
      simp only [← ring_hom.map_mul, ← ring_hom.map_add, ← (algebra_map A K).map_one, ← h],
      congr' 1, ring }
  end }

lemma mem_integer_iff (x : K) : x ∈ (valuation A K).integer ↔ ∃ a : A, algebra_map A K a = x :=
begin
  split,
  { rintros ⟨c,rfl⟩,
    use c,
    rw [algebra.smul_def, mul_one] },
  { rintro ⟨c,rfl⟩,
    use c,
    rw [algebra.smul_def, mul_one] }
end

/-- The valuation ring `A` is isomorphic to the ring of integers of its associated valuation. -/
noncomputable def equiv_integer : A ≃+* (valuation A K).integer :=
ring_equiv.of_bijective
{ to_fun := λ a, ⟨algebra_map A K a, (mem_integer_iff _ _ _).mpr ⟨a,rfl⟩⟩,
  map_one' := by { ext1, exact (algebra_map A K).map_one },
  map_mul' := λ _ _, by { ext1, exact (algebra_map A K).map_mul _ _ },
  map_zero' := by { ext1, exact (algebra_map A K).map_zero },
  map_add' := λ _ _, by { ext1, exact (algebra_map A K).map_add _ _ } }
begin
  split,
  { intros x y h,
    apply_fun (coe : _ → K) at h,
    dsimp at h,
    exact is_fraction_ring.injective _ _ h },
  { rintros ⟨a,(ha : a ∈ (valuation A K).integer)⟩,
    rw mem_integer_iff at ha,
    obtain ⟨a,rfl⟩ := ha,
    use [a, rfl] }
end

@[simp]
lemma coe_equiv_integer_apply (a : A) : (equiv_integer A K a : K) = algebra_map A K a := rfl

lemma range_algebra_map_eq : (valuation A K).integer = (algebra_map A K).range :=
by { ext, exact mem_integer_iff _ _ _ }

end

section

variables (A : Type*) [comm_ring A] [is_domain A] [valuation_ring A]

@[priority 100]
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

end

end valuation_ring
