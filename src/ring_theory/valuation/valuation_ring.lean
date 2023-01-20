/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.valuation.integers
import ring_theory.ideal.local_ring
import ring_theory.localization.fraction_ring
import ring_theory.localization.integer
import ring_theory.discrete_valuation_ring
import ring_theory.bezout
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

We also provide the equivalence of the following notions for a domain `R` in `valuation_ring.tfae`.
1. `R` is a valuation ring.
2. For each `x : fraction_ring K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

-/

universes u v w

/-- An integral domain is called a `valuation ring` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
class valuation_ring (A : Type u) [comm_ring A] [is_domain A] : Prop :=
(cond [] : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a)

namespace valuation_ring

section
variables (A : Type u) [comm_ring A]
variables (K : Type v) [field K] [algebra A K]

/-- The value group of the valuation ring `A`. Note: this is actually a group with zero. -/
def value_group : Type v := quotient (mul_action.orbit_rel Aˣ K)

instance : inhabited (value_group A K) := ⟨quotient.mk' 0⟩

instance : has_le (value_group A K) := has_le.mk $ λ x y,
quotient.lift_on₂' x y (λ a b, ∃ c : A, c • b = a)
begin
  rintros _ _ a b ⟨c,rfl⟩ ⟨d,rfl⟩, ext,
  split,
  { rintros ⟨e,he⟩, use ((c⁻¹ : Aˣ) * e * d),
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
    mul_inv, map_units_inv],
end

variables [is_domain A] [valuation_ring A] [is_fraction_ring A K]

protected lemma le_total (a b : value_group A K) : a ≤ b ∨ b ≤ a :=
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
      exact is_fraction_ring.injective _ _ (mul_right_cancel₀ hb hf).symm },
    apply quotient.sound',
    use [this.unit, rfl],
  end,
  le_total := valuation_ring.le_total _ _,
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
ring_equiv.of_bijective (show A →ₙ+* (valuation A K).integer, from
{ to_fun := λ a, ⟨algebra_map A K a, (mem_integer_iff _ _ _).mpr ⟨a,rfl⟩⟩,
  map_mul' := λ _ _, by { ext1, exact (algebra_map A K).map_mul _ _ },
  map_zero' := by { ext1, exact (algebra_map A K).map_zero },
  map_add' := λ _ _, by { ext1, exact (algebra_map A K).map_add _ _ } })
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

variables (A : Type u) [comm_ring A] [is_domain A] [valuation_ring A]

@[priority 100]
instance : local_ring A :=
local_ring.of_is_unit_or_is_unit_one_sub_self
begin
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

section

variables {R : Type*} [comm_ring R] [is_domain R] {K : Type*}
variables [field K] [algebra R K] [is_fraction_ring R K]

lemma iff_dvd_total :
  valuation_ring R ↔ is_total R (∣) :=
begin
  classical,
  refine ⟨λ H, ⟨λ a b, _⟩, λ H, ⟨λ a b, _⟩⟩; resetI,
  { obtain ⟨c,rfl|rfl⟩ := @@valuation_ring.cond _ _ H a b; simp },
  { obtain (⟨c, rfl⟩|⟨c, rfl⟩) := @is_total.total _ _ H a b; use c; simp }
end

lemma iff_ideal_total :
  valuation_ring R ↔ is_total (ideal R) (≤) :=
begin
  classical,
  refine ⟨λ _, by exactI ⟨le_total⟩, λ H, iff_dvd_total.mpr ⟨λ a b, _⟩⟩,
  have := @is_total.total _ _ H (ideal.span {a}) (ideal.span {b}),
  simp_rw ideal.span_singleton_le_span_singleton at this,
  exact this.symm
end

variables {R} (K)

lemma dvd_total [h : valuation_ring R] (x y : R) : x ∣ y ∨ y ∣ x :=
@@is_total.total _ (iff_dvd_total.mp h) x y

lemma unique_irreducible [valuation_ring R] ⦃p q : R⦄
  (hp : irreducible p) (hq : irreducible q) : associated p q :=
begin
  have := dvd_total p q,
  rw [irreducible.dvd_comm hp hq, or_self] at this,
  exact associated_of_dvd_dvd (irreducible.dvd_symm hq hp this) this,
end

variable (R)

lemma iff_is_integer_or_is_integer :
  valuation_ring R ↔ ∀ x : K, is_localization.is_integer R x ∨ is_localization.is_integer R x⁻¹ :=
begin
  split,
  { introsI H x,
    obtain ⟨x : R, y, hy, rfl⟩ := is_fraction_ring.div_surjective x,
    any_goals { apply_instance },
    have := (map_ne_zero_iff _ (is_fraction_ring.injective R K)).mpr (non_zero_divisors.ne_zero hy),
    obtain ⟨s, rfl|rfl⟩ := valuation_ring.cond x y,
    { exact or.inr ⟨s, eq_inv_of_mul_eq_one_left $
        by rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩ },
    { exact or.inl ⟨s, by rwa [eq_div_iff, map_mul, mul_comm]⟩ } },
  { intro H,
    constructor,
    intros a b,
    by_cases ha : a = 0, { subst ha, exact ⟨0, or.inr $ mul_zero b⟩ },
    by_cases hb : b = 0, { subst hb, exact ⟨0, or.inl $ mul_zero a⟩ },
    replace ha := (map_ne_zero_iff _ (is_fraction_ring.injective R K)).mpr ha,
    replace hb := (map_ne_zero_iff _ (is_fraction_ring.injective R K)).mpr hb,
    obtain ⟨c, e⟩|⟨c, e⟩ := H (algebra_map R K a / algebra_map R K b),
    { rw [eq_div_iff hb, ← map_mul, (is_fraction_ring.injective R K).eq_iff, mul_comm] at e,
      exact ⟨c, or.inr e⟩ },
    { rw [inv_div, eq_div_iff ha, ← map_mul,
        (is_fraction_ring.injective R K).eq_iff, mul_comm c] at e,
      exact ⟨c, or.inl e⟩ } }
end

variable {K}

lemma is_integer_or_is_integer [h : valuation_ring R] (x : K) :
  is_localization.is_integer R x ∨ is_localization.is_integer R x⁻¹ :=
(iff_is_integer_or_is_integer R K).mp h x

variable {R}

-- This implies that valuation rings are integrally closed through typeclass search.
@[priority 100]
instance [valuation_ring R] : is_bezout R :=
begin
  classical,
  rw is_bezout.iff_span_pair_is_principal,
  intros x y,
  rw ideal.span_insert,
  cases le_total (ideal.span {x} : ideal R) (ideal.span {y}),
  { erw sup_eq_right.mpr h, exact ⟨⟨_, rfl⟩⟩ },
  { erw sup_eq_left.mpr h, exact ⟨⟨_, rfl⟩⟩ }
end

lemma iff_local_bezout_domain :
  valuation_ring R ↔ local_ring R ∧ is_bezout R :=
begin
  classical,
  refine ⟨λ H, by exactI ⟨infer_instance, infer_instance⟩, _⟩,
  rintro ⟨h₁, h₂⟩,
  resetI,
  refine iff_dvd_total.mpr ⟨λ a b, _⟩,
  obtain ⟨g, e : _ = ideal.span _⟩ := is_bezout.span_pair_is_principal a b,
  obtain ⟨a, rfl⟩ := ideal.mem_span_singleton'.mp
    (show a ∈ ideal.span {g}, by { rw [← e], exact ideal.subset_span (by simp) }),
  obtain ⟨b, rfl⟩ := ideal.mem_span_singleton'.mp
    (show b ∈ ideal.span {g}, by { rw [← e], exact ideal.subset_span (by simp) }),
  obtain ⟨x, y, e'⟩ := ideal.mem_span_pair.mp
    (show g ∈ ideal.span {a * g, b * g}, by { rw e, exact ideal.subset_span (by simp) }),
  cases eq_or_ne g 0 with h h, { simp [h] },
  have : x * a + y * b = 1,
  { apply mul_left_injective₀ h, convert e'; ring_nf },
  cases local_ring.is_unit_or_is_unit_of_add_one this with h' h',
  left, swap, right,
  all_goals
  { exact mul_dvd_mul_right (is_unit_iff_forall_dvd.mp (is_unit_of_mul_is_unit_right h') _) _ },
end

protected lemma tfae (R : Type u) [comm_ring R] [is_domain R] :
  tfae [valuation_ring R,
    ∀ x : fraction_ring R, is_localization.is_integer R x ∨ is_localization.is_integer R x⁻¹,
    is_total R (∣),
    is_total (ideal R) (≤),
    local_ring R ∧ is_bezout R] :=
begin
  tfae_have : 1 ↔ 2, { exact iff_is_integer_or_is_integer R _ },
  tfae_have : 1 ↔ 3, { exact iff_dvd_total },
  tfae_have : 1 ↔ 4, { exact iff_ideal_total },
  tfae_have : 1 ↔ 5, { exact iff_local_bezout_domain },
  tfae_finish
end

end

lemma _root_.function.surjective.valuation_ring {R S : Type*} [comm_ring R] [is_domain R]
  [valuation_ring R] [comm_ring S] [is_domain S] (f : R →+* S) (hf : function.surjective f) :
  valuation_ring S :=
⟨λ a b, begin
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨hf a, hf b⟩,
  obtain ⟨c, rfl|rfl⟩ := valuation_ring.cond a b,
  exacts [⟨f c, or.inl $ (map_mul _ _ _).symm⟩, ⟨f c, or.inr $ (map_mul _ _ _).symm⟩],
end⟩

section

variables {𝒪 : Type u} {K : Type v} {Γ : Type w}
  [comm_ring 𝒪] [is_domain 𝒪] [field K] [algebra 𝒪 K]
  [linear_ordered_comm_group_with_zero Γ]
  (v : _root_.valuation K Γ) (hh : v.integers 𝒪)

include hh

/-- If `𝒪` satisfies `v.integers 𝒪` where `v` is a valuation on a field, then `𝒪`
is a valuation ring. -/
lemma of_integers : valuation_ring 𝒪 :=
begin
  constructor,
  intros a b,
  cases le_total (v (algebra_map 𝒪 K a)) (v (algebra_map 𝒪 K b)),
  { obtain ⟨c,hc⟩ := valuation.integers.dvd_of_le hh h,
    use c, exact or.inr hc.symm },
  { obtain ⟨c,hc⟩ := valuation.integers.dvd_of_le hh h,
    use c, exact or.inl hc.symm }
end

end

section

variables (K : Type u) [field K]

/-- A field is a valuation ring. -/
@[priority 100]
instance of_field : valuation_ring K :=
begin
  constructor,
  intros a b,
  by_cases b = 0,
  { use 0, left, simp [h] },
  { use a * b⁻¹, right, field_simp, rw mul_comm }
end

end

section

variables (A : Type u) [comm_ring A] [is_domain A] [discrete_valuation_ring A]

/-- A DVR is a valuation ring. -/
@[priority 100]
instance of_discrete_valuation_ring : valuation_ring A :=
begin
  constructor,
  intros a b,
  by_cases ha : a = 0, { use 0, right, simp [ha] },
  by_cases hb : b = 0, { use 0, left, simp [hb] },
  obtain ⟨ϖ,hϖ⟩ := discrete_valuation_ring.exists_irreducible A,
  obtain ⟨m,u,rfl⟩ := discrete_valuation_ring.eq_unit_mul_pow_irreducible ha hϖ,
  obtain ⟨n,v,rfl⟩ := discrete_valuation_ring.eq_unit_mul_pow_irreducible hb hϖ,
  cases le_total m n with h h,
  { use (u⁻¹ * v : Aˣ) * ϖ^(n-m), left,
    simp_rw [mul_comm (u : A), units.coe_mul, ← mul_assoc, mul_assoc _ (u : A)],
    simp only [units.mul_inv, mul_one, mul_comm _ (v : A), mul_assoc, ← pow_add],
    congr' 2,
    linarith },
  { use (v⁻¹ * u : Aˣ) * ϖ^(m-n), right,
    simp_rw [mul_comm (v : A), units.coe_mul, ← mul_assoc, mul_assoc _ (v : A)],
    simp only [units.mul_inv, mul_one, mul_comm _ (u : A), mul_assoc, ← pow_add],
    congr' 2,
    linarith }
end

end

end valuation_ring
