/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.ordered_pi
import algebra.smul_with_zero
import group_theory.group_action.group

/-!
# Ordered scalar product

In this file we define

* `ordered_smul R M` : an ordered additive commutative monoid `M` is an `ordered_smul`
  over an `ordered_semiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `analysis/convex/cone.lean`.

## Implementation notes

* We choose to define `ordered_smul` as a `Prop`-valued mixin, so that it can be
  used for actions, modules, and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/


/--
The ordered scalar product property is when an ordered additive commutative monoid
with a partial order has a scalar multiplication which is compatible with the order.
-/
@[protect_proj]
class ordered_smul (R M : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid M] [smul_with_zero R M] : Prop :=
(smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b)

section ordered_smul

variables {R M : Type*}
  [ordered_semiring R] [ordered_add_comm_monoid M] [smul_with_zero R M] [ordered_smul R M]
  {a b : M} {c : R}

lemma smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b := ordered_smul.smul_lt_smul_of_pos

lemma smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b :=
begin
  by_cases H₁ : c = 0,
  { simp [H₁, zero_smul] },
  { by_cases H₂ : a = b,
    { rw H₂ },
    { exact le_of_lt
        (smul_lt_smul_of_pos (lt_of_le_of_ne h₁ H₂) (lt_of_le_of_ne h₂ (ne.symm H₁))), } }
end

lemma eq_of_smul_eq_smul_of_pos_of_le (h₁ : c • a = c • b) (hc : 0 < c) (hle : a ≤ b) :
  a = b :=
hle.lt_or_eq.resolve_left $ λ hlt, (smul_lt_smul_of_pos hlt hc).ne h₁

lemma lt_of_smul_lt_smul_of_nonneg (h : c • a < c • b) (hc : 0 ≤ c) : a < b :=
hc.eq_or_lt.elim (λ hc, false.elim $ lt_irrefl (0:M) $ by rwa [← hc, zero_smul, zero_smul] at h)
  (ordered_smul.lt_of_smul_lt_smul_of_pos h)

lemma smul_lt_smul_iff_of_pos (hc : 0 < c) : c • a < c • b ↔ a < b :=
⟨λ h, lt_of_smul_lt_smul_of_nonneg h hc.le, λ h, smul_lt_smul_of_pos h hc⟩

lemma smul_pos_iff_of_pos (hc : 0 < c) : 0 < c • a ↔ 0 < a :=
calc 0 < c • a ↔ c • 0 < c • a : by rw smul_zero'
           ... ↔ 0 < a         : smul_lt_smul_iff_of_pos hc

end ordered_smul

/-- If `R` is a linear ordered semifield, then it suffices to verify only the first axiom of
`ordered_smul`. Moreover, it suffices to verify that `a < b` and `0 < c` imply
`c • a ≤ c • b`. We have no semifields in `mathlib`, so we use the assumption `∀ c ≠ 0, is_unit c`
instead. -/
lemma ordered_smul.mk'' {R M : Type*} [linear_ordered_semiring R] [ordered_add_comm_monoid M]
  [mul_action_with_zero R M] (hR : ∀ {c : R}, c ≠ 0 → is_unit c)
  (hlt : ∀ ⦃a b : M⦄ ⦃c : R⦄, a < b → 0 < c → c • a ≤ c • b) :
  ordered_smul R M :=
begin
  have hlt' : ∀ ⦃a b : M⦄ ⦃c : R⦄, a < b → 0 < c → c • a < c • b,
  { refine λ a b c hab hc, (hlt hab hc).lt_of_ne _,
    rw [ne.def, (hR hc.ne').smul_left_cancel],
    exact hab.ne },
  refine { smul_lt_smul_of_pos := hlt', .. },
  intros a b c h hc,
  rcases (hR hc.ne') with ⟨c, rfl⟩,
  rw [← inv_smul_smul c a, ← inv_smul_smul c b],
  refine hlt' h (pos_of_mul_pos_left _ hc.le),
  simp only [c.mul_inv, zero_lt_one]
end

/-- If `R` is a linear ordered field, then it suffices to verify only the first axiom of
`ordered_smul`. -/
lemma ordered_smul.mk' {k M : Type*} [linear_ordered_field k] [ordered_add_comm_monoid M]
  [mul_action_with_zero k M] (hlt : ∀ ⦃a b : M⦄ ⦃c : k⦄, a < b → 0 < c → c • a ≤ c • b) :
  ordered_smul k M :=
ordered_smul.mk'' (λ c hc, is_unit.mk0 _ hc) hlt

instance linear_ordered_semiring.to_ordered_smul {R : Type*} [linear_ordered_semiring R] :
  ordered_smul R R :=
{ smul_lt_smul_of_pos        := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_pos  := λ _ _ _ h hc, lt_of_mul_lt_mul_left h hc.le }

section field

variables {k M : Type*} [linear_ordered_field k]
  [ordered_add_comm_group M] [mul_action_with_zero k M] [ordered_smul k M]
  {a b : M} {c : k}

lemma smul_le_smul_iff_of_pos (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b :=
⟨λ h, inv_smul_smul' hc.ne' a ▸ inv_smul_smul' hc.ne' b ▸
  smul_le_smul_of_nonneg h (inv_nonneg.2 hc.le),
  λ h, smul_le_smul_of_nonneg h hc.le⟩

lemma smul_lt_iff_of_pos (hc : 0 < c) : c • a < b ↔ a < c⁻¹ • b :=
calc c • a < b ↔ c • a < c • c⁻¹ • b : by rw [smul_inv_smul' hc.ne']
... ↔ a < c⁻¹ • b : smul_lt_smul_iff_of_pos hc

lemma lt_smul_iff_of_pos (hc : 0 < c) : a < c • b ↔ c⁻¹ • a < b :=
calc a < c • b ↔ c • c⁻¹ • a < c • b : by rw [smul_inv_smul' hc.ne']
... ↔ c⁻¹ • a < b : smul_lt_smul_iff_of_pos hc

lemma smul_le_iff_of_pos (hc : 0 < c) : c • a ≤ b ↔ a ≤ c⁻¹ • b :=
calc c • a ≤ b ↔ c • a ≤ c • c⁻¹ • b : by rw [smul_inv_smul' hc.ne']
... ↔ a ≤ c⁻¹ • b : smul_le_smul_iff_of_pos hc

lemma le_smul_iff_of_pos (hc : 0 < c) : a ≤ c • b ↔ c⁻¹ • a ≤ b :=
calc a ≤ c • b ↔ c • c⁻¹ • a ≤ c • b : by rw [smul_inv_smul' hc.ne']
... ↔ c⁻¹ • a ≤ b : smul_le_smul_iff_of_pos hc

end field

namespace order_dual

variables {R M : Type*}

instance [has_scalar R M] : has_scalar R (order_dual M) :=
{ smul := λ k x, order_dual.rec (λ x', (k • x' : M)) x }

instance [semiring R] [ordered_add_comm_monoid M] [h : smul_with_zero R M] :
  smul_with_zero R (order_dual M) :=
{ zero_smul := λ m, order_dual.rec (zero_smul _) m,
  smul_zero := λ r, order_dual.rec (smul_zero' _) r,
  ..order_dual.has_scalar }

instance [semiring R] [mul_action R M] : mul_action R (order_dual M) :=
{ one_smul := λ m, order_dual.rec (one_smul _) m,
  mul_smul := λ r, order_dual.rec mul_smul r,
  ..order_dual.has_scalar }

instance [semiring R] [ordered_add_comm_monoid M] [mul_action_with_zero R M] :
  mul_action_with_zero R (order_dual M) :=
{ ..order_dual.mul_action, ..order_dual.smul_with_zero }

instance [semiring R] [ordered_add_comm_monoid M] [distrib_mul_action R M] :
  distrib_mul_action R (order_dual M) :=
{ smul_add := λ k a, order_dual.rec (λ a' b, order_dual.rec (smul_add _ _) b) a,
  smul_zero := λ r, order_dual.rec smul_zero r }

instance [ordered_semiring R] [ordered_add_comm_monoid M] [smul_with_zero R M]
  [ordered_smul R M] :
  ordered_smul R (order_dual M) :=
{ smul_lt_smul_of_pos := λ a b, @ordered_smul.smul_lt_smul_of_pos R M _ _ _ _ b a,
  lt_of_smul_lt_smul_of_pos := λ a b,
    @ordered_smul.lt_of_smul_lt_smul_of_pos R M _ _ _ _ b a }

end order_dual
