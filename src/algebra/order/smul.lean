/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import algebra.module.pi
import algebra.module.prod
import algebra.order.field
import algebra.order.pi
import data.set.pointwise

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

open_locale pointwise

/--
The ordered scalar product property is when an ordered additive commutative monoid
with a partial order has a scalar multiplication which is compatible with the order.
-/
@[protect_proj]
class ordered_smul (R M : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid M] [smul_with_zero R M] : Prop :=
(smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b)

variables {ι 𝕜 R M N : Type*}

namespace order_dual

instance [has_smul R M] : has_smul R Mᵒᵈ := ⟨λ k x, order_dual.rec (λ x', (k • x' : M)) x⟩

instance [has_zero R] [add_zero_class M] [h : smul_with_zero R M] : smul_with_zero R Mᵒᵈ :=
{ zero_smul := λ m, order_dual.rec (zero_smul _) m,
  smul_zero := λ r, order_dual.rec (smul_zero' _) r,
  ..order_dual.has_smul }

instance [monoid R] [mul_action R M] : mul_action R Mᵒᵈ :=
{ one_smul := λ m, order_dual.rec (one_smul _) m,
  mul_smul := λ r, order_dual.rec mul_smul r,
  ..order_dual.has_smul }

instance [monoid_with_zero R] [add_monoid M] [mul_action_with_zero R M] :
  mul_action_with_zero R Mᵒᵈ :=
{ ..order_dual.mul_action, ..order_dual.smul_with_zero }

instance [monoid_with_zero R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action R Mᵒᵈ :=
{ smul_add := λ k a, order_dual.rec (λ a' b, order_dual.rec (smul_add _ _) b) a,
  smul_zero := λ r, order_dual.rec smul_zero r }

instance [ordered_semiring R] [ordered_add_comm_monoid M] [smul_with_zero R M]
  [ordered_smul R M] :
  ordered_smul R Mᵒᵈ :=
{ smul_lt_smul_of_pos := λ a b, @ordered_smul.smul_lt_smul_of_pos R M _ _ _ _ b a,
  lt_of_smul_lt_smul_of_pos := λ a b,
    @ordered_smul.lt_of_smul_lt_smul_of_pos R M _ _ _ _ b a }

@[simp] lemma to_dual_smul [has_smul R M] {c : R} {a : M} : to_dual (c • a) = c • to_dual a := rfl
@[simp] lemma of_dual_smul [has_smul R M] {c : R} {a : Mᵒᵈ} : of_dual (c • a) = c • of_dual a :=
rfl

end order_dual

section ordered_smul
variables [ordered_semiring R] [ordered_add_comm_monoid M] [smul_with_zero R M] [ordered_smul R M]
  {s : set M} {a b : M} {c : R}

lemma smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b := ordered_smul.smul_lt_smul_of_pos

lemma smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b :=
begin
  rcases h₁.eq_or_lt with rfl|hab,
  { refl },
  { rcases h₂.eq_or_lt with rfl|hc,
    { rw [zero_smul, zero_smul] },
    { exact (smul_lt_smul_of_pos hab hc).le } }
end

lemma smul_nonneg (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ c • a :=
calc (0 : M) = c • (0 : M) : (smul_zero' M c).symm
         ... ≤ c • a : smul_le_smul_of_nonneg ha hc

lemma smul_nonpos_of_nonneg_of_nonpos (hc : 0 ≤ c) (ha : a ≤ 0) : c • a ≤ 0 :=
@smul_nonneg R Mᵒᵈ _ _ _ _ _ _ hc ha

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

alias smul_pos_iff_of_pos ↔ _ smul_pos

lemma monotone_smul_left (hc : 0 ≤ c) : monotone (has_smul.smul c : M → M) :=
λ a b h, smul_le_smul_of_nonneg h hc

lemma strict_mono_smul_left (hc : 0 < c) : strict_mono (has_smul.smul c : M → M) :=
λ a b h, smul_lt_smul_of_pos h hc

lemma smul_lower_bounds_subset_lower_bounds_smul (hc : 0 ≤ c) :
  c • lower_bounds s ⊆ lower_bounds (c • s) :=
(monotone_smul_left hc).image_lower_bounds_subset_lower_bounds_image

lemma smul_upper_bounds_subset_upper_bounds_smul (hc : 0 ≤ c) :
  c • upper_bounds s ⊆ upper_bounds (c • s) :=
(monotone_smul_left hc).image_upper_bounds_subset_upper_bounds_image

lemma bdd_below.smul_of_nonneg (hs : bdd_below s) (hc : 0 ≤ c) : bdd_below (c • s) :=
(monotone_smul_left hc).map_bdd_below hs

lemma bdd_above.smul_of_nonneg (hs : bdd_above s) (hc : 0 ≤ c) : bdd_above (c • s) :=
(monotone_smul_left hc).map_bdd_above hs

end ordered_smul

instance linear_ordered_semiring.to_ordered_smul {R : Type*} [linear_ordered_semiring R] :
  ordered_smul R R :=
{ smul_lt_smul_of_pos        := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_pos  := λ _ _ _ h hc, lt_of_mul_lt_mul_left h hc.le }

section linear_ordered_semifield
variables [linear_ordered_semifield 𝕜]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid M] [ordered_add_comm_monoid N] [mul_action_with_zero 𝕜 M]
  [mul_action_with_zero 𝕜 N]

/-- To prove that a vector space over a linear ordered field is ordered, it suffices to verify only
the first axiom of `ordered_smul`. -/
lemma ordered_smul.mk' (h : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a ≤ c • b) :
  ordered_smul 𝕜 M :=
begin
  have hlt' : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a < c • b,
  { refine λ a b c hab hc, (h hab hc).lt_of_ne _,
    rw [ne.def, hc.ne'.is_unit.smul_left_cancel],
    exact hab.ne },
  refine { smul_lt_smul_of_pos := hlt', .. },
  intros a b c hab hc,
  obtain ⟨c, rfl⟩ := hc.ne'.is_unit,
  rw [← inv_smul_smul c a, ← inv_smul_smul c b],
  refine hlt' hab (pos_of_mul_pos_right _ hc.le),
  simp only [c.mul_inv, zero_lt_one]
end

instance [ordered_smul 𝕜 M] [ordered_smul 𝕜 N] : ordered_smul 𝕜 (M × N) :=
ordered_smul.mk' $ λ a b c h hc,
  ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance pi.ordered_smul {M : ι → Type*} [Π i, ordered_add_comm_monoid (M i)]
  [Π i, mul_action_with_zero 𝕜 (M i)] [∀ i, ordered_smul 𝕜 (M i)] :
  ordered_smul 𝕜 (Π i, M i) :=
ordered_smul.mk' $ λ v u c h hc i, smul_le_smul_of_nonneg (h.le i) hc.le

/- Sometimes Lean fails to apply the dependent version to non-dependent functions, so we define
another instance. -/
instance pi.ordered_smul' [ordered_smul 𝕜 M] : ordered_smul 𝕜 (ι → M) := pi.ordered_smul

/- Sometimes Lean fails to unify the module with the scalars, so we define another instance. -/
instance pi.ordered_smul'' : ordered_smul 𝕜 (ι → 𝕜) := @pi.ordered_smul' ι 𝕜 𝕜 _ _ _ _

end ordered_add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group M] [mul_action_with_zero 𝕜 M] [ordered_smul 𝕜 M] {s : set M}
  {a b : M} {c : 𝕜}

lemma smul_le_smul_iff_of_pos (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b :=
⟨λ h, inv_smul_smul₀ hc.ne' a ▸ inv_smul_smul₀ hc.ne' b ▸
  smul_le_smul_of_nonneg h (inv_nonneg.2 hc.le),
  λ h, smul_le_smul_of_nonneg h hc.le⟩

lemma smul_lt_iff_of_pos (hc : 0 < c) : c • a < b ↔ a < c⁻¹ • b :=
calc c • a < b ↔ c • a < c • c⁻¹ • b : by rw [smul_inv_smul₀ hc.ne']
... ↔ a < c⁻¹ • b : smul_lt_smul_iff_of_pos hc

lemma lt_smul_iff_of_pos (hc : 0 < c) : a < c • b ↔ c⁻¹ • a < b :=
calc a < c • b ↔ c • c⁻¹ • a < c • b : by rw [smul_inv_smul₀ hc.ne']
... ↔ c⁻¹ • a < b : smul_lt_smul_iff_of_pos hc

lemma smul_le_iff_of_pos (hc : 0 < c) : c • a ≤ b ↔ a ≤ c⁻¹ • b :=
calc c • a ≤ b ↔ c • a ≤ c • c⁻¹ • b : by rw [smul_inv_smul₀ hc.ne']
... ↔ a ≤ c⁻¹ • b : smul_le_smul_iff_of_pos hc

lemma le_smul_iff_of_pos (hc : 0 < c) : a ≤ c • b ↔ c⁻¹ • a ≤ b :=
calc a ≤ c • b ↔ c • c⁻¹ • a ≤ c • b : by rw [smul_inv_smul₀ hc.ne']
... ↔ c⁻¹ • a ≤ b : smul_le_smul_iff_of_pos hc

variables (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps] def order_iso.smul_left (hc : 0 < c) : M ≃o M :=
{ to_fun := λ b, c • b,
  inv_fun := λ b, c⁻¹ • b,
  left_inv := inv_smul_smul₀ hc.ne',
  right_inv := smul_inv_smul₀ hc.ne',
  map_rel_iff' := λ b₁ b₂, smul_le_smul_iff_of_pos hc }

variables {M}

@[simp] lemma lower_bounds_smul_of_pos (hc : 0 < c) : lower_bounds (c • s) = c • lower_bounds s :=
(order_iso.smul_left _ hc).lower_bounds_image

@[simp] lemma upper_bounds_smul_of_pos (hc : 0 < c) : upper_bounds (c • s) = c • upper_bounds s :=
(order_iso.smul_left _ hc).upper_bounds_image

@[simp] lemma bdd_below_smul_iff_of_pos (hc : 0 < c) : bdd_below (c • s) ↔ bdd_below s :=
(order_iso.smul_left _ hc).bdd_below_image

@[simp] lemma bdd_above_smul_iff_of_pos (hc : 0 < c) : bdd_above (c • s) ↔ bdd_above s :=
(order_iso.smul_left _ hc).bdd_above_image

end ordered_add_comm_group
end linear_ordered_semifield
