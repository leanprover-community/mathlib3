/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ring_theory.valuation.valuation_ring

/-!

# Valuation subrings of a field

# Projects

The order structure on `valuation_subring K`.

-/

variables (K : Type*) [field K]

/-- A valuation subring of a field `K` is a subring `A` such that for every `x : K`,
either `x ∈ A` or `x⁻¹ ∈ K`. -/
structure valuation_subring extends subring K :=
(mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier)

namespace valuation_subring

variables {K} (A : valuation_subring K)

instance : set_like (valuation_subring K) K :=
{ coe := λ A, A.to_subring,
  coe_injective' := begin
    intros A B h,
    cases A, cases B, congr, apply set_like.ext,
    exact set.ext_iff.mp h,
  end }

@[simp] lemma mem_carrier (x : K) : x ∈ A.carrier ↔ x ∈ A := iff.refl _
@[simp] lemma mem_to_subring (x : K) : x ∈ A.to_subring ↔ x ∈ A := iff.refl _

@[ext] lemma ext (A B : valuation_subring K)
  (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := set_like.ext h

lemma mem_or_inv_mem (x : K) : x ∈ A ∨ x⁻¹ ∈ A := A.mem_or_inv_mem' _

instance : comm_ring A := show comm_ring A.to_subring, by apply_instance
instance : is_domain A := show is_domain A.to_subring, by apply_instance

instance : has_top (valuation_subring K) := has_top.mk $
{ mem_or_inv_mem' := λ x, or.inl trivial,
  ..(⊤ : subring K) }

lemma mem_top (x : K) : x ∈ (⊤ : valuation_subring K) := trivial

lemma le_top : A ≤ ⊤ := λ a ha, mem_top _

instance : inhabited (valuation_subring K) := ⟨⊤⟩

instance : valuation_ring A :=
begin
  constructor,
  intros a b,
  by_cases (b : K) = 0, { use 0, left, rw mul_zero, exact_mod_cast h.symm },
  by_cases (a : K) = 0, { use 0, right, rw mul_zero, exact_mod_cast h.symm },
  cases A.mem_or_inv_mem (a/b) with hh hh,
  { use ⟨a/b,hh⟩, right, apply subtype.ext, field_simp, ring },
  { rw (show ((a : K)/b)⁻¹ = b/a, by field_simp) at hh,
    use ⟨b/a,hh⟩, left, apply subtype.ext, field_simp, ring }
end

instance : algebra A K :=
show algebra A.to_subring K, by apply_instance

@[simp]
lemma algebra_map_apply (a : A) : algebra_map A K a = a := rfl

instance : is_fraction_ring A K :=
{ map_units := λ ⟨y,hy⟩,
    (units.mk0 (y : K)
      (λ c, non_zero_divisors.ne_zero hy (by exact_mod_cast c))).is_unit,
  surj := begin
    intros z,
    by_cases z = 0, { use (0,1), simp [h] },
    cases A.mem_or_inv_mem z with hh hh,
    { use (⟨z,hh⟩,1), simp },
    { refine ⟨⟨1,⟨⟨_,hh⟩,_⟩⟩,_⟩,
      { rw mem_non_zero_divisors_iff_ne_zero,
        intro c, apply h,
        exact inv_eq_zero.mp (congr_arg coe c) },
      { dsimp, exact mul_inv_cancel h } }
  end,
  eq_iff_exists := begin
    intros a b,
    dsimp,
    split,
    { intro h, use 1, simp only [submonoid.coe_one, mul_one], exact_mod_cast h },
    { rintro ⟨c,h⟩,
      simp only [mul_eq_mul_right_iff] at h,
      cases h,
      { exact_mod_cast h },
      { exact false.elim (non_zero_divisors.ne_zero c.2 h) } },
  end }

/-- Any valuation subring of `K` induces a natural valuation on `K`. -/
def valuation := valuation_ring.valuation A K

lemma valuation_le_one (a : A) : A.valuation a ≤ 1 :=
begin
  change (a : K) ∈ A.valuation.integer,
  erw valuation_ring.mem_integer_iff,
  use a, refl,
end

lemma mem_of_valuation_le_one (x : K) : A.valuation x ≤ 1 → x ∈ A :=
begin
  rintro (h : x ∈ A.valuation.integer),
  erw valuation_ring.mem_integer_iff at h,
  obtain ⟨a,ha⟩ := h,
  rw ← ha, exact a.2,
end

lemma valuation_le_one_iff (x : K) : A.valuation x ≤ 1 ↔ x ∈ A :=
⟨mem_of_valuation_le_one _ _, λ ha, A.valuation_le_one ⟨x,ha⟩⟩

lemma valuation_eq_iff (x y : K) : A.valuation x = A.valuation y ↔
  ∃ a : Aˣ, (a : K) * y = x :=
begin
  change quotient.mk' _ = quotient.mk' _ ↔ _,
  rw quotient.eq', apply iff.refl,
end

lemma valuation_le_iff (x y : K) : A.valuation x ≤ A.valuation y ↔
  ∃ a : A, (a : K) * y = x := iff.rfl

lemma valuation_surjective : function.surjective A.valuation := surjective_quot_mk _

end valuation_subring
