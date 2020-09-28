/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.polynomial.ring_division
import group_theory.order_of_element
import ring_theory.integral_domain
import tactic.zify

/-!
# Roots of unity

We define roots of unity in the context in the context of an arbitrary commutative monoid,
as a subgroup of the group of units.

## Main declarations

-/

open_locale classical
noncomputable theory

open polynomial
open finset

section move_this

lemma pow_gcd_eq_one {G : Type*} [group G] (x : G) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) :
  x ^ (m.gcd n) = 1 :=
begin
  rw [← gpow_coe_nat] at *,
  simp only [nat.gcd_eq_gcd_ab, gpow_add, gpow_mul, hm, hn, one_gpow, one_mul]
end

end move_this

variables {k l : ℕ+} {M N R : Type*} [comm_monoid M] [comm_monoid N] [integral_domain R]

section roots_of_unity

/-- `roots_of_unity k M` is the subgroup of elements `m : units M` that satisfy `m ^ k = 1` -/
def roots_of_unity (k : ℕ+) (M : Type*) [comm_monoid M] : subgroup (units M) :=
{ carrier := { ζ | ζ ^ (k : ℕ) = 1 },
  one_mem' := one_pow _,
  mul_mem' := λ ζ ξ hζ hξ, by simp only [*, set.mem_set_of_eq, mul_pow, one_mul] at *,
  inv_mem' := λ ζ hζ, by simp only [*, set.mem_set_of_eq, inv_pow, one_inv] at * }

@[simp] lemma mem_roots_of_unity (k : ℕ+) (ζ : units M) :
  ζ ∈ roots_of_unity k M ↔ ζ ^ (k : ℕ) = 1 := iff.rfl

lemma roots_of_unity_le_of_dvd (h : k ∣ l) : roots_of_unity k M ≤ roots_of_unity l M :=
begin
  obtain ⟨d, rfl⟩ := h,
  intros ζ h,
  simp only [mem_roots_of_unity, pnat.mul_coe, pow_mul, one_pow, *] at *,
end

lemma map_roots_of_unity (f : units M →* units N) (k : ℕ+) :
  (roots_of_unity k M).map f ≤ roots_of_unity k N :=
begin
  rintros _ ⟨ζ, h, rfl⟩,
  simp only [←monoid_hom.map_pow, *, mem_roots_of_unity, subgroup.mem_coe, monoid_hom.map_one] at *
end

lemma mem_roots_of_unity_iff_mem_nth_roots {ζ : units R} :
  ζ ∈ roots_of_unity k R ↔ (ζ : R) ∈ nth_roots k (1 : R) :=
by simp only [mem_roots_of_unity, mem_nth_roots k.pos, units.ext_iff, units.coe_one, units.coe_pow]

variables (k R)

lemma roots_of_unity_equiv_nth_roots :
  roots_of_unity k R ≃ {x // x ∈ nth_roots k (1 : R)} :=
begin
  refine
  { to_fun := λ x, ⟨x, mem_roots_of_unity_iff_mem_nth_roots.mp x.2⟩,
    inv_fun := λ x, ⟨⟨x, x ^ (k - 1 : ℕ), _, _⟩, _⟩,
    left_inv := _,
    right_inv := _ },
  swap 4, { rintro ⟨x, hx⟩, ext, refl },
  swap 4, { rintro ⟨x, hx⟩, ext, refl },
  all_goals
  { rcases x with ⟨x, hx⟩, rw [mem_nth_roots k.pos] at hx,
    simp only [subtype.coe_mk, ← pow_succ, ← pow_succ', hx,
      nat.sub_add_cancel (show 1 ≤ (k : ℕ), from k.one_le)] },
  { show (_ : units R) ^ (k : ℕ) = 1,
    simp only [units.ext_iff, hx, units.coe_mk, units.coe_one, subtype.coe_mk, units.coe_pow] }
end

variables {k R}

@[simp] lemma roots_of_unity_equiv_nth_roots_apply (x : roots_of_unity k R) :
  (roots_of_unity_equiv_nth_roots k R x : R) = x :=
by { delta roots_of_unity_equiv_nth_roots, refl } -- rfl fails

@[simp] lemma roots_of_unity_equiv_nth_roots_symm_apply (x : {x // x ∈ nth_roots k (1 : R)}) :
  ((roots_of_unity_equiv_nth_roots k R).symm x : R) = x :=
by { delta roots_of_unity_equiv_nth_roots, refl } -- rfl fails

variables (k R)

instance roots_of_unity.fintype : fintype (roots_of_unity k R) :=
fintype.of_equiv {x // x ∈ nth_roots k (1 : R)} $ (roots_of_unity_equiv_nth_roots k R).symm

instance roots_of_unity.is_cyclic : is_cyclic (roots_of_unity k R) :=
is_cyclic_of_subgroup_integral_domain ((units.coe_hom R).comp (roots_of_unity k R).subtype)
  (units.ext.comp subtype.val_injective)

lemma card_roots_of_unity : fintype.card (roots_of_unity k R) ≤ k :=
calc  fintype.card (roots_of_unity k R)
    = fintype.card {x // x ∈ nth_roots k (1 : R)} : fintype.card_congr (roots_of_unity_equiv_nth_roots k R)
... ≤ (nth_roots k (1 : R)).attach.card           : multiset.card_le_of_le (multiset.erase_dup_le _)
... = (nth_roots k (1 : R)).card                  : multiset.card_attach
... ≤ k                                           : card_nth_roots k 1

end roots_of_unity

namespace units

/-- A unit `ζ` is a primitive `k`-th root of unity if `ζ ^ k = 1`,
but `ζ ^ i ≠ 1` for all positive strict divisors of `k`. -/
structure is_primitive_root (ζ : units M) (k : ℕ+) : Prop :=
(mem_roots_of_unity : ζ ∈ roots_of_unity k M)
(primitive : ∀ (i : ℕ+) (hi1 : i < k) (hi2 : i ∣ k), ζ ∉ roots_of_unity i M)

namespace is_primitive_root

lemma pow_eq_one {ζ : units M} (h : ζ.is_primitive_root k) :
  ζ ^ (k : ℕ) = 1 := h.mem_roots_of_unity

lemma gpow_eq_one {ζ : units M} (h : ζ.is_primitive_root k) :
  ζ ^ (k : ℤ) = 1 := h.mem_roots_of_unity

lemma not_mem_roots_of_unity {ζ : units M} (h : ζ.is_primitive_root k) (hl : l < k) :
  ζ ∉ roots_of_unity l M :=
assume H, h.primitive (k.gcd l)
  (lt_of_le_of_lt (nat.gcd_le_right _ l.pos) hl)
  (pnat.gcd_dvd_left _ _)
  (pow_gcd_eq_one ζ h.pow_eq_one H)

lemma gpowers_eq {ζ : units R} (h : ζ.is_primitive_root k) :
  subgroup.gpowers ζ = roots_of_unity k R :=
begin
  apply subgroup.ext',
  haveI F : fintype (subgroup.gpowers ζ) := _,
  refine @set.eq_of_subset_of_card_le (units R) (subgroup.gpowers ζ) (roots_of_unity k R)
    F (roots_of_unity.fintype k R) (subgroup.gpowers_subset h.mem_roots_of_unity) _,

end

set_option trace.app_builder true

lemma eq_pow_of_mem_roots_of_unity {ζ ξ : units R}
  (h : ζ.is_primitive_root k) (hξ : ξ ∈ roots_of_unity k R) :
  ∃ (i : ℕ) (hi : i < k), ζ ^ i = ξ :=
begin
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ζ ^ n = ξ, by rwa [← h.gpowers_eq] at hξ,
  have hk0 : (0 : ℤ) < k := by exact_mod_cast k.pos,
  let i := n % k,
  have hi0 : 0 ≤ i := int.mod_nonneg _ (ne_of_gt hk0),
  lift i to ℕ using hi0 with i₀ hi₀,
  refine ⟨i₀, _, _⟩,
  { zify, rw [hi₀], exact int.mod_lt_of_pos _ hk0 },
  { rw [← gpow_coe_nat, hi₀, ← int.mod_add_div n k, gpow_add, gpow_mul,
        h.gpow_eq_one, one_gpow, mul_one] }
end

end is_primitive_root

end units
