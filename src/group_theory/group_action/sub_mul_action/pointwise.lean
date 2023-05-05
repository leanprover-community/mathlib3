/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import group_theory.group_action.sub_mul_action

/-!
# Pointwise monoid structures on sub_mul_action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides `sub_mul_action.monoid` and weaker typeclasses, which show that `sub_mul_action`s
inherit the same pointwise multiplications as sets.

To match `submodule.idem_semiring`, we do not put these in the `pointwise` locale.

-/

open_locale pointwise

variables {R M : Type*}

namespace sub_mul_action

section has_one
variables [monoid R] [mul_action R M] [has_one M]

instance : has_one (sub_mul_action R M) :=
{ one := { carrier := set.range (λ r : R, r • (1 : M)),
           smul_mem' := λ r m ⟨r', hr'⟩, hr' ▸ ⟨r * r', mul_smul _ _ _⟩ } }

lemma coe_one : ↑(1 : sub_mul_action R M) = set.range (λ r : R, r • (1 : M)) := rfl

@[simp] lemma mem_one {x : M} : x ∈ (1 : sub_mul_action R M) ↔ ∃ r : R, r • 1 = x := iff.rfl

lemma subset_coe_one : (1 : set M) ⊆ (1 : sub_mul_action R M) :=
λ x hx, ⟨1, (one_smul _ _).trans hx.symm⟩

end has_one

section has_mul
variables [monoid R] [mul_action R M] [has_mul M] [is_scalar_tower R M M]

instance : has_mul (sub_mul_action R M) :=
{ mul := λ p q, { carrier := set.image2 (*) p q,
                  smul_mem' := λ r m ⟨m₁, m₂, hm₁, hm₂, h⟩,
                    h ▸ smul_mul_assoc r m₁ m₂ ▸ set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ } }

@[norm_cast] lemma coe_mul (p q : sub_mul_action R M) : ↑(p * q) = (p * q : set M) := rfl

lemma mem_mul {p q : sub_mul_action R M} {x : M} : x ∈ p * q ↔ ∃ y z, y ∈ p ∧ z ∈ q ∧ y * z = x :=
set.mem_mul

end has_mul

section mul_one_class
variables [monoid R] [mul_action R M] [mul_one_class M] [is_scalar_tower R M M]
  [smul_comm_class R M M]

instance : mul_one_class (sub_mul_action R M) :=
{ mul := (*),
  one := 1,
  mul_one := λ a, begin
    ext,
    simp only [mem_mul, mem_one, mul_smul_comm, exists_and_distrib_left, exists_exists_eq_and,
      mul_one],
    split,
    { rintros ⟨y, hy, r, rfl⟩,
      exact smul_mem _ _ hy },
    { intro hx,
      exact ⟨x, hx, 1, one_smul _ _⟩ },
  end,
  one_mul := λ a, begin
    ext,
    simp only [mem_mul, mem_one, smul_mul_assoc, exists_and_distrib_left, exists_exists_eq_and,
      one_mul],
    refine ⟨_, λ hx, ⟨1, x, hx, one_smul _ _⟩⟩,
    rintro ⟨r, y, hy, rfl⟩,
    exact smul_mem _ _ hy,
  end, }

end mul_one_class

section semigroup
variables [monoid R] [mul_action R M] [semigroup M] [is_scalar_tower R M M]

instance : semigroup (sub_mul_action R M) :=
{ mul := (*),
  mul_assoc := λ a b c, set_like.coe_injective (mul_assoc (_ : set _) _ _), }

end semigroup

section monoid
variables [monoid R] [mul_action R M] [monoid M] [is_scalar_tower R M M] [smul_comm_class R M M]

instance : monoid (sub_mul_action R M) :=
{ mul := (*),
  one := 1,
  ..sub_mul_action.semigroup,
  ..sub_mul_action.mul_one_class }

lemma coe_pow (p : sub_mul_action R M) : ∀ {n : ℕ} (hn : n ≠ 0), ↑(p ^ n) = (p ^ n : set M)
| 0 hn := (hn rfl).elim
| 1 hn := by rw [pow_one, pow_one]
| (n + 2) hn := by rw [pow_succ _ (n + 1), pow_succ _ (n + 1), coe_mul, coe_pow (n.succ_ne_zero)]

lemma subset_coe_pow (p : sub_mul_action R M) : ∀ {n : ℕ},
   (p ^ n : set M) ⊆ ↑(p ^ n)
| 0 := by { rw [pow_zero, pow_zero], exact subset_coe_one }
| (n + 1) := (coe_pow p n.succ_ne_zero).superset

end monoid

end sub_mul_action
