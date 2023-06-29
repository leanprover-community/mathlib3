/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.hom.ring
import data.polynomial.reverse

/-!
# Floors and ceils aren't preserved under ordered ring homomorphisms

Intuitively, if `f : α → β` is an ordered ring homomorphism, then floors and ceils should be
preserved by `f` because:
* `f` preserves the naturals/integers in `α` and `β` because it's a ring hom.
* `f` preserves what's between `n` and `n + 1` because it's monotone.

However, there is a catch. Potentially something whose floor was `n` could
get mapped to `n + 1`, and this has floor `n + 1`, not `n`. Note that this is at most an off by one
error.

This pathology disappears if you require `f` to be strictly monotone or `α` to be archimedean.

## The counterexample

Consider `ℤ[ε]` (`int_with_epsilons`), the integers with infinitesimals adjoined. This is a linearly
ordered commutative floor ring (`int_with_epsilons.linear_ordered_comm_ring`,
`int_with_epsilons.floor_ring`).

The map `f : ℤ[ε] → ℤ` that forgets about the epsilons (`int_with_epsilons.forget_epsilons`) is an
ordered ring homomorphism.

But it does not preserve floors (nor ceils) as `⌊-ε⌋ = -1` while `⌊f (-ε)⌋ = ⌊0⌋ = 0`
(`int_with_epsilons.forget_epsilons_floor_lt`, `int_with_epsilons.lt_forget_epsilons_ceil`).
-/

noncomputable theory

open function int polynomial
open_locale polynomial

/-- The integers with infinitesimals adjoined. -/
@[derive [comm_ring, nontrivial, inhabited]] def int_with_epsilon := ℤ[X]

local notation `ℤ[ε]` := int_with_epsilon

local notation `ε` := (X : ℤ[ε])

namespace int_with_epsilon

instance : linear_order ℤ[ε] := linear_order.lift' (to_lex ∘ coeff) coeff_injective

instance : ordered_add_comm_group ℤ[ε] :=
by refine (to_lex.injective.comp coeff_injective).ordered_add_comm_group _ _ _ _ _ _ _;
  refl <|> intros; ext; simp [←nsmul_eq_mul, ←zsmul_eq_mul]

lemma pos_iff {p : ℤ[ε]} : 0 < p ↔ 0 < p.trailing_coeff :=
begin
  rw trailing_coeff,
  refine ⟨_, λ h,
    ⟨p.nat_trailing_degree, λ m hm, (coeff_eq_zero_of_lt_nat_trailing_degree hm).symm, h⟩⟩,
  rintro ⟨n, hn⟩,
  convert hn.2,
  exact (nat_trailing_degree_le_of_ne_zero hn.2.ne').antisymm
    (le_nat_trailing_degree (by { rintro rfl, cases hn.2.false }) $ λ m hm, (hn.1 _ hm).symm),
end

instance : linear_ordered_comm_ring ℤ[ε] :=
{ zero_le_one := or.inr ⟨0, by simp⟩,
  mul_pos := λ p q, by { simp_rw [pos_iff, trailing_coeff_mul], exact mul_pos },
  ..int_with_epsilon.linear_order, ..int_with_epsilon.comm_ring,
  ..int_with_epsilon.ordered_add_comm_group, ..int_with_epsilon.nontrivial }

instance : floor_ring ℤ[ε] :=
floor_ring.of_floor _ (λ p, if (p.coeff 0 : ℤ[ε]) ≤ p then p.coeff 0 else p.coeff 0 - 1) $ λ p q,
  begin
    simp_rw [←not_lt, not_iff_not],
    split,
    { split_ifs,
      { rintro ⟨_ | n, hn⟩,
        { refine (sub_one_lt _).trans _,
          simpa using hn },
        { dsimp at hn,
          simp [hn.1 _ n.zero_lt_succ] } },
      { exact λ h', cast_lt.1 ((not_lt.1 h).trans_lt h') } },
    { split_ifs,
      { exact λ h', h.trans_le (cast_le.2 $ sub_one_lt_iff.1 h') },
      { exact λ h', ⟨0, by simpa using h'⟩ } }
  end

/-- The ordered ring homomorphisms from `ℤ[ε]` to `ℤ` that "forgets" the `ε`s. -/
def forget_epsilons : ℤ[ε] →+*o ℤ :=
{ to_fun := λ p, coeff p 0,
  map_zero' := coeff_zero _,
  map_one' := coeff_one_zero,
  map_add' := λ _ _, coeff_add _ _ _,
  map_mul' := mul_coeff_zero,
  monotone' := monotone_iff_forall_lt.2 begin
    rintro p q ⟨n, hn⟩,
    cases n,
    { exact hn.2.le },
    { exact (hn.1 _ n.zero_lt_succ).le }
  end }

@[simp] lemma forget_epsilons_apply (p : ℤ[ε]) : forget_epsilons p = coeff p 0 := rfl

/-- The floor of `n - ε` is `n - 1` but its image under `forget_epsilons` is `n`, whose floor is
itself. -/
lemma forget_epsilons_floor_lt (n : ℤ) :
  forget_epsilons ⌊(n - ε : ℤ[ε])⌋ < ⌊forget_epsilons (n - ε)⌋ :=
begin
  suffices : ⌊(n - ε : ℤ[ε])⌋ = n - 1,
  { simp [this] },
  have : (0 : ℤ[ε]) < ε := ⟨1, by simp⟩,
  exact (if_neg $ by simp [this]).trans (by simp),
end

/-- The ceil of `n + ε` is `n + 1` but its image under `forget_epsilons` is `n`, whose ceil is
itself. -/
lemma lt_forget_epsilons_ceil (n : ℤ) :
  ⌈forget_epsilons (n + ε)⌉ < forget_epsilons ⌈(n + ε : ℤ[ε])⌉ :=
begin
  rw [←neg_lt_neg_iff, ←map_neg, ←cast_neg, ←floor_neg, ←floor_neg, ←map_neg, neg_add', ←cast_neg],
  exact forget_epsilons_floor_lt _,
end

end int_with_epsilon
