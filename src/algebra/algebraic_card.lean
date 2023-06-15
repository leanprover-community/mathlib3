/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.polynomial.cardinal
import ring_theory.algebraic

/-!
### Cardinality of algebraic numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `# R[X] * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `liouville.is_transcendental`.
-/

universes u v

open cardinal polynomial set
open_locale cardinal polynomial

namespace algebraic

lemma infinite_of_char_zero (R A : Type*) [comm_ring R] [is_domain R]
  [ring A] [algebra R A] [char_zero A] : {x : A | is_algebraic R x}.infinite :=
infinite_of_injective_forall_mem nat.cast_injective is_algebraic_nat

theorem aleph_0_le_cardinal_mk_of_char_zero (R A : Type*) [comm_ring R] [is_domain R]
  [ring A] [algebra R A] [char_zero A] : ℵ₀ ≤ #{x : A // is_algebraic R x} :=
infinite_iff.1 (set.infinite_coe_iff.2 $ infinite_of_char_zero R A)

section lift

variables (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] [is_domain A] [algebra R A]
  [no_zero_smul_divisors R A]

theorem cardinal_mk_lift_le_mul :
  cardinal.lift.{u} (#{x : A // is_algebraic R x}) ≤ cardinal.lift.{v} #(R[X]) * ℵ₀ :=
begin
  rw [←mk_ulift, ←mk_ulift],
  choose g hg₁ hg₂ using λ x : {x : A | is_algebraic R x}, x.coe_prop,
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g (λ f, _),
  rw [lift_le_aleph_0, le_aleph_0_iff_set_countable],
  suffices : maps_to coe (g ⁻¹' {f}) (f.root_set A),
    from this.countable_of_inj_on (subtype.coe_injective.inj_on _) (f.root_set_finite A).countable,
  rintro x (rfl : g x = f),
  exact mem_root_set.2 ⟨hg₁ x, hg₂ x⟩
end

theorem cardinal_mk_lift_le_max :
  cardinal.lift.{u} (#{x : A // is_algebraic R x}) ≤ max (cardinal.lift.{v} (#R)) ℵ₀ :=
(cardinal_mk_lift_le_mul R A).trans $
  (mul_le_mul_right' (lift_le.2 cardinal_mk_le_max) _).trans $ by simp

@[simp] lemma cardinal_mk_lift_of_infinite [infinite R] :
  cardinal.lift.{u} (#{x : A // is_algebraic R x}) = cardinal.lift.{v} (#R) :=
((cardinal_mk_lift_le_max R A).trans_eq (max_eq_left $ aleph_0_le_mk _)).antisymm $
  lift_mk_le'.2 ⟨⟨λ x, ⟨algebra_map R A x, is_algebraic_algebra_map _⟩,
    λ x y h, no_zero_smul_divisors.algebra_map_injective R A (subtype.ext_iff.1 h)⟩⟩

variable [countable R]

@[simp] protected theorem countable : set.countable {x : A | is_algebraic R x} :=
begin
  rw [←le_aleph_0_iff_set_countable, ←lift_le],
  apply (cardinal_mk_lift_le_max R A).trans,
  simp
end

@[simp] theorem cardinal_mk_of_countble_of_char_zero [char_zero A] [is_domain R] :
  #{x : A // is_algebraic R x} = ℵ₀ :=
(algebraic.countable R A).le_aleph_0.antisymm (aleph_0_le_cardinal_mk_of_char_zero R A)

end lift

section non_lift

variables (R A : Type u) [comm_ring R] [comm_ring A] [is_domain A] [algebra R A]
  [no_zero_smul_divisors R A]

theorem cardinal_mk_le_mul : #{x : A // is_algebraic R x} ≤ #R[X] * ℵ₀ :=
by { rw [←lift_id (#_), ←lift_id #R[X]], exact cardinal_mk_lift_le_mul R A }

theorem cardinal_mk_le_max : #{x : A // is_algebraic R x} ≤ max (#R) ℵ₀ :=
by { rw [←lift_id (#_), ←lift_id (#R)], exact cardinal_mk_lift_le_max R A }

@[simp] theorem cardinal_mk_of_infinite [infinite R] : #{x : A // is_algebraic R x} = #R :=
lift_inj.1 $ cardinal_mk_lift_of_infinite R A

end non_lift

end algebraic
