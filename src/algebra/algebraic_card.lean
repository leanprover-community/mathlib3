/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import data.polynomial.cardinal
import ring_theory.algebraic

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `# polynomial R * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `liouville.is_transcendental`.
-/

universes u v

open cardinal polynomial
open_locale cardinal

namespace algebraic

theorem aleph_0_le_cardinal_mk_of_char_zero (R A : Type*) [comm_ring R] [is_domain R]
  [ring A] [algebra R A] [char_zero A] : ℵ₀ ≤ #{x : A // is_algebraic R x} :=
@mk_le_of_injective (ulift ℕ) {x : A | is_algebraic R x} (λ n, ⟨_, is_algebraic_nat n.down⟩)
  (λ m n hmn, by simpa using hmn)

section lift

variables (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] [is_domain A] [algebra R A]
  [no_zero_smul_divisors R A]

theorem cardinal_mk_lift_le_mul :
  cardinal.lift.{u v} (#{x : A // is_algebraic R x}) ≤ cardinal.lift.{v u} (#(polynomial R)) * ℵ₀ :=
begin
  rw [←mk_ulift, ←mk_ulift],
  let g : ulift.{u} {x : A | is_algebraic R x} → ulift.{v} (polynomial R) :=
    λ x, ulift.up (classical.some x.1.2),
  apply cardinal.mk_le_mk_mul_of_mk_preimage_le g (λ f, _),
  suffices : fintype (g ⁻¹' {f}),
  { exact @mk_le_aleph_0 _ (@fintype.to_encodable _ this) },
  by_cases hf : f.1 = 0,
  { convert set.fintype_empty,
    apply set.eq_empty_iff_forall_not_mem.2 (λ x hx, _),
    simp only [set.mem_preimage, set.mem_singleton_iff] at hx,
    apply_fun ulift.down at hx,
    rw hf at hx,
    exact (classical.some_spec x.1.2).1 hx },
  let h : g ⁻¹' {f} → f.down.root_set A := λ x, ⟨x.1.1.1, (mem_root_set_iff hf x.1.1.1).2 begin
    have key' : g x = f := x.2,
    simp_rw ← key',
    exact (classical.some_spec x.1.1.2).2
  end⟩,
  apply fintype.of_injective h (λ _ _ H, _),
  simp only [subtype.val_eq_coe, subtype.mk_eq_mk] at H,
  exact subtype.ext (ulift.down_injective (subtype.ext H))
end

theorem cardinal_mk_lift_le_max :
  cardinal.lift.{u v} (#{x : A // is_algebraic R x}) ≤ max (cardinal.lift.{v u} (#R)) ℵ₀ :=
(cardinal_mk_lift_le_mul R A).trans $
  (mul_le_mul_right' (lift_le.2 cardinal_mk_le_max) _).trans $ by simp [le_total]

theorem cardinal_mk_lift_le_of_infinite [infinite R] :
  cardinal.lift.{u v} (#{x : A // is_algebraic R x}) ≤ cardinal.lift.{v u} (#R) :=
(cardinal_mk_lift_le_max R A).trans $ by simp

variable [encodable R]

@[simp] theorem countable_of_encodable : set.countable {x : A | is_algebraic R x} :=
begin
  rw [←mk_set_le_aleph_0, ←lift_le],
  apply (cardinal_mk_lift_le_max R A).trans,
  simp
end

@[simp] theorem cardinal_mk_of_encodable_of_char_zero [char_zero A] [is_domain R] :
  #{x : A // is_algebraic R x} = ℵ₀ :=
le_antisymm (by simp) (aleph_0_le_cardinal_mk_of_char_zero R A)

end lift

section non_lift

variables (R A : Type u) [comm_ring R] [comm_ring A] [is_domain A] [algebra R A]
  [no_zero_smul_divisors R A]

theorem cardinal_mk_le_mul : #{x : A // is_algebraic R x} ≤ #(polynomial R) * ℵ₀ :=
by { rw [←lift_id (#_), ←lift_id (#(polynomial R))], exact cardinal_mk_lift_le_mul R A }

theorem cardinal_mk_le_max : #{x : A // is_algebraic R x} ≤ max (#R) ℵ₀ :=
by { rw [←lift_id (#_), ←lift_id (#R)], exact cardinal_mk_lift_le_max R A }

theorem cardinal_mk_le_of_infinite [infinite R] : #{x : A // is_algebraic R x} ≤ #R :=
(cardinal_mk_le_max R A).trans $ by simp

end non_lift

end algebraic
