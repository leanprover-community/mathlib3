import group_theory.congruence
import group_theory.group_action.symmetric
import algebra.module.basic
import algebra.free_monoid

/-!
# Tensor product of modules over semirings.

This file constructs the tensor product of modules over semirings. Given a semiring
`R` and modules over it `M` and `N`, the standard construction of the tensor product is
`tensor_product R M N`. It is also a module over `R`.

It comes with a canonical bilinear map `M → N → tensor_product R M N`.

Given any bilinear map `M → N → P`, there is a unique linear map `tensor_product R M N → P` whose
composition with the canonical bilinear map `M → N → tensor_product R M N` is the given bilinear
map `M → N → P`.

We start by proving basic lemmas about bilinear maps.

## Notations

This file uses the localized notation `M ⊗ N` and `M ⊗[R] N` for `tensor_product R M N`, as well
as `m ⊗ₜ n` and `m ⊗ₜ[R] n` for `tensor_product.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

variables {R R' M N : Type*} [semiring R]
variables [add_comm_monoid M] [add_comm_monoid N]
variables [module Rᵒᵖ M] [module R N]

include R

variables (M N)

namespace tensor_product

section
-- open free_add_monoid
variables (R)

/-- The relation on `free_add_monoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (M × N) → free_add_monoid (M × N) → Prop
| of_zero_left : ∀ n : N, eqv (free_add_monoid.of (0, n)) 0
| of_zero_right : ∀ m : M, eqv (free_add_monoid.of (m, 0)) 0
| of_add_left : ∀ (m₁ m₂ : M) (n : N), eqv
    (free_add_monoid.of (m₁, n) + free_add_monoid.of (m₂, n)) (free_add_monoid.of (m₁ + m₂, n))
| of_add_right : ∀ (m : M) (n₁ n₂ : N), eqv
    (free_add_monoid.of (m, n₁) + free_add_monoid.of (m, n₂)) (free_add_monoid.of (m, n₁ + n₂))
| of_smul : ∀ (r : R) (m : M) (n : N), eqv
    (free_add_monoid.of (m <• r, n)) (free_add_monoid.of (m, r • n))
| add_comm : ∀ x y, eqv (x + y) (y + x)
end

end tensor_product

variables (R)

/-- The tensor product of two modules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open_locale tensor_product`. -/
def tensor_product : Type* :=
(add_con_gen (tensor_product.eqv R M N)).quotient

variables {R}

localized "infix ` ⊗ `:100 := tensor_product _" in tensor_product
localized "notation M ` ⊗[`:100 R `] `:0 N:100 := tensor_product R M N" in tensor_product

namespace tensor_product

instance : add_zero_class (M ⊗[R] N) :=
{ .. (add_con_gen (tensor_product.eqv R M N)).add_monoid }

instance : add_comm_semigroup (M ⊗[R] N) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (tensor_product.eqv R M N)).add_monoid }

instance : inhabited (M ⊗[R] N) := ⟨0⟩

variables (R) {M N}
/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open_locale tensor_product`. -/
def tmul (m : M) (n : N) : M ⊗[R] N := add_con.mk' _ $ free_add_monoid.of (m, n)
variables {R}

infix ` ⊗ₜ `:100 := tmul _
notation x ` ⊗ₜ[`:100 R `] `:0 y:100 := tmul R x y

@[elab_as_eliminator]
protected theorem induction_on
  {C : (M ⊗[R] N) → Prop}
  (z : M ⊗[R] N)
  (C0 : C 0)
  (C1 : ∀ {x : M}{y : N}, C $ x ⊗ₜ[R] y)
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
add_con.induction_on z $ λ x, free_add_monoid.rec_on x C0 $ λ ⟨m, n⟩ y ih,
by { rw add_con.coe_add, exact Cp C1 ih }

variables (M)
@[simp] lemma zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_left _
variables {M}

lemma add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
eq.symm $ quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_add_left _ _ _

variables (N)
@[simp] lemma tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_right _
variables {N}

lemma tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
eq.symm $ quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_add_right _ _ _

section

variables (R R' M N)

/--
A typeclass for `has_scalar` structures which can be moved across a tensor product.

This typeclass is generated automatically from a `is_scalar_tower` instance, but exists so that
we can also add an instance for `add_comm_group.int_module`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `module R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `tensor_product.smul_tmul`, `tensor_product.smul_tmul'`, or `tensor_product.tmul_smul` is
used.
-/
class compatible_smul [has_scalar R'ᵒᵖ M] [has_scalar R' N] :=
(rsmul_tmul : ∀ (r : R') (m : M) (n : N), (m <• r) ⊗ₜ n = m ⊗ₜ[R] (r • n))

@[priority 100]
instance compatible_smul.is_scalar_tower
  [has_scalar R' R] [has_scalar R'ᵒᵖ R] [is_symmetric_smul R' R]
  [has_scalar R'ᵒᵖ M] [is_scalar_tower R'ᵒᵖ Rᵒᵖ M]
  [has_scalar R' N] [is_scalar_tower R' R N] :
  compatible_smul R R' M N :=
⟨λ r m n, begin
  conv_lhs {rw ← one_smul Rᵒᵖ m},
  conv_rhs {rw ← one_smul R n},
  rw [←smul_assoc, ←smul_assoc, ←opposite.op_one, ←op_smul_eq_op_smul_op],
  exact quotient.sound' (add_con_gen.rel.of _ _ (eqv.of_smul (r • (1 : R)) m n)),
end⟩

instance compatible_smul.self : compatible_smul R R M N :=
⟨λ r m n, quotient.sound' (add_con_gen.rel.of _ _ (eqv.of_smul r m n))⟩

/-- A right `smul` can be moved from one side of the product to the other. -/
lemma rsmul_tmul [has_scalar R'ᵒᵖ M] [has_scalar R' N] [compatible_smul R R' M N]
  (r : R') (m : M) (n : N) : (m <• r) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
compatible_smul.rsmul_tmul _ _ _

variables {R R' M N}
/-- In the case of a symmetric action on `M`, we can move a `smul` vom the left to the
right of the tensor product. -/
lemma smul_tmul [has_scalar R' M] [has_scalar R'ᵒᵖ M] [is_symmetric_smul R' M]
  [has_scalar R' N] [compatible_smul R R' M N] (r : R') (m : M) (n : N) :
  (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
by rw [←is_symmetric_smul.op_smul_eq_smul, ←rsmul_tmul]

instance : add_comm_monoid (M ⊗[R] N) :=
{ .. tensor_product.add_comm_semigroup _ _, .. tensor_product.add_zero_class _ _}

end

end tensor_product
