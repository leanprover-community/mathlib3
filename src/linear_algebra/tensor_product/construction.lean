/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/

import linear_algebra.tensor_product.basic

/-!
# Construction of the tensor product of modules over commutative semirings.

This file constructs the tensor product of modules over commutative semirings. Given a semiring
`R` and modules over it `M` and `N`, the standard construction of the tensor product is
`tensor_product R M N`. It is also a module over `R`.

It comes with a canonical bilinear map `M → N → tensor_product R M N`.

Given any bilinear map `M → N → P`, there is a unique linear map `tensor_product R M N → P` whose
composition with the canonical bilinear map `M → N → tensor_product R M N` is the given bilinear
map `M → N → P`.

We start by proving basic lemmas about bilinear maps.

## Notations

This file uses the localized notation `M ⊗ₜ N` and `M ⊗ₜ[R] N` for `tensor_product R M N`, as well
as `m ⊗[R] n` and `m ⊗[R] n` for `tensor_product.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

open_locale tensor_product

section semiring
variables {R : Type*} [comm_semiring R]
variables {R' : Type*} [monoid R']
variables {R'' : Type*} [semiring R'']
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}

variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q]
  [add_comm_monoid S]
variables [module R M] [module R N] [module R P] [module R Q] [module R S]
variables [distrib_mul_action R' M]
variables [module R'' M]
include R

variables (M N)

variables (R)

/-- The tensor product of two modules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗[R] N` and `M ⊗ₜ[R] N`, accessed by `open_locale tensor_product`. -/
def tensor_product : Type* :=
(add_con_gen (tensor_product.eqv R M N)).quotient

variables {R}

localized "infix ` ⊗ₜ `:100 := tensor_product _" in tensor_product
localized "notation M ` ⊗ₜ[`:100 R `] `:0 N:100 := tensor_product R M N" in tensor_product

namespace tensor_product

section module

instance : add_zero_class (M ⊗ₜ[R] N) :=
{ .. (add_con_gen (tensor_product.eqv R M N)).add_monoid }

instance : add_comm_semigroup (M ⊗ₜ[R] N) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (tensor_product.eqv R M N)).add_monoid }

instance : inhabited (M ⊗ₜ[R] N) := ⟨0⟩

protected def has_tmul : has_tmul R M N (M ⊗ₜ[R] N) :=
{ tmul := λ m n, add_con.mk' _ $ free_add_monoid.of (m, n) }

local attribute [instance] tensor_product.has_tmul

lemma tmul_def (m : M) (n : N) : m ⊗[R] n = add_con.mk' _ (free_add_monoid.of (m, n)) := rfl

variables {R} {M N}

@[elab_as_eliminator]
protected theorem induction_on
  {C : (M ⊗ₜ[R] N) → Prop}
  (z : M ⊗ₜ[R] N)
  (C0 : C 0)
  (C1 : ∀ {x:M} {y:N}, C $ x ⊗[R] y)
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
add_con.induction_on z $ λ x, free_add_monoid.rec_on x C0 $ λ ⟨m, n⟩ y ih,
by { rw add_con.coe_add, exact Cp C1 ih }

variables (M)
@[simp] lemma zero_tmul (n : N) : (0 : M) ⊗[R] n = (0:_) :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_left _
variables {M}

lemma add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗[R] n = m₁ ⊗[R] n + m₂ ⊗[R] n :=
eq.symm $ quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_add_left _ _ _

variables (N)
@[simp] lemma tmul_zero (m : M) : m ⊗[R] (0 : N) = (0:_) :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_right _
variables {N}

lemma tmul_add (m : M) (n₁ n₂ : N) : m ⊗[R] (n₁ + n₂) = m ⊗[R] n₁ + m ⊗[R] n₂ :=
eq.symm $ quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_add_right _ _ _

section

variables (R R' M N)

/--
A typeclass for `has_scalar` structures which can be moved across a tensor product.

This typeclass is generated automatically from a `is_scalar_tower` instance, but exists so that
we can also add an instance for `add_comm_group.int_module`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `module R' (M ⊗ₜ[R] N)` is available even without this typeclass on `R'`; it's only
needed if `tensor_product.smul_tmul`, `tensor_product.smul_tmul'`, or `tensor_product.tmul_smul` is
used.
-/
class compatible_smul [distrib_mul_action R' N] :=
(smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗[R] n = m ⊗[R] (r • n))

end

/-- Note that this provides the default `compatible_smul R R M N` instance through
`mul_action.is_scalar_tower.left`. -/
@[priority 100]
instance compatible_smul.is_scalar_tower
  [has_scalar R' R] [is_scalar_tower R' R M] [distrib_mul_action R' N] [is_scalar_tower R' R N] :
  compatible_smul R R' M N :=
⟨λ r m n, begin
  conv_lhs {rw ← one_smul R m},
  conv_rhs {rw ← one_smul R n},
  rw [←smul_assoc, ←smul_assoc],
  exact (quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _),
end⟩

/-- `smul` can be moved from one side of the product to the other .-/
lemma smul_tmul [distrib_mul_action R' N] [compatible_smul R R' M N] (r : R') (m : M) (n : N) :
  (r • m) ⊗[R] n = m ⊗[R] (r • n) :=
compatible_smul.smul_tmul _ _ _

instance : add_monoid (M ⊗ₜ[R] N) := by { delta tensor_product, apply_instance }

/-- Auxiliary function to defining scalar multiplication on tensor product. -/
def smul.aux {R' : Type*} [has_scalar R' M] (r : R') : free_add_monoid (M × N) →+ M ⊗ₜ[R] N :=
free_add_monoid.lift $ λ p : M × N, (r • p.1) ⊗[R] p.2

theorem smul.aux_of {R' : Type*} [has_scalar R' M] (r : R') (m : M) (n : N) :
  smul.aux r (free_add_monoid.of (m, n)) = (r • m) ⊗[R] n :=
rfl

variables [smul_comm_class R R' M]
variables [smul_comm_class R R'' M]

/-- Given two modules over a commutative semiring `R`, if one of the factors carries a
(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module which has the `R'`
action. Two natural ways in which this situation arises are:
 * Extension of scalars
 * A tensor product of a group representation with a module not carrying an action

Note that in the special case that `R = R'`, since `R` is commutative, we just get the usual scalar
action on a tensor product of two modules. This special case is important enough that, for
performance reasons, we define it explicitly below. -/
instance left_has_scalar : has_scalar R' (M ⊗ₜ[R] N) :=
⟨λ r, (add_con_gen (tensor_product.eqv R M N)).lift (smul.aux r : _ →+ M ⊗ₜ[R] N) $
add_con.add_con_gen_le $ λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero_left n)       := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, smul.aux_of, smul_zero, zero_tmul]
| _, _, (eqv.of_zero_right m)      := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, smul.aux_of, tmul_zero]
| _, _, (eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, smul.aux_of, smul_add, add_tmul]
| _, _, (eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, smul.aux_of, tmul_add]
| _, _, (eqv.of_smul s m n)        := (add_con.ker_rel _).2 $
    by rw [smul.aux_of, smul.aux_of, ←smul_comm, smul_tmul]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end⟩

instance : has_scalar R (M ⊗ₜ[R] N) := tensor_product.left_has_scalar

protected theorem smul_zero (r : R') : (r • 0 : M ⊗ₜ[R] N) = 0 :=
add_monoid_hom.map_zero _

protected theorem smul_add (r : R') (x y : M ⊗ₜ[R] N) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

protected theorem zero_smul (x : M ⊗ₜ[R] N) : (0 : R'') • x = 0 :=
have ∀ (r : R'') (m : M) (n : N), r • (m ⊗[R] n) = (r • m) ⊗[R] n := λ _ _ _, rfl,
tensor_product.induction_on x
  (by rw tensor_product.smul_zero)
  (λ m n, by rw [this, zero_smul, zero_tmul])
  (λ x y ihx ihy, by rw [tensor_product.smul_add, ihx, ihy, add_zero])

protected theorem one_smul (x : M ⊗ₜ[R] N) : (1 : R') • x = x :=
have ∀ (r : R') (m : M) (n : N), r • (m ⊗[R] n) = (r • m) ⊗[R] n := λ _ _ _, rfl,
tensor_product.induction_on x
  (by rw tensor_product.smul_zero)
  (λ m n, by rw [this, one_smul])
  (λ x y ihx ihy, by rw [tensor_product.smul_add, ihx, ihy])

protected theorem add_smul (r s : R'') (x : M ⊗ₜ[R] N) : (r + s) • x = r • x + s • x :=
have ∀ (r : R'') (m : M) (n : N), r • (m ⊗[R] n) = (r • m) ⊗[R] n := λ _ _ _, rfl,
tensor_product.induction_on x
  (by simp_rw [tensor_product.smul_zero, add_zero])
  (λ m n, by simp_rw [this, add_smul, add_tmul])
  (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy, add_add_add_comm] })

instance : add_comm_monoid (M ⊗ₜ[R] N) :=
{ nsmul := λ n v, n • v,
  nsmul_zero' := by simp [tensor_product.zero_smul],
  nsmul_succ' := by simp [nat.succ_eq_one_add, tensor_product.one_smul, tensor_product.add_smul],
  .. tensor_product.add_comm_semigroup _ _, .. tensor_product.add_zero_class _ _}

instance left_distrib_mul_action : distrib_mul_action R' (M ⊗ₜ[R] N) :=
have ∀ (r : R') (m : M) (n : N), r • (m ⊗[R] n) = (r • m) ⊗[R] n := λ _ _ _, rfl,
{ smul := (•),
  smul_add := λ r x y, tensor_product.smul_add r x y,
  mul_smul := λ r s x, tensor_product.induction_on x
    (by simp_rw tensor_product.smul_zero)
    (λ m n, by simp_rw [this, mul_smul])
    (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy] }),
  one_smul := tensor_product.one_smul,
  smul_zero := tensor_product.smul_zero }

instance : distrib_mul_action R (M ⊗ₜ[R] N) := tensor_product.left_distrib_mul_action

theorem smul_tmul' (r : R') (m : M) (n : N) :
  r • (m ⊗[R] n) = (r • m) ⊗[R] n :=
rfl

@[simp] lemma tmul_smul
  [distrib_mul_action R' N] [compatible_smul R R' M N] (r : R') (x : M) (y : N) :
  x ⊗[R] (r • y) = r • (x ⊗[R] y) :=
(smul_tmul _ _ _).symm

instance left_module : module R'' (M ⊗ₜ[R] N) :=
{ smul := (•),
  add_smul := tensor_product.add_smul,
  zero_smul := tensor_product.zero_smul,
  ..tensor_product.left_distrib_mul_action }

instance : module R (M ⊗ₜ[R] N) := tensor_product.left_module

variables (R M N)

/-- The simple (aka pure) elements span the tensor product. -/
lemma span_tmul_eq_top :
  submodule.span R { t : M ⊗ₜ[R] N | ∃ (m:M) (n:N), m ⊗[R] n = t } = ⊤ :=
begin
  ext t, simp only [submodule.mem_top, iff_true],
  apply t.induction_on,
  { exact submodule.zero_mem _, },
  { intros m n, apply submodule.subset_span, use [m, n], },
  { intros t₁ t₂ ht₁ ht₂, exact submodule.add_mem _ ht₁ ht₂, },
end

protected def is_tensor_product : is_tensor_product R M N (M ⊗ₜ[R] N) :=
{ smul_tmul' := λ c m n, (smul_tmul' c m n).symm,
  tmul_smul' := λ c m n, (tmul_smul c m n),
  add_tmul' := add_tmul,
  tmul_add' := tmul_add,
  span_tmul := span_tmul_eq_top R M N,
  add_con :=
  begin
    rw ← add_con.add_ker_mk_eq (add_con_gen (eqv R M N)),
    suffices : ⇑(free_add_monoid.lift (tmul' R M N (M ⊗ₜ N))) =
      (coe : free_add_monoid (M × N) → (add_con_gen (eqv R M N)).quotient),
    { simpa only [← this] },
    show _ = ⇑(add_con_gen (eqv R M N)).mk', congr' 1,
    refine free_add_monoid.hom_eq _,
    rintro ⟨m, n⟩,
    simpa only [free_add_monoid.lift_eval_of, add_con.coe_mk', tmul'_apply]
  end }

local attribute [instance] tensor_product.is_tensor_product

variables {R M N}

section

-- Like `R'`, `R'₂` provides a `distrib_mul_action R'₂ (M ⊗ₜ[R] N)`
variables {R'₂ : Type*} [monoid R'₂] [distrib_mul_action R'₂ M]
variables [smul_comm_class R R'₂ M] [has_scalar R'₂ R']

/-- `is_scalar_tower R'₂ R' M` implies `is_scalar_tower R'₂ R' (M ⊗ₜ[R] N)` -/
instance is_scalar_tower_left [is_scalar_tower R'₂ R' M] :
  is_scalar_tower R'₂ R' (M ⊗ₜ[R] N) :=
⟨λ s r x, tensor_product.induction_on x
  (by simp)
  (λ m n, by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc])
  (λ x y ihx ihy, by rw [smul_add, smul_add, smul_add, ihx, ihy])⟩

variables [distrib_mul_action R'₂ N] [distrib_mul_action R' N]
variables [compatible_smul R R'₂ M N] [compatible_smul R R' M N]

/-- `is_scalar_tower R'₂ R' N` implies `is_scalar_tower R'₂ R' (M ⊗ₜ[R] N)` -/
instance is_scalar_tower_right [is_scalar_tower R'₂ R' N] :
    is_scalar_tower R'₂ R' (M ⊗ₜ[R] N) :=
⟨λ s r x, tensor_product.induction_on x
  (by simp)
  (λ m n, by rw [←tmul_smul, ←tmul_smul, ←tmul_smul, smul_assoc])
  (λ x y ihx ihy, by rw [smul_add, smul_add, smul_add, ihx, ihy])⟩

end

/-- A short-cut instance for the common case, where the requirements for the `compatible_smul`
instances are sufficient. -/
instance is_scalar_tower [has_scalar R' R] [is_scalar_tower R' R M] :
  is_scalar_tower R' R (M ⊗ₜ[R] N) :=
tensor_product.is_scalar_tower_left  -- or right

end module

local attribute [instance] tensor_product.is_tensor_product

section UMP

variables {M N P Q}
variables (f : M →ₗ[R] N →ₗ[R] P)

/-- Auxiliary function to constructing a linear map `M ⊗[R] N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗[R] N` is
the given bilinear map `M → N → P`. -/
def lift_aux : (M ⊗ₜ[R] N) →+ P :=
(add_con_gen (tensor_product.eqv R M N)).lift (free_add_monoid.lift $ λ p : M × N, f p.1 p.2) $
add_con.add_con_gen_le $ λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero_left n)       := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, free_add_monoid.lift_eval_of, f.map_zero₂]
| _, _, (eqv.of_zero_right m)      := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, free_add_monoid.lift_eval_of, (f m).map_zero]
| _, _, (eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, free_add_monoid.lift_eval_of, f.map_add₂]
| _, _, (eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, free_add_monoid.lift_eval_of, (f m).map_add]
| _, _, (eqv.of_smul r m n)        := (add_con.ker_rel _).2 $
    by simp_rw [free_add_monoid.lift_eval_of, f.map_smul₂, (f m).map_smul]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end

lemma lift_aux_tmul (m n) : lift_aux f (m ⊗[R] n) = f m n :=
zero_add _

variable {f}

@[simp] lemma lift_aux.smul (r : R) (x) : lift_aux f (r • x) = r • lift_aux f x :=
tensor_product.induction_on x (smul_zero _).symm
  (λ p q, by rw [← tmul_smul, lift_aux_tmul, lift_aux_tmul, (f p).map_smul])
  (λ p q ih1 ih2, by rw [smul_add, (lift_aux f).map_add, ih1, ih2, (lift_aux f).map_add, smul_add])

variable (f)
/-- Constructing a linear map `M ⊗[R] N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗[R] N` is
the given bilinear map `M → N → P`. -/
def lift' : M ⊗ₜ[R] N →ₗ[R] P :=
{ map_smul' := lift_aux.smul,
  .. lift_aux f }
variable {f}

@[simp] lemma lift'.tmul (x y) : lift' f (x ⊗[R] y) = f x y :=
zero_add _

@[simp] lemma lift'.tmul' (x y) : (lift' f).1 (x ⊗[R] y) = f x y :=
lift'.tmul _ _

theorem ext' {g h : (M ⊗ₜ[R] N) →ₗ[R] P}
  (H : ∀ (x:M) (y:N), g (x ⊗[R] y) = h (x ⊗[R] y)) : g = h :=
linear_map.ext $ λ z, tensor_product.induction_on z (by simp_rw linear_map.map_zero) H $
λ x y ihx ihy, by rw [g.map_add, h.map_add, ihx, ihy]

theorem lift'.unique {g : (M ⊗ₜ[R] N) →ₗ[R] P} (H : ∀ x y, g (x ⊗[R] y) = f x y) :
  g = lift' f :=
ext' $ λ m n, by rw [H, lift'.tmul]

theorem lift'_tmul : lift' (tmul R M N) = linear_map.id :=
eq.symm $ lift'.unique $ λ x y, rfl

theorem lift'_compr₂ (g : P →ₗ[R] Q) : lift' (f.compr₂ g) = g.comp (lift' f) :=
eq.symm $ lift'.unique $ λ x y, by simp

theorem lift'_tmul_compr₂ (f : M ⊗ₜ[R] N →ₗ[R] P) :
  lift' ((tmul R M N).compr₂ f) = f :=
by rw [lift'_compr₂ f, lift'_tmul, linear_map.comp_id]

end UMP

end tensor_product

end semiring
