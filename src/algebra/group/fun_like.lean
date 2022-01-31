/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.module.pi
import algebra.group.inj_surj

/-!
# Algebraic operations on `fun_like` types
-/

variables (F : Type*) {ι : out_param (Type*)} {α : out_param (ι → Type*)}

class has_pointwise_zero [Π i, has_zero (α i)] [fun_like F ι α] extends has_zero F :=
(zero_apply : ∀ i : ι, (0 : F) i = 0)

@[to_additive]
class has_pointwise_one [Π i, has_one (α i)] [fun_like F ι α] extends has_one F :=
(one_apply : ∀ i : ι, (1 : F) i = 1)

class has_pointwise_add [Π i, has_add (α i)] [fun_like F ι α] extends has_add F :=
(add_apply : ∀ (f g : F) (i : ι), (f + g) i = f i + g i)

@[to_additive]
class has_pointwise_mul [Π i, has_mul (α i)] [fun_like F ι α] extends has_mul F :=
(mul_apply : ∀ (f g : F) (i : ι), (f * g) i = f i * g i)

class has_pointwise_neg [Π i, has_neg (α i)] [fun_like F ι α] extends has_neg F :=
(neg_apply : ∀ (f : F) (i : ι), (-f) i = -f i)

@[to_additive]
class has_pointwise_inv [Π i, has_inv (α i)] [fun_like F ι α] extends has_inv F :=
(inv_apply : ∀ (f : F) (i : ι), f⁻¹ i = (f i)⁻¹)

class has_pointwise_sub [Π i, has_sub (α i)] [fun_like F ι α] extends has_sub F :=
(sub_apply : ∀ (f g : F) (i : ι), (f - g) i = f i - g i)

@[to_additive]
class has_pointwise_div [Π i, has_div (α i)] [fun_like F ι α] extends has_div F :=
(div_apply : ∀ (f g : F) (i : ι), (f / g) i = f i / g i)

class has_pointwise_vadd (γ : Type*) [Π i, has_vadd γ (α i)] [fun_like F ι α]
  extends has_vadd γ F :=
(vadd_apply : ∀ (f : F) (c : γ) (i : ι), (c +ᵥ f) i = c +ᵥ f i)

@[to_additive has_pointwise_vadd]
class has_pointwise_scalar (γ : Type*) [Π i, has_scalar γ (α i)] [fun_like F ι α]
  extends has_scalar γ F :=
(smul_apply : ∀ (f : F) (c : γ) (i : ι), (c • f) i = c • f i)

@[to_additive has_pointwise_scalar]
class has_pointwise_pow (γ : Type*) [Π i, has_pow (α i) γ] [fun_like F ι α] extends has_pow F γ :=
(pow_apply : ∀ (f : F) (c : γ) (i : ι), (f ^ c) i = f i ^ c)

namespace fun_like

@[to_additive]
lemma one_apply [Π i, has_one (α i)] [fun_like F ι α] [has_pointwise_one F] (i : ι) :
  (1 : F) i = 1 :=
has_pointwise_one.one_apply i

@[simp, to_additive]
lemma coe_fn_one [Π i, has_one (α i)] [fun_like F ι α] [has_pointwise_one F] :
  ((1 : F) : Π i, α i) = 1 :=
funext $ one_apply F

variable {F}

@[to_additive]
lemma mul_apply [Π i, has_mul (α i)] [fun_like F ι α] [has_pointwise_mul F] (f g : F) (i : ι) :
  (f * g) i = f i * g i :=
has_pointwise_mul.mul_apply f g i

@[simp, to_additive]
lemma coe_fn_mul [Π i, has_mul (α i)] [fun_like F ι α] [has_pointwise_mul F] (f g : F) :
  ⇑(f * g) = f * g :=
funext (mul_apply f g)

@[to_additive]
lemma inv_apply [Π i, has_inv (α i)] [fun_like F ι α] [has_pointwise_inv F] (f : F) (i : ι) :
  f⁻¹ i = (f i)⁻¹ :=
has_pointwise_inv.inv_apply f i

@[to_additive]
lemma coe_fn_inv [Π i, has_inv (α i)] [fun_like F ι α] [has_pointwise_inv F] (f : F) :
  ⇑(f⁻¹) = f⁻¹ :=
funext $ inv_apply f

@[to_additive]
lemma div_apply [Π i, has_div (α i)] [fun_like F ι α] [has_pointwise_div F] (f g : F) (i : ι) :
  (f / g) i = f i / g i :=
has_pointwise_div.div_apply f g i

@[simp, to_additive]
lemma coe_fn_div [Π i, has_div (α i)] [fun_like F ι α] [has_pointwise_div F] (f g : F) :
  ⇑(f / g) = f / g :=
funext (div_apply f g)

@[to_additive]
lemma smul_apply {γ} [Π i, has_scalar γ (α i)] [fun_like F ι α] [has_pointwise_scalar F γ] (c : γ)
  (f : F) (i : ι) :
  (c • f) i = c • f i :=
has_pointwise_scalar.smul_apply f c i

@[to_additive smul_apply, to_additive_reorder 8]
lemma pow_apply {γ} [Π i, has_pow (α i) γ] [fun_like F ι α] [has_pointwise_pow F γ] (f : F)
  (c : γ) (i : ι) :
  (f ^ c) i = f i ^ c :=
has_pointwise_pow.pow_apply f c i

@[simp, to_additive]
lemma coe_fn_smul {γ} [Π i, has_scalar γ (α i)] [fun_like F ι α] [has_pointwise_scalar F γ] (c : γ)
  (f : F) :
  ⇑(c • f) = c • f :=
funext $ smul_apply c f

@[simp, to_additive coe_fn_nsmul]
lemma coe_fn_pow [Π i, monoid (α i)] [fun_like F ι α] [has_pointwise_pow F ℕ] (f : F)
  (n : ℕ) :
  ⇑(f ^ n) = f ^ n :=
funext $ pow_apply f n

@[simp, to_additive]
lemma coe_fn_zpow [Π i, div_inv_monoid (α i)] [fun_like F ι α] [has_pointwise_pow F ℤ] (f : F)
  (n : ℤ) :
  ⇑(f ^ n) = f ^ n :=
funext $ pow_apply f n

variable (F)

@[to_additive]
instance [Π i, semigroup (α i)] [fun_like F ι α] [has_pointwise_mul F] : semigroup F :=
fun_like.coe_injective.semigroup _ coe_fn_mul

@[to_additive]
instance [Π i, comm_semigroup (α i)] [fun_like F ι α] [has_pointwise_mul F] :
  comm_semigroup F :=
fun_like.coe_injective.comm_semigroup _ coe_fn_mul

@[to_additive]
instance [Π i, left_cancel_semigroup (α i)] [fun_like F ι α] [has_pointwise_mul F] :
  left_cancel_semigroup F :=
fun_like.coe_injective.left_cancel_semigroup _ coe_fn_mul

@[to_additive]
instance [Π i, right_cancel_semigroup (α i)] [fun_like F ι α] [has_pointwise_mul F] :
  right_cancel_semigroup F :=
fun_like.coe_injective.right_cancel_semigroup _ coe_fn_mul

@[to_additive]
instance [Π i, mul_one_class (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F] :
  mul_one_class F :=
fun_like.coe_injective.mul_one_class _ (coe_fn_one F) coe_fn_mul

@[to_additive]
instance [Π i, monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F]
  [has_pointwise_pow F ℕ] :
  monoid F :=
fun_like.coe_injective.monoid_pow _ (coe_fn_one F) coe_fn_mul coe_fn_pow

@[to_additive]
instance [Π i, comm_monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F]
  [has_pointwise_pow F ℕ] :
  comm_monoid F :=
{ .. fun_like.monoid F, .. @@fun_like.comm_semigroup F _ _ ‹_› }

@[to_additive]
instance [Π i, left_cancel_monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F]
  [has_pointwise_pow F ℕ] :
  left_cancel_monoid F :=
{ .. fun_like.monoid F, .. @@fun_like.left_cancel_semigroup F _ _ ‹_› }

@[to_additive]
instance [Π i, right_cancel_monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F]
  [has_pointwise_pow F ℕ] :
  right_cancel_monoid F :=
{ .. fun_like.monoid F, .. @@fun_like.right_cancel_semigroup F _ _ ‹_› }

@[to_additive]
instance [Π i, cancel_monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F]
  [has_pointwise_pow F ℕ] :
  cancel_monoid F :=
{ .. @@fun_like.left_cancel_monoid F _ _ ‹_› ‹_› _,
  .. @@fun_like.right_cancel_semigroup F _ _ ‹_› }

@[to_additive]
instance [Π i, cancel_comm_monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F]
  [has_pointwise_pow F ℕ] :
  cancel_comm_monoid F :=
{ .. fun_like.cancel_monoid F, .. @@fun_like.comm_semigroup F _ _ ‹_› }

@[to_additive]
instance [Π i, div_inv_monoid (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F] [has_pointwise_inv F] [has_pointwise_div F]
  [has_pointwise_pow F ℕ] [has_pointwise_pow F ℤ] :
  div_inv_monoid F :=
fun_like.coe_injective.div_inv_monoid_pow _ (coe_fn_one F) coe_fn_mul coe_fn_inv coe_fn_div coe_fn_pow coe_fn_zpow

@[to_additive]
instance [Π i, group (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F] [has_pointwise_inv F] [has_pointwise_div F]
  [has_pointwise_pow F ℕ] [has_pointwise_pow F ℤ] :
  group F :=
fun_like.coe_injective.group_pow _ (coe_fn_one F) coe_fn_mul coe_fn_inv coe_fn_div coe_fn_pow coe_fn_zpow

@[to_additive]
instance [Π i, comm_group (α i)] [fun_like F ι α] [has_pointwise_one F] [has_pointwise_mul F] [has_pointwise_inv F] [has_pointwise_div F]
  [has_pointwise_pow F ℕ] [has_pointwise_pow F ℤ] :
  comm_group F :=
{ .. fun_like.group F, .. @fun_like.comm_semigroup F _ _ _ _ ‹_› }

end fun_like
