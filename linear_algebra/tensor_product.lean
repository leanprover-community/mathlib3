/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Tensor product of modules over commutative rings.

-/

import group_theory.free_abelian_group
import linear_algebra.basic tactic.squeeze

variables (R : Type*) [comm_ring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*}
variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
variables [module R M] [module R N] [module R P] [module R Q]
include R

structure is_bilinear_map (f : M → N → P) : Prop :=
(linear_left : ∀ y, is_linear_map (λ x, f x y))
(linear_right : ∀ x, is_linear_map (λ y, f x y))
variable {R}

namespace is_bilinear_map
variables {M N P Q}
variables {f : M → N → P} (hf : is_bilinear_map R f)
include hf

def left (y : N) : M →ₗ P := (hf.linear_left y).mk' _
def right (x : M) : N →ₗ P := (hf.linear_right x).mk' _

@[simp] theorem left_apply (x : M) (y : N) : left hf y x = f x y := rfl
@[simp] theorem right_apply (x : M) (y : N) : right hf x y = f x y := rfl

theorem zero_left (y) : f 0 y = 0 := (left hf y).map_zero
theorem zero_right (x) : f x 0 = 0 := (right hf x).map_zero

theorem neg_left (x y) : f (-x) y = -f x y := (left hf y).map_neg _
theorem neg_right (x y) : f x (-y) = -f x y := (right hf x).map_neg _

theorem add_left (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y := (left hf y).map_add _ _
theorem add_right (x y₁ y₂) : f x (y₁ + y₂) = f x y₁ + f x y₂ := (right hf x).map_add _ _

theorem smul_left (r x y) : f (r • x) y = r • f x y := (left hf y).map_smul _ _
theorem smul_right (r x y) : f x (r • y) = r • f x y := (right hf x).map_smul _ _

theorem comm : is_bilinear_map R (λ y x, f x y) :=
{ linear_left := hf.linear_right,
  linear_right := hf.linear_left }

section comp
variables (g : P →ₗ Q)

theorem comp : is_bilinear_map R (λ x y, g (f x y)) :=
{ linear_left := λ y, (g.comp (hf.left y)).is_linear,
  linear_right := λ x, (g.comp (hf.right x)).is_linear }
end comp

end is_bilinear_map

variables (M N)

namespace tensor_product

def relators : set (free_abelian_group (M × N)) :=
add_group.closure { x : free_abelian_group (M × N) |
  (∃ (m₁ m₂ : M) (n : N), x = (m₁, n) + (m₂, n) - (m₁ + m₂, n)) ∨
  (∃ (m : M) (n₁ n₂ : N), x = (m, n₁) + (m, n₂) - (m, n₁ + n₂)) ∨
  (∃ (r : R) (m : M) (n : N), x = (r • m, n) - (m, r • n)) }

namespace relators

instance : normal_add_subgroup (relators M N) :=
by unfold relators; apply normal_add_subgroup_of_add_comm_group

end relators

end tensor_product

def tensor_product : Type* :=
quotient_add_group.quotient (tensor_product.relators M N)

local infix ` ⊗ `:100 := tensor_product

namespace tensor_product

section module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

instance : add_comm_group (M ⊗ N) := quotient_add_group.add_comm_group _

instance quotient.mk.is_add_group_hom :
  is_add_group_hom (quotient.mk : free_abelian_group (M × N) → M ⊗ N) :=
quotient_add_group.is_add_group_hom _

variables {M N}

def tmul (m : M) (n : N) : M ⊗ N := quotient_add_group.mk $ free_abelian_group.of (m, n)

infix ` ⊗ₜ `:100 := tmul

lemma add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ n :=
eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inl $ ⟨m₁, m₂, n, rfl⟩

lemma tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ n₂ :=
eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inr $ or.inl $ ⟨m, n₁, n₂, rfl⟩

lemma smul_tmul (r : R) (m : M) (n : N) : (r • m) ⊗ₜ n = m ⊗ₜ (r • n) :=
sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inr $ or.inr $ ⟨r, m, n, rfl⟩

local attribute [instance] quotient_add_group.is_add_group_hom_quotient_lift

def smul.aux (r : R) : free_abelian_group (M × N) → M ⊗ N :=
free_abelian_group.lift (λ (y : M × N), (r • y.1) ⊗ₜ y.2)

instance (r : R) : is_add_group_hom (smul.aux r : _ → M ⊗ N) :=
by unfold smul.aux; apply_instance

instance : has_scalar R (M ⊗ N) :=
⟨λ r, quotient_add_group.lift _ (smul.aux r) $ λ x hx, begin
  refine (is_add_group_hom.mem_ker (smul.aux r : _ → M ⊗ N)).1
    (add_group.closure_subset _ hx),
  clear hx x, rintro x (⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨q, m, n, rfl⟩);
  simp only [smul.aux, is_add_group_hom.mem_ker, -sub_eq_add_neg,
    sub_self, add_tmul, tmul_add, smul_tmul,
    smul_add, smul_smul, mul_comm, free_abelian_group.lift.coe,
    free_abelian_group.lift.add, free_abelian_group.lift.sub]
end⟩

instance smul.is_add_group_hom (r : R) : is_add_group_hom ((•) r : M ⊗ N → M ⊗ N) :=
by unfold has_scalar.smul; apply_instance

protected theorem smul_add (r : R) (x y : M ⊗ N) :
  r • (x + y) = r • x + r • y :=
is_add_group_hom.add _ _ _

instance : module R (M ⊗ N) := module.of_core
{ smul := (•),
  smul_add := tensor_product.smul_add,
  add_smul := begin
      intros r s x,
      apply quotient_add_group.induction_on' x,
      intro z,
      symmetry,
      refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
      { simp [tensor_product.smul_add] },
      rintro ⟨m, n⟩,
      change (r • m) ⊗ₜ n + (s • m) ⊗ₜ n = ((r + s) • m) ⊗ₜ n,
      rw [add_smul, add_tmul]
    end,
  mul_smul := begin
      intros r s x,
      apply quotient_add_group.induction_on' x,
      intro z,
      symmetry,
      refine @free_abelian_group.lift.unique _ _ _ _ _
        ⟨λ p q, _⟩ _ z,
      { simp [tensor_product.smul_add] },
      rintro ⟨m, n⟩,
      change r • s • (m ⊗ₜ n) = ((r * s) • m) ⊗ₜ n,
      rw mul_smul, refl
    end,
  one_smul := λ x, quotient.induction_on x $ λ _,
    eq.symm $ free_abelian_group.lift.unique _ _ $ λ ⟨p, q⟩,
    by rw one_smul; refl }

@[simp] lemma tmul_smul (r : R) (x : M) (y : N) : x ⊗ₜ (r • y) = r • (x ⊗ₜ y) :=
(smul_tmul _ _ _).symm

variables (M N)
theorem bilinear : is_bilinear_map R ((⊗ₜ) : M → N → M ⊗ N) :=
{ linear_left := λ y, { add := λ _ _, add_tmul _ _ _, smul := λ r x, rfl },
  linear_right := λ x, { add := tmul_add _, smul := λ _ _, tmul_smul _ _ _ } }

end module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[elab_as_eliminator]
protected theorem induction_on
  {C : M ⊗ N → Prop}
  (z : M ⊗ N)
  (C0 : C 0)
  (C1 : ∀ x y, C $ x ⊗ₜ y)
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, free_abelian_group.induction_on x
  C0 (λ ⟨p, q⟩, C1 p q)
  (λ ⟨p, q⟩ _, show C (-(p ⊗ₜ q)), by rw ← (bilinear M N).neg_left; from C1 (-p) q)
  (λ _ _, Cp _ _)

section UMP

variables {M N P Q}
variables (f : M → N → P) (hf : is_bilinear_map R f)
include hf

local attribute [instance] free_abelian_group.lift.is_add_group_hom
/-#check tensor_product.has_scalar
instance : has_scalar R (M ⊗ N) :=
⟨λ r, quotient_add_group.lift _ (smul.aux r) $ λ x hx, begin
  refine (is_add_group_hom.mem_ker (smul.aux r : _ → M ⊗ N)).1
    (add_group.closure_subset _ hx),
  clear hx x, rintro x (⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨q, m, n, rfl⟩);
  simp only [smul.aux, is_add_group_hom.mem_ker, -sub_eq_add_neg,
    sub_self, add_tmul, tmul_add, smul_tmul,
    smul_add, smul_smul, mul_comm, free_abelian_group.lift.coe,
    free_abelian_group.lift.add, free_abelian_group.lift.sub]
end⟩-/

def lift_aux : M ⊗ N → P :=
quotient_add_group.lift _
  (free_abelian_group.lift $ λ z, f z.1 z.2) $ λ x hx,
begin
  refine (is_add_group_hom.mem_ker _).1 (add_group.closure_subset _ hx),
  clear hx x, rintro x (⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨q, m, n, rfl⟩);
    simp [is_add_group_hom.mem_ker, -sub_eq_add_neg,
      hf.add_left, hf.add_right, hf.smul_left, hf.smul_right, sub_self],
end
variable {f}

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[simp] lemma lift_aux.add (x y) : lift_aux f hf (x + y) = lift_aux f hf x + lift_aux f hf y :=
quotient.induction_on₂ x y $ λ m n,
free_abelian_group.lift.add _ _ _

@[simp] lemma lift_aux.smul (r x) : lift_aux f hf (r • x) = r • lift_aux f hf x :=
tensor_product.induction_on _ _ x (smul_zero _).symm
  (λ p q, by rw [← (bilinear M N).smul_left];
    simp [lift_aux, tmul, hf.smul_left])
  (λ p q ih1 ih2, by simp [@smul_add _ _ _ _ _ r p q,
    lift_aux.add, ih1, ih2, smul_add])

variable f
def lift : M ⊗ N →ₗ P :=
{ to_fun := lift_aux f hf,
  add := lift_aux.add hf,
  smul := lift_aux.smul hf }
variable {f}

@[simp] lemma lift.tmul (x y) :
  lift f hf (x ⊗ₜ y) = f x y :=
show lift_aux f hf (x ⊗ₜ y) = _, by simp [lift_aux, tmul]

theorem lift.unique {g : linear_map (M ⊗ N) P} (H : ∀ x y, g (x ⊗ₜ y) = f x y)
  (z : M ⊗ N) : g z = lift f hf z :=
begin
  apply quotient_add_group.induction_on' z,
  intro z,
  refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
  { simp [g.2] },
  exact λ ⟨m, n⟩, H m n
end

omit hf

theorem lift.ext {g h : M ⊗ N → P}
  (hg : is_linear_map g) (hh : is_linear_map h)
  (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y))
  (z : M ⊗ N) : g z = h z :=
begin
  apply quotient_add_group.induction_on' z,
  intro z,
  apply free_abelian_group.lift.ext (g ∘ _) _ _,
  { constructor,
    intros p q,
    simp [hg.add] },
  { constructor,
    intros p q,
    simp [hh.add] },
  rintro ⟨m, n⟩,
  exact H m n
end

def lift.equiv : { f : M → N → P // is_bilinear_map R f }
  ≃ linear_map (M ⊗ N) P :=
{ to_fun := λ f, lift f.1 f.2,
  inv_fun := λ f, ⟨λ m n, f (m ⊗ₜ n),
    is_bilinear_map.comp (bilinear M N) f⟩,
  left_inv := λ f, subtype.eq $ funext $ λ x, funext $ λ y,
    lift.tmul f.2 _ _,
  right_inv := λ f, linear_map.ext $ λ z, eq.symm $
    lift.unique _ (λ x y, rfl) z }

end UMP

protected def id : R ⊗ M ≃ₗ M :=
{ to_fun := (tensor_product.lift (λ c x, c • x)
    ⟨λ m : M, ⟨λ r s : R, by rw add_smul, λ _ _, by rw smul_smul; refl⟩,
    λ _, ⟨smul_add _, λ _ _, by rw [smul_smul, smul_smul, mul_comm]⟩⟩).1,
  inv_fun := λ x, 1 ⊗ₜ x,
  left_inv := λ z, by refine lift.ext
    (((bilinear R M).linear_right 1).comp $ lift.linear _)
    is_linear_map.id (λ c x, _) z;
    simp; rw [← smul_tmul, smul_eq_mul, mul_one],
  right_inv := λ z, by simp,
  linear_fun := lift.linear _ }

protected def comm : M ⊗ N ≃ₗ N ⊗ M :=
{ to_fun := lift _ (bilinear N M).comm,
  inv_fun := lift _ (bilinear M N).comm,
  left_inv := λ z, by refine lift.ext
    ((lift.linear _).comp (lift.linear _))
    is_linear_map.id (λ x y, _) z; simp,
  right_inv := λ z, by refine lift.ext
    ((lift.linear _).comp (lift.linear _))
    is_linear_map.id (λ x y, _) z; simp,
  linear_fun := lift.linear _ }

protected def assoc : (M ⊗ N) ⊗ P ≃ₗ M ⊗ (N ⊗ P) :=
{ to_fun := begin
      refine lift (λ mn p, lift (λ m n, m ⊗ₜ (n ⊗ₜ p)) _ mn) _;
      constructor; intros; simp,
      { symmetry,
        refine lift.unique _
          (is_linear_map.map_add (lift.linear _) (lift.linear _)) _ _,
        intros; simp },
      { symmetry,
        refine lift.unique _
          (is_linear_map.map_smul_right (lift.linear _)) _ _,
        intros; simp }
    end,
  inv_fun := begin
      refine lift (λ m, lift (λ n p, (m ⊗ₜ n) ⊗ₜ p) _) _;
      constructor; intros; simp,
      { symmetry,
        refine lift.unique _
          (is_linear_map.map_add (lift.linear _) (lift.linear _)) _ _,
        intros; simp },
      { symmetry,
        refine lift.unique _
          (is_linear_map.map_smul_right (lift.linear _)) _ _,
        intros; simp }
    end,
  left_inv :=
  begin
    intro z,
    refine lift.ext ((lift.linear _).comp
      (lift.linear _)) is_linear_map.id (λ mn p, _) z,
    simp,
    refine lift.ext ((lift.linear _).comp
      (lift.linear _)) ((bilinear _ _).linear_left p) (λ m n, _) mn,
    simp
  end,
  right_inv :=
  begin
    intro z,
    refine lift.ext ((lift.linear _).comp
      (lift.linear _)) is_linear_map.id (λ m np, _) z,
    simp,
    refine lift.ext ((lift.linear _).comp
      (lift.linear _)) ((bilinear _ _).linear_right m) (λ n p, _) np,
    simp
  end,
  linear_fun := lift.linear _ }

end tensor_product
