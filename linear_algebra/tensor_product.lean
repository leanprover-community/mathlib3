/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Tensor product of modules over commutative rings.

-/

import group_theory.free_abelian_group
import linear_algebra.linear_map_module

variables {R : Type*} [comm_ring R]
variables (M : Type*) (N : Type*) (P : Type*) (Q : Type*)
variables [module R M] [module R N] [module R P] [module R Q]
include R

structure is_bilinear_map {M N P} [module R M] [module R N] [module R P] (f : M → N → P) : Prop :=
(add_left : ∀ x y z, f (x + y) z = f x z + f y z)
(add_right : ∀ x y z, f x (y + z) = f x y + f x z)
(smul_left : ∀ r x y, f (r • x) y = r • f x y)
(smul_right : ∀ r x y, f x (r • y) = r • f x y)

namespace is_bilinear_map
variables {M N P Q}
variables {f : M → N → P} (hf : is_bilinear_map f)
include hf

theorem zero_left : ∀ y, f 0 y = 0 :=
λ y, calc f 0 y
        = f (0 + 0) y - f 0 y : by rw [hf.add_left 0 0 y]; simp
    ... = 0 : by simp

theorem zero_right : ∀ x, f x 0 = 0 :=
λ x, calc f x 0
        = f x (0 + 0) - f x 0 : by rw [hf.add_right x 0 0]; simp
    ... = 0 : by simp

theorem neg_left : ∀ x y, f (-x) y = -f x y :=
λ x y, by convert hf.smul_left (-1) x y; simp

theorem neg_right : ∀ x y, f x (-y) = -f x y :=
λ x y, by convert hf.smul_right (-1) x y; simp

theorem linear_left (y : N) : is_linear_map (λ x, f x y) :=
{ add  := λ m n, hf.add_left m n y,
  smul := λ r m, hf.smul_left r m y }

theorem linear_right (x : M) : is_linear_map (λ y, f x y) :=
{ add  := λ m n, hf.add_right x m n,
  smul := λ r m, hf.smul_right r x m }

theorem comm : is_bilinear_map (λ y x, f x y) :=
by cases hf; constructor; intros; solve_by_elim

section comp
variables {g : P → Q} (hg : is_linear_map g)
include hg

theorem comp : is_bilinear_map (λ x y, g (f x y)) :=
{ add_left  := λ x y z, by rw [hf.add_left, hg.add],
  add_right  := λ x y z, by rw [hf.add_right, hg.add],
  smul_left := λ r x y, by rw [hf.smul_left, hg.smul],
  smul_right := λ r x y, by rw [hf.smul_right, hg.smul] }
end comp

end is_bilinear_map

namespace tensor_product

def relators : set (free_abelian_group (M × N)) :=
add_group.closure { x : free_abelian_group (M × N) |
  (∃ (m₁ m₂ : M) (n : N), x = (m₁, n) + (m₂, n) - (m₁ + m₂, n)) ∨
  (∃ (m : M) (n₁ n₂ : N), x = (m, n₁) + (m, n₂) - (m, n₁ + n₂)) ∨
  (∃ (r : R) (m : M) (n : N), x = (r • m, n) - (m, r • n)) }

namespace relators

instance : normal_add_subgroup (relators M N) :=
{ normal := λ x hx g, by rwa [add_sub_cancel'],
  .. add_group.closure.is_add_subgroup _ }

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
  @is_add_group_hom (free_abelian_group (M × N)) (M ⊗ N) _ _
    quotient.mk :=
quotient_add_group.is_add_group_hom _

section tmul
variables {M N}

def tmul (m : M) (n : N) : M ⊗ N := quotient_add_group.mk $ free_abelian_group.of (m, n)

infix ` ⊗ₜ `:100 := tmul

lemma tmul.add_left (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ n :=
eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inl $ ⟨m₁, m₂, n, rfl⟩

lemma tmul.add_right (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ n₂ :=
eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inr $ or.inl $ ⟨m, n₁, n₂, rfl⟩

lemma tmul.smul (r : R) (m : M) (n : N) : (r • m) ⊗ₜ n = m ⊗ₜ (r • n) :=
sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inr $ or.inr $ ⟨r, m, n, rfl⟩

end tmul

local attribute [instance] free_abelian_group.lift.is_add_group_hom
local attribute [instance] quotient_add_group.is_add_group_hom_quotient_lift

@[reducible] def smul.aux (r : R) (x : free_abelian_group (M × N)) : M ⊗ N :=
free_abelian_group.lift (λ (y : M × N), (r • y.1) ⊗ₜ (y.2)) x

@[reducible] def smul (r : R) : M ⊗ N → M ⊗ N :=
quotient_add_group.lift _ (smul.aux M N r)
begin
  assume x hx,
  induction hx with _ hx _ _ ih _ _ _ _ ih1 ih2,
  { rcases hx with ⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨q, m, n, rfl⟩;
      simp [smul.aux, -sub_eq_add_neg, sub_self, tmul.add_left, tmul.add_right, tmul.smul,
        smul_add, smul_smul, mul_comm] },
  { refl },
  { change smul.aux M N r (-_) = 0,
    rw [is_add_group_hom.neg (smul.aux M N r), ih, neg_zero] },
  { change smul.aux M N r (_ + _) = 0,
    rw [is_add_group_hom.add (smul.aux M N r), ih1, ih2, zero_add] }
end

lemma smul.is_add_group_hom (r : R) : is_add_group_hom (smul M N r) :=
by apply_instance
local attribute [instance] smul.is_add_group_hom

protected theorem smul_add (r : R) (x y : M ⊗ N) :
  smul M N r (x + y) = smul M N r x + smul M N r y :=
is_add_group_hom.add _ _ _

instance : module R (M ⊗ N) :=
{ smul := smul M N,
  smul_add := tensor_product.smul_add M N,
  add_smul := begin
      intros r s x,
      apply quotient_add_group.induction_on' x,
      intro z,
      symmetry,
      refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
      { simp [tensor_product.smul_add] },
      rintro ⟨m, n⟩,
      show (r • m) ⊗ₜ n + (s • m) ⊗ₜ n = ((r + s) • m) ⊗ₜ n,
      simp [add_smul, tmul.add_left]
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
      simp [smul, smul.aux, mul_smul, tmul]
    end,
  one_smul := λ x, quotient.induction_on x $ λ _,
    eq.symm $ free_abelian_group.lift.unique _ _ $ λ ⟨p, q⟩,
    by rw [one_smul]; refl,
  .. tensor_product.add_comm_group M N }

theorem bilinear : is_bilinear_map (@tmul R _ M N _ _) :=
{ add_left := tmul.add_left,
  add_right := tmul.add_right,
  smul_left := λ r x y, rfl,
  smul_right := assume r m n, (tmul.smul r m n).symm }

@[simp] lemma add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ n :=
(bilinear M N).add_left m₁ m₂ n

@[simp] lemma tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ n₂ :=
(bilinear M N).add_right m n₁ n₂

@[simp] lemma smul_tmul (r : R) (x : M) (y : N) : (r • x) ⊗ₜ y = r • (x ⊗ₜ y) :=
rfl

@[simp] lemma tmul_smul (r : R) (x : M) (y : N) : x ⊗ₜ (r • y) = r • (x ⊗ₜ y) :=
(bilinear M N).smul_right r x y

end module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

variables {M N}
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
variables (f : M → N → P) (hf : is_bilinear_map f)
include hf

local attribute [instance] free_abelian_group.lift.is_add_group_hom

def to_module : M ⊗ N → P :=
quotient_add_group.lift _
  (free_abelian_group.lift $ λ z, f z.1 z.2) $ λ x hx,
begin
  induction hx with _ hx _ _ ih _ _ _ _ ih1 ih2,
  { rcases hx with ⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨r, m, n, rfl⟩;
      simp [-sub_eq_add_neg, hf.add_left, hf.add_right, hf.smul_left, hf.smul_right, sub_self] },
  { refl },
  { change free_abelian_group.lift _ (-_) = (0:P),
    simp [ih] },
  { change free_abelian_group.lift _ (_ + _) = (0:P),
    simp [ih1, ih2] }
end
variable {f}

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[simp] lemma to_module.add (x y) :
  to_module f hf (x + y)
  = to_module f hf x + to_module f hf y :=
quotient.induction_on₂ x y $ λ m n,
free_abelian_group.lift.add _ _ _

@[simp] lemma to_module.smul (r x) :
  to_module f hf (r • x)
  = r • to_module f hf x :=
tensor_product.induction_on x smul_zero.symm
  (λ p q, by rw [← (bilinear M N).smul_left];
    simp [to_module, tmul, hf.smul_left])
  (λ p q ih1 ih2, by simp [@smul_add _ _ _ _ r p q,
    to_module.add, ih1, ih2, smul_add])

def to_module.linear :
  is_linear_map (to_module f hf) :=
{ add := to_module.add hf,
  smul := to_module.smul hf }

@[simp] lemma to_module.tmul (x y) :
  to_module f hf (x ⊗ₜ y) = f x y :=
by simp [to_module, tmul]

theorem to_module.unique {g : M ⊗ N → P}
  (hg : is_linear_map g) (H : ∀ x y, g (x ⊗ₜ y) = f x y)
  (z : M ⊗ N) : g z = to_module f hf z :=
begin
  apply quotient_add_group.induction_on' z,
  intro z,
  refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
  { simp [hg.add] },
  exact λ ⟨m, n⟩, H m n
end

omit hf

theorem to_module.ext {g h : M ⊗ N → P}
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

def to_module.equiv : { f : M → N → P // is_bilinear_map f }
  ≃ linear_map (M ⊗ N) P :=
{ to_fun := λ f, ⟨to_module f.1 f.2, to_module.linear f.2⟩,
  inv_fun := λ f, ⟨λ m n, f (m ⊗ₜ n),
    is_bilinear_map.comp (bilinear M N) f.2⟩,
  left_inv := λ f, subtype.eq $ funext $ λ x, funext $ λ y,
    to_module.tmul f.2 _ _,
  right_inv := λ f, subtype.eq $ eq.symm $ funext $ λ z,
    to_module.unique _ f.2 (λ x y, rfl) _ }

end UMP

protected def id : R ⊗ M ≃ₗ M :=
{ to_fun := @to_module _ _ _ _ _ _ _ _ (λ c x, c • x) $
    by refine {..}; intros; simp [smul_add, add_smul, smul_smul, mul_comm, mul_left_comm],
  inv_fun := λ x, 1 ⊗ₜ x,
  left_inv := λ z, by refine to_module.ext
    (((bilinear R M).linear_right 1).comp $ to_module.linear _)
    is_linear_map.id (λ c x, _) z;
    simp; rw [← smul_tmul, smul_eq_mul, mul_one],
  right_inv := λ z, by simp,
  linear_fun := to_module.linear _ }

protected def comm : M ⊗ N ≃ₗ N ⊗ M :=
{ to_fun := to_module _ (bilinear N M).comm,
  inv_fun := to_module _ (bilinear M N).comm,
  left_inv := λ z, by refine to_module.ext
    ((to_module.linear _).comp (to_module.linear _))
    is_linear_map.id (λ x y, _) z; simp,
  right_inv := λ z, by refine to_module.ext
    ((to_module.linear _).comp (to_module.linear _))
    is_linear_map.id (λ x y, _) z; simp,
  linear_fun := to_module.linear _ }

protected def assoc : (M ⊗ N) ⊗ P ≃ₗ M ⊗ (N ⊗ P) :=
{ to_fun := begin
      refine to_module (λ mn p, to_module (λ m n, m ⊗ₜ (n ⊗ₜ p)) _ mn) _;
      constructor; intros; simp,
      { symmetry,
        refine to_module.unique _
          (is_linear_map.map_add (to_module.linear _) (to_module.linear _)) _ _,
        intros; simp },
      { symmetry,
        refine to_module.unique _
          (is_linear_map.map_smul_right (to_module.linear _)) _ _,
        intros; simp }
    end,
  inv_fun := begin
      refine to_module (λ m, to_module (λ n p, (m ⊗ₜ n) ⊗ₜ p) _) _;
      constructor; intros; simp,
      { symmetry,
        refine to_module.unique _
          (is_linear_map.map_add (to_module.linear _) (to_module.linear _)) _ _,
        intros; simp },
      { symmetry,
        refine to_module.unique _
          (is_linear_map.map_smul_right (to_module.linear _)) _ _,
        intros; simp }
    end,
  left_inv :=
  begin
    intro z,
    refine to_module.ext ((to_module.linear _).comp
      (to_module.linear _)) is_linear_map.id (λ mn p, _) z,
    simp,
    refine to_module.ext ((to_module.linear _).comp
      (to_module.linear _)) ((bilinear _ _).linear_left p) (λ m n, _) mn,
    simp
  end,
  right_inv :=
  begin
    intro z,
    refine to_module.ext ((to_module.linear _).comp
      (to_module.linear _)) is_linear_map.id (λ m np, _) z,
    simp,
    refine to_module.ext ((to_module.linear _).comp
      (to_module.linear _)) ((bilinear _ _).linear_right m) (λ n p, _) np,
    simp
  end,
  linear_fun := to_module.linear _ }

end tensor_product