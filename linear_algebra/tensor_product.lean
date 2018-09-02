/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Tensor product of modules over commutative rings.

-/

import group_theory.free_abelian_group
import linear_algebra.linear_map_module

universes u v w u₁ v₁

variables {R : Type u} [comm_ring R]
variables (M : Type v) (N : Type w) (P : Type u₁) (Q : Type v₁)
variables [module R M] [module R N] [module R P] [module R Q]
include R

section bilinear

variables {M N P Q}
structure is_bilinear_map {M N P}
  [module R M] [module R N] [module R P]
  (f : M → N → P) : Prop :=
(add_pair : ∀ x y z, f (x + y) z = f x z + f y z)
(pair_add : ∀ x y z, f x (y + z) = f x y + f x z)
(smul_pair : ∀ r x y, f (r • x) y = r • f x y)
(pair_smul : ∀ r x y, f x (r • y) = r • f x y)

variables {f : M → N → P} (hf : is_bilinear_map f)
include hf

theorem is_bilinear_map.zero_pair : ∀ y, f 0 y = 0 :=
λ y, calc f 0 y
        = f (0 + 0) y - f 0 y : by rw [hf.add_pair 0 0 y]; simp
    ... = 0 : by simp

theorem is_bilinear_map.pair_zero : ∀ x, f x 0 = 0 :=
λ x, calc f x 0
        = f x (0 + 0) - f x 0 : by rw [hf.pair_add x 0 0]; simp
    ... = 0 : by simp

theorem is_bilinear_map.neg_pair : ∀ x y, f (-x) y = -f x y :=
λ x y, by convert hf.smul_pair (-1) x y; simp

theorem is_bilinear_map.pair_neg : ∀ x y, f x (-y) = -f x y :=
λ x y, by convert hf.pair_smul (-1) x y; simp

theorem is_bilinear_map.linear_pair (y : N) : is_linear_map (λ x, f x y) :=
{ add  := λ m n, hf.add_pair m n y,
  smul := λ r m, hf.smul_pair r m y }

theorem is_bilinear_map.pair_linear (x : M) : is_linear_map (λ y, f x y) :=
{ add  := λ m n, hf.pair_add x m n,
  smul := λ r m, hf.pair_smul r x m }

theorem is_bilinear_map.comm : is_bilinear_map (λ y x, f x y) :=
by cases hf; constructor; intros; solve_by_elim

variables {g : P → Q} (hg : is_linear_map g)
include hg

theorem is_bilinear_map.comp : is_bilinear_map (λ x y, g (f x y)) :=
{ add_pair  := λ x y z, by rw [hf.add_pair, hg.add],
  pair_add  := λ x y z, by rw [hf.pair_add, hg.add],
  smul_pair := λ r x y, by rw [hf.smul_pair, hg.smul],
  pair_smul := λ r x y, by rw [hf.pair_smul, hg.smul] }

end bilinear

namespace tensor_product

def relators : set (free_abelian_group (M × N)) :=
add_group.closure { x : free_abelian_group (M × N) |
  (∃ (m1 m2 : M) (n : N), x = (m1, n) + (m2, n) - (m1 + m2, n)) ∨
  (∃ (m : M) (n1 n2 : N), x = (m, n1) + (m, n2) - (m, n1 + n2)) ∨
  (∃ (r : R) (m : M) (n : N), x = (r • m, n) - (m, r • n)) }

instance relators.normal_add_subgroup : normal_add_subgroup (relators M N) :=
{ normal := λ x hx g, by rwa [add_sub_cancel'],
  .. add_group.closure.is_add_subgroup _ }

end tensor_product

def tensor_product : Type (max v w) :=
quotient_add_group.quotient (tensor_product.relators M N)

local infix ` ⊗ `:100 := tensor_product

namespace tensor_product

section module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

variables {M N}
def of (m : M) (n : N) : M ⊗ N :=
quotient_add_group.mk $ free_abelian_group.of (m, n)
variables (M N)

infix ` ⊗ₛ `:100 := of

instance : add_comm_group (M ⊗ N) :=
quotient_add_group.add_comm_group _

instance quotient.mk.is_add_group_hom :
  @is_add_group_hom (free_abelian_group (M × N)) (M ⊗ N) _ _
    quotient.mk :=
quotient_add_group.is_add_group_hom _

local attribute [instance] free_abelian_group.to_add_comm_group.is_add_group_hom
local attribute [instance] quotient_add_group.is_add_group_hom_quotient_lift

@[reducible] def smul.aux (r : R) (x : free_abelian_group (M × N)) : M ⊗ N :=
free_abelian_group.to_add_comm_group (λ (y : M × N), (r • y.1) ⊗ₛ (y.2)) x

@[reducible] def smul (r : R) : M ⊗ N → M ⊗ N :=
quotient_add_group.lift _ (smul.aux M N r) $ λ x hx,
begin
  induction hx with _ hx _ _ ih _ _ _ _ ih1 ih2,
  { rcases hx with ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩ | ⟨_, _, _, hx⟩;
    rw [hx, smul.aux]; symmetry; simp [free_abelian_group.coe_def];
    apply quotient.sound,
    { rw [smul_add],
      apply group.in_closure.basic, left,
      exact ⟨_, _, _, by simp; refl⟩ },
    { apply group.in_closure.basic, right, left,
      exact ⟨_, _, _, by simp; refl⟩ },
    { rw [smul_smul, mul_comm r, ← smul_smul],
      apply group.in_closure.basic, right, right,
      exact ⟨_, _, _, by simp; refl⟩ } },
  { refl },
  { change smul.aux M N r (-_) = 0,
    rw [is_add_group_hom.neg (smul.aux M N r), ih, neg_zero] },
  { change smul.aux M N r (_ + _) = 0,
    rw [is_add_group_hom.add (smul.aux M N r), ih1, ih2, zero_add] }
end

def smul.is_add_group_hom (r : R) : is_add_group_hom (smul M N r) :=
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
      apply quotient_add_group.induction_on x,
      intro z,
      symmetry,
      refine @free_abelian_group.to_add_comm_group.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
      { simp [smul, smul.aux] },
      intro x,
      cases x with m n,
      exact eq.symm (quotient.sound $ group.in_closure.basic $ or.inl
      ⟨_, _, _, by simp [add_smul]; refl⟩),
    end,
  mul_smul := begin
      intros r s x,
      apply quotient_add_group.induction_on' x,
      intro z,
      symmetry,
      refine @free_abelian_group.to_add_comm_group.unique _ _ _ _ _
        ⟨λ p q, _⟩ _ z,
      { simp [tensor_product.smul_add] },
      intro x,
      cases x with m n,
      simp [smul, smul.aux, mul_smul, of]
    end,
  one_smul := λ x, quotient.induction_on x $ λ _,
    eq.symm $ free_abelian_group.to_add_comm_group.unique _ _ $ λ ⟨p, q⟩,
    by rw [one_smul]; refl,
  .. tensor_product.add_comm_group M N }

theorem bilinear : is_bilinear_map (@of R _ M N _ _) :=
{ add_pair := λ m1 m2 n, eq.symm $ sub_eq_zero.1 $ eq.symm $
    quotient.sound $ group.in_closure.basic $ or.inl
      ⟨_, _, _, by simp; refl⟩,
  pair_add := λ m1 m2 n, eq.symm $ sub_eq_zero.1 $ eq.symm $
    quotient.sound $ group.in_closure.basic $ or.inr $ or.inl
      ⟨_, _, _, by simp; refl⟩,
  smul_pair := λ r x y, rfl,
  pair_smul := λ r x y, eq.symm $ sub_eq_zero.1 $ eq.symm $
    quotient.sound $ group.in_closure.basic $ or.inr $ or.inr
      ⟨_, _, _, by simp; refl⟩ }

@[simp] lemma add_of (m₁ m₂ : M) (n : N) :
  (m₁ + m₂) ⊗ₛ n = m₁ ⊗ₛ n + m₂ ⊗ₛ n :=
(bilinear M N).add_pair m₁ m₂ n

@[simp] lemma of_add (m : M) (n₁ n₂ : N) :
  m ⊗ₛ (n₁ + n₂) = m ⊗ₛ n₁ + m ⊗ₛ n₂ :=
(bilinear M N).pair_add m n₁ n₂

@[simp] lemma smul_of (r : R) (x : M) (y : N) :
  (r • x) ⊗ₛ y = r • (x ⊗ₛ y) :=
rfl

@[simp] lemma of_smul (r : R) (x : M) (y : N) :
  x ⊗ₛ (r • y) = r • (x ⊗ₛ y) :=
(bilinear M N).pair_smul r x y

end module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

variables {M N}
@[elab_as_eliminator]
protected theorem induction_on
  {C : M ⊗ N → Prop}
  (z : M ⊗ N)
  (C0 : C 0)
  (C1 : ∀ x y, C $ x ⊗ₛ y)
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, free_abelian_group.induction_on x
  C0 (λ ⟨p, q⟩, C1 p q)
  (λ ⟨p, q⟩ _, show C (-(p ⊗ₛ q)), by rw ← (bilinear M N).neg_pair; from C1 (-p) q)
  (λ _ _, Cp _ _)

section UMP

variables {M N P Q}
variables (f : M → N → P) (hf : is_bilinear_map f)
include hf

local attribute [instance] free_abelian_group.to_add_comm_group.is_add_group_hom

def to_module : M ⊗ N → P :=
quotient_add_group.lift _
  (free_abelian_group.to_add_comm_group $ λ z, f z.1 z.2) $ λ x hx,
begin
  induction hx with _ hx _ _ ih _ _ _ _ ih1 ih2,
  { rcases hx with ⟨_, m, n, hx⟩ | ⟨m, n, _, hx⟩ | ⟨_, _, _, hx⟩;
    rw [hx]; symmetry; simp [free_abelian_group.coe_def],
    { rw [hf.add_pair], simp [add_left_comm (f m n)] },
    { rw [hf.pair_add], simp [add_left_comm (f m n)] },
    { rw [hf.smul_pair, hf.pair_smul, add_neg_self] } },
  { refl },
  { change free_abelian_group.to_add_comm_group _ (-_) = (0:P),
    simp [ih] },
  { change free_abelian_group.to_add_comm_group _ (_ + _) = (0:P),
    simp [ih1, ih2] }
end
variable {f}

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[simp] lemma to_module.add (x y) :
  to_module f hf (x + y)
  = to_module f hf x + to_module f hf y :=
quotient.induction_on₂ x y $ λ m n,
free_abelian_group.to_add_comm_group.add _ _ _

@[simp] lemma to_module.smul (r x) :
  to_module f hf (r • x)
  = r • to_module f hf x :=
tensor_product.induction_on x smul_zero.symm
  (λ p q, by rw [← (bilinear M N).smul_pair];
    simp [to_module, of, hf.smul_pair])
  (λ p q ih1 ih2, by simp [@smul_add _ _ _ _ r p q,
    to_module.add, ih1, ih2, smul_add])

def to_module.linear :
  is_linear_map (to_module f hf) :=
{ add := to_module.add hf,
  smul := to_module.smul hf }

@[simp] lemma to_module.of (x y) :
  to_module f hf (x ⊗ₛ y) = f x y :=
by simp [to_module, of]

theorem to_module.unique {g : M ⊗ N → P}
  (hg : is_linear_map g) (H : ∀ x y, g (x ⊗ₛ y) = f x y)
  (z : M ⊗ N) : g z = to_module f hf z :=
begin
  apply quotient_add_group.induction_on' z,
  intro z,
  refine @free_abelian_group.to_add_comm_group.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
  { simp [hg.add] },
  exact λ ⟨m, n⟩, H m n
end

omit hf

theorem to_module.ext {g h : M ⊗ N → P}
  (hg : is_linear_map g) (hh : is_linear_map h)
  (H : ∀ x y, g (x ⊗ₛ y) = h (x ⊗ₛ y))
  (z : M ⊗ N) : g z = h z :=
begin
  apply quotient_add_group.induction_on' z,
  intro z,
  apply free_abelian_group.to_add_comm_group.ext (g ∘ _) _ _,
  { constructor,
    intros p q,
    simp [hg.add] },
  { constructor,
    intros p q,
    simp [hh.add] },
  intro x,
  cases x with m n,
  exact H m n
end

def to_module.equiv : { f : M → N → P // is_bilinear_map f }
  ≃ linear_map (M ⊗ N) P :=
{ to_fun := λ f, ⟨to_module f.1 f.2, to_module.linear f.2⟩,
  inv_fun := λ f, ⟨λ m n, f (m ⊗ₛ n),
    is_bilinear_map.comp (bilinear M N) f.2⟩,
  left_inv := λ f, subtype.eq $ funext $ λ x, funext $ λ y,
    to_module.of f.2 _ _,
  right_inv := λ f, subtype.eq $ eq.symm $ funext $ λ z,
    to_module.unique _ f.2 (λ x y, rfl) _ }

end UMP

protected def id : R ⊗ M ≃ₗ M :=
{ to_fun := @to_module _ _ _ _ _ _ _ _ (λ c x, c • x) $
    by refine {..}; intros; simp [smul_add, add_smul, smul_smul, mul_comm, mul_left_comm],
  inv_fun := λ x, 1 ⊗ₛ x,
  left_inv := λ z, by refine to_module.ext
    (((bilinear R M).pair_linear 1).comp $ to_module.linear _)
    is_linear_map.id (λ c x, _) z;
    simp; rw [← smul_of, smul_eq_mul, mul_one],
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
      refine to_module (λ mn p, to_module (λ m n, m ⊗ₛ (n ⊗ₛ p)) _ mn) _;
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
      refine to_module (λ m, to_module (λ n p, (m ⊗ₛ n) ⊗ₛ p) _) _;
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
  left_inv := λ z, by refine to_module.ext ((to_module.linear _).comp (to_module.linear _)) is_linear_map.id (λ mn p, _) z;
    simp;
    refine to_module.ext ((to_module.linear _).comp (to_module.linear _)) ((bilinear _ _).linear_pair p) (λ m n, _) mn;
    simp,
  right_inv := λ z, by refine to_module.ext ((to_module.linear _).comp (to_module.linear _)) is_linear_map.id (λ m np, _) z;
    simp;
    refine to_module.ext ((to_module.linear _).comp (to_module.linear _)) ((bilinear _ _).pair_linear m) (λ n p, _) np;
    simp,
  linear_fun := to_module.linear _ }

end tensor_product