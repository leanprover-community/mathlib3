/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Tensor product of modules over commutative rings.

-/

import group_theory.free_abelian_group
import linear_algebra.basic tactic.squeeze

variables (R : Type*) [comm_ring R]
variables (M : Type*) (N : Type*) (P : Type*) {Q : Type*}
variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
variables [module R M] [module R N] [module R P] [module R Q]
include R

@[reducible] def bilinear_map := M →ₗ N →ₗ P
instance bilinear_map.has_coe_to_fun : has_coe_to_fun (bilinear_map R M N P) :=
linear_map.has_coe_to_fun

variables {R M N P}

namespace bilinear_map
variables {M N P Q}

section mk
variable (f : M → N → P)
variable (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
variable (H2 : ∀ c m n, f (c • m) n = c • f m n)
variable (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
variable (H4 : ∀ c m n, f m (c • n) = c • f m n)

def mk : bilinear_map R M N P :=
⟨λ m, ⟨f m, H3 m, λ c, H4 c m⟩,
λ m₁ m₂, linear_map.ext $ H1 m₁ m₂,
λ c m, linear_map.ext $ H2 c m⟩

theorem mk_apply (m : M) (n : N) :
  bilinear_map.mk f H1 H2 H3 H4 m n = f m n := rfl

end mk

variables (f : bilinear_map R M N P)

theorem ext {f g : bilinear_map R M N P}
  (H : ∀ m n, f m n = g m n) : f = g :=
linear_map.ext (λ m, linear_map.ext $ λ n, H m n)

def comm : bilinear_map R N M P :=
mk (λ n m, f m n)
  (λ n₁ n₂ m, (f m).map_add _ _)
  (λ c n m, (f m).map_smul _ _)
  (λ n m₁ m₂, by rw f.map_add; refl)
  (λ c n m, by rw f.map_smul; refl)

@[simp] theorem comm_apply (m : M) (n : N) : f.comm n m = f m n := rfl

theorem comm_inj {f g : bilinear_map R M N P} (H : f.comm = g.comm) : f = g :=
bilinear_map.ext $ λ m n, show f.comm n m = g.comm n m, by rw H

variables (R M N P)
def comm' : bilinear_map R M N P →ₗ bilinear_map R N M P :=
⟨comm, λ _ _, rfl, λ _ _, rfl⟩
variables {R M N P}

set_option class.instance_max_depth 60
@[simp] theorem comm'_apply (m : M) (n : N) : comm' R M N P f n m = f m n := rfl
set_option class.instance_max_depth 32

def left (y : N) : M →ₗ P := f.comm y
def right (x : M) : N →ₗ P := f x

@[simp] theorem left_apply (x : M) (y : N) : f.left y x = f x y := rfl
@[simp] theorem right_apply (x : M) (y : N) : f.right x y = f x y := rfl

theorem zero_left (y) : f 0 y = 0 := (f.left y).map_zero
theorem zero_right (x) : f x 0 = 0 := (f.right x).map_zero

theorem neg_left (x y) : f (-x) y = -f x y := (f.left y).map_neg _
theorem neg_right (x y) : f x (-y) = -f x y := (f.right x).map_neg _

theorem add_left (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y := (f.left y).map_add _ _
theorem add_right (x y₁ y₂) : f x (y₁ + y₂) = f x y₁ + f x y₂ := (f.right x).map_add _ _

theorem smul_left (r x y) : f (r • x) y = r • f x y := (f.left y).map_smul _ _
theorem smul_right (r x y) : f x (r • y) = r • f x y := (f.right x).map_smul _ _

def comp₁ (g : Q →ₗ M) : bilinear_map R Q N P :=
linear_map.comp f g

@[simp] theorem comp₁_apply (g : Q →ₗ M) (q : Q) (n : N) :
  f.comp₁ g q n = f (g q) n := rfl

def comp₂ (g : Q →ₗ N) : bilinear_map R M Q P :=
linear_map.comp ⟨λ x, linear_map.comp x g, λ _ _, rfl, λ _ _, rfl⟩ f

@[simp] theorem comp₂_apply (g : Q →ₗ N) (m : M) (q : Q) :
  f.comp₂ g m q = f m (g q) := rfl

def comp₃ (g : P →ₗ Q) : bilinear_map R M N Q :=
linear_map.comp ⟨g.comp, λ x y, linear_map.ext $ λ n, g.map_add _ _,
  λ c x, linear_map.ext $ λ n, g.map_smul _ _⟩ f

@[simp] theorem comp₃_apply (g : P →ₗ Q) (m : M) (n : N) :
  f.comp₃ g m n = g (f m n) := rfl

variables (R M N P Q)
def comp₃' : bilinear_map R (bilinear_map R M N P) (P →ₗ Q) (bilinear_map R M N Q) :=
bilinear_map.mk comp₃ (λ _ _ g, bilinear_map.ext $ λ _ _, g.map_add _ _)
  (λ _ _ g, bilinear_map.ext $ λ _ _, g.map_smul _ _)
  (λ f g₁ g₂, bilinear_map.ext $ λ m n, by simp only [comp₃_apply, pi.add_apply]; refl)
  (λ c f g, bilinear_map.ext $ λ m n, by simp only [comp₃_apply, pi.smul_apply]; refl)
variables {R M N P Q}

set_option class.instance_max_depth 90
@[simp] theorem comp₃'_apply (f : bilinear_map R M N P) (g : P →ₗ Q) (m : M) (n : N) :
  comp₃' R M N P Q f g m n = g (f m n) := rfl
set_option class.instance_max_depth 32

variables (R M)
def smul : bilinear_map R R M M :=
bilinear_map.mk (•) add_smul (λ _ _ _, eq.symm $ smul_smul _ _ _) smul_add
(λ r s m, by simp only [smul_smul, smul_eq_mul, mul_comm])
variables {R M}

@[simp] theorem smul_apply (r : R) (m : M) : smul R M r m = r • m := rfl

end bilinear_map

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

variables (R M N)
def mk : bilinear_map R M N (M ⊗ N) :=
bilinear_map.mk (⊗ₜ) add_tmul (λ c m n, by rw [smul_tmul, tmul_smul]) tmul_add tmul_smul
variables {R M N}

@[simp] lemma mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n := rfl

lemma zero_tmul (n : N) : (0 ⊗ₜ n : M ⊗ N) = 0 := (mk R M N).zero_left _
lemma tmul_zero (m : M) : (m ⊗ₜ 0 : M ⊗ N) = 0 := (mk R M N).zero_right _
lemma neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -(m ⊗ₜ n) := (mk R M N).neg_left _ _
lemma tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -(m ⊗ₜ n) := (mk R M N).neg_right _ _

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
  (λ ⟨p, q⟩ _, show C (-(p ⊗ₜ q)), by rw ← neg_tmul; from C1 (-p) q)
  (λ _ _, Cp _ _)

section UMP

variables {M N P Q}
variables (f : bilinear_map R M N P)

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
      f.add_left, f.add_right, f.smul_left, f.smul_right, sub_self],
end
variable {f}

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[simp] lemma lift_aux.add (x y) : lift_aux f (x + y) = lift_aux f x + lift_aux f y :=
quotient.induction_on₂ x y $ λ m n, free_abelian_group.lift.add _ _ _

@[simp] lemma lift_aux.smul (r x) : lift_aux f (r • x) = r • lift_aux f x :=
tensor_product.induction_on _ _ x (smul_zero _).symm
  (λ p q, by rw [← tmul_smul]; simp [lift_aux, tmul])
  (λ p q ih1 ih2, by simp [@smul_add _ _ _ _ _ _ p _,
    lift_aux.add, ih1, ih2, smul_add])

variable (f)
def lift : M ⊗ N →ₗ P :=
{ to_fun := lift_aux f,
  add := lift_aux.add,
  smul := lift_aux.smul }
variable {f}

@[simp] lemma lift.tmul (x y) :
  lift f (x ⊗ₜ y) = f x y :=
zero_add _

@[simp] lemma lift.tmul' (x y) :
  (lift f).1 (x ⊗ₜ y) = f x y :=
lift.tmul _ _

theorem lift.unique {g : linear_map (M ⊗ N) P} (H : ∀ x y, g (x ⊗ₜ y) = f x y)
  (z : M ⊗ N) : g z = lift f z :=
begin
  apply quotient_add_group.induction_on' z,
  intro z,
  refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
  { simp [g.2] },
  exact λ ⟨m, n⟩, H m n
end

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

theorem lift.ext' {g h : M ⊗ N →ₗ P}
  (H : (mk R M N).comp₃ g = (mk R M N).comp₃ h) : g = h :=
linear_map.ext $ lift.ext g.is_linear h.is_linear $ λ m n,
show bilinear_map.comp₃ (mk R M N) g m n = bilinear_map.comp₃ (mk R M N) h m n, by rw H

variables (R M N P)
def lift.equiv : bilinear_map R M N P ≃ₗ linear_map (M ⊗ N) P :=
{ to_fun := lift,
  add := λ f g, lift.ext' $ bilinear_map.ext $ λ m n,
    by simp only [bilinear_map.comp₃_apply, mk_apply, lift.tmul, linear_map.add_apply]; refl,
  smul := λ c f, lift.ext' $ bilinear_map.ext $ λ m n,
    by simp only [bilinear_map.comp₃_apply, mk_apply, lift.tmul, linear_map.smul_apply]; refl,
  inv_fun := λ f, bilinear_map.comp₃ (mk R M N) f,
  left_inv := λ f, bilinear_map.ext $ λ m n, lift.tmul m n,
  right_inv := λ f, lift.ext' $ bilinear_map.ext $ λ m n, lift.tmul m n }

set_option class.instance_max_depth 80

def lift' : bilinear_map R M N P →ₗ linear_map (M ⊗ N) P :=
lift.equiv R M N P

@[simp] theorem lift'_apply (f : bilinear_map R M N P) :
  lift' R M N P f = lift f := rfl

def unlift' : linear_map (M ⊗ N) P →ₗ bilinear_map R M N P :=
(lift.equiv R M N P).symm

@[simp] theorem unlift'_apply (f : linear_map (M ⊗ N) P) (m : M) (n : N) :
  unlift' R M N P f m n = f (m ⊗ₜ n) := rfl

variables {R M N P}
def unlift : linear_map (M ⊗ N) P → bilinear_map R M N P :=
(unlift' R M N P).1

@[simp] theorem unlift_apply (f : linear_map (M ⊗ N) P) (m : M) (n : N) :
  unlift f m n = f (m ⊗ₜ n) := rfl

set_option class.instance_max_depth 32

end UMP

variables {M N}
protected def id : R ⊗ M ≃ₗ M :=
linear_equiv.of_linear (lift $ bilinear_map.smul R M) (mk R R M 1)
  (linear_map.ext $ λ _, by simp)
  (lift.ext' $ bilinear_map.ext $ λ r m, by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

protected def comm : M ⊗ N ≃ₗ N ⊗ M :=
linear_equiv.of_linear (lift (mk R N M).comm) (lift (mk R M N).comm)
  (lift.ext' $ bilinear_map.ext $ λ m n, by dsimp; refl)
  (lift.ext' $ bilinear_map.ext $ λ m n, by dsimp; refl)

open linear_map bilinear_map
set_option class.instance_max_depth 80
protected def assoc : (M ⊗ N) ⊗ P ≃ₗ M ⊗ (N ⊗ P) :=
linear_equiv.of_linear
  (lift $ lift $ comp (unlift' _ _ _ _) $ mk _ _ _)
  (lift $ comp (lift' _ _ _ _) $ unlift $ mk _ _ _)
  (lift.ext' $ linear_map.ext $ λ m, lift.ext' $ bilinear_map.ext $ λ n p,
    by repeat { rw lift.tmul <|> rw comp₃_apply <|> rw comp_apply <|> rw mk_apply <|>
        rw lift'_apply <|> rw comm'_apply <|> rw unlift_apply <|> rw unlift'_apply <|> rw id_apply })
  (lift.ext' $ comm_inj $ linear_map.ext $ λ p, lift.ext' $ bilinear_map.ext $ λ m n,
    by repeat { rw lift.tmul <|> rw comp₃_apply <|> rw comp_apply <|> rw comm_apply <|> rw mk_apply <|>
        rw lift'_apply <|> rw comm'_apply <|> rw unlift_apply <|> rw unlift'_apply <|> rw id_apply })
set_option class.instance_max_depth 32

def map (f : M →ₗ P) (g : N →ₗ Q) : M ⊗ N →ₗ P ⊗ Q :=
lift $ comp₁ (comp₂ (mk _ _ _) g) f

@[simp] theorem map_tmul (f : M →ₗ P) (g : N →ₗ Q) (m : M) (n : N) :
  map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
rfl

def congr (f : M ≃ₗ P) (g : N ≃ₗ Q) : M ⊗ N ≃ₗ P ⊗ Q :=
linear_equiv.of_linear (map f g) (map f.symm g.symm)
  (lift.ext' $ bilinear_map.ext $ λ m n, by simp; simp only [linear_equiv.apply_symm_apply])
  (lift.ext' $ bilinear_map.ext $ λ m n, by simp; simp only [linear_equiv.symm_apply_apply])

end tensor_product
